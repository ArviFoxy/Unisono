// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at https://mozilla.org/MPL/2.0/.

//! Fixed-point spanning-tree-anchored `LDL^T` Graph-Laplacian BLUE solver.
//!
//! Given directed pairwise clock-offset observations `y_e = phi(to) - phi(from)`
//! with positive variances `variance_ns2` on a host graph (`0` = stream sender,
//! `1..host_count` = receivers), this module computes the Best Linear Unbiased
//! Estimator (BLUE, Thomson's principle) pinned at `phi(0) = 0`, together with
//! the exact correlated common-mode variance `(1 / R^2) 1^T L_red^{-1} 1` and
//! the self differential-mode variance `(e_r - 1/R)^T L_red^{-1} (e_r - 1/R)`.
//!
//! Algorithm (zero floating point, zero heap allocation, zero square roots):
//! 1. **BFS spanning-tree anchor from sender `0`:** finds the exact connected
//!    component reachable from `0` (excluding partitioned/isolated nodes) and
//!    constructs baseline offsets `tree[v]`. Subtracting `tree[to] - tree[from]`
//!    from each edge measurement reduces all cycle residuals to microseconds,
//!    eliminates cancellation on 64-bit clock epochs, and recovers `phi` with
//!    zero rounding error when measurements are noiseless.
//! 2. **Scale-invariant weight normalization:** normalizes edge weights to
//!    `w_e = clamp(floor(v_min * 2^32 / var_e), 1, 2^32)` so the normalized
//!    reduced Laplacian `L_tilde` has uniform Q32 bit scale across any variance
//!    magnitude (covering variance ratios up to `2^32`).
//! 3. **Square-root-free `LDL^T` factorization:** because `L_tilde` is a
//!    symmetric M-matrix on the sender-connected component, no pivoting is
//!    required, every off-diagonal of unit lower-triangular `L` lies in
//!    `[-1, 0]` (exact Q32 `i64`), and every diagonal pivot `D_i > 0`.
//! 4. **Three triangular solves:** solves for the residual offset vector
//!    `delta_phi`, the common-mode variance vector `L_tilde z_com = 1`, and
//!    the self differential variance vector `L_tilde z_diff = e_self - 1/m`.

use crate::fixed::{div_floor_wide, saturate, saturating_mul_i128, scale_div_pow2};

/// Maximum number of receivers in the host graph.
pub const MAX_PEERS: usize = 16;

/// Maximum number of hosts (`1` sender at index `0` + [`MAX_PEERS`] receivers).
pub const MAX_HOSTS: usize = 17;

/// Maximum number of directed edge observations (`17 * 16 / 2` undirected).
pub const MAX_EDGES: usize = 136;

/// Flattened reduced-Laplacian matrix size (`MAX_PEERS * MAX_PEERS`).
pub const MAX_MAT: usize = 256;

/// `2^32` (unity in Q32).
const Q32_ONE: i128 = 4_294_967_296;

/// Maximum residual offset clamped during assembly (`10 s`), preventing `i128`
/// overflow on pathological inputs.
const MAX_RESIDUAL_NS: i128 = 10_000_000_000;

/// Maximum output variance in square nanoseconds (`(1 s)^2`).
const MAX_OUT_VAR_NS2: u64 = 1_000_000_000_000_000_000;

/// One directed pairwise offset observation `clock(to) - clock(from)`.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct EdgeObs {
    /// Source host index (`0` = sender, `1..MAX_HOSTS` = receivers).
    pub from: usize,
    /// Destination host index (`0` = sender, `1..MAX_HOSTS` = receivers).
    pub to: usize,
    /// Measured offset `clock(to) - clock(from)`, in nanoseconds.
    pub offset_ns: i64,
    /// Estimated measurement variance, in square nanoseconds (`> 0`).
    pub variance_ns2: u64,
}

impl EdgeObs {
    /// Empty placeholder observation.
    pub const ZERO: EdgeObs = EdgeObs {
        from: 0,
        to: 0,
        offset_ns: 0,
        variance_ns2: 0,
    };
}

/// Output of [`solve_blue`] for one receiver's local view of the host graph.
#[derive(Clone, Copy, PartialEq, Eq)]
#[cfg_attr(not(translating), derive(Debug))]
pub struct BlueResult {
    /// Number of receivers (including `self_idx`) reachable from sender `0`.
    /// `0` if `self_idx` is not reachable from the sender.
    pub active_count: usize,
    /// Whether each host `0..MAX_HOSTS` lies in the sender's connected
    /// component.
    pub reachable: [bool; MAX_HOSTS],
    /// Estimated offset `clock(h) - clock(0)` (host minus sender) for each
    /// reachable host, in nanoseconds.
    pub offsets_ns: [i64; MAX_HOSTS],
    /// Mean offset `mean_r (clock(0) - clock(r))` (sender minus fleet mean)
    /// across all reachable receivers, in nanoseconds.
    pub common_offset_ns: i64,
    /// Exact correlated variance of `common_offset_ns`, in square nanoseconds.
    pub common_var_ns2: u64,
    /// Differential offset `fleet_mean_clock - clock(self)` =
    /// `(clock(0) - clock(self)) - common_offset_ns`, in nanoseconds.
    pub self_diff_offset_ns: i64,
    /// Exact variance of `self_diff_offset_ns`, in square nanoseconds.
    pub self_diff_var_ns2: u64,
}

impl BlueResult {
    /// Empty result returned when the receiver cannot reach the sender.
    pub const EMPTY: BlueResult = BlueResult {
        active_count: 0,
        reachable: [false; MAX_HOSTS],
        offsets_ns: [0; MAX_HOSTS],
        common_offset_ns: 0,
        common_var_ns2: 0,
        self_diff_offset_ns: 0,
        self_diff_var_ns2: 0,
    };
}

/// Safe `i128` clamp to `[-hi, hi]` for `hi >= 0`.
fn clamp_sym(x: i128, hi: i128) -> i128 {
    let lo = 0i128.wrapping_sub(hi);
    if x > hi {
        hi
    } else if x < lo {
        lo
    } else {
        x
    }
}

/// Helper to read `slice[idx]` with default `0`.
fn get_i128(slice: &[i128], idx: usize) -> i128 {
    match slice.get(idx) {
        Some(v) => *v,
        None => 0,
    }
}

/// Helper to read `slice[idx]` with default `0`.
fn get_i64(slice: &[i64], idx: usize) -> i64 {
    match slice.get(idx) {
        Some(v) => *v,
        None => 0,
    }
}

/// Helper to read `slice[idx]` with default `false`.
fn get_bool(slice: &[bool], idx: usize) -> bool {
    match slice.get(idx) {
        Some(v) => *v,
        None => false,
    }
}

/// Helper to read `slice[idx]` with default `0`.
fn get_usize(slice: &[usize], idx: usize) -> usize {
    match slice.get(idx) {
        Some(v) => *v,
        None => 0,
    }
}

/// Helper to add `delta` into `mat[row * dim + col]`.
fn mat_add(mat: &mut [i128; MAX_MAT], dim: usize, row: usize, col: usize, delta: i128) {
    let idx = row.wrapping_mul(dim).wrapping_add(col);
    if let Some(cell) = mat.get_mut(idx) {
        *cell = cell.saturating_add(delta);
    }
}

/// Helper to read `mat[row * dim + col]`.
fn mat_get(mat: &[i128; MAX_MAT], dim: usize, row: usize, col: usize) -> i128 {
    let idx = row.wrapping_mul(dim).wrapping_add(col);
    get_i128(mat, idx)
}

/// Solves `L D L^T x = rhs` for a `dim x dim` system where `l_q32` holds unit
/// lower-triangular `L` in Q32 and `d_q32` holds strictly positive pivots `D`
/// in Q32. `rhs` is in `Q32 * units` and the returned `x` is in `units`
/// (with `scale_shift` extra fractional bits if requested, `<= 32`).
#[allow(clippy::many_single_char_names)]
fn solve_ldlt(
    dim: usize,
    l_q32: &[i64; MAX_MAT],
    d_q32: &[i128; MAX_PEERS],
    rhs: &[i128; MAX_PEERS],
    scale_shift: u32,
) -> [i128; MAX_PEERS] {
    let mut y = [0i128; MAX_PEERS];
    // Forward substitution: `L y = rhs` (keeping `y` in same scale as `rhs`).
    let mut i = 0usize;
    while i < dim {
        let mut sum = get_i128(rhs, i);
        let mut j = 0usize;
        while j < i {
            let lij = get_i64(l_q32, i.wrapping_mul(dim).wrapping_add(j)) as i128;
            let yj = get_i128(&y, j);
            let term = saturating_mul_i128(lij, yj).wrapping_shr(32);
            sum = sum.saturating_sub(term);
            j = j.saturating_add(1);
        }
        if let Some(dst) = y.get_mut(i) {
            *dst = sum;
        }
        i = i.saturating_add(1);
    }

    // Diagonal divide: `z_i = floor(y_i * 2^scale_shift / D_i)`.
    let mut z = [0i128; MAX_PEERS];
    let mut k = 0usize;
    while k < dim {
        let dk = get_i128(d_q32, k);
        let yk = get_i128(&y, k);
        let zk = scale_div_pow2(yk, scale_shift, dk);
        if let Some(dst) = z.get_mut(k) {
            *dst = zk;
        }
        k = k.saturating_add(1);
    }

    // Back substitution: `L^T x = z`.
    let mut x = [0i128; MAX_PEERS];
    let mut rev = dim;
    while rev > 0 {
        rev = rev.wrapping_sub(1);
        let mut sum = get_i128(&z, rev);
        let mut j = rev.saturating_add(1);
        while j < dim {
            let lji = get_i64(l_q32, j.wrapping_mul(dim).wrapping_add(rev)) as i128;
            let xj = get_i128(&x, j);
            let term = saturating_mul_i128(lji, xj).wrapping_shr(32);
            sum = sum.saturating_sub(term);
            j = j.saturating_add(1);
        }
        if let Some(dst) = x.get_mut(rev) {
            *dst = sum;
        }
    }
    x
}

/// Computes `floor((a * b) / 2^32)` safely without intermediate `i128` overflow.
fn mul_shr32(a: i128, b: i128) -> i128 {
    if let Some(prod) = a.checked_mul(b) {
        return prod.wrapping_shr(32);
    }
    let hi = a.wrapping_shr(32);
    let lo = a & 4_294_967_295i128;
    let t1 = saturating_mul_i128(hi, b);
    let t2 = if let Some(p) = lo.checked_mul(b) {
        p.wrapping_shr(32)
    } else {
        let b_hi = b.wrapping_shr(32);
        let b_lo = b & 4_294_967_295i128;
        saturating_mul_i128(lo, b_hi).saturating_add(saturating_mul_i128(lo, b_lo).wrapping_shr(32))
    };
    t1.saturating_add(t2)
}

/// Converts a positive `i128` variance into a clamped `u64` in `[1, MAX_OUT_VAR_NS2]`.
#[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
fn clamp_out_var(v: i128) -> u64 {
    if v <= 1 {
        1
    } else if v > MAX_OUT_VAR_NS2 as i128 {
        MAX_OUT_VAR_NS2
    } else {
        v as u64
    }
}

/// Solves the Graph-Laplacian BLUE on `edges[..edge_count]` for a host graph of
/// `host_count <= MAX_HOSTS` hosts (sender = `0`), from the perspective of
/// receiver `self_idx` (`1 <= self_idx < host_count`).
///
/// Edge `e` encodes `clock(e.to) - clock(e.from) = e.offset_ns`. Note that
/// `BlueResult.common_offset_ns` and `BlueResult.self_diff_offset_ns` are
/// expressed in the receiver-side sign convention `sender - receiver` (i.e.
/// `-offsets_ns[r]`), matching [`crate::kalman::KalmanFilter`] and
/// [`crate::min_rtt::ntp_exchange`].
#[must_use]
#[allow(clippy::too_many_lines, clippy::many_single_char_names)]
pub fn solve_blue(
    host_count: usize,
    self_idx: usize,
    edges: &[EdgeObs],
    edge_count: usize,
) -> BlueResult {
    let hosts = if host_count > MAX_HOSTS {
        MAX_HOSTS
    } else {
        host_count
    };
    let n_edges = if edge_count > edges.len() {
        edges.len()
    } else {
        edge_count
    };
    if hosts < 2 || self_idx == 0 || self_idx >= hosts || n_edges == 0 {
        return BlueResult::EMPTY;
    }

    // Step 1: BFS spanning tree from sender `0` (also finds connected component).
    let mut reachable = [false; MAX_HOSTS];
    let mut tree_off = [0i64; MAX_HOSTS];
    let mut queue = [0usize; MAX_HOSTS];
    let mut q_head = 0usize;
    let mut q_tail = 1usize;
    if let Some(r0) = reachable.get_mut(0) {
        *r0 = true;
    }
    if let Some(q0) = queue.get_mut(0) {
        *q0 = 0;
    }
    while q_head < q_tail && q_head < MAX_HOSTS {
        let cur = get_usize(&queue, q_head);
        q_head = q_head.saturating_add(1);
        let cur_off = get_i64(&tree_off, cur);
        let mut e = 0usize;
        while e < n_edges {
            if let Some(edge) = edges.get(e)
                && edge.variance_ns2 > 0
                && edge.from < hosts
                && edge.to < hosts
                && edge.from != edge.to
            {
                if edge.from == cur && !get_bool(&reachable, edge.to) {
                    if let Some(r) = reachable.get_mut(edge.to) {
                        *r = true;
                    }
                    if let Some(t) = tree_off.get_mut(edge.to) {
                        *t = cur_off.saturating_add(edge.offset_ns);
                    }
                    if let Some(q) = queue.get_mut(q_tail) {
                        *q = edge.to;
                        q_tail = q_tail.saturating_add(1);
                    }
                } else if edge.to == cur && !get_bool(&reachable, edge.from) {
                    if let Some(r) = reachable.get_mut(edge.from) {
                        *r = true;
                    }
                    if let Some(t) = tree_off.get_mut(edge.from) {
                        *t = cur_off.saturating_sub(edge.offset_ns);
                    }
                    if let Some(q) = queue.get_mut(q_tail) {
                        *q = edge.from;
                        q_tail = q_tail.saturating_add(1);
                    }
                }
            }
            e = e.saturating_add(1);
        }
    }

    if !get_bool(&reachable, self_idx) {
        return BlueResult::EMPTY;
    }

    // Step 2: Map reachable non-sender hosts `1..hosts` into dense `0..dim`.
    let mut host_to_idx = [MAX_PEERS; MAX_HOSTS];
    let mut idx_to_host = [0usize; MAX_PEERS];
    let mut dim = 0usize;
    let mut h = 1usize;
    while h < hosts && dim < MAX_PEERS {
        if get_bool(&reachable, h) {
            if let Some(slot) = host_to_idx.get_mut(h) {
                *slot = dim;
            }
            if let Some(slot) = idx_to_host.get_mut(dim) {
                *slot = h;
            }
            dim = dim.saturating_add(1);
        }
        h = h.saturating_add(1);
    }
    let self_dense = get_usize(&host_to_idx, self_idx);
    if dim == 0 || self_dense >= dim {
        return BlueResult::EMPTY;
    }

    // Step 3: Find minimum variance `v_min` across active component edges.
    let mut v_min = 0u64;
    let mut e = 0usize;
    while e < n_edges {
        if let Some(edge) = edges.get(e)
            && edge.variance_ns2 > 0
            && edge.from < hosts
            && edge.to < hosts
            && edge.from != edge.to
            && get_bool(&reachable, edge.from)
            && get_bool(&reachable, edge.to)
            && (v_min == 0 || edge.variance_ns2 < v_min)
        {
            v_min = edge.variance_ns2;
        }
        e = e.saturating_add(1);
    }
    if v_min == 0 {
        return BlueResult::EMPTY;
    }

    // Step 4: Assemble normalized reduced Laplacian `mat` (Q32) and residual
    // RHS `rhs` (Q32 * ns).
    let mut mat = [0i128; MAX_MAT];
    let mut rhs = [0i128; MAX_PEERS];
    let mut e = 0usize;
    while e < n_edges {
        if let Some(edge) = edges.get(e)
            && edge.variance_ns2 > 0
            && edge.from < hosts
            && edge.to < hosts
            && edge.from != edge.to
            && get_bool(&reachable, edge.from)
            && get_bool(&reachable, edge.to)
        {
            let w_raw = scale_div_pow2(v_min as i128, 32, edge.variance_ns2 as i128);
            let w = if w_raw < 1 {
                1
            } else if w_raw > Q32_ONE {
                Q32_ONE
            } else {
                w_raw
            };
            // Residual `r = y_e - (tree[to] - tree[from])`.
            let tree_diff = (get_i64(&tree_off, edge.to) as i128)
                .wrapping_sub(get_i64(&tree_off, edge.from) as i128);
            let res = clamp_sym(
                (edge.offset_ns as i128).wrapping_sub(tree_diff),
                MAX_RESIDUAL_NS,
            );
            let wr = saturating_mul_i128(w, res);
            let u = get_usize(&host_to_idx, edge.from);
            let v = get_usize(&host_to_idx, edge.to);
            if edge.from != 0 && u < dim {
                mat_add(&mut mat, dim, u, u, w);
                if let Some(b) = rhs.get_mut(u) {
                    *b = b.saturating_sub(wr);
                }
            }
            if edge.to != 0 && v < dim {
                mat_add(&mut mat, dim, v, v, w);
                if let Some(b) = rhs.get_mut(v) {
                    *b = b.saturating_add(wr);
                }
            }
            if edge.from != 0 && edge.to != 0 && u < dim && v < dim {
                let neg_w = 0i128.wrapping_sub(w);
                mat_add(&mut mat, dim, u, v, neg_w);
                mat_add(&mut mat, dim, v, u, neg_w);
            }
        }
        e = e.saturating_add(1);
    }

    // Step 5: Square-root-free `L D L^T` factorization of SPD M-matrix `mat`.
    let mut l_q32 = [0i64; MAX_MAT];
    let mut d_q32 = [0i128; MAX_PEERS];
    let mut j = 0usize;
    while j < dim {
        let mut dj = mat_get(&mat, dim, j, j);
        let mut k = 0usize;
        while k < j {
            let ljk = get_i64(&l_q32, j.wrapping_mul(dim).wrapping_add(k)) as i128;
            let dk = get_i128(&d_q32, k);
            // `ljk` is in `[-2^32, 0]`, so `ljk * ljk >> 32` is in `[0, 2^32]`.
            let ljk_sq = ljk.wrapping_mul(ljk).wrapping_shr(32);
            let sub = saturating_mul_i128(ljk_sq, dk).wrapping_shr(32);
            dj = dj.saturating_sub(sub);
            k = k.saturating_add(1);
        }
        if dj <= 0 {
            // Connected graph guarantee makes `dj > 0` in exact arithmetic;
            // guard defensively against any degenerate input.
            return BlueResult::EMPTY;
        }
        if let Some(dst) = d_q32.get_mut(j) {
            *dst = dj;
        }
        if let Some(diag) = l_q32.get_mut(j.wrapping_mul(dim).wrapping_add(j)) {
            *diag = 4_294_967_296;
        }
        let mut i = j.saturating_add(1);
        while i < dim {
            let mut sum = mat_get(&mat, dim, i, j);
            let mut k2 = 0usize;
            while k2 < j {
                let lik = get_i64(&l_q32, i.wrapping_mul(dim).wrapping_add(k2)) as i128;
                let ljk = get_i64(&l_q32, j.wrapping_mul(dim).wrapping_add(k2)) as i128;
                let dk = get_i128(&d_q32, k2);
                let prod_l = lik.wrapping_mul(ljk).wrapping_shr(32);
                let sub = saturating_mul_i128(prod_l, dk).wrapping_shr(32);
                sum = sum.saturating_sub(sub);
                k2 = k2.saturating_add(1);
            }
            let lij = scale_div_pow2(sum, 32, dj);
            if let Some(dst) = l_q32.get_mut(i.wrapping_mul(dim).wrapping_add(j)) {
                *dst = saturate(lij);
            }
            i = i.saturating_add(1);
        }
        j = j.saturating_add(1);
    }

    // Step 6a: Solve `L_tilde * delta_phi = rhs` (`scale_shift = 0` because
    // both `rhs` and `d_q32` carry one factor of `2^32`).
    let delta_phi = solve_ldlt(dim, &l_q32, &d_q32, &rhs, 0);
    let mut offsets_ns = [0i64; MAX_HOSTS];
    let mut idx = 0usize;
    while idx < dim {
        let host = get_usize(&idx_to_host, idx);
        let base = get_i64(&tree_off, host) as i128;
        let d = get_i128(&delta_phi, idx);
        if let Some(slot) = offsets_ns.get_mut(host) {
            *slot = saturate(base.saturating_add(d));
        }
        idx = idx.saturating_add(1);
    }

    // Step 6b: Common-mode variance `(v_min / dim^2) * 1^T L_tilde^{-1} 1`.
    // Pass `rhs_ones` in Q32 (`1 * 2^32`) and `scale_shift = 32` so `z_com` is
    // returned in Q32 units (`L_tilde^{-1} 1 * 2^32`).
    let mut rhs_ones = [0i128; MAX_PEERS];
    let mut i_one = 0usize;
    while i_one < dim {
        if let Some(slot) = rhs_ones.get_mut(i_one) {
            *slot = Q32_ONE;
        }
        i_one = i_one.saturating_add(1);
    }
    let z_com = solve_ldlt(dim, &l_q32, &d_q32, &rhs_ones, 32);
    let mut sum_z_com = 0i128;
    let mut i_zc = 0usize;
    while i_zc < dim {
        sum_z_com = sum_z_com.saturating_add(get_i128(&z_com, i_zc));
        i_zc = i_zc.saturating_add(1);
    }
    // `sum_z_com` is `2^32 * 1^T L_tilde^{-1} 1`, and `L_red^{-1} = v_min * 2^32 * L_tilde^{-1}`
    // wait: `L_tilde = v_min * 2^32 * L_red`, so `L_red^{-1} = v_min * 2^32 * L_tilde^{-1}`.
    // Because `rhs_ones = 2^32 * 1` and `d_q32 = 2^32 * (L_tilde / 2^32)`, we have
    // `z_com = 2^32 * (L_tilde / 2^32)^{-1} 1 = 2^32 * (v_min * L_red)^{-1} 1`, so
    // `L_red^{-1} 1 = (v_min / 2^32) * z_com`.
    let dim_sq = (dim as i128).wrapping_mul(dim as i128);
    let total_com = mul_shr32(sum_z_com, v_min as i128);
    let common_var_ns2 = clamp_out_var(div_floor_wide(total_com, dim_sq));

    // Step 6c: Differential variance `(e_self - 1/dim)^T L_red^{-1} (e_self - 1/dim)`.
    // Put `rhs_diff[i] = Q32_ONE * (1 if i == self_dense else 0) - Q32_ONE / dim`.
    let mut rhs_diff = [0i128; MAX_PEERS];
    let inv_dim_q32 = div_floor_wide(Q32_ONE, dim as i128);
    let mut i_d = 0usize;
    while i_d < dim {
        let entry = if i_d == self_dense {
            Q32_ONE.wrapping_sub(inv_dim_q32)
        } else {
            0i128.wrapping_sub(inv_dim_q32)
        };
        if let Some(slot) = rhs_diff.get_mut(i_d) {
            *slot = entry;
        }
        i_d = i_d.saturating_add(1);
    }
    let z_diff = solve_ldlt(dim, &l_q32, &d_q32, &rhs_diff, 32);
    let mut quad_q32 = 0i128;
    let mut i_q = 0usize;
    while i_q < dim {
        let ri = get_i128(&rhs_diff, i_q);
        let zi = get_i128(&z_diff, i_q);
        quad_q32 = quad_q32.saturating_add(saturating_mul_i128(ri, zi).wrapping_shr(32));
        i_q = i_q.saturating_add(1);
    }
    let self_diff_var_ns2 = if dim <= 1 {
        0
    } else {
        clamp_out_var(mul_shr32(quad_q32, v_min as i128))
    };

    // Step 7: Receiver-side `sender - receiver` offsets = `-offsets_ns[r]`,
    // anchored safely around `self_theta` so summing never overflows `i64`.
    let self_theta = 0i128.wrapping_sub(get_i64(&offsets_ns, self_idx) as i128);
    let mut rel_sum = 0i128;
    let mut i_m = 0usize;
    while i_m < dim {
        let host = get_usize(&idx_to_host, i_m);
        let theta_h = 0i128.wrapping_sub(get_i64(&offsets_ns, host) as i128);
        rel_sum = rel_sum.saturating_add(theta_h.wrapping_sub(self_theta));
        i_m = i_m.saturating_add(1);
    }
    let delta_mean = div_floor_wide(rel_sum, dim as i128);
    let common_offset_ns = saturate(self_theta.saturating_add(delta_mean));
    let self_diff_offset_ns = saturate(0i128.wrapping_sub(delta_mean));

    BlueResult {
        active_count: dim,
        reachable,
        offsets_ns,
        common_offset_ns,
        common_var_ns2,
        self_diff_offset_ns,
        self_diff_var_ns2,
    }
}

#[cfg(test)]
mod tests {
    use super::{EdgeObs, solve_blue};

    #[test]
    fn noiseless_graph_with_huge_offsets_is_recovered_with_zero_error() {
        // Sender = 0; 3 receivers with arbitrary 64-bit offsets (days apart).
        let phi = [
            0i64,
            3_600_000_000_000,
            -86_400_000_000_000,
            1_000_000_000_123_456,
        ];
        let edges = [
            EdgeObs {
                from: 0,
                to: 1,
                offset_ns: phi[1] - phi[0],
                variance_ns2: 22_500_000_000, // (150 us)^2
            },
            EdgeObs {
                from: 0,
                to: 2,
                offset_ns: phi[2] - phi[0],
                variance_ns2: 22_500_000_000,
            },
            EdgeObs {
                from: 0,
                to: 3,
                offset_ns: phi[3] - phi[0],
                variance_ns2: 22_500_000_000,
            },
            EdgeObs {
                from: 1,
                to: 2,
                offset_ns: phi[2] - phi[1],
                variance_ns2: 25_000_000, // (5 us)^2
            },
            EdgeObs {
                from: 2,
                to: 3,
                offset_ns: phi[3] - phi[2],
                variance_ns2: 25_000_000,
            },
        ];
        let res = solve_blue(4, 1, &edges, edges.len());
        assert_eq!(res.active_count, 3);
        assert_eq!(res.offsets_ns[1], phi[1]);
        assert_eq!(res.offsets_ns[2], phi[2]);
        assert_eq!(res.offsets_ns[3], phi[3]);
    }

    #[test]
    fn degenerates_exactly_to_star_with_single_edge() {
        let edges = [EdgeObs {
            from: 0,
            to: 1,
            offset_ns: -42_000_000,
            variance_ns2: 100_000_000,
        }];
        let res = solve_blue(2, 1, &edges, 1);
        assert_eq!(res.active_count, 1);
        assert_eq!(res.offsets_ns[1], -42_000_000);
        // `common_offset_ns` = sender - receiver = -offsets_ns[1] = +42_000_000.
        assert_eq!(res.common_offset_ns, 42_000_000);
        assert_eq!(res.self_diff_offset_ns, 0);
        assert_eq!(res.common_var_ns2, 100_000_000);
        assert_eq!(res.self_diff_var_ns2, 0);
    }

    #[test]
    fn triangle_wifi_sender_wired_peer_matches_thomson_resistance_and_bias() {
        // Wi-Fi sender links: std = 150 us, var = 2.25e10 ns^2, opp asymmetry +/- 750 us.
        // Wired peer link: std = 5 us, var = 2.5e7 ns^2, bias = 0.
        // Theoretical BLUE pair bias = (25e6 / (45e9 + 25e6)) * 1_500_000 ns = 832.87 ns.
        let var_w = 22_500_000_000u64;
        let var_p = 25_000_000u64;
        let edges = [
            EdgeObs {
                from: 0,
                to: 1,
                offset_ns: 750_000,
                variance_ns2: var_w,
            },
            EdgeObs {
                from: 0,
                to: 2,
                offset_ns: -750_000,
                variance_ns2: var_w,
            },
            EdgeObs {
                from: 1,
                to: 2,
                offset_ns: 0,
                variance_ns2: var_p,
            },
        ];
        let r1 = solve_blue(3, 1, &edges, 3);
        let r2 = solve_blue(3, 2, &edges, 3);
        assert_eq!(r1.active_count, 2);
        let pair_diff = (r1.offsets_ns[1] - r1.offsets_ns[2]).abs();
        assert!(
            (pair_diff - 833).abs() <= 5,
            "expected ~833 ns BLUE bias, got {pair_diff}"
        );
        // Common variance = var_w / 2 = 11_250_000_000 ns^2.
        assert!(
            r1.common_var_ns2.abs_diff(var_w / 2) < 10_000,
            "common_var={}",
            r1.common_var_ns2
        );
        // Self differential variance = R_eff(1, 2) / 4 = (2*var_w*var_p / (2*var_w + var_p)) / 4
        // ~= 24_986_119 / 4 ~= 6_246_530 ns^2.
        let expected_diff_var = 6_246_530u64;
        assert!(
            r1.self_diff_var_ns2.abs_diff(expected_diff_var) < 1_000,
            "diff_var={}",
            r1.self_diff_var_ns2
        );
        // Opposite differential offsets sum to ~0.
        assert!((r1.self_diff_offset_ns + r2.self_diff_offset_ns).abs() <= 1);
    }

    #[test]
    fn complete_graph_k5_matches_exact_variances() {
        // K_5 (1 sender + 4 receivers), every edge has variance 1e8 ns^2.
        // Exact reduced Laplacian L_red = 5 I - 1 1^T, inverse = (I + 1 1^T) / 5.
        // Common variance = (1/16) * 1^T ((I + 1 1^T)/5) 1 = (1/16) * (4 + 16)/5 = 1/4 = 2.5e7 ns^2.
        // Wait: (1/4^2) * sum((I + J)/5) = (1/16) * (4 * 2/5 + 12 * 1/5) = (1/16) * 20/5 = 1/4!
        // Self diff variance = (e_r - 1/4 1)^T ((I + J)/5) (e_r - 1/4 1)
        // = (1/5) * ||e_r - 1/4 1||^2 = (1/5) * (3/4) = 3/20 = 1.5e7 ns^2.
        let v = 100_000_000u64;
        let mut edges = [EdgeObs::ZERO; 10];
        let mut idx = 0usize;
        for u in 0..5usize {
            for w in (u + 1)..5usize {
                edges[idx] = EdgeObs {
                    from: u,
                    to: w,
                    offset_ns: 0,
                    variance_ns2: v,
                };
                idx += 1;
            }
        }
        let res = solve_blue(5, 1, &edges, 10);
        assert_eq!(res.active_count, 4);
        assert!(
            res.common_var_ns2.abs_diff(25_000_000) < 100,
            "common_var={}",
            res.common_var_ns2
        );
        assert!(
            res.self_diff_var_ns2.abs_diff(15_000_000) < 100,
            "diff_var={}",
            res.self_diff_var_ns2
        );
    }
}
