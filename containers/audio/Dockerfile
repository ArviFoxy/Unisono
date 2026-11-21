# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Shared container for PipeWire and ALSA integration tests: Arch Linux with
# packages from a pinned snapshot so every run gets the same PipeWire (1.6),
# WirePlumber, ALSA library, and repository Rust toolchain.
FROM docker.io/library/archlinux:base-devel@sha256:fa2d4ce3310ddd90a4208e5168be8ad367da5129af1245f38fd2d803bcbe3239

# The archive at times refuses a download; retry before failing the build.
RUN echo 'Server = https://archive.archlinux.org/repos/2026/11/15/$repo/os/$arch' \
        > /etc/pacman.d/mirrorlist \
    && for attempt in 1 2 3 4 5; do \
           pacman -Syyuu --noconfirm pipewire pipewire-alsa alsa-lib wireplumber clang rustup && break; \
           if [ "$attempt" = 5 ]; then exit 1; fi; \
           sleep 20; \
       done \
    && pacman -Scc --noconfirm

ENV RUSTUP_HOME=/opt/rustup HOME=/tmp
COPY rust-toolchain.toml /opt/toolchain/rust-toolchain.toml
RUN cd /opt/toolchain \
    && CARGO_HOME=/opt/cargo rustup toolchain install \
    && chmod -R a+rX /opt/rustup
