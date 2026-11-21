# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# The container that the tests against PipeWire run in: Arch Linux with the
# packages of a set day, so that every run has the same PipeWire (1.6) and
# WirePlumber, and the Rust toolchain of the repository.
FROM docker.io/library/archlinux:base-devel@sha256:fa2d4ce3310ddd90a4208e5168be8ad367da5129af1245f38fd2d803bcbe3239

RUN echo 'Server = https://archive.archlinux.org/repos/2026/11/15/$repo/os/$arch' \
        > /etc/pacman.d/mirrorlist \
    && pacman -Syyuu --noconfirm pipewire wireplumber clang rustup \
    && pacman -Scc --noconfirm

ENV RUSTUP_HOME=/opt/rustup HOME=/tmp
COPY rust-toolchain.toml /opt/toolchain/rust-toolchain.toml
RUN cd /opt/toolchain \
    && CARGO_HOME=/opt/cargo rustup toolchain install \
    && chmod -R a+rX /opt/rustup
