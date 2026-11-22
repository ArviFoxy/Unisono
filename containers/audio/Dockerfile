# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at https://mozilla.org/MPL/2.0/.

# Shared container for the PipeWire and ALSA integration tests: Ubuntu 26.04
# LTS with PipeWire, WirePlumber, pipewire-alsa, the C development headers, and
# the Rust toolchain pinned in rust-toolchain.toml.
FROM docker.io/library/ubuntu:26.04@sha256:d66b366dac61b575bee2aef07e9c26e8070096fbe84a3d4d3eb0da069b5d76db

RUN export DEBIAN_FRONTEND=noninteractive \
    && apt-get -o Acquire::Retries=5 update \
    && apt-get -o Acquire::Retries=5 install -y --no-install-recommends \
        build-essential \
        ca-certificates \
        clang \
        curl \
        libasound2-dev \
        libclang-dev \
        libpipewire-0.3-dev \
        pipewire \
        pipewire-alsa \
        pipewire-bin \
        pkg-config \
        wireplumber \
    && rm -rf /var/lib/apt/lists/*

ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    PATH="/opt/cargo/bin:$PATH" \
    HOME=/tmp

RUN curl --proto '=https' --tlsv1.2 -sSf --retry 5 --retry-all-errors \
        https://sh.rustup.rs \
        | sh -s -- -y --no-modify-path --profile minimal --default-toolchain none \
    && chmod -R a+rX /opt/rustup /opt/cargo

COPY rust-toolchain.toml /opt/toolchain/rust-toolchain.toml
RUN cd /opt/toolchain \
    && rustup toolchain install \
    && chmod -R a+rX /opt/rustup /opt/cargo
