FROM rust:slim

RUN echo /etc/apt/sources.list << deb http://apt.llvm.org/bookworm/ llvm-toolchain-bookworm main
RUN wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key | tee /etc/apt/trusted.gpg.d/apt.llvm.org.asc

RUN apt-get update \
    && apt-get install -y --no-install-recommends libclang-19-dev wget make python3 \
        xz-utils python3-venv ninja-build bzip2 meson \
        pkg-config libglib2.0-dev git libslirp-dev \
    && rm -rf /var/lib/apt/lists/*

RUN cargo install cargo-binutils axconfig-gen cargo-axplat

COPY rust-toolchain.toml /rust-toolchain.toml

RUN rustc --version

RUN wget https://musl.cc/aarch64-linux-musl-cross.tgz \
    && wget https://musl.cc/riscv64-linux-musl-cross.tgz \
    && wget https://musl.cc/x86_64-linux-musl-cross.tgz \
    && wget https://github.com/LoongsonLab/oscomp-toolchains-for-oskernel/releases/download/loongarch64-linux-musl-cross-gcc-13.2.0/loongarch64-linux-musl-cross.tgz \
    && tar zxf aarch64-linux-musl-cross.tgz \
    && tar zxf riscv64-linux-musl-cross.tgz \
    && tar zxf x86_64-linux-musl-cross.tgz \
    && tar zxf loongarch64-linux-musl-cross.tgz \
    && rm -f *.tgz

RUN wget https://download.qemu.org/qemu-9.2.4.tar.xz \
    && tar xf qemu-9.2.4.tar.xz \
    && cd qemu-9.2.4 \
    && ./configure --prefix=/qemu-bin-9.2.4 \
        --target-list=loongarch64-softmmu,riscv64-softmmu,aarch64-softmmu,x86_64-softmmu \
        --enable-gcov --enable-debug --enable-slirp \
    && make -j$(nproc) \
    && make install
RUN rm -rf qemu-9.2.4 qemu-9.2.4.tar.xz

ENV PATH="/x86_64-linux-musl-cross/bin:/aarch64-linux-musl-cross/bin:/riscv64-linux-musl-cross/bin:/loongarch64-linux-musl-cross/bin:$PATH"
ENV PATH="/qemu-bin-9.2.4/bin:$PATH"
