FROM ubuntu:22.04

ENV UID=1000
ENV GID=1000
ENV USER=ubuntu

WORKDIR /tmp
COPY requirements.txt .

SHELL ["/bin/bash", "-c"]

RUN apt-get clean \
    && apt-get update \
    && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    build-essential \
    clang-format cmake gcc-11 g++-11 gdb \
    git \
    lcov \
    libfmt-dev \
    libpython3-dev \
    libspdlog-dev \
    locales \
    ninja-build \
    packaging-dev \
    python3-pip \
    python3-venv \
    ruby \
    software-properties-common \
    tmux \
    uncrustify \
    && pip3 install -r requirements.txt \
    && wget --progress=dot:giga https://github.com/danmar/cppcheck/archive/2.6.tar.gz \
    && tar xvzf 2.6.tar.gz \
    && mkdir cppcheck-2.6/build \
    && cd cppcheck-2.6/build \
    && cmake .. -GNinja \
    && ninja \
    && ninja install \
    && groupadd $USER -g $GID \
    && adduser $USER --gid $UID --uid 1000 \
    && apt-get clean \
    && rm -rf /var/lib/apt/lists/* \
    && locale-gen en_US.UTF-8 \
    && echo "${USER} ALL=(ALL) NOPASSWD: ALL" >> /etc/sudoers


USER $USER

RUN wget -qO - https://sh.rustup.rs | sh -s -- --no-modify-path -y

ENV PATH="/home/${USER}/.cargo/bin:${PATH}"

RUN rustup component add rustfmt clippy
