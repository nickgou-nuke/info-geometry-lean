FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive
ENV ELAN_HOME=/opt/elan
ENV PATH=/opt/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin

RUN apt-get update \
  && apt-get install -y --no-install-recommends \
    bash \
    ca-certificates \
    curl \
    git \
    jq \
    python3 \
    python3-pip \
    nodejs \
    npm \
    build-essential \
  && if apt-cache show bubblewrap >/dev/null 2>&1; then apt-get install -y --no-install-recommends bubblewrap; fi \
  && rm -rf /var/lib/apt/lists/*

RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none \
  && elan toolchain install leanprover/lean4:v4.28.1 \
  && elan default leanprover/lean4:v4.28.1 \
  && lean --version | grep -E '^Lean \(version 4\.28\.1'

WORKDIR /workspace
