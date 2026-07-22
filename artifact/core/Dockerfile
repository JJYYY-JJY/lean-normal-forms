# syntax=docker/dockerfile:1.7@sha256:a57df69d0ea827fb7266491f2813635de6f17269be881f696fbfdf2d83dda33e

FROM debian:13.1-slim@sha256:ae614fe11cb373155bf26b938154c34bed87aa701f2f55a4ef03f872e4314ab0

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        git \
        python3 \
        ripgrep \
        zstd \
    && rm -rf /var/lib/apt/lists/*

ADD --checksum=sha256:fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516 \
    https://github.com/leanprover/lean4/releases/download/v4.32.0/lean-4.32.0-linux.tar.zst \
    /tmp/lean-4.32.0-linux.tar.zst

RUN tar --use-compress-program=unzstd \
      -xf /tmp/lean-4.32.0-linux.tar.zst \
      -C /opt \
    && rm /tmp/lean-4.32.0-linux.tar.zst

ENV PATH="/opt/lean-4.32.0-linux/bin:${PATH}"

WORKDIR /src/lean-normal-forms
COPY lean-toolchain lakefile.toml lake-manifest.json ./

RUN lean --version \
    && lake --version \
    && lake exe cache get

# Keep verifier-only tools below the Lake dependency layer so changes to
# the audit harness do not invalidate the pinned mathlib cache.
RUN apt-get update \
    && apt-get install --yes --no-install-recommends time \
    && rm -rf /var/lib/apt/lists/*

COPY . .

RUN scripts/verify.sh core

CMD ["scripts/verify.sh", "core"]
