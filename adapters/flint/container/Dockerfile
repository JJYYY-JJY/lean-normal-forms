# syntax=docker/dockerfile:1.7@sha256:a57df69d0ea827fb7266491f2813635de6f17269be881f696fbfdf2d83dda33e

FROM debian:13.1-slim@sha256:ae614fe11cb373155bf26b938154c34bed87aa701f2f55a4ef03f872e4314ab0

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install --yes --no-install-recommends \
        build-essential \
        ca-certificates \
        curl \
        file \
        m4 \
        python3 \
        xz-utils \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /src/lean-normal-forms

COPY adapters/flint/versions.env adapters/flint/versions.env
COPY scripts/BuildFlintAdapter.sh scripts/BuildFlintAdapter.sh

ADD --checksum=sha256:b95e2c7792f5eea4a1c8d2d42c4098434756832e57a094b295eb5dfdc9b4c36b \
    https://flintlib.org/download/flint-3.6.0.tar.gz \
    .lake/externals/downloads/flint-3.6.0.tar.gz
ADD --checksum=sha256:a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898 \
    https://gmplib.org/download/gmp/gmp-6.3.0.tar.xz \
    .lake/externals/downloads/gmp-6.3.0.tar.xz
ADD --checksum=sha256:b67ba0383ef7e8a8563734e2e889ef5ec3c3b898a01d00fa0a6869ad81c6ce01 \
    https://www.mpfr.org/mpfr-current/mpfr-4.2.2.tar.xz \
    .lake/externals/downloads/mpfr-4.2.2.tar.xz

RUN NORMALFORMS_FLINT_LIBRARIES_ONLY=1 scripts/BuildFlintAdapter.sh

COPY adapters/flint/c adapters/flint/c
COPY adapters/flint/python adapters/flint/python
COPY adapters/flint/README.md adapters/flint/README.md
COPY adapters/flint/REBUILD.md adapters/flint/REBUILD.md
COPY adapters/flint/SOURCES.sha256 adapters/flint/SOURCES.sha256

RUN scripts/BuildFlintAdapter.sh

ENV PATH="/src/lean-normal-forms/.lake/externals/prefix/bin:${PATH}"
ENV LD_LIBRARY_PATH="/src/lean-normal-forms/.lake/externals/prefix/lib"

CMD ["python3", "adapters/flint/python/normalforms_flint.py", "--help"]
