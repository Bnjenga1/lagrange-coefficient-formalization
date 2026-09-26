FROM ghcr.io/leanprover-community/mathlib4/lean:2026-08-30@sha256:ad7d671404b347b74e6ec2d5e4088b6afb5d124c5c47f075e323a5294707ea9b

USER root
RUN apt-get update && apt-get install -y --no-install-recommends python3 python3-pip && rm -rf /var/lib/apt/lists/*
RUN python3 -m pip install --no-cache-dir pytest==8.4.1 pytest-json-ctrf==0.3.5 --break-system-packages
COPY . /tests/
RUN mkdir -p /app /logs/verifier /mathlib/Submission && chown -R lean:lean /app /logs/verifier /mathlib/Submission
USER lean

ENTRYPOINT []
