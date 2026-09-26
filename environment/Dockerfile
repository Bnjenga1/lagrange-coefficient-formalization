FROM ghcr.io/leanprover-community/mathlib4/lean:2026-08-30@sha256:ad7d671404b347b74e6ec2d5e4088b6afb5d124c5c47f075e323a5294707ea9b

USER root
RUN mkdir -p /app && chown -R lean:lean /app
USER lean

WORKDIR /app
RUN lake +leanprover-community/mathlib4:lean-toolchain new mathproject math

WORKDIR /app/mathproject
RUN lake exe cache get

ENTRYPOINT []
CMD ["sleep", "infinity"]
