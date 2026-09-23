#!/usr/bin/env bash
# One-time setup: the Bend compiler (pinned), the TigerBeetle binary, and
# the npm dependencies. Needs git, curl, unzip and bun.
set -euo pipefail
cd "$(dirname "$0")/.."

BEND_COMMIT=ff7a40cc9070a34c78399ecd2bbe46a044ad9b4b   # Bend 2.0.25
TB_VERSION=0.17.9

command -v bun >/dev/null || { echo "bun is required: https://bun.sh"; exit 1; }

if [ ! -d .tools/bend ]; then
  echo "==> Bend ($BEND_COMMIT)"
  git clone -q https://github.com/bendlang/bend .tools/bend
  git -C .tools/bend checkout -q "$BEND_COMMIT"
fi

if [ ! -x .tools/tigerbeetle ]; then
  echo "==> TigerBeetle $TB_VERSION"
  case "$(uname -s)-$(uname -m)" in
    Linux-x86_64)  asset=tigerbeetle-x86_64-linux.zip ;;
    Linux-aarch64) asset=tigerbeetle-aarch64-linux.zip ;;
    Darwin-*)      asset=tigerbeetle-universal-macos.zip ;;
    *) echo "unsupported platform $(uname -s)-$(uname -m)"; exit 1 ;;
  esac
  mkdir -p .tools
  curl -fsSL -o .tools/tb.zip "https://github.com/tigerbeetle/tigerbeetle/releases/download/$TB_VERSION/$asset"
  unzip -o -q .tools/tb.zip -d .tools && rm .tools/tb.zip
  chmod +x .tools/tigerbeetle
fi

echo "==> npm packages"
bun install --silent

echo "==> checking the proofs"
bun .tools/bend/bend2/main.ts core/PROOF.bend

echo "Ready. Run ./scripts/dev.sh"
