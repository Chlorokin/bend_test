#!/usr/bin/env bash
# Start a fresh single-replica TigerBeetle and the app. The data file is
# reformatted on every start: the Bend model begins at opening day, so the
# database must too. Ctrl-C stops both.
set -euo pipefail
cd "$(dirname "$0")/.."

[ -x .tools/tigerbeetle ] || ./scripts/setup.sh

TB_PORT=${TB_PORT:-3001}
export PORT=${PORT:-3000}
export TB_ADDRESS=$TB_PORT

mkdir -p data
rm -f data/0_0.tigerbeetle
.tools/tigerbeetle format --cluster=0 --replica=0 --replica-count=1 --development data/0_0.tigerbeetle 2>/dev/null
.tools/tigerbeetle start --addresses="$TB_PORT" --development data/0_0.tigerbeetle > data/tigerbeetle.log 2>&1 &
TB_PID=$!
trap 'kill $TB_PID 2>/dev/null || true' EXIT INT TERM

bun server/server.ts
