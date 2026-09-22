#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

if ! command -v rocq >/dev/null 2>&1; then
  if command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch=rocq-system --set-switch 2>/dev/null || true)"
  fi
fi

if ! command -v rocq >/dev/null 2>&1; then
  echo "rocq not on PATH; run: eval \$(opam env --switch=rocq-system --set-switch)" >&2
  exit 1
fi

dune build
./scripts/audit.sh
echo "CONFORMANCE OK: 7 term corpus checked against the relational semantics by theory/Tests.v"
echo "DIFFTEST OK"
