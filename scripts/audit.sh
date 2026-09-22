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

fail=0

echo "== forbidden tokens =="
while IFS= read -r -d '' f; do
  if grep -nE '\b(Admitted|admit|Axiom|Conjecture|native_compute)\b|TODO|FIXME|XXX' "$f"; then
    echo "forbidden token in $f" >&2
    fail=1
  fi
done < <(find theory -name '*.v' -print0 2>/dev/null)

echo "== forbidden Parameter =="
while IFS= read -r -d '' f; do
  if grep -nE '^[[:space:]]*Parameter[[:space:]]' "$f"; then
    echo "forbidden Parameter in $f" >&2
    fail=1
  fi
done < <(find theory -name '*.v' -print0 2>/dev/null)

echo "== Print Assumptions =="
mkdir -p /tmp/opencode/audit
out="$(rocq compile -o /tmp/opencode/audit/ExecReducer.vo theory/ExecReducer.v 2>&1 || true)"
echo "$out"
if echo "$out" | grep -q "Axioms:"; then
  echo "unexpected axioms reported" >&2
  fail=1
fi
if ! echo "$out" | grep -q "Closed under the global context"; then
  echo "no Closed-under-global-context report found" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "AUDIT FAIL"
  exit 1
fi
echo "AUDIT OK"
