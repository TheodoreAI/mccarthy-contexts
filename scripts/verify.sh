#!/bin/bash
# Full verification gate: build, hole scan, axiom audit.
# Exits non-zero if anything fails, so CI or an agent can branch on it.
set -u
cd "$(dirname "$0")/.." || exit 1
fail=0

echo "== 1. build =="
out=$(lake build 2>&1)
if echo "$out" | grep -q 'error:'; then
  echo "$out" | grep 'error:' | head -20
  fail=1
else
  echo "$out" | tail -1
fi

echo
echo "== 2. sorry / admit / native_decide in sources =="
hits=$(grep -rnE '\bsorry\b|\badmit\b|native_decide' Definitions Solutions Development 2>/dev/null | grep -v '^\s*--')
if [ -n "$hits" ]; then echo "$hits"; fail=1; else echo "none"; fi

echo
echo "== 3. axiom audit (no sorryAx) =="
if echo "$out" | grep -q 'sorryAx'; then
  echo "$out" | grep 'sorryAx'; fail=1
else
  echo "no sorryAx reported"
  echo "$out" | grep -c 'depends on axioms\|does not depend on any axioms' | sed 's/^/  audited declarations: /'
fi

echo
[ $fail -eq 0 ] && echo "VERIFIED" || echo "FAILED"
exit $fail
