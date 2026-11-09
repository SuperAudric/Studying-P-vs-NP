#!/usr/bin/env bash
# Smoke test for the dev container toolchain (docs/plan.md section 8).
# Run after a container rebuild, from anywhere:  bash scripts/smoke.sh
# Exits non-zero at the first failing step.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

step() { printf '\n== %s\n' "$*"; }

step "dotnet --version"
dotnet --version

step "cadical --version"
cadical --version

step "kissat --version"
kissat --version

step "drat-trim on PATH"
command -v drat-trim

step "drat-trim verifies a CaDiCaL DRAT proof of a tiny UNSAT formula"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
printf 'p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n' > "$tmp/unsat.cnf"
# CaDiCaL exits 20 for UNSAT; anything else is a failure here.
set +e
cadical -q "$tmp/unsat.cnf" "$tmp/proof.drat"
rc=$?
set -e
if [ "$rc" -ne 20 ]; then
    echo "ERROR: cadical exited with status $rc, expected 20 (UNSAT)"; exit 1
fi
# drat-trim prefixes every output line with a carriage return; strip it before matching.
drat-trim "$tmp/unsat.cnf" "$tmp/proof.drat" | tr -d '\r' | tee "$tmp/drat.log" | tail -n 2
grep -q '^s VERIFIED' "$tmp/drat.log"

step "python venv: pysat and networkx importable"
command -v python
python -c "import pysat, networkx; print('pysat', pysat.__version__, '| networkx', networkx.__version__)"

step "scripts/check_tiny.py"
python scripts/check_tiny.py

step "scripts/check_witness.py"
python scripts/check_witness.py

printf '\nSMOKE OK\n'
