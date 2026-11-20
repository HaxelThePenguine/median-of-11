#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/generate-lean-witness.py --check
python3 scripts/generate-lean-certificate.py --max-width 6 \
  --output formal/Median11/SmallData.lean --check
cd formal
lean --version
lake clean
lake build
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -t=0 Audit.lean | tee "$report"
python3 - "$report" <<'PY'
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = Path(sys.argv[1]).read_text().splitlines()
if len(lines) != 25:
    raise SystemExit("unexpected number of axiom reports")
for line in lines:
    result = re.fullmatch(r"'Median11\.\w+' (?:does not depend on any axioms|depends on axioms: \[([^\]]+)\])", line)
    if result is None or (result[1] and set(result[1].split(", ")) - allowed):
        raise SystemExit(f"unexpected axiom output: {line}")
PY
