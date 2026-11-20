#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

python="${PYTHON:-python3}"
"$python" scripts/generate-lean-witness.py --check
"$python" scripts/generate-lean-certificate.py --max-width 8 --skip-claim 8-4 \
  --output formal/Median11/SmallData.lean --check
"$python" scripts/generate-lean-certificate.py --kernel-blocks formal/Median11/KernelData
cd formal
lean --version
lake clean
lake build
report=$(mktemp)
trap 'rm -f "$report"' EXIT
lake env lean -t=0 Audit.lean | tee "$report"
"$python" - "$report" <<'PY'
import re
import sys
from pathlib import Path

allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = Path(sys.argv[1]).read_text().splitlines()
names = []
for line in lines:
    result = re.fullmatch(
        r"'(Median11\.\w+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]+)\])", line
    )
    if result is None or (result[2] and set(result[2].split(", ")) - allowed):
        raise SystemExit(f"unexpected axiom output: {line}")
    names.append(result[1])
expected = re.findall(r"^#print axioms (Median11\.\w+)$", Path("Audit.lean").read_text(), re.M)
required = {f"Median11.{name}" for name in (
    "bound_7_3", "bound_7_4", "bound_8_3", "bound_8_4", "bound_8_5",
    "bound_9_4", "bound_9_5", "median11_lower", "median11_optimal",
)}
if names != expected or len(names) != len(set(names)) or not required.issubset(names):
    raise SystemExit("missing, duplicate or unexpected axiom reports")
PY
