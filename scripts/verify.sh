#!/usr/bin/env bash
# Run from any working directory. All generated files stay in a fresh directory.
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

sha256sum --check --quiet verification/records/proof.sha256
python3 verify.py median11_25.json
python3 verification/tests/witness.py
python3 scripts/draw-witness.py > "$tmp/witness.svg"
cmp paper/figures/network.svg "$tmp/witness.svg"
python3 verify.py
python3 -m verification.tests.corruption
python3 verification/tests/audit_small.py
python3 verification/tests/structure.py

c++ -std=c++20 -O2 -Wall -Wextra -Wpedantic -Werror \
  verification/independent/check.cpp -lz -o "$tmp/check"
c++ -std=c++20 -O2 -Wall -Wextra -Wpedantic -Werror \
  verification/tests/backward.cpp -o "$tmp/backward"
"$tmp/backward" > "$tmp/ranks"
python3 -O check_certificate.py > "$tmp/python.log"
"$tmp/check" certificate > "$tmp/cpp.log"
diff -u "$tmp/python.log" "$tmp/cpp.log"
cat "$tmp/cpp.log"
python3 verification/tests/mutations.py "$tmp/check"

python3 lower.py --output "$tmp/rebuilt" > "$tmp/generator.log"
diff -u verification/records/bounds.jsonl "$tmp/generator.log"
python3 verification/tests/compare.py "$tmp/rebuilt" "$tmp/ranks"
"$tmp/check" "$tmp/rebuilt" > "$tmp/rebuilt.log"
diff -u "$tmp/cpp.log" "$tmp/rebuilt.log"
