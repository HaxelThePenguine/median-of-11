#!/usr/bin/env bash
# Full executable comparison. Its stdout is not imported as a Lean proof.
set -euo pipefail
cd "$(dirname "$0")/.."
"${PYTHON:-python3}" scripts/generate-lean-certificate.py
cd formal
lake build Median11.CertificateData >&2
lake env lean --run VerifyArchive.lean
