#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
: "${SOURCE_DATE_EPOCH:=1795132800}"
export SOURCE_DATE_EPOCH FORCE_SOURCE_DATE=1
(
  cd paper
  latexmk -C main.tex >/dev/null
  rm -f main.bbl
  latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
  if grep -E 'undefined references|undefined citations|Citation .* undefined|Reference .* undefined|Overfull \\[hv]box|destination with the same identifier' main.log; then
    exit 1
  fi
)
(
  cd review
  latexmk -C summary.tex >/dev/null
  latexmk -pdf -interaction=nonstopmode -halt-on-error summary.tex
  if grep -E 'Overfull \\[hv]box' summary.log; then
    exit 1
  fi
)
