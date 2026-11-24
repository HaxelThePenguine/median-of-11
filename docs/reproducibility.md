# Reproducing artifact version 1.0.3

Use Linux with Bash, standard GNU command-line tools, Python 3.10 or newer, a C++20 compiler with zlib development headers, and Lean 4.19.0 with Lake. PDF builds require pdfLaTeX, BibTeX, latexmk, TikZ and the LaTeX packages imported by the two manuscripts. On Debian or Ubuntu the LaTeX dependencies are provided by `latexmk`, `texlive-latex-extra`, `texlive-pictures` and `texlive-fonts-recommended`.

Run from the repository root:

```sh
bash scripts/verify.sh
bash scripts/verify-lean.sh
bash scripts/evaluate-lean-archive.sh
bash scripts/build-paper.sh
```

| Command | Expected result |
| --- | --- |
| `verify.sh` | 25 gates, zero errors on 2,048 binary and 177,147 ternary inputs, agreement between Python and C++ on all 26 exclusions, rejection of corrupted inputs, and regeneration of the proof streams. |
| `verify-lean.sh` | Clean Lake build and an axiom report for every archived exclusion and the three required theorem declarations. |
| `evaluate-lean-archive.sh` | 26 claim lines and the same final line as the Python and C++ readers. |
| `build-paper.sh` | Rebuilt `paper/main.pdf` and `review/summary.pdf`. The script checks the manuscript for unresolved references and overfull boxes. |

The three readers finish with `ACCEPT median(11) >= 25; 174008 proof nodes`. To compare the Lean executable output line for line with Python:

```sh
bash scripts/evaluate-lean-archive.sh > /tmp/median11-lean.txt
python3 -O check_certificate.py > /tmp/median11-python.txt
diff -u /tmp/median11-python.txt /tmp/median11-lean.txt
```

To inspect or regenerate the computational certificate independently:

```sh
sha256sum --check verification/records/proof.sha256
python3 verify.py median11_25.json
python3 check_certificate.py
scratch=$(mktemp -d)
python3 lower.py --output "$scratch/rebuilt"
python3 check_certificate.py "$scratch/rebuilt"
```

The distribution hashes bind the exact gzip bytes. The regeneration test compares the manifest and uncompressed opcode streams, which avoids dependence on the zlib version used to compress them. It also compares the [generator record](../verification/records/bounds.jsonl).

Use `bash scripts/archive.sh /path/to/output HEAD` to export a committed snapshot with a SHA-256 checksum. The archive name includes the version and full Git SHA. The committed [bibliography output](../paper/main.bbl) supports submission workflows that compile the LaTeX without running BibTeX.
