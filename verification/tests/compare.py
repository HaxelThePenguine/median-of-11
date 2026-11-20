"""Compare regenerated proof streams, the reverse BFS, witness size and diagram."""
import gzip
import json
from pathlib import Path
import sys

rebuilt, bfs_log = map(Path, sys.argv[1:])
original = Path("certificate")
claims = json.loads((original / "claims.json").read_bytes())
if (original / "claims.json").read_bytes() != (rebuilt / "claims.json").read_bytes():
    raise ValueError("manifest mismatch")
if {p.name for p in original.iterdir()} != {p.name for p in rebuilt.iterdir()}:
    raise ValueError("certificate file set mismatch")
for p in original.glob("*.gz"):
    if gzip.decompress(p.read_bytes()) != gzip.decompress((rebuilt / p.name).read_bytes()):
        raise ValueError(f"proof stream differs: {p.name}")

expected = {}
for n, r, budget in claims:
    if n <= 6:
        expected[n, r] = expected[n, n+1-r] = budget+1
rows = [tuple(map(int, line.split())) for line in bfs_log.read_text().splitlines()]
if sorted(rows) != sorted((n, r, cost) for (n, r), cost in expected.items()):
    raise ValueError("exact reverse BFS disagrees")

gates = json.loads(Path("median11_25.json").read_bytes())
if len(gates) != 25:
    raise ValueError("wrong upper-bound witness size")
drawing = "".join(r"\gate{%d}{%d}{%d}" % (k,i,j) + "\n" for k,(i,j) in enumerate(gates,1))
if Path("paper/figures/gates.tex").read_text() != drawing:
    raise ValueError("figure disagrees with witness")
print("26 regenerated streams, 20 exact ranks, witness length and figure agree.")
