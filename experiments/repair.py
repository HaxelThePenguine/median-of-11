"""Build exhaustive radius-three repairs around each annealing endpoint."""
import json
from itertools import combinations
from pathlib import Path
edges=list(combinations(range(11),2))
for size in [25,26]:
    line=Path(f'anneal{size}.log').read_text().splitlines()[-1]
    net=json.loads(line.split(maxsplit=3)[-1])
    ids=[edges.index(tuple(e))+1 for e in net]
    for slots in combinations(range(24),3):
        free=set(slots)
        print(f"repair{size}-"+'-'.join(map(str,slots)),24,
              *[-1 if k in free else e for k,e in enumerate(ids)])
