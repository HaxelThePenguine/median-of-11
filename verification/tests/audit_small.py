"""Independent breadth-first cross-check of the small cases, without certificate pruning."""
from itertools import combinations, permutations
from pathlib import Path
import json

def minimum(n, rank):
    start = tuple(tuple(x for x in range(1 << n) if x.bit_count() == w)
                  for w in (n-rank, n-rank+1))
    frontier, seen = {start}, {start}
    for cost in range(20):
        upcoming = set()
        for layers in frontier:
            for i in range(n):
                if all(x >> i & 1 == label for label, layer in enumerate(layers) for x in layer):
                    return cost
            for i, j in combinations(range(n), 2):
                swap = (1 << i) | (1 << j)
                state = tuple(tuple(sorted({x ^ swap if x >> i & 1 and not x >> j & 1 else x
                                           for x in layer})) for layer in layers)
                if state not in seen:
                    upcoming.add(state)
        seen.update(upcoming)
        frontier = upcoming
    raise RuntimeError("Search depth exceeded")

if __name__ == "__main__":
    claims = json.loads(Path("certificate/claims.json").read_text())
    for n, r, budget in claims:
        if n <= 5:
            value = minimum(n,r)
            if value != budget+1:
                raise ValueError((n,r,value,budget))
            print(f"n={n}, rank={r}, BFS optimum={value}")
    net = json.loads(Path("median11_25.json").read_text())
    # Six varying positions and five fixed distinct values, all eleven ranks represented.
    for perm in permutations(range(0,11,2)):
        data = list(perm) + list(range(1,11,2))
        for i,j in net:
            data[i],data[j] = min(data[i],data[j]),max(data[i],data[j])
        if data[5] != 5:
            raise ValueError(perm)
    print("720 distinct-value cases passed")
