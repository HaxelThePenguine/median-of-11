import json
from itertools import combinations
from synth import SEEDS,windows,reordered,jobs
edges=list(combinations(range(11),2))
def emit(label,net):
    print(label,len(net),*[(-1 if p is None else edges.index(tuple(p))+1) for p in net])
for mode in ('control','small','wide'):
    for label,t in jobs(mode):
        emit(label,t)
for key,net in json.loads(SEEDS.read_text()).items():
    if not key.startswith('11'):
        continue
    for order,seed in [('original',net),('reordered',reordered(net))]:
        # Each contiguous window leaves five arbitrary comparators.
        k=5+len(seed)-24
        for pos in range(len(seed)-k+1):
            emit(f'{key}-{order}-five-{pos}',windows(seed,[(pos,k,5)]))
