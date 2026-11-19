"""Stand-alone checker for the finite exclusion proof (Python standard library).

The states are explicit sets of integers, and the extreme traces follow each
original input separately. The checker imports no part of the proof generator.
Run without python -O: explicit checks below also work under -O.
"""
import argparse
import gzip
import json
from functools import lru_cache
from itertools import combinations
from pathlib import Path

def require(condition,message):
    if not condition:
        raise ValueError(message)

def check(n,r,budget,data,established):
    masks=range(1<<n)
    choices=list(combinations(range(n),2))
    allowed={}
    for sign,rank_after in [(0,r-1),(1,r)]:
        rank=min(rank_after,n-rank_after)
        lower=established.get((n-1,rank),0) if 1<=rank_after<n else 0
        allowed[sign]=budget-lower
    start=tuple(frozenset(x for x in masks if x.bit_count()==weight)
                for weight in (n-r,n-r+1))
    memo={}
    codes=iter(data)
    visited=0

    @lru_cache(maxsize=2048)
    def variations(layer):
        representative=next(iter(layer))
        varies=0
        for x in layer: varies |= x^representative
        return varies

    @lru_cache(maxsize=2048)
    def columns(layer):
        return tuple(sum((x>>i)&1 for x in layer) for i in range(n))

    @lru_cache(maxsize=4096)
    def perm_table(order):
        return tuple(sum(((x>>i)&1)<<dst for dst,i in enumerate(order)) for x in masks)

    def key_for(layers):
        a,b=map(columns,layers)
        order=tuple(sorted(range(n),key=lambda i:(a[i],b[i])))
        perm=perm_table(order)
        return tuple(frozenset(perm[x] for x in layer) for layer in layers)

    @lru_cache(maxsize=8192)
    def transform(layer,i,j):
        a,b=1<<i,1<<j
        return frozenset(x^a^b if x&a and not x&b else x for x in layer)

    def visit(layers,trace,k):
        nonlocal visited
        visited+=1
        code=next(codes,None)
        require(code in (0,1,2,3),"invalid or missing proof node")
        # Directly check whether a wire already realises the threshold.
        varying=variations(layers[0])|variations(layers[1])
        u,v=map(next,map(iter,layers))
        require(not ((~varying)&(~u)&v),"prefix already computes the order statistic")
        if code==1:
            require(max(map(len,layers))>2**k,"invalid image-size lower bound")
            return
        if code==3:
            require(any(d==allowed[sign] and varying&(1<<wire)
                        for sign in [0,1] for wire,d in trace[sign]),"invalid frozen wire")
            return
        key=key_for(layers)
        if code==2:
            require(memo.get(key,-1)>=k,"unproven reference")
            return
        require(k>0,"invalid expansion at zero remaining budget")
        for i,j in choices:
            # An unconditional exchange, like an identity, is only a wire
            # renaming on these layers. Check this in both directions.
            touched=[((x>>i)&1,(x>>j)&1) for layer in layers for x in layer]
            if (1,0) not in touched or (0,1) not in touched:
                continue
            new_trace=tuple(tuple(((i if sign==0 else j),d+1) if w in (i,j) else (w,d)
                                  for w,d in trace[sign]) for sign in [0,1])
            if any(any(d>allowed[sign] for _,d in new_trace[sign]) for sign in [0,1]):
                continue
            visit(tuple(transform(layer,i,j) for layer in layers),new_trace,k-1)
        memo[key]=max(k,memo.get(key,-1))

    initial=tuple((i,0) for i in range(n))
    visit(start,(initial,initial),budget)
    require(next(codes,None) is None,"unconsumed proof nodes")
    return visited

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('directory',nargs='?',type=Path,default=Path('certificate'))
    args=p.parse_args()
    known={}
    total=0
    for item in json.loads((args.directory/'claims.json').read_text()):
        n,r,budget=item
        require(n>=2 and 1<=r<=n and budget>=0,"invalid claim")
        proof=gzip.decompress((args.directory/f'{n}-{r}.gz').read_bytes())
        count=check(n,r,budget,proof,known)
        known[n,min(r,n+1-r)]=budget+1
        total+=count
        print(f'checked n={n} rank={r} lower={budget+1} nodes={count}',flush=True)
    require(known.get((11,6),0)>=25,"missing requested conclusion")
    print(f'ACCEPT median(11) >= 25; {total} proof nodes')
