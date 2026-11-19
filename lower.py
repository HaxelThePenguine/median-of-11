"""Finite lower-bound certificate by deleting an extreme input and exhaustive prefix search.
No SAT solver or third-party Python packages are needed. See PROOF.md.
"""
import argparse
import hashlib
import gzip
import json
from itertools import combinations
from pathlib import Path

# Proposed lower bounds. Each row is checked using already verified smaller rows.
ROWS={2:[1],3:[2,3],4:[3,5],5:[4,7,7],6:[5,9,10],
      7:[6,11,12,13],8:[7,13,14,16],9:[8,15,16,19,19],10:[0,0,0,0,22],11:[0,0,0,0,0,25]}
def bound(n,r):
    if not 1<=r<=n or n<=1:
        return 0
    return ROWS[n][min(r-1,n-r)]

def prove(n,r,L, output=None):
    # Exclude all solutions of size at most L; edges with either orientation
    # are equivalent up to permuting their two outputs for future operations.
    num=1<<n
    wire=[sum(1<<x for x in range(num) if x>>i&1) for i in range(n)]
    layers=[sum(1<<x for x in range(num) if x.bit_count()==w) for w in [n-r,n-r+1]]
    edges=[(i,j,wire[i]&~wire[j],(1<<j)-(1<<i)) for i,j in combinations(range(n),2)]
    cap0=L-bound(n-1,r-1) if r>1 else L
    cap1=L-bound(n-1,r) if r<n else L
    memo={}
    stats=[0]*6
    proof=bytearray()
    def canonical(A,B):
        order=sorted(range(n),key=lambda i:((A&wire[i]).bit_count(),(B&wire[i]).bit_count()))
        labels=list(range(n))
        for i,w in enumerate(order):
            j=labels.index(w)
            if i==j: continue
            mask=wire[i]&~wire[j]
            shift=(1<<j)-(1<<i)
            def swap(s):
                diff=(s^(s>>shift))&mask
                return s^diff^(diff<<shift)
            A,B=swap(A),swap(B)
            labels[i],labels[j]=labels[j],labels[i]
        return A,B
    def visit(A,B,d0,d1,k):
        stats[0]+=1
        if A.bit_count()==1 and B.bit_count()==1:
            raise ValueError(f"Solution in at most {L} gates for ({n},{r})")
        if max((A.bit_count()-1).bit_length(),(B.bit_count()-1).bit_length())>k:
            proof.append(1)
            stats[1]+=1
            return
        # Outputs have to be constant on each of the two boundary layers.
        # If either extreme has exhausted its allowance on a wire, touching
        # that wire again would already contradict a smaller-width bound.
        for i in range(n):
            if d0[i]==cap0 or d1[i]==cap1:
                if (A&wire[i]) not in (0,A) or (B&wire[i]) not in (0,B):
                    proof.append(3)
                    stats[3]+=1
                    return
        key=canonical(A,B)
        if memo.get(key,-1)>=k:
            proof.append(2)
            stats[2]+=1
            return
        proof.append(0)
        for i,j,mask,shift in edges:
            X,Y=A&mask,B&mask
            if not (X or Y):
                continue
            opposite=mask<<shift
            if not (A&opposite or B&opposite):
                continue
            # Compare-exchange of constants can only merge traces of the same
            # extremum. -1 denotes that no such trace reaches the wire.
            lo=max(d0[i],d0[j]); hi=max(d1[i],d1[j])
            if (lo>=0 and lo+1>cap0) or (hi>=0 and hi+1>cap1):
                stats[4]+=1
                continue
            l=list(d0); h=list(d1)
            l[i],l[j]=(lo+1 if lo>=0 else -1),-1
            h[i],h[j]=-1,(hi+1 if hi>=0 else -1)
            visit((A^X)|(X<<shift),(B^Y)|(Y<<shift),l,h,k-1)
        memo[key]=k
        stats[5]+=1
    visit(*layers,[0]*n,[0]*n,L)
    # Commit to every residual-state cache entry, independent of dictionary order.
    digest=hashlib.sha256()
    for (a,b),k in sorted(memo.items()):
        for x in [a,b]: digest.update(x.to_bytes((num+7)//8,'little'))
        digest.update(bytes([k]))
    if output:
        output.mkdir(exist_ok=True)
        (output/f"{n}-{r}.gz").write_bytes(gzip.compress(proof,mtime=0))
    return dict(n=n,rank=r,excluded_through=L,calls=stats[0],
                count_bound=stats[1],cache=stats[2],frozen=stats[3],
                path_bound=stats[4],expanded=stats[5],residuals=len(memo),
                sha256=digest.hexdigest())

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--max-n',type=int,default=11)
    p.add_argument('--case',type=int,nargs=2)
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    cases=[tuple(args.case)] if args.case else [(n,r) for n,row in ROWS.items() if n<=args.max_n for r in range(1,len(row)+1) if row[r-1]]
    for n,r in cases:
        print(json.dumps(prove(n,r,bound(n,r)-1,args.output)),flush=True)
    if args.output and not args.case:
        claims=[[n,r,bound(n,r)-1] for n,r in cases]
        (args.output/"claims.json").write_text(json.dumps(claims))
