"""Bounded SAT synthesis with QF_BV bit-blasting and counterexample refinement."""
import argparse
import ctypes as C
import ctypes.util
import json
import random
import re
from pathlib import Path
from verify import failures, SEEDS

lib = C.CDLL(ctypes.util.find_library("z3") or "libz3.so.4")
def bind(name, result, *args):
    f = getattr(lib, "Z3_" + name)
    f.restype, f.argtypes = result, args
    return f
ptr, string = C.c_void_p, C.c_char_p
config = bind("mk_config", ptr)
context = bind("mk_context", ptr, ptr)
drop_config = bind("del_config", None, ptr)
drop_context = bind("del_context", None, ptr)
evaluate = bind("eval_smtlib2_string", string, ptr, string)
version = bind("get_full_version", string)().decode()
boundary = [m for m in range(2048) if m.bit_count() in (5, 6)]

def literal(value, width):
    return f"(_ bv{value} {width})"

def instance(template, samples, rlimit):
    width = len(samples)
    sort = f"(_ BitVec {width})"
    lines = ["(set-logic QF_BV)", f"(set-option :rlimit {rlimit})"]
    def define(name, expression):
        lines.append(f"(define-fun {name} () {sort} {expression})")
        return name
    def packed(predicate):
        return literal(sum(1 << k for k, m in enumerate(samples) if predicate(m)), width)
    def select(index, wires):
        result = wires[-1]
        for k in reversed(range(10)):
            result = f"(ite (= {index} {literal(k,4)}) {wires[k]} {result})"
        return result
    wires = [define(f"w{i}", packed(lambda m: (m >> i) & 1)) for i in range(11)]
    names = []
    for t, edge in enumerate(template):
        if edge is not None:
            i,j = edge
            a,b = wires[i],wires[j]
            wires[i] = define(f"u{t}", f"(bvand {a} {b})")
            wires[j] = define(f"v{t}", f"(bvor {a} {b})")
            continue
        left, right = f"a{t}", f"b{t}"
        names.extend([left,right])
        for name in (left,right):
            lines.append(f"(declare-const {name} (_ BitVec 4))")
        lines.extend([f"(assert (bvule {left} {right}))",
                      f"(assert (bvule {right} {literal(10,4)}))"])
        a = define(f"x{t}",select(left,wires))
        b = define(f"y{t}",select(right,wires))
        lo = define(f"u{t}",f"(bvand {a} {b})")
        hi = define(f"v{t}",f"(bvor {a} {b})")
        wires = [define(f"w{t}_{k}",
            f"(ite (= {left} {literal(k,4)}) {lo} (ite (= {right} {literal(k,4)}) {hi} {old}))")
            for k,old in enumerate(wires)]
    lines.append(f"(assert (= {wires[5]} {packed(lambda m: m.bit_count()>=6)}))")
    lines.append("(check-sat-using (then simplify bit-blast sat))")
    return "\n".join(lines), names

def solve(template, samples, rlimit):
    smt, names = instance(template,samples,rlimit)
    cfg=config()
    ctx=context(cfg)
    drop_config(cfg)
    try:
        status=evaluate(ctx,smt.encode()).decode().strip()
        if status not in ('sat','unsat','unknown'):
            raise RuntimeError(status)
        if status!='sat':
            return status,None
        answer=evaluate(ctx,("(get-value ("+" ".join(names)+"))").encode()).decode()
        values=dict((n,int(v,16)) for n,v in re.findall(r"\(([ab]\d+) #x([0-9a-f])\)",answer))
        pairs=[(values[f'a{t}'],values[f'b{t}']) if edge is None else edge
               for t,edge in enumerate(template)]
        return status,[p for p in pairs if p[0]<p[1]]
    finally:
        drop_context(ctx)

def run(label, template, rlimit):
    rng=random.Random(741)
    samples=sum((rng.sample([m for m in boundary if m.bit_count()==w],8) for w in [5,6]),[])
    trace=[]
    while True:
        status,net=solve(template,samples,rlimit)
        trace.append([len(samples),status])
        if status!='sat':
            break
        bad=list(failures(11,net))
        if not bad:
            status="verified"
            break
        counterexamples=[m for m in bad if m in boundary]
        assert counterexamples and set(samples).isdisjoint(counterexamples)
        samples.extend(rng.sample(counterexamples,min(12,len(counterexamples))))
    return dict(case=label,template=template,result=status,iterations=trace,
                network=net if status=="verified" else None,rlimit=rlimit,z3=version)

def reordered(seed):
    net=seed.copy()
    rng=random.Random(29)
    for _ in range(400):
        k=rng.randrange(len(net)-1)
        if set(net[k]).isdisjoint(net[k+1]):
            net[k],net[k+1]=net[k+1],net[k]
    return net

def windows(net, parts):
    result=[]
    cursor=0
    for start,length,keep in parts:
        assert start>=cursor and start+length<=len(net)
        result.extend(net[cursor:start])
        result.extend([None]*keep)
        cursor=start+length
    return result+net[cursor:]

def jobs(mode):
    if mode=='global':
        yield 'global', [None]*24
        return
    seeds=json.loads(SEEDS.read_text())
    for key in ('11-25','11-26'):
        for order,net in [('original',seeds[key]),('reordered',reordered(seeds[key]))]:
            cut=len(net)-24
            if mode=='control':
                yield f'{key}-positive',windows(net,[(4,2,2)])
                break
            k=3 if mode=='small' else 6
            starts=range(len(net)-k+1) if mode=='small' else [0,4,9,14,len(net)-k]
            for start in starts:
                yield f'{key}-{order}-{k}-at-{start}',windows(net,[(start,k,k-cut)])
            if mode=='wide':
                for a,b in [(0,12),(4,17),(9,19)]:
                    yield f'{key}-{order}-split-{a}-{b}',windows(net,[(a,3,2),(b,3,4-cut)])
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument("mode",choices=["small","wide","global","control"])
    p.add_argument("--rlimit",type=int,default=1500000)
    args=p.parse_args()
    for label,template in jobs(args.mode):
        print(json.dumps(run(label,template,args.rlimit)),flush=True)
