"""Audit the archived experiment records without running the historical solvers."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path.cwd()))
from synth import boundary, instance, jobs
from verify import failures

def require(ok, message):
    if not ok:
        raise ValueError(message)

seeds = json.loads(Path("seeds.json").read_bytes())
for n in (25,26):
    pairs = [list(map(int,line.split())) for line in Path(f"11-{n}.pairs").read_text().splitlines()]
    require(pairs == seeds[f"11-{n}"], "annealing seed differs")
    for line in Path(f"anneal{n}.log").read_text().splitlines():
        _, _, score, net = line.split(maxsplit=3)
        bad = list(failures(11,json.loads(net)))
        require(sum(x in boundary for x in bad) == int(score), "annealing score differs")
    print("annealing", n, "endpoint failures", bad)

for mode in ("control","small","wide","global"):
    records = [json.loads(line) for line in Path(f"{mode}.jsonl").read_text().splitlines()]
    require([(r["case"],r["template"]) for r in records] == list(jobs(mode)), "SAT job list differs")
    for row in records:
        if row["network"] is not None:
            require(not list(failures(11,row["network"])), "invalid archived SAT model")
    print(mode, dict(Counter(r["result"] for r in records)))
full = json.loads(Path("global_full.json").read_bytes())
smt,_ = instance([None]*24,boundary,full["rlimit"])
require(Path("global24.smt2").read_text()==smt+"\n", "global formula differs")
print("global_full", full["result"], full["count"], "boundary masks")

ports = list(combinations(range(11),2))
for name, generator in [("exact","templates.py"),("repair","repair.py")]:
    labels = [line.split()[0] for line in subprocess.check_output([sys.executable,generator],text=True).splitlines()]
    rows = [line.split() for line in Path(f"{name}.log").read_text().splitlines()]
    require(labels==[row[0] for row in rows], "historical log coverage differs")
    for row in rows:
        if row[1]=="SAT":
            require(not list(failures(11,[ports[int(i)-1] for i in row[4:]])), "invalid exact witness")
    print(name, dict(Counter(row[1] for row in rows)))
