"""Emit the complete unrestricted decision instance and attempt it with Z3."""
from pathlib import Path
from synth import instance,solve,version,boundary
import json
limit=30000000
net=[None]*24
smt,_=instance(net,boundary,limit)
Path('global24.smt2').write_text(smt+'\n')
status,model=solve(net,boundary,limit)
print(json.dumps(dict(z3=version,rlimit=limit,count=len(boundary),result=status,network=model)))
