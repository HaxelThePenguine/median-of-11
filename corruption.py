"""Two negative controls of logical certificate content and a targeted counterexample test."""
import gzip
import json
from pathlib import Path
from check_certificate import check
from verify import failures,SEEDS

data=gzip.decompress(Path("certificate/11-6.gz").read_bytes())
for label,changed in [('false cache reference',b'\x02'+data[1:]),('truncation',data[:-1])]:
    try:
        check(11,6,24,changed,{(10,5):22})
    except ValueError as exc:
        print("REJECT",label,str(exc))
    else:
        raise RuntimeError("corrupt certificate accepted")
net=json.loads(SEEDS.read_text())['11-25']
wrong=list(failures(11,net[:-1]))
if not wrong:
    raise RuntimeError("damaged construction accepted")
print('REJECT 24-gate truncated baseline, failing masks:',len(wrong))
