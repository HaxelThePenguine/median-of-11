"""Negative controls for the independent release reader. Run from repository root."""
import gzip
import json
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile

checker = Path(sys.argv[1]).resolve()
source = Path("certificate")
rng = random.Random(110625)
with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp) / "certificate"
    shutil.copytree(source, root)
    manifest = root / "claims.json"
    claims = json.loads(manifest.read_text())
    member = root / "8-4.gz"
    packed = member.read_bytes()
    original = gzip.decompress(packed)
    count = 0

    def rejects(label):
        result = subprocess.run([checker, root], capture_output=True, text=True)
        if result.returncode != 1 or not result.stderr.startswith("REJECT "):
            raise RuntimeError((label, result.returncode, result.stderr))
        print(label, result.stderr.strip())

    for label, replacement in {
        "drop claim": claims[1:], "duplicate claim": [claims[0], *claims],
        "unsorted claims": [claims[1], claims[0], *claims[2:]],
        "false final theorem": [*claims[:-1], [11, 6, 25]],
        "negative": [[2, 1, -1], *claims[1:]],
        "extra field": [[2, 1, 0, 0], *claims[1:]],
        "float": [[2, 1, 0.0], *claims[1:]],
        "boolean": [[2, 1, False], *claims[1:]],
    }.items():
        manifest.write_text(json.dumps(replacement))
        rejects(label)
        count += 1
    for bad_json in ['[[02,1,0]]', '[]{}', '[', '[[2,1,0],]', json.dumps(claims)+'!']:
        manifest.write_text(bad_json)
        rejects("JSON grammar")
        count += 1
    shutil.copyfile(source / manifest.name, manifest)
    for label, damaged in {
        "missing final node": gzip.compress(original[:-1]),
        "extra node": gzip.compress(original+b'\0'),
        "premature reference": gzip.compress(b'\2'+original[1:]),
        "false frozen leaf": gzip.compress(b'\3'+original[1:]),
        "false cardinality leaf": gzip.compress(b'\1'+original[1:]),
        "plain data": original, "trailing gzip garbage": packed+b'!',
        "extra gzip member": packed+gzip.compress(b''),
        "CRC failure": packed[:-8]+bytes([packed[-8]^1])+packed[-7:],
        "truncated member": packed[:-1],
    }.items():
        member.write_bytes(damaged)
        rejects(label)
        count += 1
    member.unlink()
    rejects("missing member")
    member.write_bytes(packed)
    extra = root / "unlisted.gz"
    extra.write_bytes(packed)
    rejects("unlisted member")
    extra.unlink()
    count += 2

    for _ in range(32):
        data = bytearray(original)
        position = rng.randrange(len(data))
        data[position] = rng.randrange(4, 256)
        member.write_bytes(gzip.compress(data))
        rejects(f"invalid byte at {position}")
    # Different legitimate reasons can close the same node. Compare semantic
    # acceptance of random in-alphabet substitutions against the Python checker.
    sys.path.insert(0, str(Path.cwd()))
    from check_certificate import check
    known = {(n,r): budget+1 for n,r,budget in claims if n < 8}
    equivalent = 0
    for _ in range(32):
        data = bytearray(original)
        i = rng.randrange(len(data))
        data[i] = (data[i]+rng.randrange(1,4)) % 4
        member.write_bytes(gzip.compress(data))
        native = subprocess.run([checker, root], capture_output=True)
        if native.returncode not in (0,1):
            raise RuntimeError(native.stderr)
        try:
            check(8,4,15,data,known)
            accepted = True
        except ValueError:
            accepted = False
        if accepted != (native.returncode == 0):
            raise RuntimeError(f"disagreement at {i}")
        equivalent += accepted
    print(f"{count} targeted and 32 invalid-byte mutations rejected; "
          f"32 legal-opcode substitutions agreed ({equivalent} accepted).")
