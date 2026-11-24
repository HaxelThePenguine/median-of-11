"""Independent scalar checker. Inputs and outputs use wire zero as the low bit."""
import argparse
import json
from pathlib import Path

SEEDS = Path(__file__).resolve().parent / "experiments" / "seeds.json"

def failures(n, network):
    if n % 2 != 1 or any(not (0 <= i < j < n) for i, j in network):
        raise ValueError("Invalid comparator or input dimensions")
    for mask in range(1 << n):
        wires = [(mask >> i) & 1 for i in range(n)]
        for i, j in network:
            if wires[i] > wires[j]:
                wires[i], wires[j] = wires[j], wires[i]
        if wires[n // 2] != int(mask.bit_count() > n // 2):
            yield mask

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", nargs="?", type=Path, help="JSON list of pairs")
    parser.add_argument("--n", type=int, default=11)
    args = parser.parse_args()
    cases = [(args.n, json.loads(args.file.read_text()))] if args.file else [
        (int(name.split("-")[0]), net) for name, net in json.loads(SEEDS.read_text()).items()]
    good = True
    for n, net in cases:
        bad = list(failures(n, net))
        print(f"n={n} size={len(net)} errors={len(bad)}/{1<<n} first={bad[:3]}")
        good &= not bad
    raise SystemExit(0 if good else 1)
