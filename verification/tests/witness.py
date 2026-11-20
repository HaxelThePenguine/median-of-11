"""A bit-sliced binary oracle and complete ternary test, independent of verify.py."""
import json
from itertools import product
from pathlib import Path

net = json.loads(Path("median11_25.json").read_text())
if len(net) != 25 or any(not (0 <= a < b < 11) for a, b in net):
    raise ValueError("wrong construction profile")

inputs = [sum(1 << x for x in range(2048) if x & (1 << i)) for i in range(11)]
target = sum(1 << x for x in range(2048) if x.bit_count() >= 6)

def errors(gates):
    columns = inputs.copy()
    for a,b in gates:
        columns[a],columns[b] = columns[a] & columns[b], columns[a] | columns[b]
    return (columns[5] ^ target).bit_count()

if errors(net):
    raise ValueError("binary counterexample")
damaged = [errors(net[:i]+net[i+1:]) for i in range(len(net))]
if min(damaged) == 0:
    raise ValueError("24-gate witness discovered")
print("Binary masks: 2048 correct. Failing mask counts by single-gate deletion:", damaged)
count = 0
for x in product(range(3), repeat=11):
    wires = list(x)
    for a,b in net:
        if wires[a] > wires[b]:
            wires[a],wires[b] = wires[b],wires[a]
    if wires[5] != sorted(x)[5]:
        raise ValueError(x)
    count += 1
print(f"Ternary tuples: {count} correct.")
