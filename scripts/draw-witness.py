"""Print the SVG network diagram from the ordered JSON comparator pairs."""

import json
from pathlib import Path


root = Path(__file__).resolve().parents[1]
pairs = json.loads((root / "median11_25.json").read_bytes())
left, right = 40, 790
rows = range(22, 223, 20)
print('''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 840 244"
     role="img" aria-labelledby="title description">
  <title id="title">Dobbelaere's 25-comparator median network</title>
  <desc id="description">Eleven wires, numbered zero to ten from top to bottom.
    Comparators are executed from left to right. Each sends the smaller value
    upward. The median leaves wire five at the right.</desc>
  <rect width="840" height="244" rx="12" fill="#f8fafc"/>
  <g stroke="#8e9aaa" stroke-width="1">''')
for y in rows:
    print(f'    <path d="M{left} {y}H{right}"/>')
print('  </g>')
print('  <g font-family="monospace" font-size="12" text-anchor="end" fill="#364152">')
for wire, y in enumerate(rows):
    print(f'    <text x="30" y="{y + 4}">{wire}</text>')
print('  </g>')
print('  <g stroke="#273549" fill="#273549" stroke-width="1.6">')
for index, (low, high) in enumerate(pairs, start=1):
    x = left + index * 28
    first, second = rows[low], rows[high]
    print(f'    <path d="M{x} {first}V{second}"/>')
    print(f'    <circle cx="{x}" cy="{first}" r="2.6"/>')
    print(f'    <circle cx="{x}" cy="{second}" r="2.6"/>')
print('''  </g>
  <path d="M741 122H790" stroke="#12665e" stroke-width="2"/>
  <circle cx="790" cy="122" r="3.5" fill="#12665e"/>
  <text x="802" y="126" font-family="monospace" font-size="12" fill="#12665e">q</text>
</svg>''')
