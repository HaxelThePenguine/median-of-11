#!/usr/bin/env python3
"""Render the original opcode streams with untrusted memoization hints."""
import argparse
import gzip
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from check_certificate import check

CHUNK_SIZE = 128
OFFSET_BITS = 20
HINT_BITS = 112
JOBS_PER_BLOCK = 16
BLOCKS_PER_MODULE = 6
MODULES_PER_WAVE = 6

# The large replays list expansions in postorder. A block can therefore
# import only previously proved expansions and check all other descendants
# locally. Original preorder offsets still describe the exact gzip stream.
KERNEL_CLAIMS = {
    (8, 4): ("bound_7_3", "bound_7_4"),
    (9, 2): ("bound_8_1", "bound_8_2"),
    (9, 3): ("bound_8_2", "bound_8_3"),
    (9, 4): ("bound_8_3", "bound_8_4"),
    (9, 5): ("bound_8_4", "bound_8_5"),
    (10, 5): ("bound_9_4", "bound_9_5"),
    (11, 6): ("bound_10_5", "bound_10_6"),
}

BOUND_IMPORTS = {
    (8, 4): ["Median11.ConcreteSmall"],
    (9, 2): ["Median11.ConcreteSmall"],
    (9, 3): ["Median11.ConcreteSmall"],
    (9, 4): ["Median11.KernelData.Rank8_4.Result"],
    (9, 5): ["Median11.KernelData.Rank8_4.Result"],
    (10, 5): ["Median11.KernelData.Rank9_4.Result", "Median11.KernelData.Rank9_5.Result"],
    (11, 6): ["Median11.KernelData.Rank10_5.Result"],
}


def reference_swaps(n, order, old_order):
    # The wires at corresponding canonical positions must be identified.
    # Applying the swaps to n labels records the exact forward relabelling.
    goal = dict(zip(order, old_order))
    current = list(range(n))
    swaps = []
    for source, target in goal.items():
        start = current[source]
        if start != target:
            swaps.append((start, target))
            current = [target if x == start else start if x == target else x
                       for x in current]
    assert all(current[source] == target for source, target in goal.items())
    return swaps


def wire_word(swaps):
    return sum((i | (j << 4)) << (8 * k) for k, (i, j) in enumerate(swaps))


def render_claim(n, rank, budget, opcodes, known):
    hints = {}

    def record(offset, old_offset, order, old_order):
        swaps = reference_swaps(n, order, old_order)
        assert 0 <= old_offset < 1 << OFFSET_BITS and len(swaps) < 16 and n < 16
        payload = old_offset | (len(swaps) << OFFSET_BITS) | (wire_word(swaps) << (OFFSET_BITS + 4))
        assert payload < 1 << HINT_BITS
        hints[offset] = payload

    check(n, rank, budget, opcodes, known, reference=record)
    declarations = []
    for start in range(0, len(opcodes), CHUNK_SIZE):
        block = opcodes[start : start + CHUNK_SIZE]
        codeword = sum(op << (2 * j) for j, op in enumerate(block))
        hintword = sum(payload << (HINT_BITS * j) for j, payload in
                       enumerate(hints[start + j] for j, op in enumerate(block) if op == 2))
        declarations.append(f"  decodeOps {len(block)} {codeword:#x} {hintword:#x}")

    digest = hashlib.sha256(opcodes).hexdigest()
    name = f"data{n}_{rank}"
    return (
        f"-- SHA-256 of the uncompressed opcodes: {digest}\n"
        f"def {name} : List (ReplayOp {n}) := [\n"
        + ",\n".join(declarations)
        + "\n].flatten\n"
    )


def row_mask(rows):
    return sum(1 << row for row in rows)


def bool_literal(value):
    return "true" if value else "false"


def kernel_geometry(widths):
    parts = ["import Median11.PackedReplay", "namespace Median11.KernelData",
             "open PackedRows PackedReplay", "set_option maxRecDepth 100000",
             "set_option maxHeartbeats 0"]
    for n in widths:
        values = [row_mask(x for x in range(1 << n) if x & (1 << i)) for i in range(n)]
        patterns = "\n".join(f"  | {i} => {value:#x}" for i, value in enumerate(values))
        parts.append(f"""private def ones{n} (i : Fin {n}) : Nat :=
  match i.val with
{patterns}
  | _ => 0

private theorem ones{n}_eq : (wires {n}).all (fun i => ones{n} i == column {n} i) = true := by
  decide +kernel

def columns{n} : Columns {n} := ⟨ones{n}, by
  intro i x
  have e := beq_iff_eq.mp (List.all_eq_true.mp ones{n}_eq i (mem_wires i))
  rw [e, column_bit]⟩""")
    parts.append("end Median11.KernelData")
    return "\n\n".join(parts) + "\n"


def kernel_claim(n, rank, budget, ops, known, dest):
    lower, upper = KERNEL_CLAIMS[n, rank]
    b0, b1 = (known[n - 1, min(r, n - r)] for r in (rank - 1, rank))
    caps = budget - b0, budget - b1
    nodes = {}
    references = {}
    expansions = []

    def record_node(offset, opcode, layers, traces, remaining, path):
        if opcode == 0:
            nodes[offset] = (remaining, tuple(map(row_mask, layers)), path)
        elif opcode == 1:
            side = len(layers[1]) > 2**remaining
            ids = sorted(layers[side])[:2**remaining + 1]
            nodes[offset] = side, sum(x << (i * n) for i, x in enumerate(ids))
        elif opcode == 3:
            nodes[offset] = next((origin, sign)
                for sign in (0, 1) for origin, (wire, count) in enumerate(traces[sign])
                if count == caps[sign] and any(
                    len({(x >> wire) & 1 for x in layer}) == 2 for layer in layers))

    def record_reference(offset, prior, order, old_order):
        references[offset] = prior, reference_swaps(n, order, old_order)

    def record_expansion(start, stop, edges):
        expansions.append((start, stop, edges))

    check(n, rank, budget, ops, known, reference=record_reference,
          record_node=record_node, record_expansion=record_expansion)
    locations = {start: divmod(i, JOBS_PER_BLOCK)
                 for i, (start, _, _) in enumerate(expansions)}

    def projection(start, stop, edges):
        cursor = start + 1
        assert ops[start] == 0
        for edge in edges:
            if edge[0] != "node":
                continue
            child = edge[1]
            assert child == cursor
            if ops[child] == 0:
                block, index = locations[child]
                cursor = expansions[block * JOBS_PER_BLOCK + index][1]
            else:
                cursor += 1
        assert cursor == stop

    for expansion in expansions:
        projection(*expansion)
    assert expansions[-1][:2] == (0, len(ops))

    claim = f"Rank{n}_{rank}"
    ns = f"Median11.KernelData.{claim}"
    modules = {}
    output_defs = []
    certificates = []
    for start_block in range(0, len(expansions), JOBS_PER_BLOCK):
        block = start_block // JOBS_PER_BLOCK
        module = block // BLOCKS_PER_MODULE
        entries = expansions[start_block:start_block + JOBS_PER_BLOCK]
        imports_by_block = {}
        for _, _, edges in entries:
            for edge in edges:
                if edge[0] != "node":
                    continue
                offset = edge[1]
                if ops[offset] == 2:
                    offset = references[offset][0]
                elif ops[offset] != 0:
                    continue
                source, index = locations[offset]
                if source != block:
                    imports_by_block.setdefault(source, set()).add(index)

        order = [(source, sorted(picks)) for source, picks in sorted(imports_by_block.items())]
        external = {(source, index): slot for slot, (source, index) in
                    enumerate((source, index) for source, picks in order for index in picks)}

        def slot(offset):
            source, index = locations[offset]
            return 2 * index + 1 if source == block else 2 * external[source, index]

        def render_edge(edge):
            kind, *values = edge
            if kind == "redundant":
                return ".redundant"
            if kind == "path":
                origin, sign = values
                return f".path {origin} {bool_literal(sign)}"
            offset, = values
            opcode = ops[offset]
            if opcode == 0:
                return f".child {slot(offset)}"
            if opcode == 1:
                side, ids = nodes[offset]
                return f".cardinality {bool_literal(side)} {ids:#x}"
            if opcode == 2:
                prior, swaps = references[offset]
                return f".reference {slot(prior)} {prior} (decodeSwaps {n-1} {len(swaps)} {wire_word(swaps):#x})"
            origin, sign = nodes[offset]
            return f".frozen {origin} {bool_literal(sign)}"

        outputs = []
        jobs = []
        for start, stop, edges in entries:
            remaining, (lo, hi), path = nodes[start]
            outputs.append(f"  ⟨{start}, {stop}, {remaining}, ({lo:#x}, {hi:#x})⟩")
            rules = ",\n     ".join(", ".join(render_edge(edge) for edge in edges[i:i+6])
                                     for i in range(0, len(edges), 6))
            jobs.append(f"  ⟨decodePath {n-1} {len(path)} {wire_word(path):#x},\n    [{rules}]⟩")

        sources = ", ".join(f"b{source}.pick {picks}" for source, picks in order)
        input_data = ", ".join(f"pickEntries out{source} {picks}" for source, picks in order)
        out = ",\n".join(outputs)
        work = ",\n".join(jobs)
        output_defs.append(f"def out{block} : Array Entry := #[\n{out}]")
        modules.setdefault(module, []).append(f"""def jobs{block} : List (Job {n}) := [
{work}]

theorem checked{block} : checkJobs columns{n} root (mergeEntries [{input_data}])
    out{block} {b0} {b1} 0 jobs{block} = true := by
  decide +kernel""")

        certificates.append(f"""private def b{block} : Certified {n} :=
  certify columns{n} {rank} {b0} {b1} root (Certified.merge [{sources}]) out{block} jobs{block}
    (by decide) (by decide) (Or.inr ⟨by decide, {lower}⟩)
    (Or.inr ⟨by decide, {upper}⟩) root_eq checked{block}""")

    claim_dest = dest / claim
    claim_dest.mkdir(exist_ok=True)
    root_lo, root_hi = nodes[0][1]
    geometry = "Geometry" if n <= 9 else "WideGeometry"
    bound_imports = "\n".join(f"import {module}" for module in BOUND_IMPORTS[n, rank])
    digest = hashlib.sha256(ops).hexdigest()
    header = ["-- Generated by scripts/generate-lean-certificate.py.",
              f"-- SHA-256 of the uncompressed opcodes: {digest}",
              f"namespace {ns}", "open PackedRows PackedReplay",
              "set_option maxRecDepth 100000", "set_option maxHeartbeats 0"]
    def write_module(name, contents):
        (claim_dest / f"{name}.lean").write_text("\n\n".join(contents) + "\n", encoding="utf-8")

    write_module("Outputs", [f"import Median11.KernelData.{geometry}", *header,
        f"""def root : Packed := ({root_lo:#x}, {root_hi:#x})

theorem root_eq : root = pack (Layers.initial {n} {rank}) := by
  decide +kernel""", *output_defs, f"end {ns}"])
    for module, blocks in modules.items():
        wave = module // MODULES_PER_WAVE
        prelude = f"{ns}.W{wave-1:02}" if wave else f"{ns}.Outputs"
        write_module(f"C{module:03}", [f"import {prelude}", *header, *blocks, f"end {ns}"])
    for start in range(0, len(modules), MODULES_PER_WAVE):
        stop = min(start+MODULES_PER_WAVE, len(modules))
        write_module(f"W{start // MODULES_PER_WAVE:02}",
                     [f"import {ns}.C{i:03}" for i in range(start, stop)])

    block, index = locations[0]
    last_wave = (len(modules) - 1) // MODULES_PER_WAVE
    result = f"""namespace Median11

open PackedReplay KernelData.{claim}
open {ns} in

theorem bound_{n}_{rank} : Bound {n} {rank} {budget+1} :=
  root_bound (by decide) (by decide) KernelData.{claim}.b{block} {index}
    {budget} {len(ops)} root root_eq (by decide +kernel)
"""
    if (n, rank) == (8, 4):
        result += """
theorem bound_8_5 : Bound 8 5 16 :=
  bound_dual (r := 4) (by decide) (by decide) bound_8_4
"""
    if (n, rank) == (10, 5):
        result += """
theorem bound_10_6 : Bound 10 6 22 :=
  bound_dual (r := 5) (by decide) (by decide) bound_10_5
"""
    write_module("Result", [f"import {ns}.W{last_wave:02}\n{bound_imports}",
        *header, *certificates, f"end {ns}", result + "\nend Median11"])
    print(f"Prepared {n}-{rank}: {len(ops)} opcodes, {len(expansions)} expansions, {block+1} blocks",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "formal/Median11/CertificateData.lean")
    parser.add_argument("--max-width", type=int, default=11)
    parser.add_argument("--skip-claim", action="append", default=[])
    parser.add_argument("--kernel-blocks", type=Path)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    directory = ROOT / "certificate"
    if args.kernel_blocks:
        args.kernel_blocks.mkdir(parents=True, exist_ok=True)
        (args.kernel_blocks / "Geometry.lean").write_text(kernel_geometry((8, 9)), encoding="utf-8")
        if args.max_width >= 10:
            (args.kernel_blocks / "WideGeometry.lean").write_text(
                kernel_geometry(range(10, min(11, args.max_width) + 1)), encoding="utf-8")
        known = {}
        for n, rank, budget in json.loads((directory / "claims.json").read_text()):
            if n > args.max_width:
                break
            if (n, rank) in KERNEL_CLAIMS and f"{n}-{rank}" not in args.skip_claim:
                opcodes = gzip.decompress((directory / f"{n}-{rank}.gz").read_bytes())
                kernel_claim(n, rank, budget, opcodes, known, args.kernel_blocks)
            known[n, min(rank, n + 1 - rank)] = budget + 1
        return
    known = {}
    result = [
        "-- Generated by scripts/generate-lean-certificate.py.",
        "import Median11.ReplayEncoding\n",
        "namespace Median11\n",
    ]
    calls = []
    for n, rank, budget in json.loads((directory / "claims.json").read_text()):
        if n > args.max_width:
            continue
        opcodes = gzip.decompress((directory / f"{n}-{rank}.gz").read_bytes())
        if f"{n}-{rank}" in args.skip_claim:
            known[n, min(rank, n + 1 - rank)] = budget + 1
            continue
        result.append(render_claim(n, rank, budget, opcodes, known))
        small = [known.get((n - 1, min(r, n - r)), 0) for r in (rank - 1, rank)]
        calls.append(f"  ({n}, {rank}, {budget + 1}, {len(opcodes)},\n"
                     f"    verifyReplay {n} {rank} {budget} {small[0]} {small[1]} data{n}_{rank})")
        known[n, min(rank, n + 1 - rank)] = budget + 1
    if args.max_width == 11:
        result.append("def certificateEvaluations : List (Nat × Nat × Nat × Nat × Bool) := [\n"
                      + ",\n".join(calls) + "\n]\n")
    artifact = "\n".join(result) + "\nend Median11\n"
    if args.check:
        if args.output.read_text() != artifact:
            raise SystemExit("Lean certificate data mismatch")
    else:
        args.output.write_text(artifact, encoding="utf-8")


if __name__ == "__main__":
    main()
