"""Exact connected-exchange search for a weighted BPZ terminal code."""

import argparse
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_terminal as terminal


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def connected_masks(groups, radius):
    """Generate every nonempty connected union of group masks up to radius."""
    buckets = [set() for _ in range(radius + 1)]
    touching = {}
    for mask in groups:
        if not mask or mask.bit_count() > radius:
            continue
        buckets[mask.bit_count()].add(mask)
        for bit in bits(mask):
            touching.setdefault(bit, set()).add(mask)
    for count in range(1, radius + 1):
        for mask in sorted(buckets[count]):
            yield count, mask
            if count == radius:
                continue
            possible = set.union(*(touching[bit] for bit in bits(mask)))
            for neighbor in possible:
                union = mask | neighbor
                size = union.bit_count()
                if count < size <= radius:
                    buckets[size].add(union)
        buckets[count].clear()


class CliqueSearch:
    """Use a precomputed compatibility graph for many induced subproblems."""

    def __init__(self, words, weights, compatible):
        self.words = sorted(words, key=weights.__getitem__, reverse=True)
        self.masses = [weights[word] for word in self.words]
        self.indices = {word: 1 << i for i, word in enumerate(self.words)}
        self.neighbors = [0] * len(self.words)
        for i, word in enumerate(self.words):
            for j, other in enumerate(self.words[:i]):
                if compatible(word, other):
                    self.neighbors[i] |= 1 << j
                    self.neighbors[j] |= 1 << i

    def solve(self, pool, threshold, upper):
        best, witness = threshold, ()
        masses, neighbors = self.masses, self.neighbors

        def visit(candidates, remaining, score, chosen):
            nonlocal best, witness
            if score > best:
                best, witness = score, chosen
            while candidates and score + remaining > best:
                bit = candidates & -candidates
                vertex = bit.bit_length() - 1
                mass = masses[vertex]
                candidates ^= bit
                remaining -= mass
                compatible = candidates & neighbors[vertex]
                if compatible == candidates:
                    available = remaining
                else:
                    available = sum(masses[item.bit_length() - 1] for item in bits(compatible))
                visit(compatible, available, score + mass, chosen + (vertex,))

        visit(pool, upper, 0, ())
        return best, tuple(self.words[i] for i in witness)


    def solve_colored(self, pool, threshold, upper):
        # A compatibility clique uses at most one vertex from each color.
        # Sorting by decreasing weight makes the first vertex its exact maximum.
        best, witness = threshold, ()
        masses, neighbors = self.masses, self.neighbors

        def visit(candidates, score, chosen):
            nonlocal best, witness
            if score > best:
                best, witness = score, chosen
            order = []
            total = score
            pending = candidates
            while pending:
                remaining = pending
                total += masses[(remaining & -remaining).bit_length() - 1]
                while remaining:
                    bit = remaining & -remaining
                    vertex = bit.bit_length() - 1
                    order.append((vertex, bit, total))
                    pending ^= bit
                    remaining &= pending & ~neighbors[vertex]
            for vertex, bit, bound in reversed(order):
                if bound <= best:
                    break
                visit(candidates & neighbors[vertex], score + masses[vertex], chosen + (vertex,))
                candidates ^= bit

        if upper > threshold:
            visit(pool, 0, ())
        return best, tuple(self.words[i] for i in witness)


def solve(code, weights, graphs, radius, report=False):
    def compatible(left, right):
        return terminal.separated(left, right, graphs)

    return solve_exchanges(code, weights, compatible, radius, report)


def solve_exchanges(code, weights, compatible, radius, report=False, color_pools=False):
    original = sum(weights[word] for word in code)
    groups = {}
    for word, weight in weights.items():
        if not weight or word in code:
            continue
        mask = sum(1 << i for i, chosen in enumerate(code)
                   if not compatible(word, chosen))
        if mask.bit_count() <= radius:
            groups.setdefault(mask, []).append(word)
    cliques = CliqueSearch([word for words in groups.values() for word in words], weights, compatible)
    groups = {mask: (sum(weights[word] for word in words), sum(cliques.indices[word] for word in words))
              for mask, words in groups.items()}
    best_addition = cliques.solve_colored if color_pools else cliques.solve
    retained_weights = {1 << i: weights[word] for i, word in enumerate(code)}
    stats = [[0, 0] for _ in range(radius + 1)]
    witness = None
    gain = 0
    start = monotonic()
    last_count = 0

    def examine(count, mask):
        nonlocal witness, gain
        stats[count][0] += 1
        removed = sum(retained_weights[bit] for bit in bits(mask))
        upper = 0
        pool = 0
        submask = mask
        while True:
            group = groups.get(submask)
            if group is not None:
                mass, word_mask = group
                upper += mass
                pool |= word_mask
            if not submask:
                break
            submask = (submask - 1) & mask
        # Finding one positive exchange is sufficient to refute local optimality.
        # Evaluate each component at threshold zero rather than combine gains.
        if upper <= removed:
            return
        stats[count][1] += 1
        value, added = best_addition(pool, removed, upper)
        if value - removed > gain:
            witness = tuple(word for i, word in enumerate(code) if not mask & (1 << i)) + added
            gain = value - removed

    examine(0, 0)
    for count, mask in connected_masks(groups, radius):
        if count != last_count and report:
            print(f"Radius {last_count}: {stats[last_count][0]:,} unions, "
                  f"{stats[last_count][1]:,} exact pools; {monotonic() - start:.2f}s", flush=True)
        last_count = count
        examine(count, mask)
    if report:
        for count in range(last_count, radius + 1):
            print(f"Radius {count}: {stats[count][0]:,} unions, "
                  f"{stats[count][1]:,} exact pools; {monotonic() - start:.2f}s", flush=True)
    if witness is not None:
        if len(set(witness)) != len(witness) or not all(
            compatible(a, b) for a, b in combinations(witness, 2)
        ):
            raise ValueError("replacement is not a separated code")
        if sum(weights[word] for word in witness) != original + gain:
            raise ValueError("replacement has the wrong cardinality")
    return witness, gain, stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius", type=int, required=True)
    parser.add_argument("--certificate", type=Path, default=terminal.search.UPSTREAM / "certificate.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.radius < 0:
        parser.error("radius must be nonnegative")
    cert = json.loads(args.certificate.read_text(encoding="utf-8"))
    search, check = terminal.search, terminal.check
    ledger = check.C.load_certificates()
    patterns = search.recorded_patterns(ledger, check.C.theorem2(ledger))
    base = {label: search.Candidate(profile, 5, "base", ())
            for label, profile in zip(("G5", "sG5"), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(cert, patterns, base)
    top = cert["top"]
    code = [tuple(word) for word in check.bpz.CODES[top["terminal_code"]]]
    rows = top.get("subtrees") or [top["rule_inputs"]] * len(code[0])
    rule = {label: [tuple(word) for word in words] for label, words in
            cert.get("explicit_rule", check.bpz.RULES[top["rule"]]).items()}
    if check.bpz.rule_problems(rule):
        raise ValueError("starting combining rule fails the BPZ check")
    vectors = [check.bpz.apply_rule(rule, [nodes[name[4:-1]].vector for name in row])
               for row in rows]
    graphs = [terminal.induced_separation(rule)] * len(rows)
    weights = {word: prod(vector[check.bpz.INDEX[label]] for vector, label in zip(vectors, word))
               for word in product(check.bpz.LABELS, repeat=len(rows))}
    original = sum(weights[word] for word in code)
    if (original != int(cert["M"]) or len(set(code)) != len(code) or len(rows) != len(code[0])
            or not all(terminal.separated(a, b, graphs) for a, b in combinations(code, 2))):
        raise ValueError("starting code does not reproduce the pinned certificate")
    print(f"Checked starting code, radius {args.radius}, {sum(bool(w) for w in weights.values())} positive words.",
          flush=True)
    witness, gain, stats = solve(code, weights, graphs, args.radius, report=True)
    print(f"Checked {sum(row[0] for row in stats):,} unions, including the empty exchange.", flush=True)
    if witness is None:
        print(f"No gain by removing at most {args.radius} terminal tuples.", flush=True)
    else:
        print("Improved lower bound:", check.C.nth_root_digits(original + gain, cert["dimension"], 20))
        if args.output:
            updated = dict(cert, M=str(original + gain), explicit_terminal=witness)
            args.output.write_text(json.dumps(updated, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
