"""Check weighted local exchanges in a four-factor BPZ terminal code."""
import argparse
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_c7 as search

check = search.check
labels = check.bpz.LABELS
index = check.bpz.INDEX


def induced_separation(rule):
    # Each output label is a union over the rule words. Every pair of their
    # summands is separated when some child-coordinate labels are perpendicular.
    return {(a, b) for a in labels for b in labels if a != b
            and all(any(check.bpz.perp(x, y) for x, y in zip(aw, bw))
                    for aw in rule[a] for bw in rule[b])}


def separated(left, right, graphs):
    return any((a, b) in g for a, b, g in zip(left, right, graphs))


def best_addition(pool, weights, graphs, target):
    best = target
    witness = ()
    pool = sorted(pool, key=weights.__getitem__, reverse=True)

    def visit(candidates, remaining, score, chosen):
        nonlocal best, witness
        if score > best:
            best, witness = score, chosen
        for i, word in enumerate(candidates):
            weight = weights[word]
            if score + remaining <= best:
                break
            remaining -= weight
            filtered = [other for other in candidates[i + 1:]
                        if separated(word, other, graphs)]
            visit(filtered, sum(weights[v] for v in filtered), score + weight,
                  chosen + (word,))

    visit(pool, sum(weights[v] for v in pool), 0, ())
    return best, witness


def exact_clique(words, weights, graphs, seed, max_nodes):
    words = sorted(words, key=weights.__getitem__, reverse=True)
    masses = [weights[word] for word in words]
    neighbors = [0] * len(words)
    for i, left in enumerate(words):
        for j in range(i):
            if separated(left, words[j], graphs):
                neighbors[i] |= 1 << j
                neighbors[j] |= 1 << i
    best = sum(weights[word] for word in seed)
    witness = tuple(seed)
    visited = 0
    cutoff = False

    def color_sort(candidates):
        order, bounds = [], []
        total = 0
        while candidates:
            remainder = candidates
            total += masses[(remainder & -remainder).bit_length() - 1]
            while remainder:
                bit = remainder & -remainder
                vertex = bit.bit_length() - 1
                candidates ^= bit
                remainder &= candidates & ~neighbors[vertex]
                order.append(vertex)
                bounds.append(total)
        return order, bounds

    def visit(candidates, score, chosen):
        nonlocal best, witness, visited, cutoff
        if score > best:
            best = score
            witness = tuple(words[i] for i in chosen)
        if not candidates or cutoff:
            return
        visited += 1
        if visited > max_nodes:
            cutoff = True
            return
        order, bounds = color_sort(candidates)
        for vertex, bound in zip(reversed(order), reversed(bounds)):
            if score + bound <= best or cutoff:
                return
            visit(candidates & neighbors[vertex], score + masses[vertex],
                  chosen + (vertex,))
            candidates ^= 1 << vertex

    visit((1 << len(words)) - 1, 0, ())
    return witness, best, visited, not cutoff


def solve(certificate, radius):
    ledger = check.C.load_certificates()
    theorem = check.C.theorem2(ledger)
    patterns = search.recorded_patterns(ledger, theorem)
    base = {label: search.Candidate(profile, 5, "base", ())
            for label, profile in zip(("G5", "sG5"), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(certificate, patterns, base)
    terminal = certificate["top"]
    code = [tuple(word) for word in check.bpz.CODES[terminal["terminal_code"]]]
    subtrees = terminal.get("subtrees")
    if subtrees is None:
        subtrees = [terminal["rule_inputs"]] * len(code[0])
    rule = certificate.get("explicit_rule", check.bpz.RULES[terminal["rule"]])
    graphs = [induced_separation(rule)] * len(subtrees)
    standard = {(a, b) for a in labels for b in labels if check.bpz.perp(a, b)}
    if not standard.issubset(graphs[0]):
        raise ValueError("combining rule fails required separation")
    print("Extra separated label pairs:", sorted(graphs[0] - standard), flush=True)
    vectors = [check.bpz.apply_rule(rule, [nodes[x[4:-1]].vector for x in inputs])
               for inputs in subtrees]
    weights = {word: prod(v[index[x]] for v, x in zip(vectors, word))
               for word in product(labels, repeat=len(vectors))}
    original = sum(weights[word] for word in code)
    if original != int(certificate["M"]):
        raise ValueError("starting cardinality disagrees with certificate")
    if len(set(code)) != len(code) or not all(separated(x, y, graphs) for x, y in combinations(code, 2)):
        raise ValueError("starting terminal code fails separation")
    groups = {}
    for word, weight in weights.items():
        if not weight or word in code:
            continue
        mask = sum(1 << i for i, chosen in enumerate(code)
                   if not separated(word, chosen, graphs))
        if mask.bit_count() <= radius:
            groups.setdefault(mask, []).append(word)
    examined = 0
    decisive_pools = 0
    best_gain = 0
    best_code = code
    for count in range(radius + 1):
        for indices in combinations(range(len(code)), count):
            mask = sum(1 << i for i in indices)
            needed = sum(weights[code[i]] for i in indices)
            pool = list(groups.get(0, ()))
            sub = mask
            while sub:
                pool.extend(groups.get(sub, ()))
                sub = (sub - 1) & mask
            examined += 1
            if sum(weights[word] for word in pool) <= needed + best_gain:
                continue
            decisive_pools += 1
            mass, added = best_addition(pool, weights, graphs, needed + best_gain)
            if mass > needed + best_gain:
                best_gain = mass - needed
                best_code = [word for i, word in enumerate(code) if i not in indices] + list(added)
    print(f"Terminal words: {len(code)}; alphabet tuples: {len(weights)}; "
          f"removal sets: {examined}; upper-bound survivors: {decisive_pools}", flush=True)
    if not best_gain:
        print(f"No gain by removing at most {radius} terminal tuples.", flush=True)
        return
    if not all(separated(x, y, graphs) for x, y in combinations(best_code, 2)):
        raise ValueError("improved terminal code fails separation")
    if sum(weights[word] for word in best_code) != original + best_gain:
        raise ValueError("improved terminal code fails exact weight check")
    print("New terminal bound:",
          check.C.nth_root_digits(original + best_gain, certificate["dimension"], 20), flush=True)
    updated = dict(certificate, M=str(original + best_gain), explicit_terminal=best_code)
    (search.OUTPUT / "terminal-certificate.json").write_text(json.dumps(updated, indent=2) + "\n")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--certificate", type=Path, default=search.UPSTREAM / "certificate.json")
    p.add_argument("--radius", type=int, default=3)
    args = p.parse_args()
    solve(json.loads(args.certificate.read_text()), args.radius)
