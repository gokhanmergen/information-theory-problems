"""Heuristic search of variable-dimension BPZ schedules from the pinned Tang gadgets."""

import argparse
import json
from itertools import product
import math
from pathlib import Path
import random
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / 'schedule-deps'))
sys.path.insert(0, str(HERE))
import numpy as np
import search_rule_schedules as schedules

search, check, bpz = schedules.search, schedules.check, schedules.bpz


def orientations(vector, expression):
    yield vector, expression
    yield bpz.sigma_vector(vector), ['sigma', expression]


def catalog(nodes, originals):
    leaves = {}
    for name, node in nodes.items():
        for vector, expr in orientations(node.vector, name):
            leaves.setdefault((node.dimension, vector), expr)
    profiles = dict(leaves)
    operands = tuple(leaves.items())
    by_arity = {a: [(n, r) for n, r in bpz.RULES.items() if n.startswith(f'S{a}')] for a in (2, 3)}
    for arity, rules in by_arity.items():
        for entries in product(operands, repeat=arity):
            d = sum(key[0] for key, _ in entries)
            inputs = [key[1] for key, _ in entries]
            exprs = [expr for _, expr in entries]
            for name, rule in rules:
                for v, expr in orientations(bpz.apply_rule(rule, inputs), [name, *exprs]):
                    profiles.setdefault((d, v), expr)
    rows, _ = schedules.row_variants([schedules.Row(nodes[n].vector, n) for n in originals])
    row_dim = sum(nodes[n].dimension for n in originals)
    for row in rows:
        profiles.setdefault((row_dim, row.vector), row.expression)
    return profiles


def starts_for(matrix, words, standard, random_starts):
    products = np.ones((len(matrix),len(words)))
    for column in words.T:
        products *= matrix[:, column]
    best_homogeneous = np.argsort(-products.sum(axis=1), kind='stable')[:24]
    width = words.shape[1]
    rng = random.Random(1616 + width)
    starts = [(i,) * width for i in best_homogeneous.tolist()]
    starts.append((standard,) * width)
    for i in range(random_starts):
        ranked = []
        for _ in range(width):
            coefficients = [10 ** rng.uniform(-2.5, 0) for _ in range(matrix.shape[1])]
            ranked.append(int(np.argmax(matrix @ coefficients)))
        starts.append(tuple(ranked))
    return list(dict.fromkeys(starts))


def ascent(matrix, words, start):
    picked = list(start)
    independent = len(start)
    for _ in range(16):
        changed = False
        for slot in range(independent):
            masses = np.ones(len(words))
            for i in range(independent):
                if i != slot:
                    masses *= matrix[picked[i], words[:, i]]
            coefficients = np.bincount(words[:, slot], weights=masses, minlength=matrix.shape[1])
            scores = matrix @ coefficients
            best = int(np.argmax(scores))
            if scores[best] > scores[picked[slot]] + 1e-15:
                picked[slot] = best
                changed = True
        if not changed:
            break
    return tuple(picked)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--starts', type=int, default=128)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--candidates', type=Path, help='save the distinct final schedules for further tests')
    args = parser.parse_args()
    baseline = json.loads((search.UPSTREAM / 'certificate.json').read_text(encoding='utf-8'))
    ledger = check.C.load_certificates()
    patterns = search.recorded_patterns(ledger, check.C.theorem2(ledger))
    bases = {label: search.Candidate(profile, 5, 'base', ())
             for label, profile in zip(('G5', 'sG5'), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(baseline, patterns, bases)
    originals = [label[4:-1] for label in baseline['top']['rule_inputs']]
    original_d = sum(nodes[n].dimension for n in originals)
    original_v = bpz.apply_rule(bpz.RULES[baseline['top']['rule']], [nodes[n].vector for n in originals])
    if any(bpz.rule_problems(rule) for rule in bpz.RULES.values()):
        raise ValueError('inadmissible combining rule')
    original_m = int(baseline['M'])
    if bpz.apply_code(bpz.K4a, [original_v]*4) != original_m:
        raise ValueError('baseline failed replay')
    profiles = catalog(nodes, originals)
    keys = tuple(profiles)
    anchor = keys.index((original_d, original_v))
    scale = 3.25883870544460883237
    matrix = np.array([[value / scale**d for value in vector] for d, vector in keys])
    print(f'{len(keys):,} dimension-vector profiles, dimension {min(d for d,_ in keys)}–{max(d for d,_ in keys)}.', flush=True)
    best = (original_m, baseline['dimension'], baseline['top']['terminal_code'], None)
    candidates = []
    for name, code in bpz.CODES.items():
        if bpz.code_problems(code):
            raise ValueError('inadmissible terminal code')
        words = np.array([[bpz.INDEX[label] for label in word] for word in code])
        starts = starts_for(matrix, words, anchor, args.starts)
        finals = {ascent(matrix, words, start) for start in starts}
        champion = None
        for picked in sorted(finals):
            dimensions = sum(keys[i][0] for i in picked)
            value = bpz.apply_code(code, [keys[i][1] for i in picked])
            if args.candidates:
                candidates.append({'terminal_code': name, 'dimension': dimensions, 'M':str(value),
                                   'row_expressions': [profiles[keys[i]] for i in picked]})
            if champion is None or value ** champion[1] > champion[0] ** dimensions:
                champion = value, dimensions, name, picked
        print(f'{name}: {len(starts)} starts, {len(finals)} distinct final schedules; '
              f'{check.C.nth_root_digits(champion[0], champion[1], 20)} at d={champion[1]}.', flush=True)
        if champion[0] ** best[1] > best[0] ** champion[1]:
            best = champion
    if args.candidates:
        args.candidates.write_text(json.dumps(candidates,indent=2)+'\n',encoding='utf-8')
    if best[3] is None:
        print('No stronger lower bound found by coordinate ascent.', flush=True)
        return
    mass, dimension, code, picked = best
    exprs = [profiles[keys[i]] for i in picked]
    sources = {name: node.vector for name,node in nodes.items()}
    if bpz.apply_code(bpz.CODES[code], [schedules.evaluate(expr, sources) for expr in exprs]) != mass:
        raise ValueError('winner failed exact cardinality replay')
    print('Improved lower bound:', check.C.nth_root_digits(mass, dimension, 20), flush=True)
    if args.output:
        out = dict(baseline, M=str(mass), dimension=dimension,
                   top={'terminal_code':code, 'row_expressions':exprs})
        args.output.write_text(json.dumps(out, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
