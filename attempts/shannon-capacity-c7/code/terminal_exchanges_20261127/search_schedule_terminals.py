"""Search exact terminal exchanges on recorded BPZ rule schedules."""

import argparse
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_connected_terminal as exchange
import search_rule_schedules as schedules

search, check, bpz = schedules.search, schedules.check, schedules.bpz
standard = {(a, b) for a in bpz.LABELS for b in bpz.LABELS if bpz.perp(a, b)}
mirror = dict(zip(bpz.LABELS, bpz.sigma_vector(bpz.LABELS)))


def evaluate(expression, nodes):
    if isinstance(expression, str):
        node = nodes[expression]
        return node.vector, standard, node.dimension
    name, *operands = expression
    values = [evaluate(item, nodes) for item in operands]
    if name == 'sigma':
        if len(values) != 1:
            raise ValueError('sigma must have one input')
        vector, graph, dimension = values[0]
        return bpz.sigma_vector(vector), {(mirror[a], mirror[b]) for a,b in graph}, dimension
    rule = bpz.RULES[name]
    vectors, graphs, dimensions = zip(*values)
    graph = {(a,b) for a in bpz.LABELS for b in bpz.LABELS if a != b and all(
        any((x,y) in g for x,y,g in zip(left,right,graphs))
        for left in rule[a] for right in rule[b]
    )}
    if not standard <= graph:
        raise ValueError('constructed rule lost a required label separation')
    return bpz.apply_rule(rule, vectors), graph, sum(dimensions)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidates', type=Path)
    parser.add_argument('--radius', type=int, default=3)
    parser.add_argument('--code', action='append', choices=bpz.CODES)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--variants', type=Path, help='save all strict gains over their own schedules')
    parser.add_argument('--replay-only', action='store_true', help='validate listed schedules without searching')
    args = parser.parse_args()
    if args.radius < 0:
        parser.error('--radius must be nonnegative')
    if any(bpz.rule_problems(rule) for rule in bpz.RULES.values()):
        raise ValueError('inadmissible combining rule')
    baseline = json.loads((search.UPSTREAM / 'certificate.json').read_text(encoding='utf-8'))
    ledger = check.C.load_certificates()
    patterns = search.recorded_patterns(ledger, check.C.theorem2(ledger))
    bases = {label: search.Candidate(profile, 5, 'base', ())
             for label, profile in zip(('G5', 'sG5'), check.C.base_profiles(ledger))}
    candidates = json.loads(args.candidates.read_text(encoding='utf-8'))
    sources = candidates if isinstance(candidates, dict) and 'gadgets' in candidates else baseline
    nodes = search.record_nodes(sources, patterns, bases)
    if isinstance(candidates, dict):
        candidates = candidates.get('candidates', [candidates])
    counts = {name:[0, 0, 0] for name in bpz.CODES}
    original = int(baseline['M'])
    best = (original, baseline['dimension'], None)
    variants = []
    for entry in candidates:
        name = entry['terminal_code']
        if args.code and name not in args.code:
            continue
        code = list(map(tuple, entry.get('explicit_terminal', bpz.CODES[name])))
        if not code or len(set(code)) != len(code):
            raise ValueError('candidate terminal code is empty or has duplicate tuples')
        vectors, graphs, dimensions = zip(*(evaluate(expr,nodes) for expr in entry['row_expressions']))
        dimension = sum(dimensions)
        if {len(word) for word in code} != {len(vectors)} or entry['dimension'] != dimension:
            raise ValueError('candidate has incorrect dimensions')
        weights = {word: prod(row[bpz.INDEX[label]] for row,label in zip(vectors,word))
                   for word in product(bpz.LABELS, repeat=len(vectors))}
        value = sum(weights[word] for word in code)
        if value != int(entry['M']) or not all(exchange.terminal.separated(a,b,graphs)
                                                  for a,b in combinations(code,2)):
            raise ValueError('candidate failed exact replay')
        if args.replay_only:
            print(f'{name}: replayed {len(code)} tuples at d={dimension}; '
                  f'rate {check.C.nth_root_digits(value, dimension, 20)}; '
                  f'exceeds Tang: {value ** baseline["dimension"] > original ** dimension}.', flush=True)
            continue
        witness, gain, stats = exchange.solve(code,weights,graphs,args.radius)
        counts[name][0] += 1
        counts[name][1] += sum(row[0] for row in stats)
        counts[name][2] += bool(gain)
        candidate = value + gain
        if gain:
            variants.append(dict(entry, M=str(candidate), explicit_terminal=witness))
            print('  Reweighted construction:', check.C.nth_root_digits(candidate, dimension, 20), flush=True)
        if candidate ** best[1] > best[0] ** dimension:
            best = candidate, dimension, dict(entry,M=str(candidate),explicit_terminal=witness or code)
        print(f'{name}, d={dimension}, candidate {counts[name][0]}: '
              f'{sum(row[0] for row in stats):,} masks, improvement {bool(gain)}.', flush=True)
    if args.replay_only:
        return
    for name,(trials,masks,improved) in counts.items():
        if trials:
            print(f'{name}: {trials} checked, {masks:,} masks, {improved} improved their own schedule.', flush=True)
    if args.variants:
        args.variants.write_text(json.dumps(variants, indent=2)+'\n', encoding='utf-8')
    if best[2] is not None:
        print('Stronger lower bound:', check.C.nth_root_digits(best[0],best[1],20), flush=True)
        if args.output:
            args.output.write_text(json.dumps(best[2],indent=2)+'\n',encoding='utf-8')
    else:
        print('No stronger lower bound after terminal exchanges.', flush=True)


if __name__ == '__main__':
    main()
