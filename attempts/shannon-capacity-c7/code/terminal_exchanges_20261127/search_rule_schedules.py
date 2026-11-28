"""Search certified BPZ rule schedules over Tang's three fixed gadgets."""

import argparse
from dataclasses import dataclass
from itertools import permutations, product
import json
from math import isqrt, prod
from pathlib import Path
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_c7 as search

check = search.check
bpz = check.bpz


@dataclass(frozen=True)
class Row:
    vector: tuple
    expression: object


@dataclass
class Cluster:
    high: tuple
    count: int
    spread: int
    row: Row | None = None
    children: tuple = ()


def row_variants(inputs):
    variants = {}
    binary = {name: rule for name, rule in bpz.RULES.items() if name.startswith('S2')}
    ternary = {name: rule for name, rule in bpz.RULES.items() if name.startswith('S3')}
    count = 0

    def orientations(row):
        yield row
        yield Row(bpz.sigma_vector(row.vector), ['sigma', row.expression])

    def combine(name, rule, rows):
        nonlocal count
        count += 1
        vector = bpz.apply_rule(rule, [row.vector for row in rows])
        return Row(vector, [name, *(row.expression for row in rows)])

    def record(row):
        for current in orientations(row):
            variants.setdefault(current.vector, current)

    for oriented in product(*(tuple(orientations(row)) for row in inputs)):
        for a, b, c in permutations(oriented):
            for name, rule in ternary.items():
                record(combine(name, rule, (a, b, c)))
            for key, branch_rule in binary.items():
                inner = combine(key, branch_rule, (a, b))
                for middle in orientations(inner):
                    for name, rule in binary.items():
                        for order in ((middle, c), (c, middle)):
                            record(combine(name, rule, order))
    return list(variants.values()), count


def undominated(rows, used):
    unique = {}
    for row in rows:
        unique.setdefault(tuple(row.vector[i] for i in used), row)
    return [row for values, row in unique.items() if not any(
        values != other and all(x <= y for x, y in zip(values, other)) for other in unique
    )]


def verify_dominance(rows, used, certificate):
    labels = [bpz.LABELS[i] for i in used]
    if certificate['labels'] != labels or certificate['count'] != len(rows):
        raise ValueError('dominance certificate does not match these profiles')
    entries = certificate['witnesses']
    indices = [index for index, _ in entries]
    if len(set(indices)) != len(indices) or any(type(i) is not int or not 0 <= i < len(rows) for i in indices):
        raise ValueError('duplicate or invalid dominated profile index')
    removed = set(indices)
    for index, terms in entries:
        if not terms or any(type(j) is not int or not 0 <= j < len(rows) or j in removed or
                            type(weight) is not int or weight <= 0 for j, weight in terms):
            raise ValueError('dominance witness must use only retained profiles with positive coefficients')
        denominator = sum(weight for _, weight in terms)
        if any(sum(weight * rows[j].vector[k] for j, weight in terms) < denominator * rows[index].vector[k]
               for k in used):
            raise ValueError(f'dominance inequality failed at vector {index}')
    return [row for i, row in enumerate(rows) if i not in removed]


def score(words, vectors):
    return sum(prod(vector[index] for vector, index in zip(vectors, word)) for word in words)


def linear_scores(words, vectors, coordinate):
    coeff = [0] * len(bpz.LABELS)
    for word in words:
        coeff[word[coordinate]] += prod(vectors[i][label] for i, label in enumerate(word)
                                        if i != coordinate)
    return coeff


def linear_value(coeff, vector):
    return sum(a * b for a, b in zip(coeff, vector))


def cluster(rows, used, scale):
    high = tuple(max(column) for column in zip(*(row.vector for row in rows)))
    low = tuple(min(column) for column in zip(*(row.vector for row in rows)))
    spreads = {i: (high[i] - low[i]) * 10**9 // max(scale[i], 1) for i in used}
    node = Cluster(high, len(rows), sum(spreads.values()))
    if len(rows) == 1:
        node.row = rows[0]
        return node
    axis = max(spreads, key=spreads.__getitem__)
    rows = sorted(rows, key=lambda row: row.vector[axis])
    middle = len(rows) // 2
    node.children = (cluster(rows[:middle], used, scale), cluster(rows[middle:], used, scale))
    return node


def ascent(words, rows, starts):
    width = len(words[0])
    best, witness = 0, None
    for row in starts:
        trial = [row] * width
        for _ in range(8):
            changed = False
            for i in range(width):
                coeff = linear_scores(words, [r.vector for r in trial], i)
                previous = linear_value(coeff, trial[i].vector)
                value, replacement = max(((linear_value(coeff, candidate.vector), candidate)
                                          for candidate in rows), key=lambda entry: entry[0])
                if value > previous:
                    trial[i] = replacement
                    changed = True
            if not changed:
                break
        value = score(words, [r.vector for r in trial])
        if value > best:
            best, witness = value, tuple(trial)
    return best, witness


def exact_boxes(words, roots, threshold, max_boxes=0, report=False):
    best, witness = threshold, None
    visited = pruned = covered = 0
    width = len(roots)
    start = monotonic()
    stopped = False

    def visit(box, vectors, bound):
        nonlocal best, witness, visited, pruned, covered, stopped
        if stopped:
            return
        visited += 1
        if max_boxes and visited > max_boxes:
            stopped = True
            return
        if bound <= best:
            pruned += 1
            covered += prod(node.count for node in box)
            return
        if report and visited % 100_000 == 0:
            print(f"  {visited:,} boxes, {covered:,} tuples covered in {monotonic() - start:.1f}s", flush=True)
        remaining = [i for i in range(width) if box[i].children]
        if not remaining:
            best, witness = bound, tuple(node.row for node in box)
            covered += 1
            return
        # Compute both child bounds for one coordinate. Prefer a wide cluster
        # with a loose envelope, then visit its stronger child first.
        i = max(remaining, key=lambda k: (box[k].spread, box[k].count))
        coeff = linear_scores(words, vectors, i)
        children = sorted(((linear_value(coeff, part.high), part) for part in box[i].children),
                          key=lambda entry: entry[0], reverse=True)
        for child_bound, part in children:
            visit(box[:i] + (part,) + box[i+1:], vectors[:i] + (part.high,) + vectors[i+1:], child_bound)

    initial = tuple(node.high for node in roots)
    visit(roots, initial, score(words, initial))
    if not stopped and covered != prod(node.count for node in roots):
        raise ValueError('branch coverage disagrees with search space')
    return best, witness, visited, pruned, covered, not stopped


def evaluate(expression, sources):
    if isinstance(expression, str):
        return sources[expression]
    name, *operands = expression
    values = [evaluate(item, sources) for item in operands]
    if name == 'sigma':
        return bpz.sigma_vector(values[0])
    return bpz.apply_rule(bpz.RULES[name], values)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-boxes', type=int, default=0, help='0 means complete exact search')
    parser.add_argument('--code', choices=bpz.CODES, action='append')
    parser.add_argument('--output', type=Path)
    parser.add_argument('--dominance', type=Path, help='optional exact convex-dominance certificate')
    args = parser.parse_args()
    if args.max_boxes < 0:
        parser.error('--max-boxes must be nonnegative')
    baseline = json.loads((search.UPSTREAM / 'certificate.json').read_text(encoding='utf-8'))
    ledger = check.C.load_certificates()
    patterns = search.recorded_patterns(ledger, check.C.theorem2(ledger))
    bases = {label: search.Candidate(profile, 5, 'base', ())
             for label, profile in zip(('G5', 'sG5'), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(baseline, patterns, bases)
    leaves = [label[4:-1] for label in baseline['top']['rule_inputs']]
    sources = {leaf: nodes[leaf].vector for leaf in leaves}
    dimension = sum(nodes[leaf].dimension for leaf in leaves)
    original = int(baseline['M'])
    if dimension * 4 != baseline['dimension'] or any(bpz.rule_problems(rule) for rule in bpz.RULES.values()):
        raise ValueError('bad input dimensions or inadmissible combining rule')
    baseline_vector = bpz.apply_rule(bpz.RULES[baseline['top']['rule']], [sources[name] for name in leaves])
    if bpz.apply_code(bpz.CODES[baseline['top']['terminal_code']], [baseline_vector]*4) != original:
        raise ValueError('original cardinality disagrees with certificate')
    rows, operations = row_variants([Row(sources[name], name) for name in leaves])
    if any(evaluate(row.expression, sources) != row.vector for row in rows):
        raise ValueError('row expression failed replay')
    print(f'{operations:,} combining operations, {len(rows):,} distinct row vectors, dimension {dimension}.', flush=True)
    dominance = json.loads(args.dominance.read_text(encoding='utf-8')) if args.dominance else None
    best_rate = None
    for name in args.code or bpz.CODES:
        code = bpz.CODES[name]
        if bpz.code_problems(code) or len(set(code)) != len(code):
            raise ValueError('inadmissible terminal code')
        words = [tuple(bpz.INDEX[label] for label in word) for word in code]
        width = len(words[0])
        used = sorted({i for word in words for i in word})
        frontier = undominated(rows, used)
        if dominance is not None:
            retained = verify_dominance(frontier, used, dominance)
            print(f'{name}: {len(frontier)-len(retained):,} exact convex-dominance witnesses verified.', flush=True)
            frontier = retained
        scale = tuple(map(max, zip(*(row.vector for row in frontier))))
        root = cluster(frontier, used, scale)
        # A size at or below this integer cannot beat the published rate.
        threshold = isqrt(isqrt(original ** width))
        if not threshold ** 4 <= original ** width < (threshold + 1) ** 4:
            raise ValueError('rate threshold is not the expected fourth root')
        homogeneous = sorted(frontier, key=lambda row: score(words, [row.vector] * width), reverse=True)
        heuristic, seed = ascent(words, frontier, homogeneous[:24])
        print(f'{name}: {len(frontier):,} row vectors, {len(frontier)**width:,} choices. '
              f'Coordinate ascent: {check.C.nth_root_digits(heuristic, dimension * width, 20)}.', flush=True)
        best, witness, visits, prunes, covered, complete = exact_boxes(
            words, (root,) * width, max(threshold, heuristic), args.max_boxes, report=True)
        if witness is None and heuristic > threshold:
            witness = seed
        print(f'{name}: {visits:,} boxes, {prunes:,} bounds, {covered:,} choices covered. '
              f'Complete: {complete}. Strict gain: {best > threshold}.', flush=True)
        if witness is not None:
            if bpz.apply_code(code, [evaluate(row.expression, sources) for row in witness]) != best:
                raise ValueError('new construction failed exact replay')
            if best ** baseline['dimension'] <= original ** (dimension * width):
                raise ValueError('new construction failed strict cross-power comparison')
            print('Improved lower bound:', check.C.nth_root_digits(best, dimension * width, 20), flush=True)
            candidate = (best, dimension * width, name, witness)
            if best_rate is None or best ** best_rate[1] > best_rate[0] ** candidate[1]:
                best_rate = candidate
    if best_rate and args.output:
        mass, d, name, witness = best_rate
        result = dict(baseline, M=str(mass), dimension=d,
                      top={'terminal_code': name, 'row_expressions': [row.expression for row in witness]})
        args.output.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
