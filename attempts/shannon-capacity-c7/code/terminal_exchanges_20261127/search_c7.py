"""Explore certified C7 gadget compositions near the Tang certificate."""
import argparse
from dataclasses import dataclass
from functools import reduce
from itertools import combinations
import json
from operator import mul
from os import environ
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
UPSTREAM = Path(environ.get("C7_TANG_SOURCE", HERE / "tang-source")).resolve()
OUTPUT = Path(environ.get("C7_OUTPUT_DIR", HERE)).resolve()
sys.path.insert(0, str(UPSTREAM))
import check_c9 as check

LOWER_NUM, LOWER_DEN = 3258838705444608, 10**15


@dataclass(eq=False)
class Candidate:
    profile: object
    dimension: int
    operation: str
    arguments: tuple

    @property
    def vector(self):
        return check.Phi(self.profile)


def record_nodes(cert, patterns, base):
    nodes = dict(base)
    for step in cert["gadgets"]:
        if step["op"] == "sigma":
            node = flip(nodes[step["of"]])
        elif step["op"] == "hetgao":
            node = extend(patterns, step["pattern"], nodes[step["R"]])
        elif step["op"] == "gao":
            node = product(nodes[step["L"]], nodes[step["R"]])
        else:
            raise ValueError(step)
        nodes[step["name"]] = node
    return nodes


def flip(node):
    return Candidate(check.sigma(node.profile, name="search"), node.dimension,
                     "sigma", (node,))


def extend(patterns, pattern, right):
    left, keywords, dim = patterns[pattern]
    profile = check.hetgao(left, right.profile, name="search", **keywords)
    return Candidate(profile, dim + right.dimension, "hetgao", (pattern, right))


def product(left, right):
    profile = check.gao(left.profile, right.profile, name="search")
    return Candidate(profile, left.dimension + right.dimension, "gao", (left, right))


def beam(candidates, slots):
    distinct = {}
    for node in candidates:
        distinct.setdefault(node.profile.as_tuple(), node)
    ranked = list(distinct.values())
    # Linear coordinate objectives retain profiles for distinct BPZ roles.
    objectives = [
        lambda v: v[0], lambda v: v[1], lambda v: v[2], lambda v: v[3], lambda v: v[4],
        lambda v: v[0] + v[4], lambda v: v[1] + v[2] + v[3],
        lambda v: v[0] + 2 * v[4], lambda v: v[0] + v[1],
        lambda v: v[2] + v[3], lambda v: v[0] + v[1] + 2 * v[4],
    ]
    retained = {}
    for score in objectives:
        for node in sorted(ranked, key=lambda node: score(node.vector), reverse=True)[:slots]:
            retained[node.profile.as_tuple()] = node
    return list(retained.values()), len(ranked)


def make_pool(patterns, base, records, max_dim, slots):
    by_dim = {}
    generated = 0
    for dimension in range(5, max_dim + 1, 5):
        fresh = [node for node in records.values() if node.dimension == dimension]
        for pattern, (_, _, left_dim) in patterns.items():
            fresh.extend(extend(patterns, pattern, right)
                         for right in by_dim.get(dimension - left_dim, []))
        for left in base.values():
            for right in by_dim.get(dimension - left.dimension, []):
                fresh.extend((product(left, right), product(right, left)))
        fresh += [flip(node) for node in fresh]
        by_dim[dimension], count = beam(fresh, slots)
        generated += count
    return by_dim, generated


def result(inputs, rule, code):
    subtrees = [check.bpz.apply_rule(rule, [node.vector for node in part]) for part in inputs]
    return check.bpz.apply_code(code, subtrees), sum(node.dimension for part in inputs for node in part)


def gradient(poly_words, operands, slot):
    """The polynomial is linear in the selected operand's seven labels."""
    weights = [0] * 7
    for word, scale in poly_words:
        labels = tuple(check.bpz.INDEX[label] for label in word)
        weight = reduce(mul, (vector[label] for i, (vector, label) in
                              enumerate(zip(operands, labels)) if i != slot), scale)
        weights[labels[slot]] += weight
    return weights


def best_replacement(inputs, row, slot, pool, rule, code, size, dim):
    vectors = [[node.vector for node in part] for part in inputs]
    inner = [check.bpz.apply_rule(rule, part) for part in vectors]
    outer_weights = gradient(((word, 1) for word in code), inner, row)
    words = ((word, scale) for label, scale in zip(check.bpz.LABELS, outer_weights)
             if scale for word in rule[label])
    weights = gradient(words, vectors[row], slot)
    fixed_dim = dim - inputs[row][slot].dimension
    best, best_size, best_dim = inputs[row][slot], size, dim
    tested = 0
    for new_dim, nodes in pool.items():
        if not nodes:
            continue
        new_size, node = max(
            ((sum(a * b for a, b in zip(weights, node.vector)), node) for node in nodes),
            key=lambda pair: pair[0],
        )
        tested += len(nodes)
        candidate_dim = fixed_dim + new_dim
        # Reject only points below the verified rational lower bound.
        if new_size * LOWER_DEN ** candidate_dim >= LOWER_NUM ** candidate_dim:
            if (new_size > best_size if candidate_dim == best_dim
                    else new_size ** best_dim > best_size ** candidate_dim):
                best, best_size, best_dim = node, new_size, candidate_dim
    return best, best_size, best_dim, tested



def strongest_pair(inputs, pool, rule, code, size, dim, per_dimension):
    vectors = [[node.vector for node in part] for part in inputs]
    inner = [check.bpz.apply_rule(rule, part) for part in vectors]
    best = None
    tests = 0
    for row, part in enumerate(inputs):
        outer = gradient(((word, 1) for word in code), inner, row)
        words = [(word, scale) for label, scale in zip(check.bpz.LABELS, outer)
                 if scale for word in rule[label]]
        rankings = []
        for slot in range(len(part)):
            linear = gradient(words, vectors[row], slot)
            rankings.append([
                node for nodes in pool.values() for node in sorted(
                    nodes,
                    key=lambda n: sum(a * b for a, b in zip(linear, n.vector)),
                    reverse=True,
                )[:per_dimension]
            ])
        for left, right in combinations(range(len(part)), 2):
            tensor = {}
            for word, scale in words:
                positions = tuple(check.bpz.INDEX[label] for label in word)
                for k, (v, i) in enumerate(zip(vectors[row], positions)):
                    if k != left and k != right:
                        scale *= v[i]
                key = positions[left], positions[right]
                tensor[key] = tensor.get(key, 0) + scale
            terms = [(i, j, w) for (i, j), w in tensor.items() if w]
            fixed = dim - part[left].dimension - part[right].dimension
            top_by_dim = {}
            for a in rankings[left]:
                va = a.vector
                for b in rankings[right]:
                    vb = b.vector
                    value = sum(w * va[i] * vb[j] for i, j, w in terms)
                    new_dim = fixed + a.dimension + b.dimension
                    tests += 1
                    prev = top_by_dim.get(new_dim)
                    if prev is None or value > prev[0]:
                        top_by_dim[new_dim] = value, a, b
            for new_dim, (value, a, b) in top_by_dim.items():
                if value * LOWER_DEN ** new_dim < LOWER_NUM ** new_dim:
                    continue
                if value ** dim > size ** new_dim:
                    if best is None or value ** best[1] > best[0] ** new_dim:
                        best = value, new_dim, row, left, right, a, b
    return best, tests

def encode(rows, bases, value, dimension):
    names = {node: label for label, node in bases.items()}
    steps = []

    def emit(node):
        if node not in names:
            if node.operation == "sigma":
                args = {"of": emit(node.arguments[0])}
            elif node.operation == "gao":
                args = {"L": emit(node.arguments[0]), "R": emit(node.arguments[1])}
            else:
                args = {"pattern": node.arguments[0], "R": emit(node.arguments[1])}
            names[node] = "g" + str(len(steps))
            steps.append({"name": names[node], "op": node.operation, **args})
        return "Phi(" + names[node] + ")"

    subtrees = [[emit(node) for node in part] for part in rows]
    return {"gadgets": steps, "top": {"rule": "S3b", "terminal_code": "K4a",
                                     "subtrees": subtrees},
            "dimension": dimension, "M": str(value)}



def recorded_patterns(ledger, theorem):
    """Counts recomputed by the pinned checker for the published certificate."""
    patterns = check.tan_patterns(ledger, theorem)
    g5, sg5 = check.C.base_profiles(ledger)
    operands = {
        "G5": (g5, 5), "sG5": (sg5, 5), "G10": (theorem["G10"], 10),
        "sG15AX": (check.sigma(theorem["G15AX"]), 15),
        "sG15Ah": (check.sigma(theorem["G15Ah"]), 15),
    }
    rows = (
        ("S<G15X,G10,P15X>", "P15X", "G10", 6682034753199, 2168034218823),
        ("N<S<G15X,G10,P15X>,G5>", "S<G15X,G10,P15X>", "G5",
         2455687916341537, 840885528362080),
        ("S<G15AX,G5,P15A8>", "P15A8", "G5", 18184231617, 5415710640),
        ("N<S<G15AX,G5,P15A8>,G5>", "S<G15AX,G5,P15A8>", "G5",
         6681986127279, 2167394749159),
        ("S<G15AX,sG15AX,P15A5>", "P15A5", "sG15AX",
         2455726444728097, 841149894373344),
        ("N<S<G15AX,sG15AX,P15A5>,sG15AX>", "S<G15AX,sG15AX,P15A5>", "sG15AX",
         121947917749163375722991, 44457037740952884957687),
        ("S<G15AX,sG15Ah,P15A8>", "P15A8", "sG15Ah",
         2455726444728097, 841760069965664),
        ("N<S<G15AX,sG15Ah,P15A8>,sG15Ah>", "S<G15AX,sG15Ah,P15A8>", "sG15Ah",
         121947917749163375722991, 44503522527412807055847),
    )
    for name, pattern, right, j, q in rows:
        left, kw, left_dim = patterns[pattern]
        factor, factor_dim = operands[right]
        main = check.gao(left, factor)
        refined = check.hetgao(left, factor, **kw)
        side = check.SideCodebook(j, q)
        patterns[name] = (
            main, dict(J0=check.neutral_from(refined), JH=side, JV=side), left_dim + factor_dim
        )
    return patterns

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-dimension", type=int, default=100)
    parser.add_argument("--slots", type=int, default=7)
    parser.add_argument("--passes", type=int, default=5)
    parser.add_argument("--pair-slots", type=int, default=0)
    args = parser.parse_args()

    ledger = check.C.load_certificates()
    theorem = check.C.theorem2(ledger)
    patterns = recorded_patterns(ledger, theorem)
    published = json.loads((UPSTREAM / "certificate.json").read_text())
    base = {label: Candidate(profile, 5, "base", ())
            for label, profile in zip(("G5", "sG5"), check.C.base_profiles(ledger))}
    nodes = record_nodes(published, patterns, base)
    pool, generated = make_pool(patterns, base, nodes, args.max_dimension, args.slots)
    print(f"Generated {generated} distinct dimension-profile pairs, retained "
          f"{sum(map(len, pool.values()))} in {len(pool)} dimensions.", flush=True)

    start = [nodes[label[4:-1]] for label in published["top"]["rule_inputs"]]
    rule, code = check.bpz.S3b, check.bpz.K4a
    if check.bpz.rule_problems(rule) or check.bpz.code_problems(code):
        raise ValueError("incompatible product or terminal code")
    inputs = [list(start) for _ in code[0]]
    size, dimension = result(inputs, rule, code)
    if size != int(published["M"]) or dimension != published["dimension"]:
        raise ValueError("published baseline did not reproduce")
    original_size, original_dim = size, dimension
    if size * LOWER_DEN ** dimension < LOWER_NUM ** dimension:
        raise ValueError("rational filter is above the published construction")
    print(f"Baseline: {check.C.nth_root_digits(size, dimension, 20)} at dimension {dimension}",
          flush=True)
    total_tested = 0
    for iteration in range(args.passes):
        changes = 0
        for row, part in enumerate(inputs):
            for slot in range(len(part)):
                node, new_size, new_dim, tested = best_replacement(
                    inputs, row, slot, pool, rule, code, size, dimension)
                total_tested += tested
                if (new_size, new_dim) != (size, dimension):
                    inputs[row][slot] = node
                    size, dimension = new_size, new_dim
                    changes += 1
                    if result(inputs, rule, code) != (size, dimension):
                        raise ValueError("linear scoring disagrees with direct rule evaluation")
                    print(f"Pass {iteration + 1}, row {row + 1}, slot {slot + 1}: "
                          f"{check.C.nth_root_digits(size, dimension, 20)} at d={dimension}",
                          flush=True)
        if not changes:
            if not args.pair_slots:
                break
            pair, tested = strongest_pair(inputs, pool, rule, code, size, dimension, args.pair_slots)
            print(f"Pair substitution evaluations: {tested}", flush=True)
            if pair is None:
                break
            size, dimension, row, left, right, a, b = pair
            inputs[row][left], inputs[row][right] = a, b
            if result(inputs, rule, code) != (size, dimension):
                raise ValueError("bilinear scoring disagrees with direct rule evaluation")
            print(f"Pass {iteration + 1}, row {row + 1}, slots {left + 1} and {right + 1}: "
                  f"{check.C.nth_root_digits(size, dimension, 20)} at d={dimension}", flush=True)
    print(f"Single substitution evaluations: {total_tested}", flush=True)
    if size ** original_dim <= original_size ** dimension:
        print("No improvement found in this constrained search.", flush=True)
        return
    print(f"Exact strict comparison: M^{original_dim} > M_baseline^{dimension}", flush=True)
    certificate = encode(inputs, base, size, dimension)
    (OUTPUT / "candidate-certificate.json").write_text(json.dumps(certificate, indent=2) + "\n")


if __name__ == "__main__":
    main()
