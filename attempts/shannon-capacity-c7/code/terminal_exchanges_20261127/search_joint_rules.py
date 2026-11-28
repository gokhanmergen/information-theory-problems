"""Search joint changes to a BPZ rule in one terminal coordinate at a time."""

import argparse
from itertools import product
import json
from math import prod
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_connected_terminal as exchange

terminal = exchange.terminal
search, check = terminal.search, terminal.check
bpz = check.bpz


def one_deletion_profiles(seed, child_weights, code, compatible, inputs):
    """Count all admissible replacements after at most one deletion."""
    used = sorted({label for word in code for label in word})
    groups = {}
    for entry in product(used, child_weights):
        if not child_weights[entry[1]] or entry in seed:
            continue
        conflicts = [old for old in seed if not compatible(entry, old)]
        if len(conflicts) <= 1:
            groups.setdefault(conflicts[0] if conflicts else None, []).append(entry)

    def rules(kept, added, available):
        yield kept + added
        for position, entry in enumerate(available):
            remaining = [other for other in available[position + 1:] if compatible(entry, other)]
            yield from rules(kept, added + [entry], remaining)

    profiles = {}
    free = groups.get(None, [])
    for removed in [None] + seed:
        kept = [entry for entry in seed if entry != removed]
        available = free + (groups.get(removed, []) if removed else [])
        for selected in rules(kept, [], available):
            rule = {label: [] for label in bpz.LABELS}
            for label, word in selected:
                rule[label].append(word)
            vector = tuple(bpz.apply_rule(rule, inputs))
            profiles[vector] = rule
    frontier = {vector: rule for vector, rule in profiles.items() if not any(
        vector != other and all(a <= b for a, b in zip(vector, other)) for other in profiles
    )}
    print(f"{len(profiles)} distinct vectors; {len(frontier)} undominated vectors.", flush=True)
    return frontier


def across_coordinates(seed, child_weights, code, compatible, inputs, original):
    profiles = one_deletion_profiles(seed, child_weights, code, compatible, inputs)
    indexed = [tuple(bpz.INDEX[label] for label in word) for word in code]
    width = len(indexed[0])
    maxima = tuple(max(values) for values in zip(*profiles))
    remaining = [[prod(maxima[i] for i in word[depth:]) for word in indexed]
                 for depth in range(width)]
    best, witness = original, None
    leaves, pruned = 0, 0

    def visit(depth, masses, chosen):
        nonlocal best, witness, leaves, pruned
        if sum(a * b for a, b in zip(masses, remaining[depth])) <= best:
            pruned += 1
            return
        if depth == width - 1:
            coefficients = [0] * len(bpz.LABELS)
            for mass, word in zip(masses, indexed):
                coefficients[word[depth]] += mass
            for vector in profiles:
                value = sum(a * b for a, b in zip(coefficients, vector))
                leaves += 1
                if value > best:
                    best, witness = value, chosen + (vector,)
            return
        for vector in profiles:
            selected = [mass * vector[word[depth]] for mass, word in zip(masses, indexed)]
            visit(depth + 1, selected, chosen + (vector,))

    visit(0, [1] * len(code), ())
    print(f"{len(profiles) ** width:,} combinations represented; {leaves:,} explicit leaf "
          f"evaluations; {pruned:,} bounded branches.", flush=True)
    if witness is None:
        return 0, None
    rules = [profiles[vector] for vector in witness]
    if any(bpz.rule_problems(rule) for rule in rules) or bpz.apply_code(code, witness) != best:
        raise ValueError("combined rule witness fails direct validation")
    return best - original, rules



def within_coordinate(rule, child_weights, code, compatible, inputs, vector, original, radius):
    width = len(code[0])
    best_gain, best_rules = 0, None
    for coordinate in range(width):
        coefficients = dict.fromkeys(bpz.LABELS, 0)
        for word in code:
            coefficients[word[coordinate]] += prod(vector[bpz.INDEX[label]]
                                                     for i, label in enumerate(word) if i != coordinate)
        # Keep zero-coefficient families fixed. Their existing vertices still
        # impose the separation constraints on any candidate assignment.
        fixed = [(label, tuple(word)) for label, words in rule.items() if not coefficients[label]
                 for word in words]
        seed = [(label, tuple(word)) for label, words in rule.items() if coefficients[label]
                for word in words]
        weights = {(label, word): coefficient * weight
                   for label, coefficient in coefficients.items() if coefficient
                   for word, weight in child_weights.items() if weight and
                   all(compatible((label, word), entry) for entry in fixed)}
        if not set(seed) <= weights.keys() or sum(weights[entry] for entry in seed) != original:
            raise ValueError("linearized objective disagrees with original size")
        print(f"Coordinate {coordinate + 1}, {len(weights):,} possible assignments", flush=True)
        witness, gain, stats = exchange.solve_exchanges(seed, weights, compatible, radius,
                                                        report=True, color_pools=True)
        print(f"Coordinate {coordinate + 1}: {sum(row[0] for row in stats):,} unions, positive gain {bool(gain)}.",
              flush=True)
        if gain <= best_gain:
            continue
        trial_rule = {label: [] for label in bpz.LABELS}
        for label, word in fixed + list(witness):
            trial_rule[label].append(word)
        if bpz.rule_problems(trial_rule):
            raise ValueError("modified rule is inadmissible")
        rules = [rule] * width
        rules[coordinate] = trial_rule
        final = bpz.apply_code(code, [bpz.apply_rule(item, inputs) for item in rules])
        if final != original + gain:
            raise ValueError("direct evaluation disagrees with linearized gain")
        best_gain, best_rules = gain, rules
    return best_gain, best_rules

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--radius", type=int, required=True)
    parser.add_argument("--across-coordinates", action="store_true",
                        help="allow one deletion in each terminal coordinate simultaneously")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.radius < 0:
        parser.error("radius must be nonnegative")
    if args.across_coordinates and args.radius != 1:
        parser.error("--across-coordinates requires --radius 1")
    cert = json.loads((search.UPSTREAM / "certificate.json").read_text(encoding="utf-8"))
    ledger = check.C.load_certificates()
    patterns = search.recorded_patterns(ledger, check.C.theorem2(ledger))
    bases = {label: search.Candidate(profile, 5, "base", ())
             for label, profile in zip(("G5", "sG5"), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(cert, patterns, bases)
    top = cert["top"]
    inputs = [nodes[name[4:-1]].vector for name in top["rule_inputs"]]
    rule = bpz.RULES[top["rule"]]
    code = bpz.CODES[top["terminal_code"]]
    vector = bpz.apply_rule(rule, inputs)
    original = int(cert["M"])
    width = len(code[0])
    if bpz.rule_problems(rule) or bpz.code_problems(code):
        raise ValueError("original rule or terminal code is inadmissible")
    if bpz.apply_code(code, [vector] * width) != original:
        raise ValueError("original rule has the wrong cardinality")
    child_weights = {word: prod(counts[bpz.INDEX[label]] for counts, label in zip(inputs, word))
                     for word in product(bpz.LABELS, repeat=len(inputs))}

    # Two assignments in distant output families do not constrain each other.
    # Identical or perpendicular families require a separated child coordinate.
    def compatible(left, right):
        label, word = left
        other_label, other_word = right
        return (label != other_label and not bpz.perp(label, other_label)) or any(
            bpz.perp(a, b) for a, b in zip(word, other_word))

    if args.across_coordinates:
        seed = [(label, tuple(word)) for label, words in rule.items() for word in words]
        used = {label for word in code for label in word}
        if any(label not in used for label, _ in seed):
            raise ValueError("across-coordinate search expects unused families to be empty")
        best_gain, best_rules = across_coordinates(seed, child_weights, code, compatible, inputs, original)
    else:
        best_gain, best_rules = within_coordinate(rule, child_weights, code, compatible, inputs,
                                                 vector, original, args.radius)
    if best_gain:
        print("Improved lower bound:", check.C.nth_root_digits(original + best_gain, cert["dimension"], 20))
        if args.output:
            updated = dict(cert, M=str(original + best_gain), explicit_subtree_rules=best_rules)
            args.output.write_text(json.dumps(updated, indent=2) + "\n", encoding="utf-8")
    else:
        print("No improving joint rule exchange under the tested removal limit.", flush=True)


if __name__ == "__main__":
    main()
