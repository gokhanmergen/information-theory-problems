"""Optimize one output family of a BPZ combining rule at a time."""
from itertools import combinations, product
import json
from math import prod
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import search_terminal as terminal

search, check = terminal.search, terminal.check
bpz = check.bpz


def main():
    ledger = check.C.load_certificates()
    theorem = check.C.theorem2(ledger)
    patterns = search.recorded_patterns(ledger, theorem)
    baseline = json.loads((search.UPSTREAM / "certificate.json").read_text())
    base = {label: search.Candidate(profile, 5, "base", ())
            for label, profile in zip(("G5", "sG5"), check.C.base_profiles(ledger))}
    nodes = search.record_nodes(baseline, patterns, base)
    row = [nodes[label[4:-1]].vector for label in baseline["top"]["rule_inputs"]]
    relation = {(a, b) for a in bpz.LABELS for b in bpz.LABELS if bpz.perp(a, b)}
    graphs = [relation] * len(row)
    weights = {word: prod(v[bpz.INDEX[x]] for v, x in zip(row, word))
               for word in product(bpz.LABELS, repeat=len(row))}
    rule = {key: [tuple(word) for word in group] for key, group in bpz.S3b.items()}
    code = [tuple(word) for word in bpz.K4a]
    original = int(baseline["M"])
    if bpz.rule_problems(rule) or bpz.code_problems(code):
        raise ValueError("starting rule or code invalid")
    if bpz.apply_code(code, [bpz.apply_rule(rule, row)] * len(code[0])) != original:
        raise ValueError("starting rule or code does not reproduce published count")

    for iteration in range(3):
        changes = 0
        for label in bpz.LABELS:
            neighbors = [word for mu in bpz.LABELS if bpz.perp(label, mu)
                         for word in rule[mu]]
            possible = [word for word, w in weights.items() if w and
                        all(terminal.separated(word, v, graphs) for v in neighbors)]
            seed = rule[label]
            if not set(seed).issubset(possible):
                raise ValueError("original family is outside its feasible pool")
            witness, score, tested, finished = terminal.exact_clique(
                possible, weights, graphs, seed, 200000
            )
            old = sum(weights[word] for word in seed)
            print(f"Round {iteration + 1}, output {label}, {len(possible)} tuples, "
                  f"{tested} nodes, {'exact' if finished else 'cut off'}, gain {score - old}",
                  flush=True)
            if score > old:
                rule[label] = list(witness)
                if bpz.rule_problems(rule):
                    raise ValueError("a changed rule became inadmissible")
                changes += 1
        if not changes:
            break
    inner = bpz.apply_rule(rule, row)
    value = bpz.apply_code(code, [inner] * len(code[0]))
    print("O cardinality:", inner[bpz.INDEX["O"]], flush=True)
    print("Rule search bound:", check.C.nth_root_digits(value, baseline["dimension"], 20))
    if value > original or rule["O"]:
        updated = dict(baseline, M=str(value), explicit_rule=rule)
        (search.OUTPUT / "rule-certificate.json").write_text(json.dumps(updated, indent=2) + "\n")

    # Compare all ways to require O to be separated from additional families.
    optional = ("A", "D", "H", "V")
    variants = 0
    best_value, best_rule, best_code = value, rule, code
    terminal_words = [w for w in product(bpz.LABELS, repeat=len(code[0])) if "O" in w]
    for count in range(len(optional) + 1):
        for required in combinations(optional, count):
            neighbors = [word for label in ("B", "N") + required for word in rule[label]]
            possible = [word for word, mass in weights.items() if mass and
                        all(terminal.separated(word, other, graphs) for other in neighbors)]
            if not possible:
                continue
            witness, _, _, finished = terminal.exact_clique(possible, weights, graphs, [], 200000)
            if not finished:
                raise ValueError("O family search did not finish")
            trial = dict(rule, O=list(witness))
            if bpz.rule_problems(trial):
                raise ValueError("O variant is inadmissible")
            variants += 1
            graph = terminal.induced_separation(trial)
            relation4 = [graph] * len(code[0])
            row_counts = bpz.apply_rule(trial, row)
            size = bpz.apply_code(code, [row_counts] * len(code[0]))
            masses4 = {w: prod(row_counts[bpz.INDEX[x]] for x in w) for w in terminal_words}
            available = [w for w in terminal_words
                         if masses4[w] and all(terminal.separated(w, z, relation4) for z in code)]
            extra, added = terminal.best_addition(available, masses4, relation4, 0)
            if size + extra > best_value:
                best_value, best_rule, best_code = size + extra, trial, code + list(added)
            print(f"O required neighbors {required}, {len(witness)} source tuples, "
                  f"{len(available)} eligible new terminal tuples", flush=True)
    print(f"O variants with positive weight: {variants}", flush=True)
    if best_value > original:
        path = search.OUTPUT / "terminal-certificate.json"
        path.write_text(json.dumps(dict(baseline, M=str(best_value), explicit_rule=best_rule,
                                        explicit_terminal=best_code), indent=2) + "\n")
        print("Rule variant bound:", check.C.nth_root_digits(best_value, baseline["dimension"], 20))

if __name__ == "__main__":
    main()
