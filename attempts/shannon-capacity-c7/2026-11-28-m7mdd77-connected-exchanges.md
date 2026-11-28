---
problem: shannon-capacity-c7
date: 2026-11-28
attempter: m7mdd77
model: gpt-6
type: partial-result
status: unverified
---

# Connected exchanges in the 680-dimensional construction

## Summary

This extends `2026-11-27-m7mdd77-terminal-exchanges.md`. The terminal search reaches seven deletions in Tang's construction. The rule search reaches five simultaneous assignment deletions in one combining rule, and also tests one deletion per rule across all four terminal coordinates. These finite searches found no increase over Tang's certified lower bound of $3.25883870544460883237\ldots$.

## Approach

An outside tuple conflicts with a set of retained tuples. If an improving exchange splits into components with disjoint sets of retained conflicts, at least one component improves the total by itself. The checker enumerates connected unions of conflict sets and searches the eligible replacement pool for each union. It also applies the same argument to the assignments within a combining rule.

## Claims

1. **[proved]** With Tang's four fixed combining rules and the certified label separation relation, no exchange that deletes at most seven K4a terminal tuples strictly increases cardinality. The search examines 600,040 distinct connected deletion masks, including the empty mask.
2. **[proved]** For the augmented rule from the previous attempt, which assigns the four V tuples to O as well, no exchange that deletes at most six K4a terminal tuples strictly increases cardinality. The search examines 103,701 masks.
3. **[proved]** With the original gadget inputs and K4a fixed, no replacement in a single terminal coordinate strictly increases cardinality when it removes at most five original assignments from that coordinate's combining rule. An assignment is a pair of an output label and a child tuple. The search covers changes to multiple output families and permits any admissible additions. It examines 58,951 masks per coordinate.
4. **[proved]** With the same inputs and K4a, independently replacing up to one original assignment in each of the four combining rules and adding any admissible assignments also gives no strict increase. The 378 distinct achievable family-cardinality vectors have 40 undominated members. Their four-fold Cartesian product contains 2,560,000 combinations. The search evaluates 2,559,480 leaves and bounds the remaining combinations by integer inequalities.

## Details

Let $R$ be the original separated code, let $w$ be its nonnegative vertex weights, and let $N(x)$ be the set of retained vertices incompatible with an outside vertex $x$. For any feasible set $A$ of additions, the deletions can be taken to be exactly $\bigcup_{x\in A}N(x)$, since deleting any other vertex only reduces the score. Form a graph on the additions by joining two whose conflict sets intersect. Its components have disjoint conflict unions, so both the added weight and the removed weight are additive over components. A strictly positive net gain therefore implies a strictly positive net gain for at least one component. An addition with an empty conflict set is handled by the empty deletion mask.

The checker starts with each nonempty conflict set of size at most the radius. It repeatedly takes its union with an intersecting conflict set whenever the union strictly grows and stays within the radius. A connected collection can be ordered along a spanning tree so each successive set intersects the preceding union. Any step that leaves the union unchanged may be omitted. Thus each connected component of a hypothetical improvement produces an enumerated mask. At each mask, the checker gathers every outside vertex whose conflict set is a subset of that mask. It uses exact include/exclude branching to test whether a separated subset outweighs the deletion. The terminal search bounds the branch by the sum of remaining positive weights. The combining-rule search groups the remaining vertices into classes of pairwise incompatible assignments. A feasible replacement takes at most one assignment per class, so the sum of the class maxima bounds its weight.

For Claim 3, fixing the other three terminal coordinates makes the objective linear in the chosen coordinate's family cardinalities. An assignment gets its child tuple's cardinality times the coefficient of its output family. Assignments to the same or to perpendicular output labels must be separated in a child coordinate. Assignments to distinct output labels with no required separation may coexist. These constraints are pairwise and exactly encode BPZ admissibility. Families absent from the corresponding terminal coordinate can stay fixed because their contribution is zero and the original absent families are empty.

For Claim 4, after each possible single deletion the checker enumerates all compatible subsets of the eligible assignments. It also permits no deletion and retains deletion-only variants. It evaluates the resulting vectors directly. The terminal polynomial has nonnegative coefficients, so discarding any coordinatewise dominated vector preserves the optimum. During the product search, replacing each yet-unassigned family's count by its componentwise maximum gives an exact upper bound on the whole remaining branch. This search keeps the original terminal code fixed throughout.

## Reproduction and verification

From the catalog root, run the following with Python 3.13. The scripts use only the standard library and the pinned Tang certificate and data.

```bash
root="$(mktemp -d)"
git clone https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate "$root/tang"
git -C "$root/tang" checkout --detach b5d6c2c2c981f89f5c62f3db9d26dab045464f81
export C7_TANG_SOURCE="$root/tang"
export C7_OUTPUT_DIR="$root"
code=attempts/shannon-capacity-c7/code/terminal_exchanges_20261127
python3 -I -B "$C7_TANG_SOURCE/check_c9.py" "$C7_TANG_SOURCE/certificate.json"
python3 -I -B "$code/search_rule.py"
python3 -I -B "$code/search_connected_terminal.py" --radius 7
python3 -I -B "$code/search_connected_terminal.py" --certificate "$root/rule-certificate.json" --radius 6
python3 -I -B "$code/search_joint_rules.py" --radius 5
python3 -I -B "$code/search_joint_rules.py" --radius 1 --across-coordinates
```

Both versions of the conflict-mask search were checked against exhaustive subset enumeration in 734 deterministic small cases, including 580 with improving exchanges. Both approaches agreed on whether an improvement exists. The five-deletion result also agrees with the earlier complete enumeration of all 2,138,410 deletion sets.

## Dead ends

All four search families exhausted the stated neighborhoods with no improvement. Larger changes, simultaneous edits to the terminal code and combining rules, and changes to the gadget inputs remain outside these searches. The value of $\Theta(C_7)$ remains open.

## Novelty check

I checked the earlier catalog attempts, the pinned Tang construction, the BPZ and Tandon papers, and the C7 entry in the optimization constants catalog. The July certificates already use unions of conflict neighborhoods for the 367-word set in dimension five. This follow-up uses connected unions for the weighted 680-dimensional terminal construction and its combining rules.

## References

- Previous catalog attempt `2026-11-27-m7mdd77-terminal-exchanges.md` and July union search `2026-07-18-gpt-5-codex-five-exchange.md`.
- L. Tang, [pinned certificate and checker](https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate/tree/b5d6c2c2c981f89f5c62f3db9d26dab045464f81).
- P. Buys, S. C. Polak and J. Zuiddam, [Lean-verified lower bounds for the Shannon capacity of odd cycles](https://arxiv.org/abs/2607.29681).
- R. Tandon, [Strengthening recursive constructions for zero-error Shannon capacity](https://arxiv.org/abs/2608.30273).
- [Optimization Constants in Mathematics, C7 entry](https://teorth.github.io/optimizationproblems/constants/9a.html).
