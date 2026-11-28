---
problem: shannon-capacity-c7
date: 2026-11-28
attempter: m7mdd77
model: gpt-6
type: partial-result
status: unverified
---

# BPZ rule schedules over Tang's gadgets

## Summary

This extends `2026-11-28-m7mdd77-connected-exchanges.md` by varying the combining rules and the terminal code in the same search. The exact part exhausts a family of schedules over the three gadget inputs in Tang's construction. A broader heuristic search and subsequent terminal exchanges produced a 59-tuple construction in dimension 205, of rate $3.25883023548865186515\ldots$. Its rate is below Tang's $3.25883870544460883237\ldots$.

## Approach

Use Tang's three certified input gadgets, in dimensions 35, 75, and 60, once each in every 170-dimensional row. Independently orient each input by the BPZ label involution. Try every input permutation and each published ternary rule, or combine two inputs by a published binary rule and combine the result with the third using a second binary rule. Allow both outer orders and either orientation at the intermediate and final outputs. The three published terminal codes select three or four of these rows with independent row choices.

For exploration with varying dimensions, also allow a single pinned gadget or one published combining rule over a repeated selection of pinned gadgets. Coordinate ascent uses normalized counts to choose trial rows. Exact integer cardinalities and cross-powers compare all returned trials. Terminal exchanges then use the connected-conflict method from the preceding attempt.

## Claims

1. **[proved]** None of the fixed-input schedules above and the three published terminal codes $K3a$, $K4a$, and $K4b$ yields a strictly higher rate than Tang. The generator produces 1,296 distinct row vectors. Projection to the six labels used in the terminal codes and elimination of componentwise dominated vectors leaves 924. The supplied certificate proves convex domination for another 706. The remaining 218 rows give 10,360,232 ordered choices for $K3a$ and 2,258,530,576 each for $K4a$ and $K4b$. The exhaustive branch search covers all 4,527,421,384 choices.
2. **[heuristic]** Coordinate ascent over 22,742 dimension–vector profiles and 809 distinct starts across the three published codes found no stronger bound. Its 50 distinct final schedules were then checked exactly for improvements deleting at most four terminal tuples. Four schedules improved their own rates. Those four stayed below Tang's rate. The search checked 188,886 connected deletion masks in total.
3. **[proved]** The supplied dimension-205 certificate describes an independent set in $C_7^{\boxtimes205}$. Its 59 distinct terminal tuples are pairwise separated, its exact size replays from the recorded row expressions, and its rate is $3.25883023548865186515\ldots$. An integer cross-power comparison places it below Tang's rate. An exact five-deletion search covers 181,927 connected masks for this certificate and finds no strict gain.

## Details

After projection to the labels appearing in the terminal code, a row may be removed if its vector is below a retained row coordinate by coordinate. The convex certificate uses the same argument with a weighted average. For a removed row $v$, the verifier checks positive integer coefficients $a_j$ and retained rows $u_j$ such that $(\sum_j a_j)v\leq\sum_j a_j u_j$ componentwise. Fixing the other terminal coordinates makes the objective a nonnegative linear form in this row. At least one of the retained rows therefore gives at least as large a cardinality as $v$. Applying this one coordinate at a time preserves the maximum. A numerical linear program proposed the witnesses, and the verifier checks every inequality using integers.

For the remaining ordered tuples, a branch holds one subset of candidate rows in each coordinate. Replacing each such subset by its coordinatewise maxima gives an integer upper bound, since every terminal monomial has a nonnegative coefficient. Splitting one subset into disjoint halves partitions the branch. The verifier counts the covered tuples and checks that the count equals the full Cartesian product. If $M$ is Tang's exact size in dimension 680, a size at most $\lfloor (M^k)^{1/4}\rfloor$ in dimension $170k$ cannot beat its rate. The verifier uses integer square roots twice to get that threshold. The searches visited 12,975, 22,709,033, and 4,206,625 branches for $K3a$, $K4a$, and $K4b$ respectively.

The dimension-205 certificate came from alternating improvements to a $K4b$ descendant's terminal code and its input rows, followed by wider sampling of certified gadget profiles. The verifier recomputes the row dimensions and vectors and propagates label separation through the row expressions. For two terminal tuples, it tests whether at least one coordinate certifies separation. The sum of their integer weights is the independent-set size. This verifies the resulting construction independently of the heuristic that found it.

## Reproduction and verification

From the catalog root, using Python 3.13:

```bash
root="$(mktemp -d)"
git clone https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate "$root/tang"
git -C "$root/tang" checkout --detach b5d6c2c2c981f89f5c62f3db9d26dab045464f81
export C7_TANG_SOURCE="$root/tang"
code=attempts/shannon-capacity-c7/code/terminal_exchanges_20261127
python3 -I -B "$C7_TANG_SOURCE/check_c9.py" "$C7_TANG_SOURCE/certificate.json"
python3 -I -B "$code/search_rule_schedules.py" --dominance "$code/schedule-dominance.json"
python3 -I -B "$code/search_schedule_terminals.py" "$code/near-record-schedule.json" --replay-only
python3 -I -B "$code/search_schedule_terminals.py" "$code/near-record-schedule.json" --radius 5
```

The exact commands use the standard library. To repeat Claim 2, run the following with NumPy installed in the selected Python environment:

```bash
export OPENBLAS_NUM_THREADS=1
python3 -I -B "$code/search_variable_schedules.py" --starts 256 --candidates "$root/candidates.json"
python3 -I -B "$code/search_schedule_terminals.py" "$root/candidates.json" --radius 4
```

The branch search agreed with exhaustive enumeration on 120 deterministic small problems. A deliberately invalid convex witness was rejected. The exact dimension-205 replay checks its size against the saved integer and compares its rate to Tang by cross-powers.

## Dead ends

All three terminal codes exhausted the fixed-input schedule family. The wider search revisited Tang's rate with $K4a$, while the refined $K4b$ descendant came within about $8.47\times10^{-6}$ of it. The result leaves other combining rules, deeper trees over different inputs, and other terminal codes available for investigation. The exact Shannon capacity remains open.

## Novelty check

The catalog's two November exchange attempts hold some construction layers fixed. Buys, Polak and Zuiddam supply the combining rules and terminal codes. Tandon and Tang supply the heterogeneous gadget constructions. This attempt evaluates the stated joint finite family and supplies a separate dimension-205 construction. It makes no priority claim about the best possible size in dimension 205.

## References

- Prior catalog attempts `2026-11-27-m7mdd77-terminal-exchanges.md` and `2026-11-28-m7mdd77-connected-exchanges.md`.
- L. Tang, [pinned certificate and checker](https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate/tree/b5d6c2c2c981f89f5c62f3db9d26dab045464f81).
- P. Buys, S. C. Polak and J. Zuiddam, [Lean-verified lower bounds for the Shannon capacity of odd cycles](https://arxiv.org/abs/2607.29681).
- R. Tandon, [Strengthening Recursive Constructions for Zero-Error Shannon Capacity](https://arxiv.org/abs/2608.30273).
