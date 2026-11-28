---
problem: shannon-capacity-c7
date: 2026-11-27
attempter: m7mdd77
model: gpt-6
type: partial-result
status: unverified
---

## Summary

I replayed Tang's published lower-bound certificate in dimension 680 and checked whether weighted exchanges in its 49-tuple terminal code improve the construction. The exact search reaches five deletions from the published code. A modified combining rule with a positive $O$ family was checked separately through four deletions. Neither search improved the bound $\Theta(C_7)\geq 3.25883870544460883237$.

## Approach

Tang combines four identical S3b outputs using the BPZ terminal code K4a. A terminal tuple $w=(w_1,w_2,w_3,w_4)$ has weight $\prod_{i=1}^4 n_i(w_i)$, where $n_i(\lambda)$ is the cardinality of family $\lambda$ at the $i$th output. Two terminal tuples are certified separated if, in some position, every corresponding pair of child tuples separates in at least one child coordinate under the BPZ label relation. This rule includes the separations required by BPZ admissibility.

The objective is the sum of terminal tuple weights. This makes a weighted terminal exchange a finite graph search on the $7^4$ label tuples.

## Claims

1. **[proved]** For Tang's fixed inputs, deleting at most five of the 49 K4a tuples and adding any collection of mutually separated outside tuples gives no strict weight increase, using the separation relation above. The check exhausts all 2,138,410 deletion sets. The simple weight bound leaves 1,060,990 candidate pools for the exact branching check.
2. **[proved]** The tuples \(O_T=\{VVV,VNN,NNV,NVN\}\) can populate S3b's empty $O$ family. They are the existing $V$ family, which is already separated from $B$ and $N$, the two required separations for $O$. The rule check accepts the augmented rule. With that rule fixed, the same weighted search through four deletions gives no strict increase. It checks 231,526 deletion sets, with 196,725 candidate pools surviving the simple weight bound.
3. **[proved]** None of 38,052 single-slot substitutions from the retained pool of 3,171 gadget profiles improves Tang's cardinality per dimension. None of the 95,052 two-slot trials within a single S3b subtree improves it either. The pair search takes the three strongest profiles per dimension under each slot's linear score. Both exclusions apply to the finite search pools specified here.

## Details

For every positive-weight tuple outside K4a, the checker records the set of K4a tuples from which it has no certified separation. After a deletion set $S$ is chosen, the eligible outside tuples are exactly those whose recorded sets are contained in $S$. The sum of eligible weights is an upper bound on any replacement. If that upper bound exceeds the weight removed, include/exclude branching searches for a separated replacement of greater weight. The recursion prunes only when the sum of remaining weights plus the chosen weight cannot beat the incumbent. Any improving exchange that re-adds an original tuple can be written with that tuple omitted from the deletion set.

For gadget substitutions, the two product levels are multilinear in the input family cardinalities. The code evaluates a coefficient vector for each single-slot trial and a coefficient matrix for each two-slot trial. A rational threshold verified below Tang's bound prunes smaller candidates. Remaining comparisons use exact integer cross-powers, so candidate dimensions can differ.

The extra separations involving $O$ in the original rule are vacuous because its $O$ family is empty. The augmenting rule in Claim 2 gives that label positive weight but only creates one additional unordered separation, $O$ from $D$. The original terminal code has no $O$ entries, so its cardinality is unchanged.

## Reproduction and verification

The three [Python programs](https://github.com/m7mdd77/information-theory-problems/tree/codex/c7-terminal-exchanges/attempts/shannon-capacity-c7/code/terminal_exchanges_20261127) use the standard library and Tang's pinned code and data. From the catalog root, set the source and output directories and run:

```bash
root="$(mktemp -d)"
git clone https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate "$root/tang"
git -C "$root/tang" checkout --detach b5d6c2c2c981f89f5c62f3db9d26dab045464f81
export C7_TANG_SOURCE="$root/tang"
export C7_OUTPUT_DIR="$root"
code=attempts/shannon-capacity-c7/code/terminal_exchanges_20261127
python3 -I -B "$C7_TANG_SOURCE/check_c9.py" "$C7_TANG_SOURCE/certificate.json"
python3 -I -B "$code/search_c7.py" --max-dimension 150 --slots 16 --passes 8 --pair-slots 3
python3 -I -B "$code/search_rule.py"
python3 -I -B "$code/search_terminal.py" --radius 5
python3 -I -B "$code/search_terminal.py" --certificate "$root/rule-certificate.json" --radius 4
```

The pinned checker rederived the five Tan counts and the eight auxiliary counts, and reproduced Tang's cardinality exactly. The published certificate digest is `8d55f7465bdedf6b1ea9c4ad3504c1b68c93705500590ff11b6fca66cb9d1f2a`. The proof search used Python 3.13. The weighted clique routine used in the rule experiments also matched exhaustive subset enumeration on 60 small deterministic instances.

## Dead ends

The geometry of K4a blocks the tested terminal exchanges even with the positive $O$ family. The individual rule-family search hit its node cap for $B$. It excludes neither larger exchanges nor simultaneous changes to the rule and terminal code. These results concern the label-code construction and leave the exact value of $\Theta(C_7)$ open.

## Novelty check

I checked the three prior attempts in this directory, Tang's certificate and public README, the BPZ and Tan papers, and the C7 entry in the optimization constants catalog. The earlier exchange certificates in this directory change vertices in the fifth strong power. This attempt checks weighted terminal tuples in Tang's 680-dimensional construction. I did not find an earlier account of this specific terminal exchange check in those sources.

## References

- Previous repository attempts `2026-07-18-gpt-5-codex-direct-cyclic-search.md`, `2026-07-18-gpt-5-codex-four-exchange.md` and `2026-07-18-gpt-5-codex-five-exchange.md`.
- L. Tang, [pinned certificate and checker](https://github.com/gomyway/c9-shannon-c7-lower-bound-certificate/tree/b5d6c2c2c981f89f5c62f3db9d26dab045464f81).
- R. Tandon, [Strengthening Recursive Constructions for Zero-Error Shannon Capacity](https://arxiv.org/abs/2608.30273).
- P. Buys, S. C. Polak and J. Zuiddam, [Lean-verified lower bounds for the Shannon capacity of odd cycles](https://arxiv.org/abs/2607.29681).
- [Optimization Constants in Mathematics, C7 entry](https://teorth.github.io/optimizationproblems/constants/9a.html).
