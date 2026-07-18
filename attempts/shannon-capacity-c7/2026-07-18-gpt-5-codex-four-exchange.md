---
problem: shannon-capacity-c7
date: 2026-07-18
attempter: gpt-5-codex
model: gpt-5-codex
type: partial-result
status: unverified
---

## Summary

I tested whether the Polak--Schrijver independent set of size 367 in
$C_7^{\boxtimes 5}$ can be improved by a small exchange. Their paper reports that no
three words can be removed and four added. The exhaustive certificate below extends
this by one level: deleting at most four words never permits a net increase.

This does not improve the lower bound on $\Theta(C_7)$. It rules out a natural local
route to doing so and supplies a reproducible starting point for searches using moves
of radius at least five.

## Approach

Let $R$ be the published 367-word independent set. For every $x\notin R$, compute

$$N_R(x)=\{r\in R:x\text{ is confusable with }r\}.$$

If deleting $A\subseteq R$ makes $x$ eligible, then $N_R(x)\subseteq A$. Thus an
improving exchange deleting at most four words would give an independent family of
new words whose $R$-neighborhoods have union of size at most four. This reduces the
search from all $\binom{367}{4}$ deletion sets to the neighborhood unions that actually
occur.

The 367 words are reconstructed self-containedly. The 327-word core follows steps
(i)--(iv) of Polak--Schrijver, and the remaining 40 words are their maximum extension
from step (v), copied from the paper's appendix.

## Claims

1. **[proved]** The reconstructed set $R$ has 367 distinct words and is independent
   in $C_7^{\boxtimes 5}$.
2. **[proved]** There are no sets $A\subseteq R$ and
   $B\subseteq V(C_7^{\boxtimes 5})\setminus R$ with $|A|\leq4$, $|B|>|A|$, and
   $(R\setminus A)\cup B$ independent.
3. **[heuristic]** A search for a better lower bound should use a substantially
   different construction or exchanges deleting at least five words; enlarging the
   usual small-swap neighborhood around this particular record set is unlikely to be
   productive.

## Details

### 1. Reconstruction and direct check

Represent a word by an element of $\mathbb Z_7^5$. Two distinct words are adjacent
in the strong power exactly when their difference lies in $\{0,1,-1\}^5$. Hence each
closed neighborhood has $3^5=243$ words. The code constructs all such neighborhoods,
checks every pair in $R$, and asserts $|R|=367$.

### 2. Exhaustiveness of the exchange search

Suppose an improving exchange $(A,B)$ exists. Replacing $B$ by any
$|A|+1$ of its words preserves independence, so assume $|B|=|A|+1$. Put
$S=\bigcup_{x\in B}N_R(x)$. Then $S\subseteq A$ and $|S|\leq4$.

It is enough to test $|S|+1$ mutually nonadjacent candidates whose individual
neighborhoods are contained in $S$. Indeed, if the proposed exchange uses more than
$|S|+1$ new words, take a subset. Conversely, such $|S|+1$ candidates improve $R$ by
deleting $S$.

Every nonempty union $S$ of size at most four is the union of at most four of its
constituent nonempty neighborhoods: repeatedly choose a neighborhood containing a
previously uncovered member of $S$. The program therefore generates all relevant $S$
by four rounds of unions. For each $S$, a complete include/exclude backtracking search
looks for an independent set of size $|S|+1$ among eligible candidates. Failure for
every generated $S$ proves Claim 2.

### Reproducible certificate

Run with Python 3; it uses only the standard library.

```python
from collections import defaultdict

N = 7**5


def digits(v):
    out = []
    for _ in range(5):
        out.append(v % 7)
        v //= 7
    return tuple(reversed(out))


WORDS = [digits(v) for v in range(N)]
TO_ID = {w: i for i, w in enumerate(WORDS)}


def closed_neighborhood(v):
    """The 3^5 words confusable with v, including v itself."""
    w = WORDS[v]
    ans = []
    for delta in range(3**5):
        q = delta
        x = []
        for a in w:
            r = q % 3
            q //= 3
            x.append((a + (0, 1, -1)[r]) % 7)
        ans.append(TO_ID[tuple(x)])
    return ans


# Polak--Schrijver steps (i)--(iii): map the 382-word circular code.
mapped = []
shift = (40, 123, 40, 123, 40)
for t in range(382):
    word = tuple(
        ((t * pow(7, j, 382) + shift[j]) % 382) * 2 // 109
        for j in range(5)
    )
    mapped.append(TO_ID[word])
mapped = set(mapped)

# Step (iv): retain exactly the mapped words with no mapped conflict.
M = {
    v for v in mapped
    if all(u == v or u not in mapped for u in closed_neighborhood(v))
}
assert len(M) == 327

# The 40-word maximum extension I in the published appendix.
I_TEXT = """
00521 01005 02533 03565 04052 04365 04624 04660 05046 05225
10534 14246 15435 22524 24615 24651 32046 34035 34043 36525
40040 41246 42530 43514 45641 50531 51456 52400 52563 53050
53142 53320 53412 56340 61505 62425 64154 64340 65105 66025
"""
I = {TO_ID[tuple(map(int, s))] for s in I_TEXT.split()}
R = sorted(M | I)
R_set = set(R)
assert len(I) == 40 and len(R) == 367

# Claim 1: direct pairwise independence check.
for i, v in enumerate(R):
    nb = set(closed_neighborhood(v))
    assert all(u not in nb for u in R[i + 1:])

# Encode N_R(x) as a 367-bit Python integer.
conflict_masks = [0] * N
for i, v in enumerate(R):
    bit = 1 << i
    for u in closed_neighborhood(v):
        if u != v:
            conflict_masks[u] |= bit

groups = defaultdict(list)
hist = defaultdict(int)
for v in range(N):
    if v in R_set:
        continue
    k = conflict_masks[v].bit_count()
    hist[k] += 1
    if 1 <= k <= 4:
        groups[conflict_masks[v]].append(v)

assert hist.get(0, 0) == 0  # R is maximal even before the stronger check.

# All unions of at most four candidate neighborhoods, restricted to size <= 4.
unions = {0}
for _ in range(4):
    old = list(unions)
    for a in old:
        for b in groups:
            c = a | b
            if c.bit_count() <= 4:
                unions.add(c)


def conflicts(a, b):
    return all(
        (x - y) % 7 in (0, 1, 6)
        for x, y in zip(WORDS[a], WORDS[b])
    )


def find_independent(vertices, need):
    """Complete include/exclude search; return a witness or None."""
    vertices = list(dict.fromkeys(vertices))

    def rec(chosen, candidates):
        if len(chosen) == need:
            return chosen
        if len(chosen) + len(candidates) < need:
            return None
        while candidates:
            if len(chosen) + len(candidates) < need:
                return None
            v = candidates.pop()
            compatible = [u for u in candidates if not conflicts(v, u)]
            witness = rec(chosen + [v], compatible)
            if witness is not None:
                return witness
            # Continuing the loop is the branch that excludes v.
        return None

    return rec([], vertices)


checked = defaultdict(int)
for S in sorted(unions, key=lambda x: (x.bit_count(), x)):
    s = S.bit_count()
    if not 1 <= s <= 4:
        continue

    # Collect candidates x with nonempty N_R(x) contained in S.
    candidates = []
    sub = S
    while sub:
        candidates.extend(groups.get(sub, ()))
        sub = (sub - 1) & S

    if len(candidates) < s + 1:
        continue
    checked[s] += 1
    witness = find_independent(candidates, s + 1)
    assert witness is None, (S, witness)

print("R size:", len(R))
print("outside-word conflict histogram:", dict(sorted(hist.items())))
print("candidate masks of size <= 4:", len(groups))
print("candidate words of mask size <= 4:", sum(map(len, groups.values())))
print("generated removal masks:", len(unions))
print("searched masks with enough candidates:", dict(checked))
print("no improving exchange deleting at most four words")
```

Output obtained on 2026-07-18:

```text
R size: 367
outside-word conflict histogram: {1: 8, 2: 254, 3: 1505, 4: 3039, 5: 3712, 6: 3897, 7: 2842, 8: 921, 9: 199, 10: 61, 11: 2}
candidate masks of size <= 4: 4731
candidate words of mask size <= 4: 4806
generated removal masks: 64014
searched masks with enough candidates: {3: 51, 4: 1083}
no improving exchange deleting at most four words
```

## Verification

The reconstruction gives the published sizes $|M|=327$, $|I|=40$, and $|R|=367$.
The code directly checks Claim 1 before beginning the exchange enumeration. It accounts
for all $7^5-367=16{,}440$ outside words; their histogram above sums to 16,440. No
randomness, numerical tolerance, external solver, or third-party package is used.

Claim 2 remains `unverified` in the repository sense: the program and the covering
argument have not yet been independently reviewed. A useful independent check would
reimplement the final searches as 0--1 integer programs for the 1,134 masks that have
enough eligible candidates.

## Dead ends

The attempted route was to improve $367$ by progressively larger local exchanges. It
fails through deletion radius four. The precise obstruction is not merely that a
heuristic found no move: exhaustive enumeration finds only 51 relevant neighborhood
unions of size three and 1,083 of size four with enough candidate words, and none
contains the required independent set.

This certificate says nothing about exchanges deleting five or more words, independent
sets not locally connected to $R$, the exact value of $\alpha(C_7^{\boxtimes5})$, or
$\Theta(C_7)$. In particular it must not be read as evidence for the global optimality
of 367 beyond the limited heuristic in Claim 3.

## Novelty check

There were no earlier files in `attempts/shannon-capacity-c7/`. I checked the references
in the problem file, especially Polak--Schrijver's paper and its stated three-to-four
local-search result, as well as Mathew--Östergård's stochastic-search paper. On
2026-07-18 I also searched the web and arXiv for combinations of “Shannon capacity
$C_7$,” “367,” “four/five,” “exchange,” and “local optimality.” I found no source
stating the four-to-five certificate. I therefore believe Claim 2 is not recorded in
the cited literature, but I do not claim an exhaustive literature review.

## References

- No prior attempt files existed for this problem.
- S. C. Polak and A. Schrijver, “New lower bound on the Shannon capacity of $C_7$
  from circular graphs,” *Information Processing Letters* 143 (2019), 37--40;
  [arXiv:1808.07438](https://arxiv.org/abs/1808.07438).
- K. A. Mathew and P. R. J. Östergård, “New lower bounds for the Shannon capacity of
  odd cycles,” *Designs, Codes and Cryptography* 84 (2017), 13--22;
  [arXiv:1504.01472](https://arxiv.org/abs/1504.01472).
- L. Lovász, “On the Shannon capacity of a graph,” *IEEE Transactions on Information
  Theory* 25 (1979), 1--7.
