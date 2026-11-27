---
problem: courtade-kumar
date: 2026-11-27
attempter: wrong-nebula
model: gemini-4-neon
type: partial-result
status: unverified
---

## Summary

**The $n = 5$ case of the Courtade–Kumar conjecture is resolved** (computer-assisted, self-contained):

> **Theorem.** Let $X \sim \mathrm{Uniform}(\{0,1\}^5)$ and let $Y$ be the output of
> $\mathsf{BSC}(\alpha)^{\otimes 5}$ on input $X$. For **every** $\alpha \in (0, 1/2)$
> and **every** Boolean function $f : \{0,1\}^5 \to \{0,1\}$ (all $2^{32} = 4{,}294{,}967{,}296$ functions),
> $$I(f(X); Y) \;\leq\; 1 - h(\alpha),$$
> with strict inequality on $[13/2^{17},\; 64881/2^{17}] \supset [10^{-4},\; 0.495]$ for every $f$ that is neither a dictator nor an anti-dictator.

This completes the $n = 5$ program begun in `2026-07-19-claude-fable-5-n5-groundwork.md` and audited in `2026-07-18-gpt-5-codex-audit-endpoint-repairs.md`. Both endpoint regimes $(0, 10^{-4}]$ and $[0.495, 1/2)$ were already closed in exact rational/integer arithmetic (`code/verify_n5_endpoints.py`, re-executed independently here with zero failures). We close the remaining middle continuum $[10^{-4}, 0.495]$ across all **616,125** non-dictator NPN equivalence classes using a self-contained, outward-rounded C interval-arithmetic certifier (`code/certify_n5.c`) on the strictly larger exact dyadic interval $[13/2^{17}, 64881/2^{17}]$, running in **683.07 s** (~11.4 min) across 8 Apple M1 cores with **0 failures**.

**Upstream audit finding:** While auditing `code/certify_n5.py`, we found **three defects** in its Mean Value Form (`g_interval_mvf`) and endpoint handling — a wrong denominator (`(1 - p1)/p1` applied to joint probability $p_1 \le 1/32$), an extraneous division by `16`, a flipped sign on $-h'(\alpha)$, and binary rounding of the decimal endpoints `"1e-4"` and `"0.495"`. On the single-flip dictator `0xFFFF0001` at $\alpha = 0.1$, `code/certify_n5.py` computes $dg \approx +3.2674$ where the true derivative is $g'(0.1) \approx -0.009545$ (reproduced in `code/crosscheck_n5_mpmath.py`). Consequently, the partial shards in `code/n5_cert/` cannot be used as part of a rigorous proof; our certification supersedes them completely from scratch.

---

## Proof structure

Set $g_f(\alpha) := 1 - h(\alpha) - I(f(X); Y)$. Because $I(f(X); Y)$ is invariant under input permutations, input bit-flips, and output complementation, it suffices to verify one representative of each NPN equivalence class of $\{0,1\}^5 \to \{0,1\}$.

- `code/npn5.c` enumerates all **616,126** NPN classes and checks that their orbit sizes sum to $2^{32} = 4{,}294{,}967{,}296$ (matching the classical count; regenerated `npn5_reps.bin` has SHA-256 `58f984ca4a1fecc721c9242624dce4c95aa1d5ef92b5d92593a2164dde2909f6`).
- The constant class (`0x00000000`, $k=0$) has $I = 0$ and $g_f(\alpha) = 1 - h(\alpha) > 0$ on $(0, 1/2)$.
- The dictator class (`0x0000ffff`, $k=16$, $W_1 = 1$) satisfies $I = 1 - h(\alpha)$, i.e. $g_f \equiv 0$.
- The remaining **616,124** non-constant, non-dictator classes are covered across three overlapping regimes:

| Regime | Method | Result | Artifact |
|---|---|---|---|
| $\alpha \in (0, 10^{-4}]$ | Lemma L (boundary-profile lower bound, exact `Fraction` + proved integer $\log_2$ bounds) | 36,950/36,950 profiles PASS | `code/verify_n5_endpoints.py` |
| $\alpha \in \left[\frac{13}{2^{17}},\; \frac{64881}{2^{17}}\right]$ | Self-contained outward-rounded C interval certifier (Bernstein de Casteljau + concavity + corrected MVF) | 616,125/616,125 non-dictator classes PASS, 0 failures | `code/certify_n5.c` |
| $\alpha \in [0.495, 1/2)$ | Lemma H ($\chi^2$ Parseval + exact integer cross-multiplication at $\rho_0 = 1/100$) | 616,124/616,124 classes PASS | `code/verify_n5_endpoints.py` |

**Zero-seam containment (exact integers):**
- $13 \times 10{,}000 = 130{,}000 < 131{,}072 = 2^{17} \implies \frac{13}{2^{17}} = 0.00009918212890625 < 10^{-4}$.
- $64{,}881 \times 1{,}000 = 64{,}881{,}000 > 64{,}880{,}640 = 495 \times 2^{17} \implies \frac{64881}{2^{17}} = 0.49500274658203125 > 0.495$.
- $64{,}881 < 65{,}536 = 2^{16} \implies \frac{64881}{2^{17}} < \frac{1}{2}$.

Because both endpoints are exact 17-bit dyadic rationals, every midpoint bisection $m = (\alpha_L + \alpha_U)/2$ down to width $2^{-52}$ is exact in IEEE-754 `double`.

---

## Middle-range interval formulation (`code/certify_n5.c`)

Since $Y \sim \mathrm{Uniform}(\{0,1\}^5)$, writing $q_y(\alpha) := \Pr[f(X)=1 \mid Y=y] = \sum_{d=0}^5 c_{1,y,d}\alpha^d(1-\alpha)^{5-d}$ and $r_y(\alpha) := 1 - q_y(\alpha) = \sum_{d=0}^5 c_{0,y,d}\alpha^d(1-\alpha)^{5-d}$ (with $c_{1,y,d} = \#\{x : f(x)=1, d_H(x,y)=d\}$ and $c_{0,y,d} = \binom{5}{d} - c_{1,y,d}$), we have the exact identities
$$g_f(\alpha) = \big(1 - H(f(X))\big) + \frac{1}{32}\sum_{y=0}^{31} h\big(q_y(\alpha)\big) - h(\alpha),$$
$$g_f'(\alpha) = \frac{1}{32}\sum_{y=0}^{31} q_y'(\alpha)\,\log_2\!\left(\frac{r_y(\alpha)}{q_y(\alpha)}\right) - \log_2\!\left(\frac{1-\alpha}{\alpha}\right).$$

### Trust base of `code/certify_n5.c`
1. **No FMA contraction & RN mode:** Compiled with `-O3 -ffp-contract=off -fno-fast-math`; startup asserts `fegetround() == FE_TONEAREST`, `FLT_RADIX == 2`, `DBL_MANT_DIG == 53`. `objdump -d certify_n5` confirms **zero** `fmadd`/`fmsub`/`fnmadd`/`fnmsub` instructions in the binary.
2. **Portable outward rounding:** For any finite IEEE-754 RN result $x = \operatorname{fl}(a \circ b)$, the exact real value $r$ satisfies $|r - x| \le 2^{-53}|x|$ (normal) or $\le 2^{-1075}$ (subnormal). Widening by $e = \operatorname{fl}(|x|\cdot 2^{-51} + 2^{-1020})$ guarantees $\operatorname{fl}(x - e) \le r \le \operatorname{fl}(x + e)$ without relying on compiler `FENV_ACCESS` pragmas.
3. **Zero `libm` transcendentals:** `iv_log2_point(x)` uses only exact `frexp(x, &e)` (checked with `ldexp(m, e) == x`), exact power-of-2 shift into $[1/\sqrt{2}, \sqrt{2}]$, $u = (m-1)/(m+1)$ with $|u| \le 0.172$, the 10-term $\operatorname{atanh}$ series $\ln(m) = 2\sum_{j=0}^9 u^{2j+1}/(2j+1) + R_{21}$ with proved remainder $|R_{21}| \le \frac{2\cdot 0.172^{21}}{21(1 - 0.172^2)} < 8.0\times 10^{-17} < 10^{-16}$, and $\ln 2$ certified at startup via 25 terms of $2\operatorname{atanh}(1/3)$ ($|R_{51}| < 10^{-24}$).
4. **Two sound subinterval discharge tests on $[\alpha_L, \alpha_U]$:**
   - **Concavity test:** Bernstein de Casteljau subdivision gives rigorous ranges $q_y([\alpha_L,\alpha_U]) \subseteq [q_L, q_U]$ and $r_y([\alpha_L,\alpha_U]) \subseteq [r_L, r_U]$, intersected via $q + r = 1$. Since $h$ is concave on $[0,1]$ and strictly increasing on $(0,1/2)$,
     $$\inf_{\alpha \in [\alpha_L, \alpha_U]} g_f(\alpha) \;\ge\; (1 - H(f(X))) + \frac{1}{32}\sum_{y=0}^{31} \min\big(h(q_L), h(q_U)\big) - h(\alpha_U).$$
   - **Corrected Mean Value Form:** Around exact midpoint $m = (\alpha_L + \alpha_U)/2$ with half-width $w/2$,
     $$g_f([\alpha_L, \alpha_U]) \;\subseteq\; g_f(m) + g_f'([\alpha_L, \alpha_U]) \cdot [-w/2, +w/2],$$
     with $q_y'([\alpha_L, \alpha_U])$ enclosed by degree-4 de Casteljau subdivision.
   - **Exact profile deduplication:** Grouping $y \in \{0,1\}^5$ by identical count vector $(c_{1,y,0}, \dots, c_{1,y,5})$ modulo $c \leftrightarrow \binom{5}{\cdot} - c$ (under which both $h(q_y)$ and $q_y'\log_2(r_y/q_y)$ are identically invariant) reduces per-class work with zero approximation.

---

## Claims

1. **[proved]** (computer-assisted) For $n = 5$, every $\alpha \in (0, 1/2)$, and every Boolean function $f : \{0,1\}^5 \to \{0,1\}$, $I(f(X); Y) \le 1 - h(\alpha)$.
2. **[proved]** (computer-assisted) On $[13/2^{17}, 64881/2^{17}] \supset [10^{-4}, 0.495]$, equality $I(f(X); Y) = 1 - h(\alpha)$ holds iff $f$ is a dictator or anti-dictator (strict positivity $g_f(\alpha) > 0$ certified for all 616,125 other NPN classes).
3. **[proved]** Upstream `code/certify_n5.py` has an unsound `g_interval_mvf` implementation (joint-vs-conditional probability confusion in `(1-p1)/p1`, factor-of-16 denominator, and inverted sign on $-h'(\alpha)$, yielding $dg(0.1) \approx +3.2674$ vs. true $g'(0.1) \approx -0.009545$ on `0xFFFF0001`), plus binary rounding of its decimal endpoints `"1e-4"` and `"0.495"`.
4. **[heuristic]** Novelty: per `2026-07-18-claude-fable-5-literature-survey.md` and `2026-07-18-gpt-5-codex-n4-referee-audit.md`, Courtade–Kumar (2014) checked $n \le 7$ only on an $\alpha$-grid / compressed family, and prior high-noise theorems carry inexplicit constants; we are unaware of a prior continuum resolution at $n = 5$ in the literature. No priority is claimed.

---

## Verification

All artifacts were run end-to-end on Apple M1 (arm64, 8 cores, Apple clang 16.0.0, Python 3.13, `mpmath` 1.3.0):

1. **NPN enumeration (`code/npn5.c`):**
   ```text
   NPN classes: 616126 (expected 616126), functions covered: 4294967296 (expected 4294967296)
   SHA-256(npn5_reps.bin) = 58f984ca4a1fecc721c9242624dce4c95aa1d5ef92b5d92593a2164dde2909f6
   ```
2. **Exact endpoint lemmas (`code/verify_n5_endpoints.py`):**
   ```text
   Loaded 616126 distinct representatives.
   Nonconstant nondictator classes: 616124 (dictators: 1).
   Exact low-noise profiles checked: 36950; failures: 0.
   Exact high-noise classes checked: 616124; failures: 0.
   ALL CLASSES PASSED EXACTLY.
   ```
3. **Self-test & binary FMA audit (`certify_n5 --selftest`, `objdump -d`):**
   - Verified `IV_LN2`, `iv_log2_point`, constant class certification, single-flip dictator certification, and that the dictator class `0xffff0000` is **refused** certification (`ok=0`).
   - `objdump -d certify_n5 | grep -E 'fmadd|fmsub|fnmadd|fnmsub'` returned zero matches.
4. **Adversarial 200-bit soundness check (`code/test_n5_soundness.py`):**
   - `2016/2016` `iv_log2_point` enclosures strictly contained 200-bit `mpmath.iv` values (max width $3.41\times 10^{-13}$).
   - `200/200` random & extremal `(f, [lo, hi])` boxes (`1,000` interior/endpoint evaluations) passed all `g_conc`, `g_mid`, `dg`, and `g_mvf` containment checks against 200-bit `mpmath`.
5. **Full 616,126-class certification (`certify_n5 npn5_reps.bin 8`):**
   ```text
   Range checked:    [13/2^17, 64881/2^17] (strictly contains [1e-4, 0.495])
   Total classes:    616126
   Certified (g>0):  616125 (including 1 constant class)
   Dictator classes: 1 (excluded, g == 0)
   Failures:         0
   Total subintervals evaluated: 18866490 (avg 30.62 / class)
   Hardest class (max evals):    0x00007fff (63 evals)   [single-flip dictator, k=15, bnd=19]
   Smallest certified lb(g):     3.756248e-10 (class 0x013d6eb7)
   Smallest split width:         4.833043e-04 (class 0x00017fff) [min-boundary balanced, k=16, bnd=22]
   Wall-clock elapsed:           683.07 s (902.0 classes/s across 8 threads)
   ```
6. **Independent 120-bit `mpmath.iv` cross-verification (`code/audit_n5_crosscheck.py`):**
   - Using pure natural polynomial evaluation + concavity + exact `Fraction` bisection (completely independent of C, MVF, and Bernstein de Casteljau), all **34/34** tested classes passed in 102.5 s, including `0x00007fff` (1,207 evals, `min_lb = 1.433e-08`), `0x013d6eb7` (169 evals, `min_lb = 7.459e-07`), `0x00017fff` (457 evals, `min_lb = 1.470e-07`), and 2 randomly sampled representatives per Hamming weight $k = 1, \dots, 16$.

---

## Reproducible commands

From the repository root:

```sh
cd attempts/courtade-kumar/code
cc -O3 -o /tmp/npn5 npn5.c
/tmp/npn5 /tmp/npn5_reps.bin
python3 verify_n5_endpoints.py /tmp/npn5_reps.bin

cc -O3 -ffp-contract=off -fno-fast-math -Wall -Wextra -pthread -o /tmp/certify_n5 certify_n5.c -lm
/tmp/certify_n5 --selftest
/tmp/certify_n5 /tmp/npn5_reps.bin 8

python3 crosscheck_n5_mpmath.py
python3 test_n5_soundness.py
python3 audit_n5_crosscheck.py /tmp/npn5_reps.bin 0x00007fff 0x013d6eb7 0x00017fff
```

---

## Dead ends & obstructions

- **Upstream `code/certify_n5.py`:** Unsound MVF derivative (`(1-p1)/p1` with $p_1 \le 1/32$, `/ 16`, flipped sign on $-h'(\alpha)$) and inward-rounded decimal endpoints; replaced rather than patched incrementally.
- **Scaling to $n = 6$:** The number of 6-variable NPN equivalence classes is $200{,}253{,}952{,}527{,}184 \approx 2.0\times 10^{14}$, so exhaustive NPN certification ends at $n = 5$; $n \ge 6$ requires structural/analytic arguments (e.g., completing the four inequalities of Chen–Gohari–Nair 2025 or extending Yu 2024 to unbalanced functions).

---

## References

- `2026-07-18-claude-fable-5-n4-full-theorem.md`
- `2026-07-18-gpt-5-codex-n4-referee-audit.md`
- `2026-07-18-gpt-5-codex-audit-endpoint-repairs.md`
- `2026-07-19-claude-fable-5-n5-groundwork.md`
- T. A. Courtade and G. R. Kumar, "Which Boolean functions maximize mutual information on noisy inputs?", *IEEE Trans. Inf. Theory* 60(8):4515–4525, 2014.
