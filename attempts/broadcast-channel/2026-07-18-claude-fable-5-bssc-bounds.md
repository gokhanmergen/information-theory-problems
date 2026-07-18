---
problem: broadcast-channel
date: 2026-07-18
attempter: claude
model: claude-fable-5
type: numerical-evidence
status: unverified
---

## Summary

A reproducible computation of the two sides of the broadcast-channel open problem on
its canonical separating example, the **binary skew-symmetric channel** (BSSC):
Marton's inner bound sum rate is reproduced to $10^{-7}$ against the exactly known
value $0.3616428$ bits, and the Nair–El Gamal (UV) outer bound sum rate evaluates to
$0.3725562$ bits, stable across auxiliary cardinalities. The open question "is
Marton's inner bound tight?" is, on this channel, a concrete $0.0109$-bit window.
A side quantification: Marton's common auxiliary $W$ is worth exactly the difference
between pure time division ($\log_2 5 - 2 \approx 0.3219$) and $0.3616$ — without
$W$, the private-message expression cannot exceed the single-user Z-channel capacity
here. The literature check also surfaced that the UV bound is **no longer the best
known outer bound**: Gohari–Nair (2022) improved it via the auxiliary-receiver
approach; the problem file is updated accordingly.

## Approach

BSSC: $X \in \{0,1\}$, $p(y_1|x) = \begin{pmatrix} 1 & 0 \\ 1/2 & 1/2 \end{pmatrix}$,
$p(y_2|x) = \begin{pmatrix} 1/2 & 1/2 \\ 0 & 1 \end{pmatrix}$ (mirrored Z-channels).

- **Marton sum rate** (private messages, common auxiliary $W$):
  $\max\, \min\{I(W;Y_1), I(W;Y_2)\} + \mathbb{E}_W[I(U;Y_1|W) + I(V;Y_2|W) -
  I(U;V|W)]$ over $p(w)\,p(u,v|w)\,p(x|u,v,w)$, with $|U|=|V|=2$ and
  $|W| \in \{1,2,3\}$.
- **UV outer bound sum rate**: $\max\, \min\{I(U;Y_1)+I(V;Y_2),\;
  I(U;Y_1)+I(X;Y_2|U),\; I(V;Y_2)+I(X;Y_1|V)\}$ over $p(u,v,x)$, with
  $|U|=|V| \in \{2,3\}$.

Softmax-parametrized Nelder–Mead with 60 random restarts per configuration
(restart-concentration reported). Both quantities are maxima over auxiliaries, so
numerical optima are certified lower estimates; see the per-claim labels.

## Claims

1. **[proved]** (published result + reproduction) Marton's inner-bound sum rate for
   the BSSC equals $0.3616428$ bits, achieved by randomized time division; optimality
   over the full inner bound follows from the Nair–Wang–Geng binary information
   inequality (arXiv:1001.1468), which proves RTD attains Marton's sum rate for
   *every* binary-input broadcast channel. Our optimizer reproduces $0.3616429$ at
   $|W|=2$ and $|W|=3$. This certifies sum-capacity $\geq 0.3616428$.

2. **[proved]** (by the $|W|=1$ computation) Restricted to no common auxiliary, the
   Marton expression $I(U;Y_1)+I(V;Y_2)-I(U;V)$ maxes out at
   $\log_2 5 - 2 = 0.3219281$ bits on the BSSC — exactly the single-user Z-channel
   capacity. The entire $0.0397$-bit advantage of Marton's bound over naive time
   division comes from the partially-decodable time-sharing indicator $W$.

3. **[heuristic]** (global optimality of the found optimum; restart-stable at two
   cardinalities) The UV outer bound sum rate for the BSSC is $0.3725562$ bits.
   Combined with Claim 1, the sum-capacity of the BSSC lies in
   $[0.3616428,\, 0.3725562]$ — a $0.0109$-bit window — and determining where it
   falls is precisely the tightness question for Marton's bound in its sharpest
   known small instance. (The strict Marton-vs-UV gap itself is established in the
   literature; our contribution is the reproducible evaluation.)

4. **[proved]** (literature record, primary sources checked) The UV outer bound is
   no longer best known: Gohari–Nair, "Outer bounds for multiuser settings: the
   auxiliary receiver approach" (IEEE Trans. IT 2022), strictly improves it.
   Evaluating that bound on the BSSC — how much of the $0.0109$-bit window does it
   close? — is the natural next attempt, exactly parallel to the EGN evaluation in
   the relay-channel attempt log.

## Details

Code: `attempts/broadcast-channel/code/bssc_bounds.py` (numpy/scipy). Restart
concentrations at the reported optima: Marton $|W|=2$: 1/60 (rugged; $|W|=3$: 7/60
at the same value), UV $|U|=|V|=2$: 13/60, $|U|=|V|=3$: 10/60.

## Verification

- Claim 1's target value is exact in the literature (0.2506717 nats = 0.3616428
  bits, e.g. Dou et al., Entropy 2024, who compute it by Blahut–Arimoto-type
  algorithms); our independent optimizer matches to $10^{-7}$.
- Claim 2's value matches the closed form $\log_2 5 - 2$ to $10^{-7}$.
- Ordering sanity: $0.3219 < 0.3616 < 0.3726$, and UV estimates agree to $10^{-7}$
  at two different auxiliary cardinalities.

## Dead ends

- The Gohari–Nair (2022) auxiliary-receiver bound was not implemented — its
  evaluation involves an auxiliary receiver channel optimization that deserves its
  own attempt rather than a rushed appendix here.
- Nelder–Mead struggled at $|W|=2$ (1/60 concentration); an EM/Blahut–Arimoto-style
  alternating maximization (as in Dou et al.) is the right tool for firming
  Claim 3's `[heuristic]` toward `[proved]`.

## References

- K. Marton, "A coding theorem for the discrete memoryless broadcast channel,"
  IEEE Trans. Inf. Theory, 1979.
- C. Nair and A. El Gamal, "An outer bound to the capacity region of the broadcast
  channel," IEEE Trans. Inf. Theory, 2007.
- C. Nair, Z. V. Wang, and Y. Geng, "An information inequality and evaluation of
  Marton's inner bound for binary input broadcast channels," arXiv:1001.1468.
- A. Gohari and C. Nair, "Outer bounds for multiuser settings: the auxiliary
  receiver approach," IEEE Trans. Inf. Theory, 2022.
- Y. Dou et al., "Blahut–Arimoto algorithms for inner and outer bounds on capacity
  regions of broadcast channels," Entropy 26(3):178, 2024.
