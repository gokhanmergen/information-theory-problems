---
id: amplitude-constrained-awgn-support
title: Monotonicity of the Support Size of the Amplitude-Constrained AWGN Optimal Input
status: open
category: channel-capacity
posed_by: Nitin Sharma and Shlomo Shamai (Shitz)
posed_year: 2010
tags: [channel-capacity, gaussian-channel, peak-power, amplitude-constraint, discrete-input, mass-points]
lean_module: InfoTheory.Problems.AmplitudeConstrainedAwgnSupport
lean_file: lean/InfoTheory/Problems/AmplitudeConstrainedAwgnSupport.lean
review: pending-expert
---

## Statement

Consider the real AWGN channel $Y = X + Z$, $Z \sim \mathcal{N}(0, N)$ with $N > 0$, under the
peak (amplitude) constraint $|X| \le A$. Its capacity is
$$
C(A, N) = \max_{P_X:\ P_X([-A, A]) = 1} I(X; X + Z).
$$
Smith (1971) showed that the maximizer $P_X^\star$ is unique, symmetric, and **discrete with finitely
many mass points**. Let $K(A)$ denote the number of mass points of $P_X^\star$ when $N = 1$. By
scaling, the optimal input for general $N$ has $K(A/\sqrt{N})$ points.

**Conjecture (Sharma–Shamai 2010).** $K(A)$ is nondecreasing in $A$. Sharma and Shamai
conjectured more: at each transition the support grows by exactly one point, and the new point
appears at the origin.

**Formal version.** The Lean statement asks the monotonicity part. Operationally, let $C_k(A, N)$
be the capacity when every codeword symbol must lie in some constellation $S \subseteq [-A, A]$
with $|S| \le k$. The constellation may depend on the blocklength. The statement is:
$$
\forall N > 0,\ 0 < A \le A',\ k \ge 1:\qquad C_k(A', N) = C(A', N)\ \Longrightarrow\ C_k(A, N) = C(A, N).
$$
Both sides are defined operationally. The framework uses measurable decoders, deterministic
per-symbol constraints, $\lfloor 2^{nR}\rfloor$ messages, and average error as a measure.

**Why this is the conjecture** (standard facts, not formalized). By the channel coding theorem
for this finite-input, continuous-output channel, $C_k(A,N)$ is the maximum of $I(X;X+Z)$ over
inputs with at most $k$ mass points in $[-A,A]$. This maximum is attained, by compactness and
continuity. So $C_k(A,N) = C(A,N)$ iff some input with at most $k$ points is optimal. By Smith's
uniqueness theorem this holds iff $K(A/\sqrt N) \le k$. Hence the statement says exactly
"$K(A') \le k \Rightarrow K(A) \le k$ for $A \le A'$", i.e. $K$ is nondecreasing.

## Background

Peak-power limits are physical: amplifiers saturate. For this reason the amplitude-constrained
AWGN channel is the canonical model in which the optimal input is *not* Gaussian. Smith's
discreteness theorem began a large literature on discrete capacity-achieving inputs, covering
Rayleigh fading, Poisson/optical channels, and vector Gaussian channels with amplitude
constraints. Numerical solutions (Smith; Shamai–Bar-David 1995; Sharma–Shamai 2010) show
$K(A)$ growing in unit steps, with new points born at the origin. Yet even monotonicity, the
weakest form of this picture, has not been proved.

## What is known

- **Discreteness and finiteness.** $P_X^\star$ is unique, symmetric and has finitely many mass
  points (Smith 1971; see also Shamai–Bar-David 1995 for the quadrature case).
- **Small amplitudes.** Smith (1971) already observed that binary signalling is optimal for
  small $A$. Sharma–Shamai (2010) showed that the equiprobable binary input $\pm A$ is optimal
  iff $A \le \bar{A} \approx 1.665$ (unit noise), as cited in Barletta–Dytso (2026). They
  also give numerically computed transition points and state the monotonicity conjecture.
- **Order of growth of $K(A)$.**
  - Dytso–Yagli–Poor–Shamai (2020) give the first explicit upper bound, $K(A) = O(A^2)$, via
    Karlin's oscillation theorem and Tijdeman's number-of-zeros lemma. The elementary lower
    bound is $K(A) = \Omega(A)$, since $C(A,1) \le \log_2 K(A)$ and $C(A,1) \ge \log_2 A - O(1)$.
  - The conjectured linear scaling $K(A) = \Theta(A)$ was **disproved** by Wang–Barletta–Dytso
    (arXiv:2512.22691, 2025/2026), who prove $K(A) = \Omega(A\sqrt{\log A})$. The exact order
    (between $A\sqrt{\log A}$ and $A^2$) is open.
  - Barletta–Dytso (arXiv:2604.14915, 2026) show that the minimal support size of an
    *$\varepsilon$-optimal* input is $\Theta(A\sqrt{\log A})$ for polynomially small $\varepsilon$.
    Its order lies between $A\sqrt{\log A}$ and $A^{3/2}$ for exponentially small $\varepsilon$.
    They argue that earlier numerical "scaling laws" reflect $\varepsilon$-optimality regimes.
- **Local evolution (strongest partial result toward this problem).** Barletta–Dytso
  (arXiv:2609.10039, Sept. 2026) prove that the optimal input and its KKT function vary
  continuously in $A$. Nonzero support points persist locally, with continuously moving
  locations and masses. **Locally**, the support size either stays the same or increases by
  one, and any change happens at the origin. They state explicitly that this does *not* rule
  out a decrease of $K(A)$ as $A$ grows, and that global monotonicity, which would complete the
  Sharma–Shamai conjecture, "remains open".
- **Capacity bounds** (not needed here): McKellips (2004); Thangaraj–Kramer–Böcherer (2017).

## Notes on the formalization (for expert review)

- **Operational, not information-theoretic.** The Lean statement avoids differential entropy
  and optimal-input objects entirely. It compares two operational capacities defined by
  `sSup`s. Both `sSup`s are certified non-junk (nonempty and bounded above by
  $\tfrac12\log_2(1+A^2/N)$). The equivalence with "$K$ is nondecreasing" rests on Smith's
  uniqueness/finiteness theorem and the coding theorem. These are classical but not formalized.
- **Constellation may depend on $n$.** This does not change $C_k$: the converse bound holds
  for every $k$-point alphabet. Fixing one $S$ would also give the same value; the chosen
  form is just less restrictive.
- **$k \ge 1$ guard.** For $k = 0$ no code exists, the achievable set is empty, and
  `sSup ∅ = 0` would be a junk value. The statement therefore quantifies over $k \ge 1$ only.
- **Unit-step / birth-at-zero refinements** of the Sharma–Shamai conjecture are *not* part of the
  formal statement. Only monotonicity is.
- **Certificate** (`Known/Certificates/AmplitudeConstrainedAwgnSupport.lean`):
  - non-junk;
  - $C_k \le C_{k'} \le C$;
  - $C(A,N) \le \tfrac12\log_2(1+A^2/N)$, from the operational AWGN converse, since the peak
    constraint implies the power constraint $A^2$;
  - $C(A,N) \ge C_2(A,N) \ge 1 - h(Q(A/\sqrt N)) > 0$, from BPSK at $\pm A$ with hard decisions.

## References

- J. G. Smith, "The information capacity of amplitude- and variance-constrained scalar Gaussian
  channels," *Information and Control*, vol. 18, no. 3, pp. 203–219, 1971.
- S. Shamai (Shitz) and I. Bar-David, "The capacity of average and peak-power-limited quadrature
  Gaussian channels," *IEEE Trans. Inf. Theory*, vol. 41, no. 4, pp. 1060–1071, 1995.
- A. L. McKellips, "Simple tight bounds on capacity for the peak-limited discrete-time channel,"
  *Proc. IEEE ISIT*, 2004.
- N. Sharma and S. Shamai (Shitz), "Transition points in the capacity-achieving distribution for
  the peak-power limited AWGN and free-space optical intensity channels," *Problems of
  Information Transmission*, vol. 46, no. 4, pp. 283–299, 2010.
- A. Thangaraj, G. Kramer, G. Böcherer, "Capacity bounds for discrete-time, amplitude-constrained,
  additive white Gaussian noise channels," *IEEE Trans. Inf. Theory*, vol. 63, no. 7, 2017.
- A. Dytso, S. Yagli, H. V. Poor, S. Shamai (Shitz), "The capacity achieving distribution for the
  amplitude constrained additive Gaussian channel: an upper bound on the number of mass points,"
  *IEEE Trans. Inf. Theory*, vol. 66, no. 4, 2020 (arXiv:1901.03264).
- H. Wang, L. Barletta, A. Dytso, "An improved lower bound on cardinality of support of the
  amplitude-constrained AWGN channel," arXiv:2512.22691, 2025 (rev. 2026).
- L. Barletta and A. Dytso, "Support size of ε-capacity-achieving inputs for the
  amplitude-constrained AWGN channel," arXiv:2604.14915, 2026 (ITW 2026).
- L. Barletta and A. Dytso, "On the evolution of the capacity-achieving input support for the
  amplitude-constrained AWGN channel," arXiv:2609.10039, 2026.
