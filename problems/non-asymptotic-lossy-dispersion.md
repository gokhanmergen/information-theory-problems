---
id: non-asymptotic-lossy-dispersion
title: Second-Order Dispersion of Lossy Source Coding with Side Information (Wyner–Ziv)
status: open
category: source-coding
posed_by: Victoria Kostina, Sergio Verdú; Shun Watanabe, Shigeaki Kuzuoka, Vincent Y. F. Tan
posed_year: 2012
tags: [source-coding, finite-blocklength, dispersion, wyner-ziv, rate-distortion]
lean_module: InfoTheory.Problems.NonAsymptoticLossyDispersion
lean_file: lean/InfoTheory/Problems/NonAsymptoticLossyDispersion.lean
---

## Statement

Let $(X_i, Y_i)_{i=1}^n \stackrel{\text{i.i.d.}}{\sim} P_{X,Y}$ be a discrete memoryless source
with decoder side information $Y^n$, single-letter distortion measure
$d : \mathcal{X} \times \hat{\mathcal{X}} \to \mathbb{R}_{\ge 0}$, and interior distortion
threshold $D$ (strictly between the minimum achievable distortion and the zero-rate distortion).
For blocklength $n$ and excess-distortion probability $\varepsilon \in (0, 1)$, let
$R_{\mathrm{WZ}}(n, D, \varepsilon)$ denote the minimum rate $\frac{1}{n} \log_2 M$ of an
$(n, M)$ Wyner–Ziv code $(f_n, g_n)$ satisfying
$$\mathbb{P}\!\left[\frac{1}{n} \sum_{i=1}^n d(X_i, g_n(f_n(X^n), Y^n)_i) > D\right] \le \varepsilon .$$
By the Wyner–Ziv theorem (1976), the first-order asymptotic rate is
$$R_{\mathrm{WZ}}(D) = \inf_{\substack{U - X - Y \\ \mathbb{E}[d(X, g(U, Y))] \le D}} I(X; U \mid Y) .$$

**Determine the exact second-order coding rate (dispersion) of Wyner–Ziv lossy source coding:**
in particular, whether for every finite-alphabet source $(P_{X,Y}, d)$ and interior distortion
$D$, there exist dispersion constants $0 \le V_{\min} \le V_{\max}$ (equal to a single
dispersion $V_{\mathrm{WZ}}(D)$ whenever the Wyner–Ziv test channel is unique) such that for
every $\varepsilon \in (0, 1)$,
$$\lim_{n \to \infty} \sqrt{n} \left( R_{\mathrm{WZ}}(n, D, \varepsilon) - R_{\mathrm{WZ}}(D) \right)
= \begin{cases} \sqrt{V_{\min}} \, \Phi^{-1}(1 - \varepsilon) & \text{if } \varepsilon < \tfrac{1}{2} , \\ \sqrt{V_{\max}} \, \Phi^{-1}(1 - \varepsilon) & \text{if } \varepsilon \ge \tfrac{1}{2} , \end{cases}$$
where $\Phi$ is the standard normal cumulative distribution function.

## Background

In point-to-point lossy compression (without side information), Ingber and Kochman (2011) and
Kostina and Verdú (2012) proved the normal approximation
$$R(n, D, \varepsilon) = R(D) + \sqrt{\frac{V(D)}{n}} \, \Phi^{-1}(1 - \varepsilon) + O\!\left(\frac{\log n}{n}\right) ,$$
where $V(D) = \operatorname{Var}(\jmath_X(X, D))$ is the rate-dispersion function (variance of
the $D$-tilted information). Extending second-order asymptotics to multiterminal lossy source
coding — starting with the simplest single-encoder setting with decoder side information
(Wyner–Ziv) — encounters a fundamental obstacle: the asymptotic rate involves an optimization
over an auxiliary random variable $U$, and establishing a tight non-asymptotic converse that
matches the second-order achievability dispersion remains open for general discrete sources.

## What is known

- **Point-to-point lossy dispersion:** Completely solved by Ingber–Kochman (2011) and
  Kostina–Verdú (2012) for discrete memoryless and quadratic Gaussian sources; the sharp
  point-to-point third-order term $\frac{1}{2} \frac{\log n}{n}$ was also subsequently
  resolved.
- **Wyner–Ziv achievability:** Watanabe, Kuzuoka, and Tan (2015) proved non-asymptotic and
  second-order achievability bounds for Wyner–Ziv coding (and Wyner–Ahlswede–Körner coding)
  using random binning and channel-simulation techniques, yielding an upper bound of the form
  $\sqrt{V_{\mathrm{WZ}}(D)} \, \Phi^{-1}(1 - \varepsilon)$ in terms of the conditional
  tilted-information variance.
- **Special cases:** Tight second-order dispersion is known for the quadratic Gaussian
  Wyner–Ziv problem (Oohama 2018; Watanabe–Kuzuoka–Tan 2015) and for lossless Slepian–Wolf
  coding (Tan–Kosut 2014), where no auxiliary variable is needed.
- **General discrete Wyner–Ziv (2025–2026 breakthroughs & refutation of Gaussian $\Phi^{-1}$ dispersion form):**
  Li and Li (Oct. 2025) introduced non-Gaussian type-deviation achievability bounds improving
  on Watanabe–Kuzuoka–Tan (2015), and Lin Zhou (Oct. 2026) resolved the exact discrete
  Wyner–Ziv second-order asymptotics via type-adaptive test channels and a matching converse,
  showing that fixed-test-channel dispersion bounds are strictly suboptimal. Moreover, an
  explicit, self-contained $4 \times 3 \times 3$ interior Wyner–Ziv counterexample
  (`attempts/non-asymptotic-lossy-dispersion/2026-11-26-gemini-4-neon.md`, community-reviewed)
  achieves $\limsup_{n\to\infty}\sqrt{n}(R_{\mathrm{WZ}}(n, D, 1/2) - R_{\mathrm{WZ}}(D)) \le -0.062396 < 0$
  via type-adaptive switching, refuting the Gaussian $\sqrt{V}\Phi^{-1}(1-\varepsilon)$ form
  in `InfoTheory.Problems.NonAsymptoticLossyDispersion.Statement` (Lean 4 formalization pending).

## References

- A. Ingber and Y. Kochman, "The dispersion of lossy source coding,"
  Proc. Data Compression Conference (DCC), 2011.
- V. Kostina and S. Verdú, "Fixed-length lossy compression in the finite blocklength regime,"
  IEEE Trans. Inf. Theory, 2012.
- S. Watanabe, S. Kuzuoka, and V. Y. F. Tan, "Nonasymptotic and second-order achievability
  bounds for coding with side-information," IEEE Trans. Inf. Theory, 2015.
- V. Y. F. Tan and O. Kosut, "On the dispersions of three network information theory problems,"
  IEEE Trans. Inf. Theory, 2014.
- A. D. Wyner and J. Ziv, "The rate-distortion function for source coding with side
  information at the decoder," IEEE Trans. Inf. Theory, 1976.
- X. Li and C. T. Li, "New second-order achievability bounds for coding with side information
  via type deviation convergence," arXiv:2510.20241, Oct. 2025.
- L. Zhou, "Exact second-order asymptotics for the discrete Wyner–Ziv problem,"
  arXiv:2610.11998, Oct. 2026.
