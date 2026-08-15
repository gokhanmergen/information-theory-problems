# Theoretical Bounds on Neural Scaling Laws

This directory contains a critical survey of mathematical explanations and limits for neural scaling laws. The survey distinguishes three levels of evidence:

- rigorous results for specified source, function-class, kernel, or teacher--student models;
- asymptotic or heuristic mechanisms that can generate power laws under explicit assumptions;
- empirical fits whose exponents depend on the dataset, tokenizer, architecture, optimization protocol, and fitted range.

The central conclusion is deliberately limited: there is no general theorem that derives real-language-model scaling exponents from Shannon theory, manifold dimension, or kernel spectra alone. These frameworks explain power laws in particular models and suggest measurable mechanisms, but the identification of their mathematical resources with parameter count, token count, or training compute requires additional assumptions.

## Files

- [`theoretical_bounds_on_ai_scaling_laws.pdf`](theoretical_bounds_on_ai_scaling_laws.pdf) -- compiled survey
- [`theoretical_bounds_on_ai_scaling_laws.tex`](theoretical_bounds_on_ai_scaling_laws.tex) -- LaTeX source
- [`references.bib`](references.bib) -- bibliography used by the survey
- [`build.sh`](build.sh) -- Tectonic build script

## Executive summary

The recurring theme: every framework below produces a power law from the *tail of some ranked quantity* — covariance eigenvalues, kernel eigenvalues and target projections, cells on a manifold, quantum utilities, input frequencies, token correlations. They differ in what they rank and in what they assume about the learner, not in the mathematics that turns a heavy tail into a power law. This is why a straight line on a log–log plot is weak evidence for any one mechanism, and why the discriminating measurements are of the ranked quantity, not of the loss curve.

1. **Empirical status.** Power-law loss fits are useful local summaries, not universal asymptotic laws. Hoffmann et al. fit
   \(L(N,D)=E+A N^{-\alpha_N}+B D^{-\alpha_D}\) with \(E=1.69\), \(\alpha_N=0.34\), and \(\alpha_D=0.28\) for their data and training setup. Compute-optimal allocation follows from these as \(N_{\mathrm{opt}}\propto C^{\alpha_D/(\alpha_N+\alpha_D)}\) and \(D_{\mathrm{opt}}\propto C^{\alpha_N/(\alpha_N+\alpha_D)}\), so it depends only on the ratio \(\alpha_N/\alpha_D\) — which the fit pins down far less tightly than the reported digits suggest. Besiroglu et al. found the reported confidence intervals implausibly narrow; Porian et al. traced the Kaplan–Chinchilla discrepancy to compute accounting, warmup, and optimizer tuning.

2. **Cross-entropy floor.** For a fixed evaluation distribution and conditioning information, expected log loss equals the corresponding conditional entropy plus a conditional KL divergence, so the entropy is exactly the Bayes risk. A fitted constant \(E\) need not equal the infinite-context entropy rate: finite context, distribution shift, misspecification, and optimization each raise it, all in the same direction, and \(E\) is an extrapolated intercept rather than an observed limit. Nats per token cannot be compared with bits per character without converting on the same corpus and tokenizer.

3. **Rate–distortion.** Reverse water-filling gives \(D(R)\asymp R^{-\rho}\) for a Gaussian Hilbert-space source with covariance eigenvalues \(\lambda_k\asymp k^{-(1+\rho)}\), while a fixed finite-dimensional Gaussian source has high-rate exponential decay. The exponent is the spectral tail exponent minus one — a property of the source, not of the coder. This is a rigorous source-coding example, not a proof that neural parameter scaling is governed by rate–distortion: parameter count is not a bit rate unless an explicit coding model and precision constraint are supplied.

4. **Metric entropy and minimax rates.** Under the regularity and testing conditions of nonparametric estimation, a balance of metric entropy and sample information leads to rates such as \(n^{-2s/(2s+d)}\) for Sobolev-smooth classes. These are minimax statements for specified classes and losses, not predictions for arbitrary trained transformers, and neither \(s\) nor \(d\) has an agreed operational meaning for next-token prediction.

5. **Language statistics.** Cagnetta, Raventós, Ganguli, and Wyart (ICML 2026, arXiv:2602.07488) predict the data-limited exponent \(\alpha_D=\gamma/(2\beta)\) in a horizon-limited regime, assuming conditional entropy decays as \(n^{-\gamma}\), token-covariance signal as \(n^{-\beta}\), and within-horizon learning is faster than the truncation error. Their measured statistics give 0.185 for TinyStories and 0.141 for WikiText with no free parameters — the closest thing in this literature to a parameter-free prediction of a real exponent, and falsifiable on any new corpus.

6. **Manifold and regime theories.** The \(4/d\) relation of Sharma and Kaplan follows from a piecewise-linear smooth-regression model and is explicitly conjectural when transferred to realistic neural networks. Their GPT experiment measured intrinsic dimension above 90 while \(4/\alpha_N\approx53\), so it supported the inequality \(d\ge4/\alpha_N\) rather than equality; measuring within a single passage instead gives ID ≈ 7, indicating a scale-dependent manifold rather than one intrinsic dimension. Bahri et al. identify four regimes — variance- and resolution-limited behavior along both data and model axes — and their *proved* resolution-limited bounds are the weaker Lipschitz statements \(O(D^{-1/d})\), \(O(P^{-1/d})\); the \(D^{-c/d}\) form with \(c\ge2\) is a typical-case estimate under analyticity.

7. **Kernel and linear models.** Kernel learning curves depend jointly on eigenvalues, target alignment, noise, and regularization; there is no general exponent determined by the eigenvalue tail alone, and the noiseless and optimally-regularized-noisy regimes have different exponents with a crossover between them. Lin et al. rigorously obtain \(\Theta(N^{-(a-1)}+D^{-(a-1)/a})\) — the additive two-term form with *both* exponents fixed by the single spectral exponent \(a\) — for a specific infinite-dimensional linear regression model trained by one-pass SGD under a Gaussian prior.

8. **Discrete mechanisms and limitations.** The quantization model and feature superposition offer plausible mechanisms, supported mainly by toy models and suggestive empirical evidence; in both cases any loss scaling comes from an assumed heavy-tailed importance distribution rather than from the mechanism itself. Hutter's 2021 paper studies a memorization classifier on countably many inputs; it does not derive neural scaling from universal algorithmic probability. Approximation widths, parametric redundancy, and statistical-query lower bounds constrain particular worst-case or restricted-algorithm models — SGD is not an SQ algorithm, and the continuous-width bound is beaten by discontinuous parameter selection — so none of them imposes a universal limit on SGD-trained networks.

## Build

```bash
cd ai_scaling
./build.sh
```
