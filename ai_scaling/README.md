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

## Corrected executive summary

1. **Empirical status.** Power-law loss fits are useful local summaries, not universal asymptotic laws. Hoffmann et al. fit
   \(L(N,D)=E+A N^{-\alpha}+B D^{-\beta}\) with \(E=1.69\), \(\alpha=0.34\), and \(\beta=0.28\) for their data and training setup. These constants are not tokenizer- or protocol-invariant, and later work has examined the sensitivity and reproducibility of compute-optimal fits.

2. **Cross-entropy floor.** For a fixed evaluation distribution and conditioning information, expected log loss equals the corresponding conditional entropy plus a conditional KL divergence. The entropy is therefore a Bayes lower bound. A fitted constant \(E\), however, need not equal the infinite-context entropy rate; finite context, distribution shift, model misspecification, and optimization can all raise it. Nats per token cannot be compared directly with bits per character without converting on the same corpus and tokenizer.

3. **Rate--distortion.** Reverse water-filling gives \(D(R)\asymp R^{-\beta}\) for a Gaussian Hilbert-space source with covariance eigenvalues \(\lambda_k\asymp k^{-(1+\beta)}\), while a fixed finite-dimensional Gaussian source has high-rate exponential decay. This is a rigorous source-coding example, not a proof that neural parameter scaling is governed by rate--distortion: parameter count is not a bit rate unless an explicit coding model and precision constraint are supplied.

4. **Metric entropy and minimax rates.** Under the regularity and testing conditions of nonparametric estimation, a balance of metric entropy and sample information leads to rates such as \(n^{-2s/(2s+d)}\) for Sobolev-smooth classes. These are minimax statements for specified classes and losses, not predictions for arbitrary trained transformers.

5. **Language statistics.** Cagnetta, Raventós, Ganguli, and Wyart (ICML 2026, arXiv:2602.07488) predict the data-limited exponent \(\alpha_D=\gamma/(2\beta)\) in a horizon-limited regime, assuming conditional entropy decays as \(n^{-\gamma}\), token-covariance signal as \(n^{-\beta}\), and within-horizon learning is faster. Their reported values imply predictions near 0.18 for TinyStories and 0.14 for WikiText, not 0.5.

6. **Manifold and regime theories.** The \(4/d\) relation of Sharma and Kaplan follows from a piecewise-linear smooth-regression model and is explicitly conjectural when transferred to realistic neural networks. Their GPT experiment measured intrinsic dimension at least 90 while \(4/\alpha\approx53\), so it supported an inequality rather than equality. Bahri et al. identify four regimes--variance- and resolution-limited behavior along both data and model axes--rather than a universal two-term crossover formula.

7. **Kernel and linear models.** Kernel learning curves depend jointly on eigenvalues, target alignment, noise, and regularization; there is no general exponent determined by the eigenvalue tail alone. Lin et al. rigorously obtain \(\Theta(M^{-(a-1)}+N^{-(a-1)/a})\) for a specific infinite-dimensional linear regression model trained by one-pass SGD under a Gaussian prior and power-law covariance spectrum.

8. **Discrete mechanisms and limitations.** The quantization model and feature superposition offer plausible mechanisms, supported mainly by toy models and tentative empirical evidence. Hutter's 2021 paper studies a memorization classifier on countably many inputs; it does not derive neural scaling from universal algorithmic probability. Approximation widths, parametric redundancy, and statistical-query lower bounds constrain particular worst-case models but do not by themselves impose universal limits on SGD-trained neural networks.

## Build

```bash
cd ai_scaling
./build.sh
```
