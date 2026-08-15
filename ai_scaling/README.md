# Theoretical Bounds and Mechanisms for Neural Scaling Laws

This directory contains a scientific survey of mathematical explanations, mechanisms, and bounds for neural scaling laws. The survey distinguishes three levels of evidence:

- rigorous results for specified source, function-class, kernel, or teacher--student models;
- asymptotic or heuristic mechanisms that can generate power laws under explicit assumptions;
- empirical fits whose exponents depend on the dataset, tokenizer, architecture, optimization protocol, and fitted range.

The organizing conclusion is constructive: the frameworks are complementary, and each becomes predictive under a different set of measurable assumptions. Shannon theory, manifold geometry, spectral learning theory, long-range language statistics, and discrete-task models all explain power laws in specified settings. Connecting their mathematical resources to parameter count, token count, or training compute is the central scientific opportunity.

## Files

- [`theoretical_bounds_on_ai_scaling_laws.pdf`](theoretical_bounds_on_ai_scaling_laws.pdf) -- compiled survey
- [`theoretical_bounds_on_ai_scaling_laws.tex`](theoretical_bounds_on_ai_scaling_laws.tex) -- LaTeX source
- [`references.bib`](references.bib) -- bibliography used by the survey
- [`build.sh`](build.sh) -- Tectonic build script

## Executive summary

The recurring theme is that many frameworks produce a power law from the *tail of a ranked quantity* — covariance eigenvalues, kernel eigenvalues and target projections, cells on a manifold, quantum utilities, input frequencies, or token correlations. They differ in what they rank and in how the learner converts rank into effective resolution. Measuring those latent quantities alongside loss curves offers a promising way to distinguish mechanisms.

1. **Empirical status.** Power-law loss fits are useful finite-range summaries. Hoffmann et al. fit
   \(L(N,D)=E+A N^{-\alpha_N}+B D^{-\alpha_D}\) with \(E=1.69\), \(\alpha_N=0.34\), and \(\alpha_D=0.28\) for their data and training setup. Compute-optimal allocation follows as \(N_{\mathrm{opt}}\propto C^{\alpha_D/(\alpha_N+\alpha_D)}\) and \(D_{\mathrm{opt}}\propto C^{\alpha_N/(\alpha_N+\alpha_D)}\). Replication and ablation studies clarify the uncertainty in this ratio and show how compute accounting, warmup, and optimizer tuning affect the estimate.

2. **Cross-entropy floor.** For a fixed evaluation distribution and conditioning information, expected log loss equals the corresponding conditional entropy plus a conditional KL divergence, so the entropy is exactly the Bayes risk. A fitted constant \(E\) need not equal the infinite-context entropy rate: finite context, distribution shift, misspecification, and optimization each raise it, all in the same direction, and \(E\) is an extrapolated intercept rather than an observed limit. Nats per token cannot be compared with bits per character without converting on the same corpus and tokenizer.

3. **Rate–distortion.** Reverse water-filling gives \(D(R)\asymp R^{-\rho}\) for a Gaussian Hilbert-space source with covariance eigenvalues \(\lambda_k\asymp k^{-(1+\rho)}\), while a fixed finite-dimensional Gaussian source has high-rate exponential decay. The exponent is the spectral tail exponent minus one — a property of the source, not of the coder. This rigorous source-coding example can be connected to neural parameter scaling by supplying an explicit coding model, precision constraint, and distortion measure.

4. **Metric entropy and minimax rates.** Under the regularity and testing conditions of nonparametric estimation, a balance of metric entropy and sample information leads to rates such as \(n^{-2s/(2s+d)}\) for Sobolev-smooth classes. These minimax statements become candidate transformer predictions once the effective class, loss, dependence structure, and operational meanings of \(s\) and \(d\) are identified.

5. **Language statistics.** Cagnetta, Raventós, Ganguli, and Wyart (ICML 2026, arXiv:2602.07488) predict the data-limited exponent \(\alpha_D=\gamma/(2\beta)\) in a horizon-limited regime, assuming conditional entropy decays as \(n^{-\gamma}\), token-covariance signal as \(n^{-\beta}\), and within-horizon learning is faster than the truncation error. Their measured statistics give 0.185 for TinyStories and 0.141 for WikiText with no free parameters — the closest thing in this literature to a parameter-free prediction of a real exponent, and falsifiable on any new corpus.

6. **Manifold and regime theories.** The \(4/d\) relation of Sharma and Kaplan follows from a piecewise-affine smooth-regression mechanism; transferring it to realistic neural networks requires relating parameter count to effective cells. Their GPT experiment supports \(d\ge4/\alpha_N\), while the much smaller dimension measured within a single passage suggests useful scale-dependent geometry. Bahri et al. organize scaling into four variance- and resolution-limited regimes. Their rigorous Lipschitz bounds are \(O(D^{-1/d})\) and \(O(P^{-1/d})\), complemented by a typical-case \(D^{-c/d}\) estimate under analyticity.

7. **Spectral, linear, and dynamical models.** Kernel learning curves depend jointly on eigenvalues, target alignment, noise, and regularization. Lin et al. rigorously obtain \(\Theta(N^{-(a-1)}+D^{-(a-1)/a})\) for an infinite-dimensional linear regression model trained by one-pass SGD under a Gaussian prior. Random-feature theories by Bordelon et al. and Paquette et al. extend this picture to training dynamics and multiple compute-optimal phases determined by capacity, optimizer noise, and feature embedding.

8. **Discrete and controlled mechanisms.** Cabannes et al. derive sample- and parameter-scaling laws for outer-product associative memories under heavy-tailed inputs; Hutter derives a memorization curve for countably many inputs; the quantization and superposition models describe how skills or sparse features may use capacity. Barkeshli et al. complement these results with controlled transformer experiments in which scaling also appears on random-graph data without power-law correlations. Approximation widths, parametric redundancy, and statistical-query results then identify precise boundaries for particular function classes and algorithmic models.

## Build

```bash
cd ai_scaling
./build.sh
```
