# Theoretical Bounds and Mathematical Mechanisms for Neural Scaling Laws

A cross-disciplinary mathematical survey synthesizing research on **theoretical bounds for AI scaling laws** across information theory, high-dimensional statistics, approximation theory, statistical physics, and the statistics of natural language.

The central question: empirical loss curves are straight lines on log–log axes over many orders of magnitude. *Why a straight line, and what determines its slope?*

---

## 📂 Deliverables

- **Compiled PDF monograph** (32 pp.): [`theoretical_bounds_on_ai_scaling_laws.pdf`](theoretical_bounds_on_ai_scaling_laws.pdf)
- **LaTeX source**: [`theoretical_bounds_on_ai_scaling_laws.tex`](theoretical_bounds_on_ai_scaling_laws.tex)
- **BibTeX bibliography** (83 entries, thematically organised): [`references.bib`](references.bib)
- **Build script** (Tectonic): [`build.sh`](build.sh)

---

## 🧭 How the monograph is organised

| § | Topic | What you get |
| :-- | :--- | :--- |
| 1 | Introduction | Roadmap, unified notation table, four-level evidence scale |
| 2 | Empirical laws | Published exponents, compute-optimal allocation, the compute exponent $\alpha_C$, Kaplan-vs-Chinchilla, metric artefacts |
| 3 | Information theory | Cross-entropy floor, rate–distortion theorem with full proof, Yang–Barron minimax, MDL redundancy, Jeon–Van Roy |
| 4 | Language statistics | Zipf, Hilberg/Dębowski, the parameter-free prediction $\alpha_D=\gamma/(2\beta)$, and a control experiment that complicates it |
| 5 | Geometry & limits | Manifold tiling, variance/resolution phase diagram, $n$-widths, SQ and cryptographic hardness |
| 6 | Solvable models | The "cutoff calculus", kernel rates, exact joint $(N,D)$ laws, why the optimizer changes the data exponent |
| 7 | Discrete mechanisms | Hutter's memorizer, skill quanta, associative memories, superposition |
| 8 | Synthesis | Master taxonomy + **numerical consistency checks against published fits** |
| 9–10 | Honest gap, frontiers, conclusion | What no theory yet explains, and where the field is moving |
| A–B | Appendices | Glossary for cross-disciplinary readers; one-page cutoff/exponent cheat sheet |

---

## 🔑 The unifying principle

> **scaling exponent = (tail decay of ranked primitives) × (algorithmic resolution rule)**

Every framework in the survey is an instance of it. The primitives may be covariance eigenmodes, kernel modes, manifold cells, Zipfian skills, discrete inputs, or context scales; the resolution rule is set by the resource *and the algorithm*.

### Cutoff cheat sheet

With target power $c_k^2 \asymp k^{-b}$ and residual $\mathcal{E}\asymp k_*^{-(b-1)}$:

| Resource / algorithm | cutoff $k_*$ | excess loss |
| :--- | :--- | :--- |
| $N$-dimensional sketch / truncation | $N$ | $N^{-(b-1)}$ |
| Ridgeless kernel regression, no noise | $D$ | $D^{-(b-1)}$ |
| Kernel ridge regression, noisy, optimal ridge | $D^{1/b}$ | $D^{-(b-1)/b}$ |
| One-pass SGD, spectrum $k^{-a}$ | $D^{1/a}$ | $D^{-(b-1)/a}$ |
| Multi-pass SGD, $L \lesssim D^{a/b}$ | $L^{1/a}$ | $\to D^{-(b-1)/b}$ |
| Manifold tiling, $\mathcal{C}^2$ target | $\varepsilon = N^{-1/d}$ | $N^{-4/d}$ |
| Zipf inputs/skills $\propto i^{-\zeta}$ | $D^{1/\zeta}$ | $D^{-(\zeta-1)/\zeta}$ |
| Correlation horizon, noise floor $D^{-1/2}$ | $D^{1/(2\beta)}$ | $D^{-\gamma/(2\beta)}$ |
| Rate–distortion, $R$ bits, spectrum $k^{-(1+\rho)}$ | $R$ | $R^{-\rho}$ |

Rows 2–5 share identical data and identical targets and differ **only** in the algorithm, yet give four different data exponents.

---

## 🔬 Master taxonomy of frameworks

| Framework | Core assumptions | Derived exponent | Refs | Evidence |
| :--- | :--- | :--- | :--- | :--- |
| Rate–distortion | Gaussian source, $\lambda_k \asymp k^{-(1+\rho)}$ | $\mathcal{D}(R)\asymp R^{-\rho}$ | Shannon (1948), Berger (1971) | L1 |
| Metric entropy / minimax | Sobolev $W^s([0,1]^d)$ | $\alpha_D = \frac{2s}{2s+d}$ | Yang & Barron (1999) | L1 |
| Universal coding / MDL | Regular $k$-parameter family | $\mathcal{E}\asymp \frac{N\log D}{2D}$, $N\propto D$ | Rissanen (1996), Clarke & Barron (1990), Jeon & Van Roy (2024) | L1 |
| Language horizon | $\|C(n)\|\asymp n^{-\beta}$, $H_n-h \asymp n^{-\gamma}$ | $\alpha_D = \frac{\gamma}{2\beta}$ | Cagnetta et al. (2026), Hilberg (1990) | L3 |
| Manifold tiling | $d$-manifold, $\mathcal{C}^2$ target | $\alpha_N = \frac{4}{d}$ | Sharma & Kaplan (2020) | L3 |
| Variance / resolution phases | Finite $N$, $D$, width $w$ | $D^{-1}$, $w^{-1}$, $D^{-n/d}$, $N^{-n/d}$ | Bahri et al. (PNAS 2024) | L2/L3 |
| Kernel spectra | $\lambda_k \asymp k^{-a}$, $c_k^2 \asymp k^{-b}$ | $D^{-(b-1)}$ noiseless; $D^{-(b-1)/b}$ noisy | Bordelon et al. (2020), Cui et al. (2021) | L1/L2 |
| Joint $(N,D)$ linear | Power-law spectrum, one-pass SGD | $\Theta(N^{-(b-1)} + D^{-(b-1)/a})$ | Lin et al. (NeurIPS 2024, 2025) | L2 |
| Memorization | Zipf inputs $\theta_i \propto i^{-(1+\eta)}$ | $\alpha_D = \frac{\eta}{1+\eta}$ | Hutter (2021) | L1 |
| Skill quantization | Zipf utilities $U_i \asymp i^{-\zeta}$ | $\alpha_N = \zeta-1$, $\alpha_D = \frac{\zeta-1}{\zeta}$ | Michaud et al. (NeurIPS 2023) | L3 |
| Superposition | $M \gg d_{\text{model}}$ sparse features | noise $\propto \frac{pM}{d_{\text{model}}}$ | Elhage et al. (2022) | L2 |

**Evidence levels.** L1 rigorous theorem · L2 controlled solvable model · L3 mechanistic proposal · L4 empirical fit.

---

## ✅ Consistency checks against published fits (§8.2)

Each framework maps measured exponents onto data statistics, so each can be tested for internal consistency:

| Theory and its map | Kaplan $(0.076, 0.095)$ | Chinchilla $(0.34, 0.28)$ |
| :--- | :--- | :--- |
| Manifold tiling: $d = 4/\alpha_N$ | $d \approx 53$ | $d \approx 12$ |
| One-pass SGD: $\alpha_N = a\,\alpha_D$, needs $a>1$ | $a = 0.80$ — **inadmissible** | $a = 1.21$, $b = 1.34$ — admissible |
| Quantization: $\alpha_D = \alpha_N/(\alpha_N+1)$ | predicts $0.071$ vs. $0.095$ | predicts $0.254$ vs. $0.280$ |
| Compute frontier: $\alpha_C = \frac{\alpha_N\alpha_D}{\alpha_N+\alpha_D}$ | $0.042$ vs. reported $0.050$ | $0.154$ |

Theories that predict a *relation between* $\alpha_N$ and $\alpha_D$ are worth more than theories predicting either alone, because they can fail.

---

## ⚠️ The honest gap

No existing theory derives the empirical exponents of a real language model from first principles. What the theories establish is a **reduction**: the exponent is a function of measurable data and algorithm properties. The strongest current result (Cagnetta et al., ICML 2026) closes the loop for $\alpha_D$ by measuring $\gamma$ and $\beta$ on the actual corpus — a genuine advance, and still a reduction rather than an explanation.

---

## 🛠️ Recompilation

```bash
cd ai_scaling
./build.sh          # requires tectonic
```
