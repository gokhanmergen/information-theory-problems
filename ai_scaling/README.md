# Theoretical Bounds and Mathematical Mechanisms for Neural Scaling Laws

A cross-disciplinary mathematical survey, monograph, and reference library synthesizing research on **Theoretical Bounds on AI Scaling Laws** across Information Theory, Differential Geometry, Statistical Physics, and Approximation Theory.

---

## 📂 Key Deliverables

- **Compiled PDF Monograph**: [`theoretical_bounds_on_ai_scaling_laws.pdf`](file:///Users/gokhanmergen/PycharmProjects/information_theory_problems/ai_scaling/theoretical_bounds_on_ai_scaling_laws.pdf)
- **LaTeX Monograph Source**: [`theoretical_bounds_on_ai_scaling_laws.tex`](file:///Users/gokhanmergen/PycharmProjects/information_theory_problems/ai_scaling/theoretical_bounds_on_ai_scaling_laws.tex)
- **Complete BibTeX Bibliography**: [`references.bib`](file:///Users/gokhanmergen/PycharmProjects/information_theory_problems/ai_scaling/references.bib)
- **Automated Build Script**: [`build.sh`](file:///Users/gokhanmergen/PycharmProjects/information_theory_problems/ai_scaling/build.sh)

---

## 🏛️ Cross-Disciplinary Rosetta Stone

| Concept | Information Theory | Geometry / Approximation | Statistical Physics / ML |
| :--- | :--- | :--- | :--- |
| **Data Complexity** | Covariance spectrum $\lambda_k \sim k^{-(1+\rho)}$; Metric entropy $H(\varepsilon) \sim \varepsilon^{-d/s}$ | Manifold intrinsic dimension $d$; Sobolev smoothness $s$ | Kernel / NTK spectrum $\lambda_k \sim k^{-a}$; Target power $c_k^2 \sim k^{-b}$ |
| **Model Capacity** | Description rate $R \approx N b$ bits; Representation states | Tiling cells $K \asymp N$; Linear regions; Metric covering | Parameter count $N$; Feature width $w$; Mode cutoff $k_*$ |
| **Data Budget** | Sequence blocklength $n$; Sample count $D$ | Metric sample covering radius $\varepsilon \sim D^{-1/d}$ | Training samples / tokens $D$; Gradient update steps |
| **Limiting Loss** | Distortion--rate function $D(R) \sim R^{-\rho}$; Entropy rate $h$ | Piecewise Taylor error $N^{-4/d}$; Nonparametric rate $D^{-\frac{2s}{2s+d}}$ | Asymptotic generalization error $\mathcal{E}(D) \sim D^{-\frac{a+b-1}{a}}$; Bayes risk $E$ |

---

## 🔬 Master Taxonomy of Scaling Frameworks

| Theoretical Framework | Core Assumptions | Mathematical Machinery | Derived Exponent | Primary References |
| :--- | :--- | :--- | :--- | :--- |
| **Rate--Distortion Theory** | Gaussian/heavy-tailed source, spectrum $\lambda_k \sim k^{-(1+\rho)}$ | Shannon Reverse Water-Filling, high-rate asymptotics | $D(R) \sim R^{-\rho}$ | Shannon (1948), Berger (1971) |
| **Metric Entropy / Minimax** | Sobolev/Besov target class $W^s(\mathbb{R}^d)$, $H(\varepsilon) \sim \varepsilon^{-d/s}$ | Yang--Barron balance $H(\varepsilon_n) \asymp n \varepsilon_n^2$, Fano testing | $\alpha_D = \frac{2s}{2s+d}$ | Yang & Barron (1999), Tsybakov (2009) |
| **Language Context Horizon** | Correlation decay $\|C(n)\| \sim n^{-\beta}$, entropy decay $H_n - h \sim n^{-\gamma}$ | Sample noise cutoff $n^*(D) \sim D^{1/(2\beta)}$, entropy truncation | $\alpha_D = \frac{\gamma}{2\beta}$ | Cagnetta et al. (2024/2026), Hilberg (1990) |
| **Manifold Tiling Geometry** | Data on $d$-dimensional Riemannian manifold $\mathcal{M}$, $\mathcal{C}^2$ target | Voronoi partition, 2nd-order Taylor remainder on tiles | $\alpha_N = \frac{4}{d}$ | Sharma & Kaplan (2020) |
| **Resolution vs. Variance Phase Diagram** | Interplay of finite parameter count $N$ and dataset size $D$ | Nonparametric manifold covering + CLT variance | $\Delta L \sim N^{-4/d} + D^{-1}$ | Bahri et al. (PNAS 2024) |
| **Kernel Spectra / NTK Physics** | Kernel eigenvalues $\lambda_k \sim k^{-a}$, target projections $c_k^2 \sim k^{-b}$ | Replica method, Random Matrix Theory, spectral bias | $\mathcal{E}(D) \sim D^{-\frac{a+b-1}{a}}$ | Bordelon et al. (2020), Cui et al. (2021) |
| **Linear Model Joint $(N, D)$ Laws** | Covariance $\lambda_k \sim k^{-a}$, target decay $c_k^2 \sim k^{-b}$, one-pass SGD | Sketch dimension truncation + accumulated gradient SNR | $\mathcal{E} = \Theta(N^{-(b-1)} + D^{-\frac{b-1}{a}})$ | Lin et al. (NeurIPS 2024) |
| **Skill Quantization** | Independent skills/quanta with Zipfian utilities $U_i \sim i^{-q}$ | Greedy capacity allocation, tail integration of unlearned mass | $\alpha_N = q - 1$ | Michaud et al. (NeurIPS 2023) |
| **Feature Superposition** | $M \gg d_{\mathrm{model}}$ sparse features, almost-orthogonal frame | Johnson--Lindenstrauss lemma, cross-talk variance | $\text{Noise} \propto \frac{p M}{d_{\mathrm{model}}}$ | Elhage et al. (2022) |

---

## 🛠️ Recompilation

To recompile the monograph using Tectonic:
```bash
cd /Users/gokhanmergen/PycharmProjects/information_theory_problems/ai_scaling
./build.sh
```
