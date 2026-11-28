---
id: interactive-info-complexity-compression
title: Optimal Compression of Interactive Protocols by External Information Cost
status: open
category: security-privacy
posed_by: Boaz Barak, Mark Braverman, Xi Chen, and Anup Rao
posed_year: 2010
tags: [information-complexity, communication-complexity, interactive-compression, privacy]
lean_module: InfoTheory.Problems.InteractiveInfoComplexityCompression
lean_file: lean/InfoTheory/Problems/InteractiveInfoComplexityCompression.lean
---

## Statement

Consider a two-party public-coin randomized interactive protocol $\pi$ computing a Boolean function $f : \mathcal{X} \times \mathcal{Y} \to \{0, 1\}$ on inputs $(X, Y) \sim \mu$ with public randomness $R$ and transcript $\Pi$ of length $C(\pi)$ bits. Its **external information cost** is
$$
\mathrm{IC}^{\mathrm{ext}}(\pi, \mu) := I(X, Y; \Pi \mid R),
$$
and its **internal information cost** is
$$
\mathrm{IC}^{\mathrm{int}}(\pi, \mu) := I(X; \Pi \mid Y, R) + I(Y; \Pi \mid X, R).
$$
Always $\mathrm{IC}^{\mathrm{int}}(\pi, \mu) \le \mathrm{IC}^{\mathrm{ext}}(\pi, \mu) \le C(\pi)$, with equality $\mathrm{IC}^{\mathrm{int}} = \mathrm{IC}^{\mathrm{ext}}$ whenever $\mu = \mu_X \times \mu_Y$ is a product distribution.

**Determine the optimal compression of interactive protocols in terms of their external information cost $I = \mathrm{IC}^{\mathrm{ext}}(\pi, \mu)$ (and for bounded-round protocols in terms of internal information cost). In particular, resolve the Linear External Information Compression Conjecture (formalized in Lean):**

Does there exist a universal constant $C > 0$ such that every two-party interactive protocol $\pi$ computing a Boolean function $f$ with error $\le 1/10$ under $\mu$ and external information cost $I = \mathrm{IC}^{\mathrm{ext}}(\pi, \mu)$ can be compressed to a protocol $\pi'$ computing $f$ with error $\le 1/3$ under $\mu$ and communication length
$$
C(\pi') \le C \cdot (I + 1) \quad ?
$$

## Background

Information complexity (Chakrabarti–Shi–Wirth–Yao 2001; Barak–Braverman–Chen–Rao 2010; Braverman 2012) bridges Shannon theory and communication complexity by measuring how much information the transcript reveals about the parties' inputs. For *amortized* computation of $n$ independent instances, Braverman and Rao (2011) proved that the amortized communication complexity equals the internal information cost exactly — the interactive analogue of Shannon's source coding theorem.

The **single-shot interactive compression** problem asks whether a single execution of an interactive protocol with low information cost $I$ can be compressed to communication proportional to $I$, independent of its original length $C(\pi)$. For *internal* information cost on non-product distributions, Ganor, Kol, and Raz (2014) stunned the community by proving an exponential separation $2^{\Omega(I)}$; however, for **external** information cost (and equivalently for internal information cost on product distributions), whether linear compression $O(I)$ is possible — or whether a logarithmic penalty $\Theta(I \log I)$ is unavoidable — remains wide open.

## What is known

- **Amortized compression (direct sum):** Braverman and Rao (2011) proved that $n$ independent copies can be compressed to $n \cdot \mathrm{IC}^{\mathrm{int}}(\pi, \mu) + o(n)$ bits.
- **Internal information cost (general non-product $\mu$):**
  - Upper bounds: Barak–Braverman–Chen–Rao (2010) achieved $\tilde{O}(\sqrt{C \cdot I})$; Braverman (2012) achieved $2^{O(I)}$ independent of $C$.
  - Lower bound: Ganor, Kol, and Raz (2014, 2015) proved that exponential blowup $2^{\Omega(I)}$ is unavoidable in general (the "pointer jumping / tribal" separation).
  - Bounded rounds: For $r$-round protocols, Braverman, Garg, Pankratov, and Weinstein (2013) compressed internal information cost to $O(I + r \log(r/\varepsilon))$ (with logarithmic/polynomial dependence on $r$ and $\varepsilon$), while the optimal round dependence remains actively studied.
- **External information cost (and product distributions $\mu = \mu_X \times \mu_Y$):**
  - Barak–Braverman–Chen–Rao (2010) achieved $O(I^{\mathrm{ext}} \cdot \mathrm{polylog}(C))$.
  - Braverman–Garg–Pankratov–Weinstein (2013) and Kol (2016) eliminated the dependence on $C$ on product distributions, achieving **$O(I \log I)$** communication (for bounded error); Sherstov (2016) and Braverman–Weinstein also studied related regimes.
  - **Linear compression $O(I^{\mathrm{ext}} + 1)$ vs $\Omega(I^{\mathrm{ext}} \log I^{\mathrm{ext}})$** remains a flagship open problem (BBCR 2010; Braverman 2012; Kol 2016).

## Formal statement and certificate

- **Adversarial check (2026-11-27): Statement is faithful and open, for Boolean functions.**
  The Lean statement quantifies over Boolean `f` (with public and private coins, error `1/10`
  compressed to error `1/3`). For *relations* the analogous claim is false: Ganor–Kol–Raz
  ("Exponential separation of communication and external information", STOC 2016 / SICOMP 2021)
  give a search problem with external information `O(k)` and distributional communication
  `≥ 2^k`. That example is not a Boolean function, and Braverman–Minzer (arXiv:2103.04049) treat
  external information of Boolean functions as a separate question (they separate external
  from internal information; their communication-side gap is only near-quadratic, for amortized
  zero-error communication). Braverman–Kol (STOC 2018) compress to `poly(I^ext) · log log C(π)`.
  The "What is known" bullet above that calls linear compression "flagship open" is accurate
  only for Boolean functions.
- **Certificate** (`Known/Certificates/InteractiveInfoComplexityCompression.lean`):
  - regression `extInfoCost_nonneg`, `extInfoCost_le_length`: `0 ≤ IC^ext(π) ≤ C(π) = L`;
  - `protocolErr_nonneg`, `protocolErr_le_one`;
  - `conclusion_of_short`, `conclusion_of_length_le_one`: the conclusion is met by `π` itself
    when `L ≤ C (IC^ext + 1)`, so the side conditions are not an obstruction.
- **Not certified:** BBCR / Braverman–Kol compression and any separation.

## References

- B. Barak, M. Braverman, X. Chen, and A. Rao, "How to compress interactive communication," *Proc. 42nd ACM STOC*, 67–76 (2010); *SIAM J. Comput.* **42**(3), 1327–1363 (2013).
- M. Braverman and A. Rao, "Information equals amortized communication," *Proc. 52nd IEEE FOCS*, 748–757 (2011); *IEEE Trans. Inf. Theory* **60**(10), 6058–6069 (2014).
- M. Braverman, "Interactive information complexity," *Proc. 44th ACM STOC*, 505–524 (2012); *SIAM J. Comput.* **44**(6), 1698–1739 (2015).
- M. Braverman, A. Garg, D. Pankratov, and O. Weinstein, "From information to exact communication," *Proc. 45th ACM STOC*, 151–160 (2013).
- A. Ganor, G. Kol, and R. Raz, "Exponential separation of information and communication," *Proc. 55th IEEE FOCS*, 176–185 (2014); *J. ACM* **63**(5), Article 46 (2016).
- G. Kol, "Interactive compression for product distributions," *Proc. 48th ACM STOC*, 987–998 (2016).
