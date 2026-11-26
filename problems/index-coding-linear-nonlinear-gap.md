---
id: index-coding-linear-nonlinear-gap
title: Optimal Asymptotic Separation Between Linear and Nonlinear Index Coding Rates
status: partially-solved
category: network-coding
posed_by: Erez Lubetzky and Uri Stav; Anna Blasiak, Robert Kleinberg, and Eyal Lubetzky
posed_year: 2009
tags: [network-coding, index-coding, linear-vs-nonlinear, graph-theory]
lean_module: InfoTheory.Problems.IndexCodingLinearNonlinearGap
lean_file: lean/InfoTheory/Problems/IndexCodingLinearNonlinearGap.lean
---

## Statement

For an $n$-vertex directed side-information graph $G$, let $\beta(G)$ denote the optimal (possibly nonlinear, vector) index coding broadcast rate, and let $\beta_{\mathrm{lin}}(G) = \inf_{\mathbb{F}_q} \beta_{\mathrm{lin}, q}(G)$ denote the optimal **field-independent vector linear** index coding rate (infimum over *all* finite fields $\mathbb{F}_q$ and *all* message vector lengths $t \ge 1$). For every $n$-vertex graph, $1 \le \beta(G) \le \beta_{\mathrm{lin}}(G) \le n$, so the multiplicative gap $\beta_{\mathrm{lin}}(G) / \beta(G)$ is at most $n$.

For a **fixed** finite field (such as $\mathbb{F}_2$), Lubetzky and Stav (2009) proved an almost-linear separation of $n^{1 - 2\varepsilon}$ (scalar linear over $\mathbb{F}_2$ requires $\ge n^{1 - \varepsilon}$ while a code linear over a different field achieves $\le n^\varepsilon$). For **arbitrary-field** vector linear index coding vs. nonlinear index coding, Blasiak, Kleinberg, and Lubetzky (2011, 2013) proved a polynomial gap $\beta_{\mathrm{lin}}(G) / \beta(G) = \Omega(n^c)$ for a small positive constant $c > 0$.

**Open Problem:** Determine the optimal asymptotic exponent $\gamma \in (0, 1]$ such that $\max_{|V(G)| = n} \beta_{\mathrm{lin}}(G) / \beta(G) = n^{\gamma - o(1)}$. In particular, **can the field-independent vector-linear vs. nonlinear index coding gap reach $\Omega(n^{1 - \varepsilon})$** for every $\varepsilon > 0$?

## Background

Bar-Yossef, Birk, Jayram, and Kol (2006, 2011) proved that scalar linear index coding over $\mathbb{F}_q$ is governed by $\mathrm{minrk}_q(G)$ and conjectured that linear coding is always optimal for index coding. Lubetzky and Stav (2007, 2009) dramatically disproved this conjecture for any fixed finite field $\mathbb{F}_q$ by constructing $n$-vertex Ramsey-type graphs (variants of Frankl–Wilson graphs) where $\mathrm{minrk}_q(G) \ge n^{1 - \varepsilon}$ yet a scalar linear code over another field $\mathbb{F}_{q'}$ achieves rate $n^\varepsilon$.

Because Lubetzky and Stav's "nonlinear" code was still linear over a *different* finite field, the deeper question of separating **all finite-field vector linear index codes** from genuinely nonlinear index codes remained open until Blasiak, Kleinberg, and Lubetzky (2011, 2013) combined matroidal non-representability (Dougherty–Freiling–Zeger) with hypergraph lexicographic products to establish a polynomial gap $n^c$. Determining how large the exponent $c$ can be—whether it reaches $1$ as in the fixed-field case or is strictly bounded away from $1$—remains wide open.

## What is known

- **Fixed-field scalar linear vs. nonlinear (Lubetzky–Stav 2009):** For every fixed finite field $\mathbb{F}_q$ and every $\varepsilon > 0$, there exist $n$-vertex graphs with $\mathrm{minrk}_q(G) \ge \Omega(n^{1 - \varepsilon})$ and $\beta(G) \le O(n^\varepsilon)$, giving a gap of $\Omega(n^{1 - 2\varepsilon})$.
- **Fixed-field vector linear vs. scalar linear:** Haviv and Langberg (2012) and Alon, Hassidim, Lubetzky, Stav, and Weinstein (2008) showed strict separations between scalar and vector linear index coding, and studied broadcast rate behavior under graph powers.
- **Arbitrary-field vector linear vs. nonlinear (Blasiak–Kleinberg–Lubetzky 2011, 2013):** Using lexicographic products of matroidal index coding instances (such as those arising from the Vámos and Fano/non-Fano matroids), they proved that there exists a constant $c > 0$ and $n$-vertex graphs $G$ with
  $$\frac{\inf_{\mathbb{F}_q} \beta_{\mathrm{lin}, q}(G)}{\beta(G)} = \Omega(n^c).$$
- **Upper bound:** Since $\beta(G) \ge 1$ and $\beta_{\mathrm{lin}}(G) \le n$ (and in fact $\beta_{\mathrm{lin}}(G) \le \chi_f(\overline{G}) \le n$), the ratio is trivially at most $n$ (and $O(n / \log n)$ via basic graph-theoretic bounds on graphs with small $\beta(G)$). Pinpointing the exact maximum exponent $\gamma \in (0, 1]$ remains open.

## References

- Z. Bar-Yossef, Y. Birk, T. S. Jayram, and T. Kol, "Index coding with side information," *IEEE Trans. Inf. Theory*, 57(3):1479–1494, 2011 (FOCS 2006).
- N. Alon, A. Hassidim, E. Lubetzky, U. Stav, and A. Weinstein, "Broadcasting with side information," *Proc. 49th IEEE FOCS*, pp. 823–832, 2008.
- E. Lubetzky and U. Stav, "Nonlinear index coding outperforming the linear optimum," *IEEE Trans. Inf. Theory*, 55(8):3544–3551, 2009 (FOCS 2007).
- A. Blasiak, R. Kleinberg, and E. Lubetzky, "Lexicographic products and the power of non-linear network coding," *Proc. 52nd IEEE FOCS*, pp. 609–618, 2011.
- A. Blasiak, R. Kleinberg, and E. Lubetzky, "Broadcasting with side information: Bounding and approximating the broadcast rate," *IEEE Trans. Inf. Theory*, 59(9):5811–5823, 2013.
- I. Haviv and M. Langberg, "On linear index coding for random graphs," *Proc. IEEE ISIT*, pp. 2231–2235, 2012.
