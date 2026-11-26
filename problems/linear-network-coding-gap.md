---
id: linear-network-coding-gap
title: Maximum Multiplicative Gap Between Nonlinear and Linear Network Coding Capacity
status: partially-solved
category: network-coding
posed_by: Randall Dougherty, Chris Freiling, and Kenneth Zeger
posed_year: 2005
tags: [network-coding, linear-network-coding, matroids, capacity-gap]
lean_module: InfoTheory.Problems.LinearNetworkCodingGap
lean_file: lean/InfoTheory/Problems/LinearNetworkCodingGap.lean
---

## Statement

Consider a finite directed acyclic multiple-unicast network $\mathcal{N}$ on $V$ vertices with unit-capacity directed edges and $s$ source–destination pairs $(a_i, b_i)$. Let $C_{\mathrm{nl}}(\mathcal{N})$ denote its symmetric (equal-rate) **nonlinear network coding capacity**, and let $C_{\mathrm{lin}}(\mathcal{N})$ denote its supremum symmetric **vector linear network coding capacity** over *all* finite fields $\mathbb{F}_q$ and *all* vector dimensions $t \ge 1$.

Dougherty, Freiling, and Zeger (2005) proved that $C_{\mathrm{nl}}(\mathcal{N}) / C_{\mathrm{lin}}(\mathcal{N})$ can strictly exceed $1$ (obtaining $11/10$), and Blasiak, Kleinberg, and Lubetzky (2011, 2013) amplified this separation to a polynomial gap $V^{\Omega(1)}$ via lexicographic products. On the other hand, trivial time-sharing routing bounds the ratio from above by $O(V)$.

**Open Problem:** Determine the optimal asymptotic exponent $\gamma \in (0, 1]$ of the maximum multiplicative capacity gap $\max_{|\mathcal{N}| = V} C_{\mathrm{nl}}(\mathcal{N}) / C_{\mathrm{lin}}(\mathcal{N})$ over arbitrary finite fields as a function of network size $V$. In particular, **can the multiplicative gap between nonlinear and arbitrary-field linear network coding approach linear growth $V^{1 - \varepsilon}$** for every $\varepsilon > 0$?

## Background

For single-source multicast networks, Ahlswede, Cai, Li, and Yeung (2000) and Li, Yeung, and Cai (2003) proved that linear network coding over a sufficiently large finite field achieves the exact max-flow/min-cut capacity. This sparked the natural question of whether linear codes always suffice for general multi-source, multiple-unicast networks.

In a landmark 2005 paper, Dougherty, Freiling, and Zeger refuted the sufficiency of linear network coding by combining the Fano matroid (representable only in characteristic $2$) and the non-Fano matroid (representable only in odd characteristic) into a single network with nonlinear capacity $1$ and linear capacity at most $10/11$ over *every* finite field. While subsequent constructions amplified the gap to arbitrarily large constants and small polynomials in network size, pinpointing the maximum possible multiplicative advantage of nonlinear over linear network coding remains open.

## What is known

- **Single-source multicast:** Linear network coding is always optimal ($C_{\mathrm{nl}} = C_{\mathrm{lin}}$; Li–Yeung–Cai 2003; Koetter–Médard 2003).
- **Constant gap (Dougherty–Freiling–Zeger 2005):** Constructed an explicit directed acyclic network (based on the Fano and non-Fano matroids, and separately the Vámos matroid) with $C_{\mathrm{nl}}(\mathcal{N}) = 1$ and $C_{\mathrm{lin}}(\mathcal{N}) \le 10/11$ over every finite field and every vector dimension.
- **Arbitrarily large constant gaps:** Dougherty, Freiling, and Zeger (2007) and Lovett (2014) showed via network composition that the multiplicative gap $C_{\mathrm{nl}} / C_{\mathrm{lin}}$ is unbounded (linear network coding cannot approximate network coding capacity within any constant factor).
- **Polynomial gaps:** Blasiak, Kleinberg, and Lubetzky (FOCS 2011 / IEEE TIT 2013) used hypergraph lexicographic products to amplify matroidal separations into polynomial multiplicative gaps $V^{c}$ (for a small constant $c > 0$) between nonlinear coding and arbitrary-field vector linear coding.
- **Upper bound:** Every feasible network with $s$ sessions admits a linear (in fact, routing) solution achieving rate at least $C_{\mathrm{nl}} / s$, yielding a trivial upper bound of $O(V)$ (or $O(|E|)$) on the multiplicative gap. Closing the exponent gap between $c$ and $1$ remains open.

## References

- R. Ahlswede, N. Cai, S.-Y. R. Li, and R. W. Yeung, "Network information flow," *IEEE Trans. Inf. Theory*, 46(4):1204–1216, 2000.
- S.-Y. R. Li, R. W. Yeung, and N. Cai, "Linear network coding," *IEEE Trans. Inf. Theory*, 49(2):371–381, 2003.
- R. Dougherty, C. Freiling, and K. Zeger, "Insufficiency of linear coding in network information flow," *IEEE Trans. Inf. Theory*, 51(8):2745–2759, 2005.
- R. Dougherty, C. Freiling, and K. Zeger, "Networks, matroids, and non-Shannon information inequalities," *IEEE Trans. Inf. Theory*, 53(6):1949–1969, 2007.
- A. Blasiak, R. Kleinberg, and E. Lubetzky, "Lexicographic products and the power of non-linear network coding," *Proc. 52nd IEEE FOCS*, pp. 609–618, 2011 (IEEE Trans. Inf. Theory, 2013).
- S. Lovett, "Network coding cannot be approximated within any constant factor by linear codes," *arXiv:1408.0596*, 2014.
