---
id: index-coding-single-letter
title: Single-Letter Characterization and Computability of the Index Coding Broadcast Rate
status: open
category: network-coding
posed_by: Yitzhak Birk and Tomer Kol; Ziv Bar-Yossef, Yitzhak Birk, T. S. Jayram, and Tomer Kol
posed_year: 1998
tags: [network-coding, index-coding, broadcast-rate, computability]
lean_module: InfoTheory.Problems.IndexCodingSingleLetter
lean_file: lean/InfoTheory/Problems/IndexCodingSingleLetter.lean
---

## Statement

An $n$-user **index coding instance** is given by a directed side-information graph $G = ([n], E)$: a single transmitter holds $n$ independent $t$-bit messages $x_1, \dots, x_n \in \{0, 1\}^t$, and receiver $i \in [n]$ demands $x_i$ while possessing $\{ x_j \mid (i, j) \in E \}$ as side information. A $(t, M)$-index code encodes $(x_1, \dots, x_n)$ into a broadcast symbol in $\{1, \dots, M\}$ from which every receiver $i$ recovers $x_i$ with zero error using its side information. The **optimal broadcast rate** of $G$ is
$$\beta(G) = \inf_{t \ge 1} \frac{1}{t} \log_2 M^*(G, t),$$
where $M^*(G, t)$ is the minimum broadcast alphabet size for message length $t$.

**Open Problem:** Find a computable single-letter (or finite graph-parameter) characterization of the optimal index coding broadcast rate $\beta(G)$ for general directed side-information graphs $G$. In particular, **is $\beta(G)$ even algorithmically computable**—does there exist a halting Turing machine that, given any finite directed graph $G$ and precision $1/k$, approximates $\beta(G)$ within additive error $1/k$? *(Whether $\beta(G)$ is always rational is likewise open.)*

## Background

Index coding was introduced by Birk and Kol (1998) for satellite broadcast with cached side information and formalized graph-theoretically by Bar-Yossef, Birk, Jayram, and Kol (2006, 2011). Despite its deceptively simple single-sender formulation, Effros, El Rouayheb, and Langberg (2015) proved that index coding is **universal for network coding**: every general directed multi-source network coding instance is equivalent to a corresponding index coding instance.

Consequently, characterizing $\beta(G)$ sits at the very core of network information theory and zero-error combinatorics (generalizing Shannon's zero-error graph capacity $\Theta(G)$, whose computability is itself a celebrated open problem). Unlike scalar linear index coding—which is completely characterized by the graph parameter $\mathrm{minrk}_q(G)$ (Bar-Yossef et al. 2011)—the unrestricted (nonlinear, arbitrary-vector-length) broadcast rate $\beta(G)$ has no known single-letter characterization, no known algorithm to compute or even constant-factor approximate it, and no known proof of undecidability.

## What is known

- **Combinatorial and information-theoretic bounds:**
  - **Lower bounds:** $\alpha_{\mathrm{MAIS}}(G) \le \beta_{\mathrm{LP}}(G) \le \beta(G)$, where $\alpha_{\mathrm{MAIS}}(G)$ is the Maximum Acyclic Induced Subgraph number (Bar-Yossef et al. 2011) and $\beta_{\mathrm{LP}}(G)$ is the Shannon-type polymatroid LP relaxation (Blasiak–Kleinberg–Lubetzky 2013; Arbabjolfaei–Bandemer–Kim–Şaşoğlu–Wang 2013).
  - **Upper bounds:** $\beta(G) \le \chi_f(\overline{G})$ (fractional clique cover number), $\beta(G) \le \chi_{\ell}(\overline{G})$ (local chromatic number, Shanmugam–Dimakis–Langberg 2013), and $\beta(G) \le \beta_{\mathrm{lin}}(G) \le \mathrm{minrk}_q(G)$.
  - **Composite coding inner bound:** Arbabjolfaei et al. (2013) introduced the composite coding scheme, which is tight for all graphs up to $n = 5$ vertices, but strictly suboptimal in general.
- **Failure of known candidates:**
  - Bar-Yossef et al. (2011) conjectured $\beta(G) = \mathrm{minrk}_2(G)$ for undirected/symmetric graphs; Lubetzky and Stav (2009) disproved this dramatically.
  - Blasiak, Kleinberg, and Lubetzky (2013) and Sun–Jafar (2015) proved that the Shannon-type polymatroid LP bound $\beta_{\mathrm{LP}}(G)$ is strictly smaller than $\beta(G)$ on matroid-derived graphs (non-Shannon inequalities are needed!).
- **Solved special cases:** $\beta(G)$ is known exactly for perfect graphs ($\beta(G) = \alpha(G) = \chi(\overline{G})$), odd holes and odd anti-holes (Blasiak–Kleinberg–Lubetzky 2013), all graphs with $n \le 5$ vertices (Arbabjolfaei et al. 2013), and special symmetric/planar families.
- **Connection to network coding undecidability:** Cheuk Ting Li's (2023) proof of undecidability for exact zero-error network coding solvability does *not* immediately prove undecidability of approximating the asymptotic broadcast rate $\beta(G)$ (the infimum over all blocklengths $t \ge 1$).

## References

- Y. Birk and T. Kol, "Informed-source coding-on-demand (ISCOD) over broadcast channels," *Proc. IEEE INFOCOM*, pp. 1257–1264, 1998.
- Z. Bar-Yossef, Y. Birk, T. S. Jayram, and T. Kol, "Index coding with side information," *IEEE Trans. Inf. Theory*, 57(3):1479–1494, 2011 (FOCS 2006).
- E. Lubetzky and U. Stav, "Nonlinear index coding outperforming the linear optimum," *IEEE Trans. Inf. Theory*, 55(8):3544–3551, 2009 (FOCS 2007).
- A. Blasiak, R. Kleinberg, and E. Lubetzky, "Broadcasting with side information: Bounding and approximating the broadcast rate," *IEEE Trans. Inf. Theory*, 59(9):5811–5823, 2013.
- F. Arbabjolfaei, B. Bandemer, Y.-H. Kim, E. Şaşoğlu, and L. Wang, "On the capacity region for index coding," *Proc. IEEE ISIT*, pp. 962–966, 2013.
- M. Effros, S. El Rouayheb, and M. Langberg, "An equivalence between network coding and index coding," *IEEE Trans. Inf. Theory*, 61(5):2478–2487, 2015.
- F. Arbabjolfaei and Y.-H. Kim, "Fundamentals of Index Coding," *Foundations and Trends in Communications and Information Theory*, 14(3–4):163–346, 2018.
