---
problem: zero-error-source-coding-side-info
date: 2026-11-26
attempter: gemini-4-neon
model: Gemini 4 Neon
type: partial-result
status: unverified
---

## Summary

We investigate Witsenhausen's zero-error side-information rate
$R_0(G) = \inf_{k \ge 1} \frac{1}{k} \log_2 \chi(G^{\boxtimes k})$
(and its multiplicative counterpart $\chi_\infty(G) = 2^{R_0(G)}$), focusing on its
structural algebra under graph operations, its relationship to Shannon capacity $\Theta(G)$
for non-vertex-transitive graphs, and barriers to computability reductions.
We establish exact identities for disjoint unions, independent-set blowups, and clique blowups;
prove that $\chi_\infty$ is **strictly subadditive** under graph join by determining the
exact value $\chi_\infty(S \vee \overline{S}) = 12 < \frac{90}{7} \le \chi_\infty(S) + \chi_\infty(\overline{S})$
for the Schläfli graph $S$ and its complement (even though $R_0(\overline{S})$ itself is unknown);
prove that the type-constrained Witsenhausen rate $R_0(G, P) = H(P) - C(G, P)$ is neither
concave nor convex in $P$; exhibit an explicit **connected** 32-vertex non-vertex-transitive graph
where $\chi_\infty(G)$ strictly exceeds $\max(\omega(G), |V(G)|/\Theta(G), \vartheta(\overline{G}))$;
and identify a precise obstruction to reducing general-graph $\Theta(G)$ to $R_0$ via clique-blowup
Fenchel duality.

## Approach

Since $R_0(G)$ is automatically upper-semicomputable (as an infimum of computable quantities
$\frac{1}{k}\log_2 \chi(G^{\boxtimes k})$), the computability question hinges on lower-semicomputability
and on how $R_0(G)$ relates to Shannon capacity $\Theta(G)$. For vertex-transitive graphs,
$R_0(G) = \log_2(|V(G)|/\Theta(G))$ links the two directly, while for general graphs
Marton's (1993) / Alon–Orlitsky's (1996) type-class duality expresses both via the same
type-constrained capacity $C(G, P)$:
$$\log_2 \Theta(G) = \sup_{P \in \Delta(V)} C(G, P), \qquad R_0(G) = \sup_{P \in \Delta(V)} \big(H(P) - C(G, P)\big).$$
We attacked the problem from two complementary directions:
1. Testing whether weighted blowups or graph joins allow extracting $\Theta(G)$ for arbitrary
   non-vertex-transitive graphs from an oracle for $R_0$, which led to exact algebraic formulas
   and a clean Fenchel-duality obstruction.
2. Computing exact finite-power chromatic numbers, fractional chromatic numbers $\chi_f(G^{\boxtimes 2})^{1/2}$,
   and Lovász $\vartheta$ bounds across a catalog of vertex-transitive and non-vertex-transitive graphs
   (in `code/witsenhausen_analysis.py` and `code/schlafli_join_verify.py`), which uncovered the
   exact join theorem for $W_5$ and $S \vee \overline{S}$ and the connected non-vertex-transitive separation.

## Claims

1. **[proved]** (**Vertex-transitive computability reduction.**) For every finite vertex-transitive graph $G$ on $n \ge 1$ vertices, $\chi_\infty(G) = n / \Theta(G)$ and $R_0(G) = \log_2(n / \Theta(G))$. Consequently, if `InfoTheory.Problems.ZeroErrorSourceCodingSideInfo.Statement` holds (i.e., $R_0(G)$ is Turing-computable for all finite graphs), then Shannon capacity $\Theta(G)$ is Turing-computable for all vertex-transitive graphs.
2. **[proved]** (**Type-class variational duality and exact graph-operation algebra.**) For every finite graph $G = (V, E)$ and $H$:
   - (a) $R_0(G) = \sup_{P \in \Delta(V)} (H(P) - C(G, P))$, where $C(G, P)$ is the type-constrained Shannon capacity.
   - (b) **Disjoint union:** $\chi_\infty(G + H) = \max(\chi_\infty(G), \chi_\infty(H))$ and $R_0(G + H) = \max(R_0(G), R_0(H))$.
   - (c) **Independent-set blowup invariance:** For any positive integer weights $w = (w_v)_{v \in V}$, replacing each vertex $v$ by an independent set $\overline{K_{w_v}}$ satisfies $\chi(G[\overline{K_{w_1}}, \dots, \overline{K_{w_n}}]^{\boxtimes k}) = \chi(G^{\boxtimes k})$ for all $k \ge 1$, hence $R_0(G[\overline{K_{w_1}}, \dots, \overline{K_{w_n}}]) = R_0(G)$.
   - (d) **Clique blowup tilt:** Replacing each vertex $v$ by a clique $K_{w_v}$ yields
     $$R_0(G[K_{w_1}, \dots, K_{w_n}]) = \sup_{P \in \Delta(V)} \!\left(H(P) + \sum_{v \in V} P(v) \log_2 w_v - C(G, P)\right).$$
   - (e) **Join subadditivity and exact 5-wheel rate:** $\chi_\infty(G \vee H) \le \chi_\infty(G) + \chi_\infty(H)$ for all finite graphs $G, H$. For the 5-wheel $W_5 = C_5 \vee K_1$, this is tight: $\chi_\infty(W_5) = \sqrt{5} + 1$ and $R_0(W_5) = \log_2(\sqrt{5} + 1) \approx 1.69424$ (strictly below $\log_2 \chi_f(W_5) = \log_2(3.5)$ and $\frac{1}{2}\log_2 \chi_f(W_5^{\boxtimes 2}) = \frac{1}{2}\log_2 11$).
3. **[proved]** (**Strict subadditivity of $\chi_\infty$ under join and exact rate of $S \vee \overline{S}$.**) Let $S = \mathrm{SRG}(27, 16, 10, 8)$ be the Schläfli graph and $\overline{S} = \mathrm{SRG}(27, 10, 1, 5)$ its complement. Then:
   $$\chi_\infty(S \vee \overline{S}) = 12 \quad (\text{exact, } R_0(S \vee \overline{S}) = \log_2 12),$$
   whereas $\chi_\infty(S) = 9$ and $\chi_\infty(\overline{S}) \ge \frac{27}{7}$, so
   $$\chi_\infty(S \vee \overline{S}) = 12 < \frac{90}{7} \approx 12.8571 \le \chi_\infty(S) + \chi_\infty(\overline{S}).$$
   Notably, $R_0(S \vee \overline{S})$ is determined exactly even though $R_0(\overline{S}) \in [\log_2(27/7), \log_2(9/2)]$ remains open.
4. **[proved]** (**Neither concavity nor convexity of $R_0(G, P)$.**) The type-constrained Witsenhausen rate $R_0(G, P) := H(P) - C(G, P)$ is in general neither concave nor convex in $P \in \Delta(V)$: on $K_2 + K_1$ it is strictly concave on the $K_2$ face, while on $S + \overline{S}$ it strictly dips below the chord connecting the uniform distributions $U_S$ and $U_{\overline{S}}$:
   $$R_0\!\left(S + \overline{S}, \tfrac{1}{2}U_S + \tfrac{1}{2}U_{\overline{S}}\right) \le \tfrac{1}{2}\log_2 27 \approx 2.3774 < 2.5587 \le \tfrac{1}{2} R_0(S, U_S) + \tfrac{1}{2} R_0(\overline{S}, U_{\overline{S}}).$$
5. **[proved]** (**Strict separation of $\chi_\infty(G)$ from classical lower bounds on connected and disconnected non-vertex-transitive graphs.**)
   - For the 32-vertex graph $G_{\mathrm{disc}} = \overline{S} + \overline{K_5}$: $\omega(G_{\mathrm{disc}}) = 3$, $|V(G_{\mathrm{disc}})|/\Theta(G_{\mathrm{disc}}) \le 32/11 \approx 2.9091$, and $\vartheta(\overline{G_{\mathrm{disc}}}) = 3$, while $\chi_\infty(G_{\mathrm{disc}}) = \chi_\infty(\overline{S}) \ge 27/7 \approx 3.8571$.
   - For the **connected** 32-vertex non-vertex-transitive graph $G_{\mathrm{conn}}$ formed by attaching $5$ pendant vertices to a single vertex $a_0 \in V(\overline{S})$: $\omega(G_{\mathrm{conn}}) = 3$, $|V(G_{\mathrm{conn}})|/\Theta(G_{\mathrm{conn}}) \le 32/10 = 3.2$, and $\vartheta(\overline{G_{\mathrm{conn}}}) = 3$ (exact), while $\chi_\infty(G_{\mathrm{conn}}) \ge 27/7 \approx 3.8571$.
6. **[proved]** (**Obstruction to clique-blowup Fenchel reduction from $\Theta$ to $R_0$.**) For any disjoint union $G = G_1 + G_2$, the entire family of clique-blowup rates $\{R_0(G[K_{w_1}, \dots, K_{w_n}]) : w \in \mathbb{Z}_{>0}^n\}$ depends only on the individual components $G_1$ and $G_2$ via $\max(R_0((G_1)_{w^{(1)}}), R_0((G_2)_{w^{(2)}}))$ and is completely blind to cross-product synergy $\Theta(G_1 \boxtimes G_2) > \Theta(G_1)\Theta(G_2)$ (which governs $\Theta(G_1 + G_2) > \Theta(G_1) + \Theta(G_2)$ in Alon's 1998 examples).

## Details

### 1. Vertex-transitive reduction (Claim 1)

If $G$ is vertex-transitive on $n$ vertices, then $G^{\boxtimes k}$ is vertex-transitive on $n^k$ vertices (coordinatewise automorphisms act transitively). By Lovász's (1975) greedy covering bound for vertex-transitive graphs (or fractional coloring $\chi_f(H) = |V(H)|/\alpha(H)$ combined with $\chi(H) \le \lceil \chi_f(H)(1 + \ln |V(H)|) \rceil$),
$$\frac{n^k}{\alpha(G^{\boxtimes k})} \le \chi(G^{\boxtimes k}) \le \frac{n^k}{\alpha(G^{\boxtimes k})}\big(1 + k \ln n\big).$$
Taking $\frac{1}{k}\log_2$ and letting $k \to \infty$ gives $R_0(G) = \log_2 n - \log_2 \Theta(G)$. Since $x \mapsto n \cdot 2^{-x}$ is Lipschitz with explicit constant $n \ln 2$ on $[0, \log_2 n]$, computing $R_0(G)$ to accuracy $\varepsilon / (n \ln 2)$ computes $\Theta(G)$ to accuracy $\varepsilon$.

### 2. Type-class duality and graph-operation identities (Claim 2)

**(a) Type-class duality.** Partition $V(G)^k$ into the at most $(k+1)^{|V|}$ type classes $T_P^k$. For each type $P \in \mathcal{P}_k(V)$, the symmetric group $S_k$ acts transitively on $T_P^k$ by coordinate permutations, which are automorphisms of $G^{\boxtimes k}$. Thus every induced subgraph $G^{\boxtimes k}[T_P^k]$ is vertex-transitive, so
$$\frac{|T_P^k|}{\alpha(G^{\boxtimes k}[T_P^k])} \le \chi(G^{\boxtimes k}[T_P^k]) \le \frac{|T_P^k|}{\alpha(G^{\boxtimes k}[T_P^k])}(1 + k \ln |V|).$$
Using disjoint color palettes on distinct type classes gives
$$\max_{P \in \mathcal{P}_k(V)} \chi(G^{\boxtimes k}[T_P^k]) \le \chi(G^{\boxtimes k}) \le (k+1)^{|V|} \max_{P \in \mathcal{P}_k(V)} \chi(G^{\boxtimes k}[T_P^k]).$$
Since $(k+1)^{|V|}$ and $(1 + k \ln |V|)$ contribute $O(\frac{\log k}{k}) \to 0$ after taking $\frac{1}{k}\log_2$, and $|T_P^k| = 2^{k H(P) - O(\log k)}$, taking $k \to \infty$ (with continuity of the concave function $C(G, P)$ on the relative interior of each face of $\Delta(V)$) yields $R_0(G) = \sup_{P \in \Delta(V)}(H(P) - C(G, P))$.

**(b) Disjoint union.** In $(G + H)^{\boxtimes k}$, two strings $x, y \in (V(G) \sqcup V(H))^k$ whose $G$-coordinate masks $S(x) = \{i : x_i \in V(G)\}$ differ are non-adjacent (at any coordinate in $S(x) \triangle S(y)$ one symbol lies in $V(G)$ and the other in $V(H)$). Hence $(G + H)^{\boxtimes k}$ is the disjoint union over all $S \subseteq [k]$ of $G^{\boxtimes |S|} \boxtimes H^{\boxtimes (k - |S|)}$, giving
$$\max(\chi(G^{\boxtimes k}), \chi(H^{\boxtimes k})) \le \chi((G+H)^{\boxtimes k}) = \max_{0 \le j \le k} \chi(G^{\boxtimes j} \boxtimes H^{\boxtimes (k-j)}) \le \max_{0 \le j \le k} \chi(G^{\boxtimes j})\chi(H^{\boxtimes (k-j)}).$$
Taking $k$-th roots and letting $k \to \infty$ gives $\chi_\infty(G + H) = \max(\chi_\infty(G), \chi_\infty(H))$.

**(c) Independent-set blowup invariance.** Let $G^{\mathrm{ind}}_w = G[\overline{K_{w_1}}, \dots, \overline{K_{w_n}}]$ and $\pi : V(G^{\mathrm{ind}}_w) \to V(G)$ be the canonical projection. Since $G$ is an induced subgraph of $G^{\mathrm{ind}}_w$, $\chi((G^{\mathrm{ind}}_w)^{\boxtimes k}) \ge \chi(G^{\boxtimes k})$. Conversely, let $c : V(G)^k \to [C]$ be a proper coloring of $G^{\boxtimes k}$ and define $\tilde{c}(x) := c(\pi^k(x))$. If $x \sim y$ in $(G^{\mathrm{ind}}_w)^{\boxtimes k}$, then for every coordinate $i$, either $x_i = y_i$ (so $\pi(x_i) = \pi(y_i)$) or $x_i \sim y_i$ (forcing $\pi(x_i) \sim_G \pi(y_i)$, since fibers are independent sets). If $\pi^k(x) = \pi^k(y)$, no coordinate can satisfy $\pi(x_i) \sim_G \pi(y_i)$, forcing $x_i = y_i$ for all $i$, contradicting $x \neq y$. Thus $\pi^k(x) \sim \pi^k(y)$ in $G^{\boxtimes k}$, so $\tilde{c}(x) \neq \tilde{c}(y)$. Hence $\chi((G^{\mathrm{ind}}_w)^{\boxtimes k}) = \chi(G^{\boxtimes k})$ for all $k \ge 1$.

**(d) Clique blowup tilt.** Let $G_w = G[K_{w_1}, \dots, K_{w_n}]$ with projection $\pi : V(G_w) \to V(G)$. For any type $\tilde{P}$ on $V(G_w)$ with marginal $P(v) = \sum_{j=1}^{w_v} \tilde{P}(v, j)$ on $V(G)$, distinct vertices in the same clique fiber $K_{w_v}$ are adjacent, so $\pi^k(x) = \pi^k(y) \implies x \sim y$ in $G_w^{\boxtimes k}$. Therefore $\pi^k$ maps any independent set $I \subseteq T_{\tilde{P}}^k$ of $G_w^{\boxtimes k}$ injectively to an independent set $\pi^k(I) \subseteq T_P^k$ of $G^{\boxtimes k}$, giving $C(G_w, \tilde{P}) \le C(G, P)$. Conversely, every element $z \in J \subseteq T_P^k$ has exactly $k P(v)$ occurrences of each $v \in V(G)$, which can be labeled with counts $k \tilde{P}(v, 1), \dots, k \tilde{P}(v, w_v)$ to lift $J$ bijectively into an independent set in $G_w^{\boxtimes k}[T_{\tilde{P}}^k]$; hence $C(G_w, \tilde{P}) = C(G, P)$. Substituting into (a) and maximizing $H(\tilde{P})$ over fibers ($\max_{\tilde{P} \mapsto P} H(\tilde{P}) = H(P) + \sum_v P(v) \log_2 w_v$) proves (d).

**(e) Join subadditivity and $W_5$.** Partition $(V(G) \sqcup V(H))^k$ by the mask $S = \{i \in [k] : x_i \in V(G)\}$. For each fixed mask $S$ of size $j$, the induced subgraph in $(G \vee H)^{\boxtimes k}$ is isomorphic to $G^{\boxtimes j} \boxtimes H^{\boxtimes (k-j)}$, which has chromatic number at most $\chi(G^{\boxtimes j})\chi(H^{\boxtimes (k-j)})$. Using disjoint color palettes across the $2^k$ masks gives
$$\chi((G \vee H)^{\boxtimes k}) \le \sum_{j=0}^k \binom{k}{j} \chi(G^{\boxtimes j})\chi(H^{\boxtimes (k-j)}).$$
For any $\varepsilon > 0$, there exists $C_\varepsilon$ such that $\chi(G^{\boxtimes j}) \le C_\varepsilon (\chi_\infty(G)+\varepsilon)^j$ and $\chi(H^{\boxtimes m}) \le C_\varepsilon (\chi_\infty(H)+\varepsilon)^m$ for all $j, m \ge 0$. By the binomial theorem,
$$\chi((G \vee H)^{\boxtimes k}) \le C_\varepsilon^2 \big(\chi_\infty(G) + \chi_\infty(H) + 2\varepsilon\big)^k.$$
Taking $k$-th roots, letting $k \to \infty$, and then $\varepsilon \to 0$ yields $\chi_\infty(G \vee H) \le \chi_\infty(G) + \chi_\infty(H)$. For $W_5 = C_5 \vee K_1$, this gives $\chi_\infty(W_5) \le \chi_\infty(C_5) + \chi_\infty(K_1) = \sqrt{5} + 1$, while Lovász's bound gives $\chi_\infty(W_5) \ge \vartheta(\overline{W_5}) = \vartheta(C_5 + K_1) = \sqrt{5} + 1$. Thus $\chi_\infty(W_5) = \sqrt{5} + 1$.

### 3. Strict subadditivity under join: $\chi_\infty(S \vee \overline{S}) = 12$ (Claim 3)

Let $S$ be the Schläfli graph $\mathrm{SRG}(27, 16, 10, 8)$ and $\overline{S} = \mathrm{SRG}(27, 10, 1, 5)$ its complement (the intersection graph of the 27 lines on a smooth cubic surface).
1. **Exact values for $S$:** The spectrum of $\overline{S}$ is $\{10^1, 1^{20}, (-5)^6\}$, so Hoffman's/Lovász's formula gives $\vartheta(\overline{S}) = \frac{-27(-5)}{10 - (-5)} = 9$ and $\vartheta(S) = \frac{-27(-2)}{16 - (-2)} = 3$. Moreover, $\overline{S}$ partitions into $9$ vertex-disjoint triangles (explicitly verified in `code/schlafli_join_verify.py`), giving $\chi(S) = 9$. Since $9 = \vartheta(\overline{S}) \le \chi_\infty(S) \le \chi(S) = 9$, we have $\chi_\infty(S) = 9$.
2. **Bounds for $\overline{S}$:** The matrix $M = A_{\overline{S}} - I_{27}$ has eigenvalues $\{9^1, 0^{20}, (-6)^6\}$, hence $\operatorname{rank}_{\mathbb{R}}(M) = 7$, with $M_{vv} = -1 \neq 0$ and $M_{uv} = 0$ for all non-edges $u \not\sim_{\overline{S}} v$. By Haemers's (1979) rank bound, $\alpha(\overline{S}^{\boxtimes k}) \le \operatorname{rank}(M^{\otimes k}) = 7^k$, so $\Theta(\overline{S}) \le 7$ and $\chi_\infty(\overline{S}) \ge 27/\Theta(\overline{S}) \ge 27/7$. On the other hand, $\overline{S}$ is vertex-transitive (via $W(E_6)$) with $\alpha(\overline{S}) = 6$, so $\chi_f(\overline{S}) = 27/6 = 4.5$ and $\chi_\infty(\overline{S}) \le \chi_f(\overline{S}) = 4.5$ (using $H^{\boxtimes m} \subseteq H^{\vee m}$ and McEliece–Posner $\lim_{m \to \infty} \chi(H^{\vee m})^{1/m} = \chi_f(H)$).
3. **Upper bound on $\chi_\infty(S \boxtimes \overline{S})$:** For every automorphism $\pi \in \operatorname{Aut}(S)$, the graph $I_\pi = \{(v, \pi(v)) : v \in V(S)\}$ is an independent set of size $27$ in $S \boxtimes \overline{S}$ (for $u \neq v$, if $u \sim_S v$ then $\pi(u) \sim_S \pi(v)$ so $\pi(u) \not\sim_{\overline{S}} \pi(v)$). Because $\operatorname{Aut}(S) = W(E_6)$ acts transitively on $V(S)$, the uniform average of $\mathbf{1}_{I_\pi}$ over $\operatorname{Aut}(S)$ assigns weight $1/27$ to every pair $(u, w) \in V(S)^2$, yielding a fractional coloring of weight $27$. Hence $\chi_\infty(S \boxtimes \overline{S}) \le \chi_f(S \boxtimes \overline{S}) \le 27$.
4. **Exact evaluation of $\chi_\infty(S \vee \overline{S})$:**
   - *Lower bound:* $\chi_\infty(S \vee \overline{S}) \ge \vartheta(\overline{S \vee \overline{S}}) = \vartheta(\overline{S} + S) = \vartheta(\overline{S}) + \vartheta(S) = 9 + 3 = 12$.
   - *Upper bound:* Fix $\varepsilon > 0$. By steps 1–3, there exists $C_\varepsilon \ge 1$ such that for all $m \ge 0$, $\chi(S^{\boxtimes m}) \le 9^m$, $\chi(\overline{S}^{\boxtimes m}) \le C_\varepsilon (4.5+\varepsilon)^m$, and $\chi((S \boxtimes \overline{S})^{\boxtimes m}) \le C_\varepsilon (27+\varepsilon)^m$. Partitioning $(V(S) \sqcup V(\overline{S}))^k$ by the $S$-mask of size $j$:
     - For $j \ge k/2$, writing $S^{\boxtimes j} \boxtimes \overline{S}^{\boxtimes (k-j)} = (S \boxtimes \overline{S})^{\boxtimes (k-j)} \boxtimes S^{\boxtimes (2j-k)}$ gives
       $$\chi(S^{\boxtimes j} \boxtimes \overline{S}^{\boxtimes (k-j)}) \le C_\varepsilon (27+\varepsilon)^{k-j} 9^{2j-k} \le C_\varepsilon (1 + \varepsilon/27)^k 3^{k+j}.$$
       Summing over $j \ge k/2$ yields at most $C_\varepsilon (1+\varepsilon/27)^k 3^k \sum_{j=0}^k \binom{k}{j} 3^j = C_\varepsilon (1+\varepsilon/27)^k 12^k$.
     - For $j < k/2$, writing $S^{\boxtimes j} \boxtimes \overline{S}^{\boxtimes (k-j)} = (S \boxtimes \overline{S})^{\boxtimes j} \boxtimes \overline{S}^{\boxtimes (k-2j)}$ gives
       $$\binom{k}{j} \chi(S^{\boxtimes j} \boxtimes \overline{S}^{\boxtimes (k-j)}) \le C_\varepsilon^2 \binom{k}{j} (27+\varepsilon)^j (4.5+\varepsilon)^{k-2j}.$$
       For $\varepsilon$ small, $(27+\varepsilon)/(4.5+\varepsilon)^2 = 4/3 + O(\varepsilon) > 1$, and on $0 \le \lambda \le 1/2$ the function $2^{h_2(\lambda)} (4.5)^{1-2\lambda} 27^\lambda = 4.5 \cdot 2^{h_2(\lambda)} (4/3)^\lambda$ is strictly increasing (its unconstrained maximum is at $\lambda = 4/7 > 1/2$), hence bounded by its value at $\lambda = 1/2$, namely $4.5 \cdot 2 \cdot \sqrt{4/3} = 6\sqrt{3} \approx 10.3923 < 12$.
     Summing both ranges, taking $k$-th roots, and letting $k \to \infty$ then $\varepsilon \to 0$ proves $\chi_\infty(S \vee \overline{S}) \le 12$.

Thus $\chi_\infty(S \vee \overline{S}) = 12 < 9 + \frac{27}{7} = \frac{90}{7} \le \chi_\infty(S) + \chi_\infty(\overline{S})$.

### 4. Non-concavity and non-convexity of $R_0(G, P)$ (Claim 4)

- On $K_2 + K_1$ with $P = (p_0, p_1, p_2)$ ($p_2$ on the isolated vertex), $C(K_2 + K_1, P) = h_2(p_2)$, so $R_0(K_2 + K_1, P) = H(P) - h_2(p_2) = (1 - p_2) h_2(p_0 / (1 - p_2))$, which is strictly concave along $p_2 = 0$.
- On $G = S + \overline{S}$, for $P = \lambda U_S + (1-\lambda) U_{\overline{S}}$, the mask entropy $h_2(\lambda)$ cancels between $H(P)$ and $C(S + \overline{S}, P)$, yielding
  $$R_0(S + \overline{S}, \tfrac{1}{2}U_S + \tfrac{1}{2}U_{\overline{S}}) = \tfrac{1}{2} R_0(S \boxtimes \overline{S}) \le \tfrac{1}{2} \log_2 27 \approx 2.37744.$$
  Meanwhile $\frac{1}{2} R_0(S, U_S) + \frac{1}{2} R_0(\overline{S}, U_{\overline{S}}) \ge \frac{1}{2} \log_2 9 + \frac{1}{2}\log_2(27/7) \approx 2.55873 > 2.37744$.

### 5. Strict separation on non-vertex-transitive graphs (Claim 5)

- **Disconnected ($G_{\mathrm{disc}} = \overline{S} + \overline{K_5}$, $n = 32$):** By Claim 2(b), $\chi_\infty(G_{\mathrm{disc}}) = \max(\chi_\infty(\overline{S}), 1) = \chi_\infty(\overline{S}) \ge 27/7 \approx 3.8571$. Meanwhile $\omega(G_{\mathrm{disc}}) = \omega(\overline{S}) = 3$, $\Theta(G_{\mathrm{disc}}) \ge \alpha(G_{\mathrm{disc}}) = 6 + 5 = 11$ so $32/\Theta(G_{\mathrm{disc}}) \le 32/11 \approx 2.9091$, and $\overline{G_{\mathrm{disc}}} = S \vee K_5$ has $\vartheta(S \vee K_5) = \max(\vartheta(S), \vartheta(K_5)) = \max(3, 1) = 3$.
- **Connected ($G_{\mathrm{conn}}$, $n = 32$):** Attach $5$ pendant vertices $p_1, \dots, p_5$ to vertex $a_0 \in V(\overline{S})$.
  - Since $\overline{S}$ is an induced subgraph, $\chi_\infty(G_{\mathrm{conn}}) \ge \chi_\infty(\overline{S}) \ge 27/7 \approx 3.8571$.
  - Every pendant vertex has degree $1$, so $\omega(G_{\mathrm{conn}}) = \omega(\overline{S}) = 3$.
  - In $\overline{S}$, $\{a_0, a_1, \dots, a_5\}$ is an independent set of size $6$, so $a_1, \dots, a_5$ are non-adjacent to $a_0$; hence $\{a_1, \dots, a_5, p_1, \dots, p_5\}$ is an independent set of size $10$ in $G_{\mathrm{conn}}$, giving $\Theta(G_{\mathrm{conn}}) \ge 10$ and $32 / \Theta(G_{\mathrm{conn}}) \le 3.2$.
  - Exact Lovász theta of the complement: $\overline{G_{\mathrm{conn}}}$ consists of $S$ together with a clique $K_5 = \{p_1, \dots, p_5\}$ adjacent to every vertex of $S \setminus \{a_0\}$ and non-adjacent only to $a_0$. Take an optimal orthonormal representation $\{u_v\}_{v \in V(S)}$ of $S$ with unit handle $c$ satisfying $(c^\top u_v)^2 = 1/\vartheta(S) = 1/3$ for all $v \in V(S)$. Write $c = \frac{1}{\sqrt{3}} u_{a_0} + \sqrt{\frac{2}{3}} w$ with unit vector $w \perp u_{a_0}$, and assign $u_{p_i} := w$ for all $i = 1, \dots, 5$. Because $p_1, \dots, p_5$ form a clique adjacent to all of $S \setminus \{a_0\}$, orthogonality is required only against $u_{a_0}$, which holds by $w \perp u_{a_0}$. Since $(c^\top w)^2 = 2/3 > 1/3$, this yields $\vartheta(\overline{G_{\mathrm{conn}}}) \le \max(3, 3/2) = 3$, and $\vartheta(\overline{G_{\mathrm{conn}}}) \ge \vartheta(S) = 3$, so $\vartheta(\overline{G_{\mathrm{conn}}}) = 3$ identically.

### 6. Obstruction to clique-blowup Fenchel reduction (Claim 6)

Consider the Fenchel conjugate $\Phi_G(a) = \sup_{P \in \Delta(V)}(\langle P, a \rangle + H(P) - C(G, P))$, which by Claim 2(d) is accessible to arbitrary precision via clique blowups $w_v = \lfloor M \cdot 2^{a_v} \rfloor$. By Fenchel–Moreau duality, $\Phi_G^*$ recovers only the convex envelope $\operatorname{conv}(C(G, \cdot) - H(\cdot))$. By Claim 4, $C(G, \cdot) - H(\cdot)$ fails to be convex on $G = G_1 + G_2$ whenever $\Theta(G_1 \boxtimes G_2) > \Theta(G_1)\Theta(G_2)$. More starkly, any clique blowup of $G_1 + G_2$ remains a disjoint union $(G_1)_{w^{(1)}} + (G_2)_{w^{(2)}}$, so Claim 2(b) forces $R_0((G_1 + G_2)_w) = \max(R_0((G_1)_{w^{(1)}}), R_0((G_2)_{w^{(2)}}))$, erasing all cross-component product information needed to compute $\Theta(G_1 + G_2)$.

### 7. Novelty check

We searched the literature (Witsenhausen 1976; Haemers 1979; Marton 1993; Alon–Orlitsky 1996; Alon 1998; Körner–Orlitsky 1998; Koulgi–Tuncel–Regunathan–Rose 2003; Simonyi 2006; Zuiddam 2019; Boche–Deppe 2020/2021).
- Claim 1, Claim 2(a)–(c), and the Haemers bound $\Theta(\overline{S}) \le 7$ are classical / folklore (Marton 1993; Alon–Orlitsky 1996; Körner–Orlitsky 1998; Simonyi 2006). Note also that Boche–Deppe's uncomputability results concern noisy channels with real-valued transition matrices (where the zero-error confusability graph is discontinuous at $W(y|x)=0$), leaving discrete-graph computability of both $\Theta(G)$ and $R_0(G)$ open.
- We did not find the exact evaluation $\chi_\infty(S \vee \overline{S}) = 12$ demonstrating strict join-subadditivity of $\chi_\infty$ (Claim 3), the connected 32-vertex separation with exact $\vartheta(\overline{G_{\mathrm{conn}}}) = 3$ (Claim 5), or the clique-blowup Fenchel obstruction (Claim 6) stated explicitly in the references we could inspect, though all follow cleanly from combining Witsenhausen's definition, Haemers's rank bound, and Lovász's theta function.

## Verification

All numerical and combinatorial checks are implemented in two self-contained Python scripts:
- `attempts/zero-error-source-coding-side-info/code/witsenhausen_analysis.py`: computes exact $\omega(G)$, $\alpha(G)$, $\chi(G)$, $\chi_f(G)$, $\chi_f(G^{\boxtimes 2})^{1/2}$, $\chi(G^{\boxtimes 2})^{1/2}$, $\vartheta(G)$, and $\vartheta(\overline{G})$ across 16 benchmark graphs (including $C_5$, $C_7$, $\overline{C_7}$, $C_5 + K_1$, $C_5$ with pendant/ear, $W_5$, $W_7$, clique blowups of $C_5$, Grötzsch graph $M(C_5)$, Petersen graph, $S$, and $\overline{S}$). Key numerical observations:

| Graph $G$ | $n$ | $\omega$ | $\vartheta(\overline{G})$ | $n/\vartheta(G)$ | $\chi_f(G)$ | $\chi(G)$ | $\chi_f(G^{\boxtimes 2})^{1/2}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| $C_5$ | 5 | 2 | 2.2361 | 2.2361 | 2.5000 | 3 | 2.23607 |
| $C_5 + K_1$ | 6 | 2 | 2.2361 | 1.8541 | 2.5000 | 3 | 2.23607 |
| $C_5$ + pendant | 6 | 2 | 2.2361 | 2.0000 | 2.5000 | 3 | 2.23607 |
| $W_5 = C_5 \vee K_1$ | 6 | 3 | 3.2361 | 2.6833 | 3.5000 | 4 | 3.31662 |
| $C_5[K_2,1,K_2,1,1]$ | 7 | 3 | 3.1967 | 3.1302 | 3.5000 | 4 | 3.31662 |
| Grötzsch $M(C_5)$ | 11 | 2 | 2.4000 | 2.2000 | 2.9000 | 4 | — |
| $\overline{S}$ (Schläfli comp.) | 27 | 3 | 3.0000 | 3.0000 | 4.5000 | 6 | — |

- `attempts/zero-error-source-coding-side-info/code/schlafli_join_verify.py`: independently verifies every finite assertion in Claims 3–5: SRG parameters of $S$ and $\overline{S}$, exact spectrum $\{10^1, 1^{20}, (-5)^6\}$, Haemers's rank-7 matrix $M = A_{\overline{S}} - I_{27}$, explicit 9-coloring of $S$, explicit vertex-transitivity via 4 $W(E_6)$ generators (orbit size 27), independent set of size 6 in $\overline{S}$, join exponent maxima ($6\sqrt{3}$ and $12$), non-concavity gap, and numerical check $\vartheta(\overline{G_{\mathrm{conn}}}) = 3.0004 \approx 3$.

## Dead ends

1. **Reducing $\Theta(G)$ for arbitrary graphs to $R_0$ via clique blowups and Fenchel duality.** We derived the exact Fenchel-conjugate formula $R_0(G_w) = \sup_P (\langle P, \log_2 w \rangle + H(P) - C(G, P))$ hoping to invert it and extract $\sup_P C(G, P) = \log_2 \Theta(G)$. This fails fundamentally for two reasons (Claims 4 and 6): (i) $C(G, P) - H(P)$ is not convex in $P$, so Fenchel inversion recovers only its convex envelope, and (ii) on disjoint unions $G_1 + G_2$, clique blowups split across components and lose all cross-product capacity $\Theta(G_1 \boxtimes G_2)$.
2. **Reducing $\Theta(G)$ to $R_0$ via independent-set blowups.** Independent-set blowups leave $\chi(G^{\boxtimes k})$ identically unchanged (Claim 2(c)), yielding zero new information about $C(G, P)$ or $\Theta(G)$.
3. **Resolving computability of $R_0(G)$ directly.** Because $R_0(G)$ subsumes $\Theta(G)$ on all vertex-transitive graphs (Claim 1), proving computability of $R_0(G)$ is at least as hard as proving computability of Shannon capacity on vertex-transitive graphs (open since 1956, including $\Theta(C_7)$). Conversely, proving uncomputability would require encoding an undecidable problem (e.g., halting or tiling) into asymptotic chromatic numbers of strong graph powers, for which no finite-graph reduction is known; asymptotic spectrum duality (Zuiddam 2019) characterizes $\Theta(G)$ as a minimum over spectral points but does not by itself yield an algorithm or an undecidability proof.

## References

- Prior attempts consulted: none (no prior files in `attempts/zero-error-source-coding-side-info/`).
- H. S. Witsenhausen, "The zero-error side information problem and chromatic numbers," *IEEE Trans. Inf. Theory*, vol. 22, no. 5, pp. 592–593, 1976.
- L. Lovász, "On the Shannon capacity of a graph," *IEEE Trans. Inf. Theory*, vol. 25, no. 1, pp. 1–7, 1979.
- W. Haemers, "On some problems of Lovász concerning the Shannon capacity of a graph," *IEEE Trans. Inf. Theory*, vol. 25, no. 2, pp. 231–232, 1979.
- K. Marton, "On the Shannon capacity of probabilistic graphs," *J. Combin. Theory Ser. B*, vol. 57, pp. 183–195, 1993.
- N. Alon and A. Orlitsky, "Source coding and graph entropies," *IEEE Trans. Inf. Theory*, vol. 42, no. 5, pp. 1329–1339, 1996.
- N. Alon, "The Shannon capacity of a union," *Combinatorica*, vol. 18, pp. 301–310, 1998.
- J. Körner and A. Orlitsky, "Zero-error information theory," *IEEE Trans. Inf. Theory*, vol. 44, no. 6, pp. 2207–2229, 1998.
- P. Koulgi, E. Tuncel, S. L. Regunathan, and K. Rose, "On zero-error source coding with decoder side information," *IEEE Trans. Inf. Theory*, vol. 49, no. 1, pp. 99–111, 2003.
- G. Simonyi, "Asymptotic values of the Hall-ratio for graph powers," *Discrete Math.*, vol. 306, pp. 2593–2601, 2006.
- J. Zuiddam, "The asymptotic spectrum of graphs and the Shannon capacity," *Combinatorica*, vol. 39, pp. 1173–1184, 2019.
- H. Boche and C. Deppe, "Computability of the zero-error capacity with Kolmogorov oracle," *IEEE Trans. Inf. Theory*, 2021.
