---
id: regenerating-codes-exact-repair
title: Exact Storage–Bandwidth Tradeoff for Exact-Repair Regenerating Codes
status: partially-solved
category: network-coding
posed_by: Alexandros G. Dimakis, P. Brighten Godfrey, Yunnan Wu, Martin J. Wainwright, and Kannan Ramchandran; Chao Tian
posed_year: 2010
tags: [network-coding, regenerating-codes, distributed-storage, exact-repair]
lean_module: InfoTheory.Problems.RegeneratingCodesExactRepair
lean_file: lean/InfoTheory/Problems/RegeneratingCodesExactRepair.lean
---

## Statement

In an $(n, k, d)$ **exact-repair regenerating code** ($2 \le k \le d < n$) storing a file of size $B$ bits across $n$ distributed storage nodes:
1. Each node stores at most $\alpha$ bits (normalized per-node storage $\bar{\alpha} = \alpha / B$).
2. **Data reconstruction:** Any $k$ of the $n$ nodes suffice to recover the entire file with zero error.
3. **Exact node repair:** Whenever any single node $i \in \{1, \dots, n\}$ fails, any $d$-subset $H \subseteq \{1, \dots, n\} \setminus \{i\}$ of helper nodes can each send at most $\beta$ bits (normalized per-helper repair bandwidth $\bar{\beta} = \beta / B$) from which the replacement node reconstructs the **exact** contents of the failed node $i$.

Let $\mathcal{R}_{\mathrm{exact}}(n, k, d) \subseteq \mathbb{R}_{>0}^2$ denote the closure of all achievable normalized storage–bandwidth pairs $(\bar{\alpha}, \bar{\beta})$, and let $\mathcal{R}_{\mathrm{Shannon}}(n, k, d)$ denote the **Shannon-type polymatroid outer bound** consisting of all $(\bar{\alpha}, \bar{\beta})$ admitting a polymatroid (submodular entropy function) on the node and helper-message variables satisfying the storage, bandwidth, helper-determinacy, exact-repair, and $k$-reconstruction constraints.

**Open Problem:** Characterize the exact storage–bandwidth tradeoff region $\mathcal{R}_{\mathrm{exact}}(n, k, d)$ in the interior regime between the Minimum Storage Regenerating (MSR) and Minimum Bandwidth Regenerating (MBR) points for general $(n, k, d)$. In particular, **do Shannon-type information inequalities completely characterize $\mathcal{R}_{\mathrm{exact}}(n, k, d)$**—i.e., does
$$\mathcal{R}_{\mathrm{exact}}(n, k, d) = \mathcal{R}_{\mathrm{Shannon}}(n, k, d)$$
hold for all $2 \le k \le d < n$?

## Background

Dimakis, Godfrey, Wu, Wainwright, and Ramchandran (2010) introduced regenerating codes and completely determined the storage–bandwidth tradeoff for **functional repair** (where a replacement node only needs to preserve the MDS reconstruction property) via the network-coding cut-set bound: $B \le \sum_{i=0}^{k-1} \min(\alpha, (d - i)\beta)$. Two corner points of this tradeoff are the **MSR** point $(\bar{\alpha}, \bar{\beta}) = \left(\frac{1}{k}, \frac{1}{k(d-k+1)}\right)$ and the **MBR** point $(\bar{\alpha}, \bar{\beta}) = \left(\frac{2d}{k(2d-k+1)}, \frac{2}{k(2d-k+1)}\right)$, both of which were subsequently shown to be achievable even under **exact repair** for all $(n, k, d)$.

In a breakthrough, Tian (2014) proved for $(n, k, d) = (4, 3, 3)$ that the exact-repair tradeoff is **strictly worse** than the functional-repair cut-set bound in the interior, and determined $\mathcal{R}_{\mathrm{exact}}(4, 3, 3)$ completely using Shannon-type information inequalities and a matching layered code construction. Sasidharan, Senthoor, and Kumar (2014) and Prakash and Krishnan (2015) proved a non-vanishing gap between exact and functional repair for all $3 \le k \le d < n$. Yet for general $(n, k, d)$—already starting at $(5, 4, 4)$ and $(5, 3, 4)$—the exact interior tradeoff curve and whether Shannon-type inequalities suffice remain open.

## What is known

- **Extreme points (MSR and MBR) are settled for all $(n, k, d)$:**
  - Rashmi, Shah, and Kumar (2011) constructed explicit exact-repair MBR codes for all $(n, k, d)$ and MSR codes for $d \ge 2k - 2$ via product-matrix constructions.
  - Ye and Barg (2017) and Sasidharan–Vajha–Kumar (2017) constructed explicit exact-repair MSR codes for all $(n, k, d)$ with $k \le d < n$.
- **Exact solution for $(n, k, d) = (4, 3, 3)$ (Tian 2014):** Tian proved $\mathcal{R}_{\mathrm{exact}}(4, 3, 3) = \mathcal{R}_{\mathrm{Shannon}}(4, 3, 3)$, showing a strict gap below the functional-repair cut-set curve via the new Shannon-type inequality $4\bar{\alpha} + 6\bar{\beta} \ge 3$ and matching it with an explicit layered code.
- **Universal non-achievability of the functional-repair interior:** Sasidharan, Senthoor, and Kumar (2014) and Prakash and Krishnan (2015) proved that the functional-repair tradeoff is strictly unachievable by exact-repair codes across almost the entire interior for all $3 \le k \le d < n$.
- **Interior code constructions:** Tian, Sasidharan, Aggarwal, Vaishampayan, and Kumar (2015) introduced **layered exact-repair codes** outperforming MSR–MBR space-sharing, and Duursma (2015), Elyasi–Mohajer (2016), and Li–Li–Wang (2019) derived tighter outer bounds and interior constructions for small parameters.
- **Exact solution for $(n, k, d) = (5, 4, 4)$ (Tian 2015):** $\mathcal{R}_{\mathrm{exact}}(5,4,4)$ is the set of $(\bar\alpha, \bar\beta)$ with $15\bar\alpha + 10\bar\beta \ge 6$, $5\bar\alpha + 10\bar\beta \ge 3$, $10\bar\beta \ge 1$ (together with the cut-set constraints); the converse is a computer-generated combination of Shannon-type inequalities and achievability uses canonical layered codes (C. Tian, "A note on the rate region of exact-repair regenerating codes," arXiv:1503.00011). So the Shannon bound is tight in every case characterized so far. *(Catalog correction 2026-11-27: an earlier version of this file listed $(5,4,4)$ as open.)*
- **Open frontier:** For general $(n, k, d)$ (already e.g. $(6,5,5)$ and other larger parameters) the exact-repair region is not known, and it is unknown whether Shannon-type inequalities suffice, i.e. whether $\mathcal{R}_{\mathrm{exact}}(n, k, d) = \mathcal{R}_{\mathrm{Shannon}}(n, k, d)$ always holds (the frozen Lean statement).
- **Formal certificate** (`lean/InfoTheory/Known/Certificates/RegeneratingCodesExactRepair.lean`): both sides of the frozen `↔` contain every point with $\bar\alpha, \bar\beta \ge 1$ and both satisfy the MSR cut-set bound $k\bar\alpha \ge 1$, so neither side is empty or everything.

## References

- A. G. Dimakis, P. B. Godfrey, Y. Wu, M. J. Wainwright, and K. Ramchandran, "Network coding for distributed storage systems," *IEEE Trans. Inf. Theory*, 56(9):4539–4551, 2010.
- K. V. Rashmi, N. B. Shah, and P. V. Kumar, "Optimal exact-regenerating codes for distributed storage at the MSR and MBR points via a product-matrix construction," *IEEE Trans. Inf. Theory*, 57(8):5227–5239, 2011.
- C. Tian, "Characterizing the rate region of the $(4, 3, 3)$ exact-repair regenerating codes," *IEEE J. Selected Areas in Communications*, 32(5):967–975, 2014.
- B. Sasidharan, K. Senthoor, and P. V. Kumar, "An improved outer bound on the storage-repair-bandwidth tradeoff of exact-repair regenerating codes," *Proc. IEEE ISIT*, pp. 2430–2434, 2014.
- N. Prakash and M. N. Krishnan, "The storage-repair-bandwidth trade-off of exact repair linear regenerating codes for the case $d = k = n - 1$," *Proc. IEEE ISIT*, pp. 859–863, 2015.
- C. Tian, B. Sasidharan, V. Aggarwal, V. A. Vaishampayan, and P. V. Kumar, "Layered exact-repair regenerating codes via embedded error correction and block designs," *IEEE Trans. Inf. Theory*, 61(4):1933–1947, 2015.
- C. Tian, "A note on the rate region of exact-repair regenerating codes," arXiv:1503.00011, 2015.
- M. Ye and A. Barg, "Explicit constructions of high-rate MDS array codes with optimal repair bandwidth," *IEEE Trans. Inf. Theory*, 63(4):2001–2014, 2017.
