---
id: deletion-channel-high-d-limit
title: High-Deletion Asymptotic Limit of the Binary Deletion Channel Capacity
status: open
category: channel-capacity
posed_by: Michael Mitzenmacher and Eleni Drinea; Marco Dalai
posed_year: 2006
tags: [channel-capacity, deletion-channel, asymptotics, synchronization]
lean_module: InfoTheory.Problems.DeletionChannelHighDLimit
lean_file: lean/InfoTheory/Problems/DeletionChannelHighDLimit.lean
---

## Statement

Let $C(d)$ be the Shannon capacity (in bits per channel use) of the i.i.d. binary deletion channel with deletion probability $d \in (0, 1)$. Marco Dalai (2011) proved that the normalized high-deletion limit
$$L := \lim_{d \to 1^-} \frac{C(d)}{1 - d} = \inf_{d \in (0, 1)} \frac{C(d)}{1 - d}$$
exists and is strictly positive and finite.

**Problem (High-Deletion Limit of the Binary Deletion Channel).** Determine the exact value of $L = \lim_{d \to 1^-} \frac{C(d)}{1 - d}$. In particular, decide whether $L$ is achieved by alternating-run renewal inputs (the continuous-time Poisson-repeat channel limit), and close the more than three-fold gap between the best known bounds $0.1221 < L < 0.3745$.

As a sharp quantitative benchmark conjecture (well below the current upper bound $0.3745$ and above the renewal lower bound $0.1221$), we formalize the conjecture:
$$\lim_{d \to 1^-} \frac{C(d)}{1 - d} \;\le\; \frac{1}{4}.$$

## Background

When $d \to 1^-$, almost all transmitted bits are deleted, and only an average fraction $1 - d$ of the input bits survive. Dividing $C(d)$ by $1 - d$ measures the **number of reliable bits conveyed per surviving output bit**. Clearly $L \le 1$ (at most one bit per surviving bit), and a long-standing question posed by Mitzenmacher and Drinea (2006) was even whether $L > 0$.

Mitzenmacher and Drinea answered positivity affirmatively by proving $C(d) \ge \frac{1}{9}(1 - d)$ via Jigsaw/run-length codes, showing that reliable communication at a positive rate per surviving bit is possible even as $d \to 1^-$. Dalai (2011) showed by channel composition $C(d_1 + d_2 - d_1 d_2) \le (1 - d_1) C(d_2)$ that $C(d)/(1 - d)$ is non-increasing, proving the limit $L$ exists and equals $\inf_{d \in (0,1)} C(d)/(1 - d)$. Despite nearly two decades of work using run-length renewal processes, Blahut–Arimoto-style numerical optimization, and genie-aided upper bounds, the gap between the best lower bound ($0.1221$) and best upper bound ($0.3745$) remains wide, and it is widely believed that the true limit $L$ is much closer to the lower bound (likely well below $1/4$).

## What is known

- **Existence of $L$ (Dalai, 2011):** $L = \lim_{d \to 1^-} \frac{C(d)}{1 - d} = \inf_{d \in (0, 1)} \frac{C(d)}{1 - d}$ exists.
- **Lower bounds:**
  - Mitzenmacher–Drinea (2006): $L \ge 1/9 \approx 0.1111$.
  - Kirsch–Drinea (2010): $L \ge 0.1185$ via optimized renewal (i.i.d. run-length) input distributions.
  - Rubinstein–Con (2023): $L > 0.1221$ via refined renewal input distributions and tighter numerical mutual-information estimation.
- **Upper bounds:**
  - Fertonani–Duman (2010) and Dalai (2011): $L \le 0.4143$.
  - Rahmati–Duman (2014): $L \le 0.4143$ (extended to general $q$-ary deletion channels).
  - Cheraghchi (2019): clean analytical upper bounds via mean-limited channels.
  - Rubinstein–Con (2023): $C(d) < 0.3745 (1 - d)$ for all $d \ge 0.68$, hence $L \le 0.3745$.
- **Exact value of $L$:** Completely open; even proving $L \le 1/4$ or $L \ge 1/5$ would be a major breakthrough.

## References

- M. Mitzenmacher and E. Drinea, "A simple lower bound for the capacity of the deletion channel," *IEEE Trans. Inf. Theory*, 52(10):4657–4660, 2006.
- A. Kirsch and E. Drinea, "Directly lower bounding the information capacity for channels with i.i.d. deletions and duplications," *IEEE Trans. Inf. Theory*, 56(1):86–102, 2010.
- D. Fertonani and T. M. Duman, "Novel bounds on the capacity of the binary deletion channel," *IEEE Trans. Inf. Theory*, 56(6):2753–2765, 2010.
- M. Dalai, "A new bound on the capacity of the binary deletion channel with high deletion probabilities," *Proc. IEEE ISIT*, pp. 499–502, 2011.
- M. Cheraghchi, "Capacity upper bounds for deletion-type channels," *J. ACM*, 66(2):Article 9, 2019.
- I. Rubinstein and R. Con, "Improved upper and lower bounds on the capacity of the binary deletion channel," arXiv:2305.07156, 2023.
