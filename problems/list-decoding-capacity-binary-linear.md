---
id: list-decoding-capacity-binary-linear
title: Optimal List Size of Binary Linear Codes Approaching List-Decoding Capacity
status: partially-solved
category: coding-theory
posed_by: Peter Elias; Venkatesan Guruswami, Johan Håstad, and Swastik Kopparty
posed_year: 1957
tags: [coding-theory, list-decoding, binary-linear-codes, capacity]
lean_module: InfoTheory.Problems.ListDecodingCapacityBinaryLinear
lean_file: lean/InfoTheory/Problems/ListDecodingCapacityBinaryLinear.lean
---

## Statement

A binary code $C \subseteq \{0, 1\}^n$ is **$(p, L)$-list-decodable** if every Hamming ball of radius $p n$ in $\{0, 1\}^n$ contains at most $L$ codewords of $C$. By the list-decoding capacity theorem (Elias 1957; Wozencraft 1958), the maximum asymptotic rate of $(p, L)$-list-decodable binary codes with subexponential list size is $1 - h(p)$ for every $p \in (0, 1/2)$.

At rate $R = 1 - h(p) - \varepsilon$ (gap $\varepsilon > 0$ to list-decoding capacity), random binary linear codes achieve $(p, L)$-list-decodability with $L \le \lfloor h(p)/\varepsilon \rfloor + 2$ and fail below $\lfloor h(p)/\varepsilon \rfloor$ (Li–Wootters 2021; Guruswami–Li–Mosheiff–Resch–Silas–Wootters 2022). Meanwhile, the best known lower bounds valid for **arbitrary** (not necessarily random) binary codes give $L = \Omega_p(1/\varepsilon)$ with a leading constant strictly smaller than $h(p)$.

**Open Problem:** Is the random-linear-code list-size threshold $L \sim h(p)/\varepsilon$ asymptotically optimal among **all** binary linear codes approaching list-decoding capacity? That is, for every $p \in (0, 1/2)$ and every constant $c < h(p)$, does there exist $\varepsilon_0 > 0$ such that for all $\varepsilon \in (0, \varepsilon_0)$ and sufficiently large $n$, no binary linear code $C \subseteq \mathbb{F}_2^n$ of rate at least $1 - h(p) - \varepsilon$ is $(p, \lfloor c / \varepsilon \rfloor)$-list-decodable?

## Background

List decoding (introduced independently by Elias and Wozencraft in 1957–1958) allows correcting up to twice as many adversarial errors as unique decoding, pushing the error radius up to $p < 1/2$ at positive rate $1 - h(p) - \varepsilon$. For decades, a major question was whether *linear* binary codes could even achieve $L = O(1/\varepsilon)$ list size (matching completely random nonlinear codes) rather than $L = 2^{O(1/\varepsilon)}$ as given by Zyablov and Pinsker (1981).

Guruswami, Håstad, and Kopparty (2011) resolved the $O(1/\varepsilon)$ scaling for random binary linear codes, and Li and Wootters (2021) pinned down the exact list size of *random* binary linear codes to $\lfloor h(p)/\varepsilon \rfloor + O(1)$, while Mosheiff, Resch, Ron-Zewi, Silas, and Wootters (2020) proved that sparse LDPC codes also achieve list-decoding capacity with constant list size. However, just as the Gilbert–Varshamov problem asks whether any binary code can beat random coding for unique decoding ($L = 1$), determining the exact optimal list size (leading constant in $1/\varepsilon$) achievable by *arbitrary* binary linear codes—as well as the exact rate–radius tradeoff $R_L(p)$ for any fixed $L \ge 2$—remains open.

## What is known

- **Random nonlinear codes:** Achieve rate $1 - h(p) - \varepsilon$ with list size $L = \lceil 1/\varepsilon \rceil$ (and random codes of size $2^{(1 - h(p) - \varepsilon)n}$ have sharp list-size threshold around $\Theta(1/\varepsilon)$).
- **Random binary linear codes:**
  - Zyablov and Pinsker (1981) proved $L \le 2^{O(1/\varepsilon)}$.
  - Guruswami, Håstad, and Kopparty (2011) proved $L \le C(p)/\varepsilon$ for random binary linear codes (and over $\mathbb{F}_q$ with $q$-dependent constant).
  - Li and Wootters (2021) proved that a random binary linear code of rate $1 - h(p) - \varepsilon$ is with high probability $(p, L)$-list-decodable for $L = \lceil h(p)/\varepsilon \rceil + 2$.
  - Guruswami, Li, Mosheiff, Resch, Silas, and Wootters (2022) proved a matching converse for *random* binary linear codes: w.h.p. they are **not** $(p, L)$-list-decodable for $L < \lfloor h(p)/\varepsilon \rfloor$.
- **Structured / LDPC codes:** Mosheiff, Resch, Ron-Zewi, Silas, and Wootters (2020) proved that random Gallager LDPC codes achieve list-decoding capacity with constant list size $L = O_{p, \varepsilon}(1)$.
- **Lower bounds for all codes:** Blinovsky (1986) established combinatorial list-size lower bounds for binary codes (and Guruswami–Vadhan 2010 gave a clean proof of $L = \Omega(1/\varepsilon^2)$ at the zero-rate radius $p = 1/2 - \varepsilon$); at interior radii $p \in (0, 1/2)$ and rate $1 - h(p) - \varepsilon$, Guruswami–Narayanan (2014) and related average-radius bounds show $L = \Omega_p(1/\varepsilon)$ with a leading constant strictly smaller than the random-linear-code threshold $h(p)$. Closing the gap between universal lower bounds and the random-linear-code threshold $h(p)/\varepsilon$ remains open.

## References

- P. Elias, "List decoding for noisy channels," *MIT Research Laboratory of Electronics Technical Report* 335, 1957.
- V. V. Zyablov and M. S. Pinsker, "List concatenated decoding," *Problems of Information Transmission*, 17(4):236–240, 1981.
- V. M. Blinovsky, "Bounds for codes in the case of list decoding of finite volume," *Problems of Information Transmission*, 22(1):7–19, 1986.
- V. Guruswami, J. Håstad, and S. Kopparty, "On the list-decodability of random linear codes," *IEEE Trans. Inf. Theory*, 57(2):718–725, 2011.
- V. Guruswami and S. Narayanan, "Combinatorial limitations of average-radius list-decoding," *IEEE Trans. Inf. Theory*, 60(10):5827–5842, 2014.
- J. Mosheiff, N. Resch, N. Ron-Zewi, S. Silas, and M. Wootters, "LDPC codes achieve list decoding capacity," *Proc. 61st IEEE FOCS*, pp. 458–469, 2020.
- R. Li and M. Wootters, "Improved list-decodability of random linear binary codes," *IEEE Trans. Inf. Theory*, 67(3):1522–1536, 2021.
- V. Guruswami, R. Li, J. Mosheiff, N. Resch, S. Silas, and M. Wootters, "Bounds for list-decoding and list-recovery of random linear codes," *IEEE Trans. Inf. Theory*, 68(2):923–939, 2022.
