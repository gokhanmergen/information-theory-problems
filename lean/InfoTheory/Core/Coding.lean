import InfoTheory.Core.Entropy
import InfoTheory.Core.Channels
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Error-Correcting Codes, Network Coding, Index Coding, Storage & Sphere Packing

Core definitions for:
- Classical error-correcting codes: `A_q(n, d)`, asymptotic rate `R_q(δ)`, Gilbert-Varshamov bound,
  linear `[n, k, d]_q` codes, MDS conjecture
- List decoding, Locally Decodable Codes (LDCs), Locally Correctable Codes (LCCs)
- Edit/deletion distance codes & trace reconstruction
- Network coding (directed & undirected multiple-unicast Li-Li conjecture)
- Index coding (scalar/vector linear vs nonlinear broadcast rate)
- Private Information Retrieval (PIR), Coded Caching, Regenerating Codes, Batch Codes
- Euclidean kissing number & sphere packing density
-/

open scoped BigOperators

namespace InfoTheory

/-- Hamming distance between two vectors of length `n`. -/
def hammingDistVec {α : Type*} [DecidableEq α] {n : ℕ} (x y : Fin n → α) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => x i ≠ y i)).card

/-- A `(n, M, d)_q` code has `M` codewords of length `n` over `Fin q` with pairwise
    Hamming distance at least `d`. -/
def IsCode (q n d : ℕ) (C : Finset (Fin n → Fin q)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDistVec x y

/-- Maximum cardinality `A_q(n, d)` of a `q`-ary code of length `n` and minimum distance `d`. -/
noncomputable def maxCodeSize (q n d : ℕ) : ℕ :=
  sSup { M : ℕ | ∃ C : Finset (Fin n → Fin q), IsCode q n d C ∧ C.card = M }

/-- Asymptotic maximum rate `R_q(δ) = limsup_{n → ∞} (1/n) log_q A_q(n, ⌈δ n⌉)`. -/
noncomputable def asymptoticCodeRate (q : ℕ) (δ : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
    (Real.log (maxCodeSize q n (Nat.ceil (δ * (n : ℝ))) : ℝ) / Real.log (q : ℝ)) / (n : ℝ) ≤ r }

/-- Binary Gilbert-Varshamov lower bound `1 - h(δ)` for `δ ∈ (0, 1/2)`. -/
noncomputable def gilbertVarshamov (δ : ℝ) : ℝ := 1 - binaryEntropy δ

/-- A linear `[n, k, d]_F` code over a finite field `F` is a `k`-dimensional subspace of `F^n`
    whose nonzero codewords all have Hamming weight at least `d`. -/
def IsLinearMDSCode (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n k : ℕ) : Prop :=
  ∃ (V : Submodule F (Fin n → F)),
    Module.finrank F V = k ∧
    ∀ v ∈ V, v ≠ 0 → n - k + 1 ≤ (Finset.univ.filter (fun i : Fin n => v i ≠ 0)).card

/-- `(p, L)`-list-decodability of a binary code `C ⊆ {0,1}^n`. -/
def IsListDecodable (n : ℕ) (p : ℝ) (L : ℕ) (C : Finset (Fin n → Bool)) : Prop :=
  ∀ y : Fin n → Bool,
    (C.filter (fun c => (hammingDistVec c y : ℝ) ≤ p * (n : ℝ))).card ≤ L

/-- A `q`-query binary Locally Decodable Code (LDC) with message length `k`, blocklength `n`,
    noise tolerance `δ`, and recovery success probability `1/2 + ε`. -/
def IsBinaryLDC (k n q : ℕ) (δ ε : ℝ) : Prop :=
  ∃ (enc : (Fin k → Bool) → (Fin n → Bool))
    (numRand : ℕ) (hR : 0 < numRand)
    (queries : Fin k → Fin numRand → Fin q → Fin n)
    (eval : Fin k → Fin numRand → (Fin q → Bool) → Bool),
    ∀ (x : Fin k → Bool) (y : Fin n → Bool),
      (hammingDistVec (enc x) y : ℝ) ≤ δ * (n : ℝ) →
      ∀ i : Fin k,
        (((Finset.univ.filter (fun r : Fin numRand =>
          eval i r (fun j => y (queries i r j)) = x i)).card : ℝ) / (numRand : ℝ)) ≥ 1 / 2 + ε

/-- A `q`-query binary Locally Correctable Code (LCC) for a linear code `C ⊆ F_2^n`. -/
def IsBinaryLCC (n k q : ℕ) (δ ε : ℝ) : Prop :=
  ∃ (C : Submodule (ZMod 2) (Fin n → ZMod 2)),
    Module.finrank (ZMod 2) C = k ∧
    ∃ (numRand : ℕ) (_ : 0 < numRand)
      (queries : Fin n → Fin numRand → Fin q → Fin n)
      (eval : Fin n → Fin numRand → (Fin q → ZMod 2) → ZMod 2),
      ∀ (c : Fin n → ZMod 2), c ∈ C → ∀ y : Fin n → ZMod 2,
        (hammingDistVec c y : ℝ) ≤ δ * (n : ℝ) →
        ∀ i : Fin n,
          (((Finset.univ.filter (fun r : Fin numRand =>
            eval i r (fun j => y (queries i r j)) = c i)).card : ℝ) / (numRand : ℝ)) ≥ 1 / 2 + ε

/-- Longest common subsequence length between two binary strings. -/
def lcsLength : List Bool → List Bool → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: xs, b :: ys =>
      if a = b then 1 + lcsLength xs ys
      else max (lcsLength xs (b :: ys)) (lcsLength (a :: xs) ys)

/-- Binary deletion distance between equal-length strings `x, y ∈ {0,1}^n`: `n - LCS(x, y)`. -/
def deletionDist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  n - lcsLength (List.ofFn x) (List.ofFn y)

/-- Maximum size of a binary code of length `n` correcting `t` adversarial deletions. -/
noncomputable def maxDeletionCodeSize (n t : ℕ) : ℕ :=
  sSup { M : ℕ | ∃ C : Finset (Fin n → Bool),
    (∀ x ∈ C, ∀ y ∈ C, x ≠ y → t < deletionDist x y) ∧ C.card = M }

/-- Asymptotic maximum rate of binary codes correcting a `δ`-fraction of adversarial deletions. -/
noncomputable def deletionCodeCapacity (δ : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ N : ℕ, ∀ n ≥ N,
    log2 (maxDeletionCodeSize n (Nat.floor (δ * (n : ℝ))) : ℝ) / (n : ℝ) ≤ r }

/-- Trace reconstruction sample complexity `T(n, d)`: minimum number of independent traces from
    `Del_d(x)` needed to distinguish any two strings `x ≠ y ∈ {0,1}^n` with TV distance ≥ 2/3. -/
noncomputable def traceReconWorstCaseSamples (n : ℕ) (d : ℝ) : ℕ :=
  sInf { T : ℕ | 0 < T ∧
    ∀ x y : Fin n → Bool, x ≠ y →
      ∃ (dec : (Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool) → Bool),
        let prob (z : Fin n → Bool) (target : Bool) : ℝ :=
          ∑ tr : Fin T → Σ k : Fin (n + 1), Fin k.1 → Bool,
            if dec tr = target then
              ∏ t : Fin T, deletionProb d (List.ofFn z) (List.ofFn (tr t).2)
            else 0
        prob x true + prob y false ≥ 4 / 3 }

/-! ### Index Coding and Network Coding -/

/-- Side-information graph for an `n`-user index coding instance: vertex `i` knows `x_j` iff
    `sideInfo i j`. Self-loops are forbidden (`irrefl`), since a receiver does not already
    possess the message it is requesting. -/
structure IndexCodingInstance (n : ℕ) where
  sideInfo : Fin n → Fin n → Prop
  irrefl : ∀ i : Fin n, ¬ sideInfo i i

/-- Optimal (possibly nonlinear, vector) broadcast rate `β(G)` of an index coding instance. -/
noncomputable def indexCodingBroadcastRate {n : ℕ} (inst : IndexCodingInstance n) : ℝ :=
  sInf { r : ℝ | ∃ (t M : ℕ), 0 < t ∧ 0 < M ∧
    ∃ (enc : (Fin n → Fin t → Bool) → Fin M)
      (dec : ∀ i : Fin n, Fin M → (Fin n → Fin t → Bool) → (Fin t → Bool)),
      (∀ i m x y, (∀ j, inst.sideInfo i j → x j = y j) → dec i m x = dec i m y) ∧
      (∀ x i, dec i (enc x) x = x i) ∧
      r = log2 (M : ℝ) / (t : ℝ) }

/-- Optimal binary linear scalar/vector index coding rate `β_lin(G)`. -/
noncomputable def linearIndexCodingRate {n : ℕ} (inst : IndexCodingInstance n) : ℝ :=
  sInf { r : ℝ | ∃ (t m : ℕ), 0 < t ∧
    ∃ (enc : (Fin n → Fin t → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
      (dec : ∀ i : Fin n, (Fin m → ZMod 2) → (Fin n → Fin t → ZMod 2) → (Fin t → ZMod 2)),
      (∀ i c x y, (∀ j, inst.sideInfo i j → x j = y j) → dec i c x = dec i c y) ∧
      (∀ x i, dec i (enc x) x = x i) ∧
      r = (m : ℝ) / (t : ℝ) }

/-- An undirected multiple-unicast network instance: undirected graph `G` with integer edge
    capacities and `k` distinct source-sink pairs `(s_i, t_i)` with `s_i ≠ t_i`. -/
structure UndirectedMultipleUnicast (V : Type*) [Fintype V] where
  cap : V → V → ℕ
  symm : ∀ u v, cap u v = cap v u
  numPairs : ℕ
  src : Fin numPairs → V
  dst : Fin numPairs → V
  src_ne_dst : ∀ i, src i ≠ dst i

/-- Multicommodity fractional routing throughput (sum of simultaneously routable unit flows
    with demand `λ` for each `(s_i, t_i)` pair) in an undirected network. -/
noncomputable def undirectedRoutingThroughput {V : Type*} [Fintype V]
    (net : UndirectedMultipleUnicast V) : ℝ :=
  sSup { lam : ℝ | 0 ≤ lam ∧
    ∃ flow : Fin net.numPairs → V → V → ℝ,
      (∀ i u v, 0 ≤ flow i u v) ∧
      (∀ u v, ∑ i : Fin net.numPairs, (flow i u v + flow i v u) ≤ (net.cap u v : ℝ)) ∧
      (∀ i v, v ≠ net.src i → v ≠ net.dst i →
        ∑ u : V, flow i u v = ∑ u : V, flow i v u) ∧
      (∀ i, ∑ u : V, flow i (net.src i) u - ∑ u : V, flow i u (net.src i) = lam) }

/-- Undirected network coding throughput for multiple-unicast sessions:
    a valid `T`-round causal network code of blocklength `N` at equal rate `lam` assigns:
    - per-round directional bit budgets `bits t u v` obeying the **shared undirected edge
      capacity** `∑ t, (bits t u v + bits t v u) ≤ N * net.cap u v` for every unordered edge `{u, v}`
      (with `bits t u u = 0`);
    - strictly **local, causal** edge transmissions `edgeVal msg t u v < 2 ^ (bits t u v)`
      that depend ONLY on the source messages originating at node `u` (`net.src i = u`) and
      the incoming edge symbols received by `u` in strictly earlier rounds `t' < t`;
    - local decoding at each sink `net.dst i` from its own originating source messages and
      all incoming edge symbols received across rounds `0..T-1`. -/
noncomputable def undirectedCodingThroughput {V : Type*} [Fintype V] [DecidableEq V]
    (net : UndirectedMultipleUnicast V) : ℝ :=
  sSup { lam : ℝ | 0 ≤ lam ∧
    ∃ (N T M : ℕ), 0 < N ∧ 0 < T ∧ (M : ℝ) ≥ (2 : ℝ) ^ ((N : ℝ) * lam) ∧
      ∃ (bits : Fin T → V → V → ℕ)
        (edgeVal : (Fin net.numPairs → Fin M) → Fin T → V → V → ℕ),
        -- Shared undirected edge capacity across both directions and all rounds
        (∀ u v, u ≠ v → ∑ t : Fin T, (bits t u v + bits t v u) ≤ N * net.cap u v) ∧
        (∀ t u, bits t u u = 0) ∧
        -- Alphabet size bound on every directed transmission
        (∀ msg t u v, edgeVal msg t u v < 2 ^ (bits t u v)) ∧
        -- Strict node locality & causality: outgoing transmissions from `u` at round `t`
        -- depend only on sources at `u` and incoming transmissions to `u` at rounds `t' < t`
        (∀ msg₁ msg₂ t u,
          (∀ i : Fin net.numPairs, net.src i = u → msg₁ i = msg₂ i) →
          (∀ (t' : Fin T) (w : V), t'.1 < t.1 → edgeVal msg₁ t' w u = edgeVal msg₂ t' w u) →
          ∀ v : V, edgeVal msg₁ t u v = edgeVal msg₂ t u v) ∧
        -- Local zero-error decodability at every sink `net.dst i`
        (∀ i msg₁ msg₂,
          (∀ j : Fin net.numPairs, net.src j = net.dst i → msg₁ j = msg₂ j) →
          (∀ t w, edgeVal msg₁ t w (net.dst i) = edgeVal msg₂ t w (net.dst i)) →
          msg₁ i = msg₂ i) }

/-! ### Euclidean Sphere Packing and Kissing Number -/

/-- Kissing number `τ(d)` in `ℝ^d`: maximum number of unit vectors with pairwise inner product ≤ 1/2. -/
noncomputable def kissingNumber (d : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ pts : Fin m → Fin d → ℝ,
    (∀ i, ∑ r : Fin d, (pts i r) ^ 2 = 1) ∧
    (∀ i j, i ≠ j → ∑ r : Fin d, pts i r * pts j r ≤ 1 / 2) }

end InfoTheory
