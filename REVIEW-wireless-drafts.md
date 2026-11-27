# Expert review: 3 drafted Gaussian/wireless problems (+ the Marton decision)

All three entries are built on the validated Gaussian framework (`Core/GaussianOperational.lean`):
measurable decoders by construction, error probability as a measure, and ⌊2^{nR}⌋ codes. The framework's
operational AWGN capacity is now proved equal to ½log₂(1+P/N) (`Known/GaussianAchievability`).
Each entry has a frozen Lean `Statement` and a proved certificate; everything builds, and the
audit shows standard axioms only. **Nothing is locked into `main` until you approve.** For each
entry: approve, edit (say how), or drop.

---

## 1. `amplitude-constrained-awgn-support`: monotonicity of the optimal support size (Sharma–Shamai 2010)

- **Status:**
  - Smith 1971: the optimal input under |X| ≤ A is unique, discrete and finitely supported.
  - K(A) = O(A²) (Dytso–Yagli–Poor–Shamai, IT 2020).
  - **The linear-growth conjecture K(A) = Θ(A) was disproved:** K(A) = Ω(A√log A)
    (Wang–Barletta–Dytso, arXiv:2512.22691).
  - Barletta–Dytso (arXiv:2609.10039, Sept 2026) show the support grows locally by one point at the
    origin, and state that **global monotonicity "remains open"**.
- **Statement:** with C(A,N) the operational peak-constrained capacity and C_k(A,N) the same with symbols
  restricted to some ≤ k-point constellation in [−A,A]:
  `∀ N A A' k, 0<N → 0<A → A ≤ A' → 1 ≤ k → C_k(A',N) = C(A',N) → C_k(A,N) = C(A,N)`.
  So "k points suffice at A' ⇒ k points suffice at A", i.e. K is nondecreasing.
- **Certificate:**
  - both sSups are genuine;
  - C_k ≤ C_{k'} ≤ C for k ≤ k', and C ≤ ½log₂(1+A²/N), via the AWGN converse;
  - BPSK gives 0 < 1−h(Q(A/√N)) ≤ C₂.
- **⚠ Decide:** the equivalence "C_k = C ⟺ K ≤ k" relies on Smith's theorem and the finite-input coding
  theorem, neither of which is formalized. It is explained in the `.md`, but the frozen statement is
  operational. Is the operational form acceptable?

## 2. `gaussian-bc-feedback-sum-capacity`: symmetric two-receiver Gaussian BC with perfect feedback

- **Status:** Belhadj Amor–Steinberg–Wigger (IT 2015, arXiv:1404.2584) list as open whether control-theoretic
  (linear-feedback) schemes achieve the sum-capacity of symmetric BCs. They show these schemes are optimal
  among linear-feedback schemes. Background: Ozarow–Leung 1984, Elia 2004, Ardestanizadeh–Minero–Franceschetti
  2012, Gastpar–Lapidoth–Steinberg–Wigger 2014.
- **Statement:** `∀ h P, h ≠ 0 → 0 < P → bcFbSumCapacity h h P = ofReal (linearFbSumRate h h P)`.
  The left side is the operational feedback sum-capacity: causal measurable encoders, expected block power,
  and an ℝ≥0∞ sSup. The right side is the ASW Cor. 2 linear-feedback sum-rate.
- **Certificate:**
  - the causal output recursion is well posed and measurable;
  - single-user rates ½log₂(1+h²P) are achievable on both sides;
  - the formula's set is bounded.
  - **Not certified:** an operational upper bound (needs a feedback converse).
- **⚠ Decide:** expected vs almost-sure power. Expected power follows the literature;
  Schalkwijk–Kailath-type schemes violate an almost-sure constraint.

## 3. `gaussian-mac-feedback-linear-optimality`: is linear feedback optimal for the symmetric K-user Gaussian MAC, K ≥ 3?

- **Status:**
  - Ozarow 1984 solved K = 2.
  - Ardestanizadeh–Wigger–Kim–Javidi (IT 2012) give the linear-feedback sum-capacity.
  - Sula–Gastpar–Kramer (IT 2020) prove that Fourier-MEC achieves the symmetric sum-capacity. They leave open
    whether it achieves all points of the capacity region.
- **Statement:**
  `∀ K P N, 3 ≤ K → 0 < P → 0 < N → closure (macFbRegion K P N) = closure (macLinearFbRegion K P N)`.
  Linear codes are as in AWKJ Def. 1.
- **Certificate:**
  - the recursion is well posed;
  - linear region ⊆ feedback region;
  - single-user axis segments are in both.
  - **Not certified:** boundedness of the feedback region (needs a feedback converse).
- **⚠ Decide:** this asks feedback = linear feedback for equal powers. It is weaker than Sula–Gastpar–Kramer's
  Fourier-MEC question, and no published formula exists for the K ≥ 3 region. Acceptable? The `.md`
  also says the cut-set bound isn't tight for K ≥ 3 at low SNR; that is the agent's reading of AWKJ Cor. 1,
  so please confirm.

## Candidates rejected

- **Noncoherent Rayleigh fading:** discreteness of the optimal input is already proved. The crisp remaining
  question (are two mass points optimal at small SNR?) is contested in the literature, and the model would
  need a new converse.
- **Exact DoF of the K-user interference channel:** no conjectured value exists for any specific matrix,
  so any statement would mean inventing a constant.

---

## Marton (decision still pending)

arXiv:2608.19869 (Huang–Liu–Liu, Aug 2026; not peer-reviewed) claims Marton's inner bound (with W) is
strictly suboptimal. The method is a computer-assisted two-letter vs one-letter gap on a ternary-input
channel. The non-numerical parts were checked by Nair and Gohari per the acknowledgments, and re-derived by
our reviewer. The numerical certificates have not been independently checked.

Proposed handling:
- `marton-inner-bound-tightness`: status stays `open`, with a "claimed resolved (negative), unverified" note.
- `broadcast-channel`: correct the line saying Marton isn't known to be suboptimal.
- BSSC: unaffected (binary input).
- 3-receiver broadcast: optional one-line note.

Alternative: a new `claimed-resolved` status with its own site badge.

---

## Independent agent review (2026-11-27)

The reviewer was an independent agent working read-only, with web literature checks:
- **#1 amplitude-constrained-awgn-support: APPROVE.** arXiv:2609.10039 says "global
  monotonicity of K(A) remains open". The operational encoding is sound: the converse holds
  uniformly over k-point constellations, the k-point maximum is attained by compactness, and
  Smith's uniqueness gives C_k < C when K > k. Nit applied: Sharma–Shamai conjecture "at most
  one point per transition".
- **#2 gaussian-bc-feedback-sum-capacity: APPROVE.** The formula matches ASW eqs. (26)–(28),
  (42)–(43) and Cor. 3 (46). Expected power matches ASW eq. (8). Edit applied: verbatim quote of
  the open question.
- **#3 gaussian-mac-feedback-linear-optimality: APPROVE after edit.** The cut-set claim is
  correct, but the attribution was wrong. Edit applied: it now cites Sula–Gastpar–Kramer 2020
  ("cut-set bounds are loose for J > 2") and Kramer's SNR threshold 2^{K+1}/K², replacing the
  AWKJ Cor. 1 "reading".
- **Marton:** keep `open` with a "claimed resolved (negative), unverified" note.
  arXiv:2608.19869 is still v1, with no rebuttal or confirmation as of Nov 2026.

**Still needed:** the user's expert sign-off, which flips `review: pending-expert`.
