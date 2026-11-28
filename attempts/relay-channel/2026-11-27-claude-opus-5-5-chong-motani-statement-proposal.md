---
problem: relay-channel
date: 2026-11-27
attempter: claude-opus-5-5
model: claude-opus-5-5
type: survey
status: unverified
---

## Summary

This is a proposed statement fix. It has **not** been applied: the frozen Statement on `main`
is unchanged. Two independent repairs of the relay-channel catalog error
(`2026-11-26-claude-opus-5-5-thm7-transcription-catalog-error.md`, verified) were written on
2026-11-27:

- **Repair A (applied, commit 49c683f).** Freezes the three-constraint Cover–El Gamal
  Theorem 7 rate.
- **Repair B (this proposal).** Freezes the larger Chong–Motani (2011) Theorem 2 rate, in
  El Gamal–Gohari–Nair form (7).

Both repairs fix the error. B is recorded here so that a reviewer or expert can choose between
them. The ready-to-apply Lean files and problem file are in `code/chong-motani-proposal/`.

## Approach

The two candidate Statements carry different risks.

- `relayCapacity W = coverElGamalTheorem7Rate W` (Repair A) is refuted by any finite channel on
  which some achievable rate strictly beats Theorem 7. Chong and Motani conjectured, from Gaussian
  numerics, that their Theorem 2 does exactly that. A proof of their conjecture would therefore
  refute A by comparing two achievable rates, without saying anything about capacity.
- `relayCapacity W = chongMotaniRate W` (Repair B) is refuted only by a scheme that beats the
  best known single-letter rate, or settled by a matching converse.

A statement that a routine comparison of known schemes can refute is a weaker catalog entry. That
is the case for B. Against it: Theorem 7 is the classical, widely quoted benchmark, and B's
formula is less familiar.

## Claims

1. **[proved]** (Lean, `code/chong-motani-proposal/Certificates_RelayChannel.lean`) The proposed
   right-hand side `chongMotaniRate W` is well posed: its defining set is nonempty and bounded
   above. It satisfies `0 ≤ chongMotaniRate W ≤ log2 |Y|`. The proof uses only `propext`,
   `Classical.choice` and `Quot.sound`.
2. **[sketch]** Form (7) equals Chong–Motani Theorem 2.
   - Theorem 2 → (7): put $S=(W,Q)$, $U'=(U,W,Q)$.
   - (7) → Theorem 2: put $Q=\emptyset$, $W=S$, $U'=(U,S)$.
   - Each conditional mutual information is unchanged, because $(X,Y,Y_r,V)$ is independent of
     $W$ given $(U,Q,X_r)$. The exception is $I(X,X_r;Y\mid Q)$, which becomes $I(X,X_r;Y)$ and
     can only increase. The third constraint is rewritten using
     $V-(S,U,X_r,Y_r)-(X,Y)$.
3. **[proved]** (by reference) $R_{\rm CM}\ge R_{\rm Thm7}$ for every channel (Chong–Motani 2011,
   Remark 6). Equality holds for channels with orthogonal receiver components (El Gamal–Gohari–Nair,
   Theorem 3).
4. **[sketch]** On the catalog-error channel $W_\star$, $R_{\rm CM}(W_\star)=3/2=C(W_\star)$. The
   point with $S,U$ constant, $X_1,X_2,X_r$ i.i.d. uniform and $V=Y_r$ gives
   $(c_1,c_2,c_3)=(1.5,2,1.5)$, and $C(W_\star)=3/2$ is proved in the catalog-error attempt. The
   former coherent point, with $X_r=S$, gives $\min=h(1/3)\approx0.918$, because $c_3$ binds.
5. **[heuristic]** Two numerical checks, whose scripts are **not** in the repository (they were
   scratch scripts of the proposing agent and were not kept):
   - an SLSQP search on $W_\star$ over $|S|,|U|,|V|\le3$ peaked at $1.5$;
   - over 3000 random channel/law pairs, the functional never exceeded the cutset value by more
     than $2\cdot10^{-15}$.

   Treat both as unreproduced.
6. **[heuristic]** The proposed Statement is open. See the literature check in Details.

## Details

**Proposed formal Statement.** For every finite DM relay channel,
$C = R_{\rm CM} = \sup \min\{c_1,c_2,c_3\}$, where
$$
\begin{aligned}
c_1 &= I(X, X_r; Y) - I(Y_r; V \mid S, U, X, X_r, Y),\\
c_2 &= I(X; V, Y \mid S, U, X_r) + I(U; Y_r \mid S, X_r),\\
c_3 &= I(X; Y \mid S, U, X_r) + I(U; Y_r \mid S, X_r) + I(X_r; Y \mid S, U)
       - I(Y_r; V \mid S, U, X, X_r, Y).
\end{aligned}
$$
The supremum is over finite $S,U,V$ and laws
$p(s,u)\,p(x\mid s,u)\,p(x_r\mid s)\,p(y,y_r\mid x,x_r)\,p(v\mid s,u,x_r,y_r)$. The Lean
definitions are `chongMotaniJoint` and `chongMotaniRate` in
`code/chong-motani-proposal/Problems_RelayChannel.lean`. The operational side `relayCapacity`, the
alphabets and the quantifiers are the same as on `main`.

**Literature check behind Claim 6 (2026-11-27).**

- Every channel class with known capacity reaches capacity inside Theorem 7, and hence inside
  $R_{\rm CM}$. The classes are: degraded (including Sato's channel), reversely degraded,
  semideterministic, orthogonal sender components, the Cover–Kim deterministic class, relay with
  feedback, and the Aleksic–Razaghi–Yu modulo-sum class (reached by quantize-forward).
- No scheme is known to beat $R_{\rm CM}$ on a standard finite DM relay channel. Each scheme claimed
  to improve on Theorem 7 is subsumed, comes without a strict example, or uses a different model:
  - Mondelli–Hassani–Urbanke 2019 is subsumed (El Gamal–Gohari–Nair, Lemma 1).
  - El Gamal–Gohari–Nair's time-sharing gain lies inside Theorem 7.
  - Lee–Chung NNC-PDF (arXiv:1505.05435) reduces to Theorem 7 for three nodes.
  - Noisy network coding equals compress-forward for one relay.
  - Kang–Ulukus (arXiv:0710.0900) gives no strict example.
  - Wu (arXiv:1504.04515) and Gabbai–Bross use relay-to-source feedback or an enhanced channel.
  - Relay-without-delay is a different model.
  - Ponniah (arXiv:2609.15709) is refuted (catalog-error attempt; Shiu arXiv:2609.18727).

**How to apply Repair B.** This needs a separate statement-fix commit.

1. Replace `lean/InfoTheory/Problems/RelayChannel.lean` with
   `code/chong-motani-proposal/Problems_RelayChannel.lean`.
2. Replace the certificate with `Certificates_RelayChannel.lean`, but **keep `main`'s
   `relayCapacity_le_cutset` and `condMutualInfo_le_log2_card`**. The proposal was written before
   those lemmas existed and does not contain them. Optionally keep Repair A's
   `coverElGamalTheorem7Rate` with its bounds as a non-Statement definition, to compare it with
   $R_{\rm CM}$.
3. Port `code/chong-motani-proposal/relay-channel.md.proposed` into `problems/relay-channel.md`. It
   was written against the pre-49c683f file, so merge it by hand.
4. Regenerate `lean/STATEMENT_LOCK.json` and run the full checks: build, AuditKnown, leanchecker,
   and `verify_proof.py --check-lock --check-catalog --self-test`.

## Verification

- 2026-11-27 (claude-opus-5-5): in a scratch worktree of `main` at 36fb580, both proposal Lean files
  replaced the live ones. `lake build InfoTheory.Known.Certificates.RelayChannel` succeeded.
  `#print axioms` on `chongMotaniRate_wellPosed`, `chongMotaniRate_nonneg` and
  `chongMotaniRate_le_log2_card` reports only `propext`, `Classical.choice` and `Quot.sound`.
- Not done: AuditKnown and leanchecker. The files are not in the Lean source tree and are not
  built by CI, so they can drift as Core changes.
- Repair A (on `main`) was independently reviewed on 2026-11-27 and found to be a faithful
  transcription of Theorem 7. Nobody has independently reviewed Repair B.

## Dead ends

None.

## References

- Prior attempt: `2026-11-26-claude-opus-5-5-thm7-transcription-catalog-error.md`.
- T. M. Cover and A. El Gamal, "Capacity theorems for the relay channel," IEEE Trans. Inf. Theory
  25(5), 1979 (Theorem 7).
- H.-F. Chong and M. Motani, "On achievable rates for the general relay channel," IEEE Trans. Inf.
  Theory 57(3), 2011 (Lemma 2, Theorem 2, Remark 6).
- A. El Gamal, A. Gohari, and C. Nair, "Achievable rates for the relay channel with orthogonal
  receiver components" (form (7), Theorem 3, Lemma 1).
- Further references: `code/chong-motani-proposal/relay-channel.md.proposed`.
