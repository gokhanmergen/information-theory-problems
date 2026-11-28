import InfoTheory.External.GeneralCKStatement
import InfoTheory.External.CourtadeKumar

/-!
# External formal results

Bridges from formal proofs developed outside this repository to the catalog's frozen
`Statement`s. Each file copies the external target proposition verbatim (with its provenance:
upstream repository, commit and checksum) and proves that it implies the frozen statement here.
The external theorem itself is trusted through its own repository's kernel check; it is not
replayed here, typically because of a Lean toolchain mismatch.

* `External/CourtadeKumar.lean`: `GeneralCK.GeneralCourtadeKumar → CourtadeKumar.Statement`
  (dpwoodru/general-courtade-kumar-lean; Chen–Gohari–Javanmard–Lin–Mirrokni–Nair–Woodruff,
  arXiv:2609.24931).
-/
