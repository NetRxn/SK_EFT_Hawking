/-
# Phase 6r Wave 1b.1 — Bulk SymTFT data: 3D TQFT predicate refinements

This module refines the FMT-wrapper `Is3DTQFT` predicate from
`SymTFT/Basic.lean` with the load-bearing bulk-side data:

1. **Braided closure** — `Is3DTQFT B` *is* the braided-category data
   on `B`; we ship sugar/aliases for the substantive consumer pattern.

2. **Modular (strong-form) bulk** — `IsModularBulk B` strengthens
   `Is3DTQFT` with non-degeneracy at the predicate-substrate level
   (interface to the modular tensor category encoding; the substantive
   non-degeneracy condition is recorded as a tracked Prop because
   Mathlib does not yet ship a `ModularTensorCategory` typeclass).

Per Wave 1a.1 §1.3 + Wave 3a.1 §Q7, Mathlib provides `Center` (Drinfeld
center) and its `BraidedCategory` instance (`braidedCategoryCenter` at
`Mathlib.CategoryTheory.Monoidal.Center.lean:347`), but no
`ModularTensorCategory` typeclass exists in Mathlib4 v4.29.1; this
module sits at the predicate-substrate level for the modular refinement.

## References

- Reshetikhin-Turaev, "Ribbon graphs and their invariants derived from
  quantum groups," Commun. Math. Phys. 127 (1990) 1-26.
- Mathlib4 `Mathlib.CategoryTheory.Monoidal.Center` (provides
  `BraidedCategory (Center C)` via `braidedCategoryCenter` instance).
- Wave 1a.3 `SymTFT/Basic.lean`.
-/
import SKEFTHawking.SymTFT.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u

/-! ## §1. Braided form of `Is3DTQFT` -/

/-- **`Is3DTQFTBraided B`** — synonym for `Is3DTQFT B`, exposing the
explicit braided-monoidal interpretation. -/
def Is3DTQFTBraided (B : Type u) [Category.{v} B] [MonoidalCategory B] : Prop :=
  Is3DTQFT B

theorem Is3DTQFT_iff_braided
    (B : Type u) [Category.{v} B] [MonoidalCategory B] :
    Is3DTQFT B ↔ Is3DTQFTBraided B := Iff.rfl

/-! ## §2. DELETED post-B10/B11 audit-remediation (2026-05-25)

`IsNonDegBraidedFusion B := Is3DTQFTBraided B` and
`IsModularBulk B := Is3DTQFT B` both deleted as P5 aliases. The
auxiliary theorems `isModularBulk_of_is3DTQFTBraided`,
`is3DTQFTBraided_of_isModularBulk`, and `isNonDegBraidedFusion_from_hyp`
(itself an identity extractor) are also deleted.

No external consumers (verified via grep). The substantive Modular
Tensor Category / S-matrix-non-degeneracy content lives at the
multi-session Mathlib MTC infrastructure level (genuinely deferred per
>20k LoC threshold for full MTC theory) and at the project's existing
`SymTFTAudit/PseudoUnitary.lean` substantive predicate. Consumers
needing modularity should:
- Use `Is3DTQFTBraided B` if the substantive content is braiding.
- Use `Is3DTQFT B` if the substantive content is bulk-TQFT shape.
- Cite `SymTFTAudit/PseudoUnitary.lean` for strict-pseudo-unitary
  refinements.

Per Davydov-Müger-Nikshych-Ostrik arXiv:1009.2117 + Reshetikhin-Turaev
1991, the substantive modularity/non-degeneracy content is real
mathematics; we just don't have it formalized at predicate-substrate
level yet. The aliases were not adding content. -/

end SKEFTHawking.SymTFT
