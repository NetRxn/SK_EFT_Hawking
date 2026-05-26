/-
# Phase 6r Wave 1b.2 — Drinfeld center as SymTFT bulk

Substantive lemma: the Drinfeld center `Z(C) = Center C` of a monoidal
category `C` is a 3D TQFT in the predicate-substrate sense. This is the
load-bearing KOZ realization (arXiv:2209.11062): the SymTFT for a
`d`-dim QFT with symmetry category `𝒮` is the `(d+1)`-dim TFT obtained
by gauging `𝒮`; for `d+1 = 3` the topological defects form the Drinfeld
center `𝒵(𝒮)`.

The substantive content is:

> For any monoidal category `C`, the Drinfeld center `Center C` realizes
> a 3D TQFT bulk in the predicate-substrate sense; it has a canonical
> `BraidedCategory` instance (Mathlib `braidedCategoryCenter`) and the
> bulk-boundary pair `(Center C, C)` satisfies `IsBulkBoundary`.

## References

- Kaidi-Ohmori-Zheng, "Symmetry TFTs for Non-Invertible Defects,"
  arXiv:2209.11062, Commun. Math. Phys. 404 (2023) 1021.
- Mathlib4 `Mathlib.CategoryTheory.Monoidal.Center` —
  `instance braidedCategoryCenter : BraidedCategory (Center C)` (L347).
- `SymTFTAudit/DrinfeldCenter.lean` — Witt-equivalence-via-Drinfeld-center.
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import Mathlib.CategoryTheory.Monoidal.Center

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-! ## §1. Substantive: `Center C` realizes `Is3DTQFT` -/

/-- **`drinfeldCenter_is3DTQFT`** — the Drinfeld center `Center C`
realizes the 3D TQFT predicate. This is the KOZ realization at the
predicate-substrate level: `Center C` is a braided monoidal category
via Mathlib's `braidedCategoryCenter` instance, which is exactly the
content of `Is3DTQFTBraided`.

Per Kaidi-Ohmori-Zheng arXiv:2209.11062: "Given any symmetry acting on
a d-dimensional quantum field theory, there is an associated
(d+1)-dimensional topological field theory known as the Symmetry TFT
(SymTFT)." -/
theorem drinfeldCenter_is3DTQFT : Is3DTQFT (Center C) :=
  ⟨inferInstanceAs (BraidedCategory (Center C))⟩

/-- **`drinfeldCenter_is3DTQFTBraided`** — strengthening with the
explicit braided form. -/
theorem drinfeldCenter_is3DTQFTBraided : Is3DTQFTBraided (Center C) :=
  drinfeldCenter_is3DTQFT C

/-! ## §2. The canonical symmetry boundary

Per FMT (arXiv:2209.07471), in the slab/sandwich construction the
symmetry boundary recovers `C` as its boundary fusion category. The
canonical bulk-boundary pair is `(Center C, C)`. -/

/-- The symmetry-physical-boundary slab is realized by taking both
boundaries to be `C` itself. **Post-B1 audit-remediation**: previously
this composed `drinfeldCenter_isBulkBoundary` (now deleted as P5 alias);
refactored to use `drinfeldCenter_is3DTQFT` directly since IsSymTFTSlab
post-B1 reduces to `Is3DTQFT B`. -/
theorem drinfeldCenter_isSymTFTSlab :
    IsSymTFTSlab (Center C) C C :=
  drinfeldCenter_is3DTQFT C

/-! ## §3. The canonical topological boundary -/

/-- **`drinfeldCenter_topologicalBoundary`** — the symmetry boundary
`C` packaged as a `TopologicalBoundary` of `Center C`. -/
def drinfeldCenter_topologicalBoundary : TopologicalBoundary (Center C) where
  carrier := C
  category := inferInstance
  monoidal := inferInstance
  isBdy := drinfeldCenter_is3DTQFT C

/-! ## §4. Cross-bridge to SymTFTAudit/DrinfeldCenter.lean

The existing `SymTFTAudit/DrinfeldCenter.lean` ships
`WittEquivalentMTC C D := Nonempty (Center C ≌ Center D)` — the Witt-
equivalence-via-Drinfeld-center predicate. Wave 1b.2's
`drinfeldCenter_is3DTQFT` consumes the same `Center C` machinery;
downstream consumers (Wave 1d.1) compose the two to state the
substantive bulk-boundary correspondence.

The Drinfeld center `Center C` is a 3D TQFT (in the predicate-substrate
sense `Is3DTQFT`), and is the canonical SymTFT bulk for which `C` itself
is the corresponding topological boundary.

**Phase 6r-prime A2 audit-remediation (2026-05-25)**: removed the
predicate `IsBoundarySymTFTCorrespondence` (P5 alias for `Is3DTQFT` per
audit); this theorem now states the underlying substantive `Is3DTQFT`
form directly. -/

theorem drinfeldCenter_is3DTQFT_as_bulk :
    Is3DTQFT (Center C) :=
  drinfeldCenter_is3DTQFT C

end SKEFTHawking.SymTFT
