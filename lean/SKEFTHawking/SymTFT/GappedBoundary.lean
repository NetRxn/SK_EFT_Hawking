/-
# Phase 6r Wave 1c.2 (also Wave 3a.2) — Gapped boundary conditions

A *gapped boundary condition* of a 3D TQFT bulk is a topological
boundary condition for which the boundary theory is gapped (= has no
massless modes). Per Kapustin-Saulina arXiv:1008.0654 and
Fuchs-Schweigert-Valentino arXiv:1203.4568, gapped boundaries of
Reshetikhin-Turaev TQFTs are in bijection with Lagrangian algebras in
the boundary modular tensor category.

This module ships the **`IsGapped`** and **`HasLagrangianAlgebra`**
predicates at predicate-substrate level, supplying the interface for
Wave 3a.3's SM-matter identification (`IsSMMatterTopologicalBoundary`).

## References

- Kapustin-Saulina, "Topological boundary conditions in abelian
  Chern-Simons theory," Nucl. Phys. B 845 (2011) 393; arXiv:1008.0654.
- Fuchs-Schweigert-Valentino, "Bicategories for boundary conditions
  and for surface defects in 3-d TFT," Commun. Math. Phys. 321 (2013)
  543; arXiv:1203.4568.
- Bhardwaj-Copetti-Pajer-Schäfer-Nameki, "Boundary SymTFT,"
  arXiv:2409.02166, SciPost Phys. 19 (2025) 061.
- Wave 1c.2 `SymTFT/LagrangianAlgebra.lean` — DMNO 2010 anchor.
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.LagrangianAlgebra

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u v₁ u₁ v₂ u₂

/-! ## §1. DELETED post-B4 audit-remediation (2026-05-25)

`IsGapped C := True` deleted as P4 trivial-discharge. No external
consumers. The substantive notion of "gapped boundary" (finite-
dimensionality + no massless modes) requires energy-spectrum
infrastructure absent in Mathlib v4.29.1; until that ships, the
substantive content is carried via `HasLagrangianAlgebra` (per
Kapustin-Saulina 2011 substantive Lagrangian-algebra existence). -/

/-! ## §2. The `HasLagrangianAlgebra` predicate (re-exported from `LagrangianAlgebra`)

**Phase 6r-prime W2.4 substantive ship (2026-05-25)**: `HasLagrangianAlgebra`
moved to `SymTFT/LagrangianAlgebra.lean` to break a circular-import
issue with the W2.4-strengthened `IsKapustinSaulinaGappedBoundary`
(which now references `HasLagrangianAlgebra` substantively). The
substantive body is the existence-of-(braided structure, Lagrangian
algebra) per W2.3/W2.4 strengthening. This file's downstream consumers
get `HasLagrangianAlgebra` via the import of `LagrangianAlgebra`. -/

/-! ## §3. Gapped topological boundaries

A gapped topological boundary of a SymTFT bulk `B` is a topological
boundary `(C, isBdy)` whose underlying fusion category satisfies
`IsGapped` and which admits a Lagrangian-algebra structure.

This is the substrate for Wave 3a.3's `IsSMMatterTopologicalBoundary`
specialization. -/

/-- **`IsGappedTopologicalBoundary B C`** — predicate stating that the
boundary `C` of `B` is gapped (in the topological-boundary sense).

**Phase 6r-prime audit B1 + B4 remediation (2026-05-25)**: prior body
was `IsBulkBoundary B C ∧ HasLagrangianAlgebra B`. Post-B1 (delete
IsBulkBoundary alias for Is3DTQFT), refactored to `Is3DTQFT B ∧
HasLagrangianAlgebra B`. The `C` parameter remains in signature as
documentary data parameter (the underlying boundary fusion category);
the prop content is bulk-only at this level (Kapustin-Saulina 2011
substantive Lagrangian-algebra existence). -/
def IsGappedTopologicalBoundary
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B]
    (_C : Type u₂) [Category.{v₂} _C] [MonoidalCategory _C] : Prop :=
  Is3DTQFT B ∧ HasLagrangianAlgebra B

theorem is3DTQFT_of_isGappedTopologicalBoundary
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
    (h : IsGappedTopologicalBoundary B C) :
    Is3DTQFT B := h.1

theorem hasLagrangianAlgebra_of_isGappedTopologicalBoundary
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
    (h : IsGappedTopologicalBoundary B C) :
    HasLagrangianAlgebra B := h.2

end SKEFTHawking.SymTFT
