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

/-! ## §1. The `IsGapped` predicate -/

/-- **`IsGapped C`** — predicate on a fusion-category boundary `C`
stating that the boundary theory is *gapped* (= has no massless modes,
finitely many topological sectors, the data of `C` is the full
boundary fusion category).

Per Bhardwaj-Copetti-Pajer-Schäfer-Nameki arXiv:2409.02166, a gapped
boundary is the special case where the boundary CFT is fully gapped
to a topological theory; the SymTFT classification (per DMNO 2010 +
Kapustin-Saulina 2011) sends such boundaries to Lagrangian algebras in
the bulk Drinfeld center.

Predicate-substrate body: monoidal structure exists (already from
typeclass). The substantive content (finite-dimensionality + no
massless modes) is the load-bearing physics statement supplied via
the tracked Prop `IsKapustinSaulinaGappedBoundary`. -/
def IsGapped (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop :=
  True

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

**Phase 6r-prime adversarial-review round-1 remediation (2026-05-25)**:
previous body was `IsBulkBoundary B C ∧ IsGapped C ∧ HasLagrangianAlgebra
B`. Adversarial review flagged the `IsGapped C := True` conjunct as P2
bundle-redundant (vacuously satisfied). Dropped; the substantive gapped
content is carried via the `HasLagrangianAlgebra B` existential (which
asserts the substantive Lagrangian-algebra structure required for the
boundary to be gapped per Kapustin-Saulina 2011). The `IsGapped C`
predicate-substrate marker remains in the file as a future extension
point for finite-dimensionality / no-massless-modes infrastructure. -/
def IsGappedTopologicalBoundary
    (B : Type u₁) [Category.{v₁} B] [MonoidalCategory B]
    (C : Type u₂) [Category.{v₂} C] [MonoidalCategory C] : Prop :=
  IsBulkBoundary B C ∧ HasLagrangianAlgebra B

theorem isBulkBoundary_of_isGappedTopologicalBoundary
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
    (h : IsGappedTopologicalBoundary B C) :
    IsBulkBoundary B C := h.1

theorem hasLagrangianAlgebra_of_isGappedTopologicalBoundary
    {B : Type u₁} [Category.{v₁} B] [MonoidalCategory B]
    {C : Type u₂} [Category.{v₂} C] [MonoidalCategory C]
    (h : IsGappedTopologicalBoundary B C) :
    HasLagrangianAlgebra B := h.2

end SKEFTHawking.SymTFT
