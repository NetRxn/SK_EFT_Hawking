/-
# Phase 6r Wave 1c.3 — Toric-code Lagrangian-algebra witness

The canonical concrete example of the bulk-boundary correspondence at
the SymTFT level. Per Wave 1a.1 §5.3 and Wave 3a.1 §Q7, this is the
*natural concrete substantive witness* of the Phase 6r framework — to
our knowledge, after surveying Mathlib, Lean physlib, Coq UniMath,
Isabelle AFP, and Agda 1Lab/agda-categories as of May 2026, the
explicit Lean-formal realization of the Lagrangian-algebra / gapped-
boundary correspondence for the toric code is new (the underlying
physics is the textbook Kitaev-Kong / Bombin et al. result).

## Content

For the toric-code SymTFT bulk `Center (Discrete (ZMod 2))` =
`Z(Vec_{Z_2})`, there are exactly **two Lagrangian algebras** up to
equivalence:

- **`lagrangian_electric`** = `𝟙 ⊕ e` — the "electric" Lagrangian
  algebra, condensing the `e` anyon. Its corresponding gapped boundary
  is the rough/smooth electric boundary of the toric code.

- **`lagrangian_magnetic`** = `𝟙 ⊕ m` — the "magnetic" Lagrangian
  algebra, condensing the `m` anyon. Its corresponding gapped boundary
  is the dual magnetic boundary.

The two Lagrangian algebras correspond, under the DMNO 2010 bulk-boundary
bijection (`SymTFT/LagrangianAlgebra.lean`), to the two Morita-
inequivalent gapped boundary conditions of the toric-code TQFT
(Kitaev-Kong arXiv:1104.5047).

## Implementation discipline

The toric-code Lagrangian-algebra content sits at predicate-substrate
level for now: the existence of the two algebras is captured as a
tracked Prop `IsToricCodeTwoLagrangianAlgebraStructure`, with the
A-class published content (Kitaev-Kong 2012, Bombin-Martín-Delgado 2009)
cited explicitly. The full Frobenius-algebra construction of `𝟙 ⊕ e`
and `𝟙 ⊕ m` in `Center (Discrete (ZMod 2))` requires direct-sum
structure on `Center C` that Mathlib does not currently ship at the
right typeclass level, so we ship the predicate-level cross-bridge.

## References

- Kitaev-Kong, "Models for gapped boundaries and domain walls,"
  Commun. Math. Phys. 313 (2012) 351; arXiv:1104.5047.
- Bombin-Martín-Delgado, "Family of non-Abelian Kitaev models on a
  lattice: Topological condensation and confinement," Phys. Rev. B 78
  (2008) 115421; arXiv:0803.5046.
- Kong, "Anyon condensation and tensor categories," Nucl. Phys. B 886
  (2014) 436; arXiv:1307.8244.
- Bhardwaj-Copetti-Pajer-Schäfer-Nameki, "Boundary SymTFT,"
  arXiv:2409.02166, SciPost Phys. 19 (2025) 061.
- Wave 1c.2 `SymTFT/LagrangianAlgebra.lean`, `SymTFT/GappedBoundary.lean`.
- Wave 1b.3 `SymTFT/BulkInstances.lean` (`toricCodeBulk`).
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.DrinfeldCenterAsBulk
import SKEFTHawking.SymTFT.BulkInstances
import SKEFTHawking.SymTFT.LagrangianAlgebra
import SKEFTHawking.SymTFT.GappedBoundary
import SKEFTHawking.SymTFT.ToricCodeLagrangianAnyons
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.Data.ZMod.Basic

namespace SKEFTHawking.SymTFT

open CategoryTheory

universe v u

/-! ## §1. Toric-code labels for electric vs magnetic Lagrangian algebras

**Phase 6r-prime C1 substantive ship (2026-05-25)**: moved before
`IsToricCodeTwoLagrangianAlgebraStructure` so the strengthened
3-conjunct body can reference `ToricCodeLagrangianLabel`. -/

/-- Label tagging Lagrangian algebras of the toric code as electric or
magnetic. Per Bhardwaj-Copetti-Pajer-Schäfer-Nameki §Q3(b), these
labels are the load-bearing data for the SM-vs-dark-sector alternative
boundary classification in Wave 3b.1. -/
inductive ToricCodeLagrangianLabel
  /-- `𝟙 ⊕ e` — the electric Lagrangian algebra (condenses `e`). -/
  | electric : ToricCodeLagrangianLabel
  /-- `𝟙 ⊕ m` — the magnetic Lagrangian algebra (condenses `m`). -/
  | magnetic : ToricCodeLagrangianLabel
  deriving DecidableEq, Repr

/-- The two labels are distinct (no electric algebra is magnetic and
vice versa). This is the categorical reflection of the toric-code's
electric-magnetic duality being a *non-trivial* automorphism of the
Lagrangian-algebra set. -/
theorem toricCode_labels_distinct :
    ToricCodeLagrangianLabel.electric ≠ ToricCodeLagrangianLabel.magnetic := by
  decide

/-! ## §2. The toric-code two-Lagrangian-algebra tracked Prop -/

/-- **`IsToricCodeTwoLagrangianAlgebraStructure`** — tracked Prop:
the toric-code SymTFT bulk `Center (Discrete (ZMod 2))` admits exactly
two Lagrangian algebras (up to equivalence), the electric `𝟙 ⊕ e` and
the magnetic `𝟙 ⊕ m`.

Per Kitaev-Kong arXiv:1104.5047, these are the two gapped boundary
conditions of the toric code; per Bombin-Martín-Delgado arXiv:0803.5046,
they correspond to condensing the electric vs magnetic anyon.

**Phase 6r-prime C1.3 substantive ship (2026-05-25)**: predicate body
strengthened from the prior predicate-substrate marker to substantively
reference the C1.1+C1.2 content (`SymTFT/ToricCodeLagrangianAnyons.lean`):
- IsBoundarySymTFTCorrespondence on the bulk
- Existence of TWO distinct Lagrangian-algebra anyon sets in the toric
  code MTC (per Kitaev-Kong arXiv:1104.5047 Theorem 5.4)
- Both satisfying the Kitaev-Kong criterion (closed under fusion + trivial
  mutual braiding + correct dimension)
- The classification: every Lagrangian-algebra anyon set in toric code
  is one of the two

**Adversarial-review history**:
- v1: extended predicate body with `(electric ≠ magnetic)` conjunct —
  adversarial review correctly flagged this as P5 structural-tautology
  (the 2-constructor inductive's distinctness is `decide`-able from
  the definition alone, adding zero substantive content).
- v2 (predicate-substrate marker): reverted body to bulk-correspondence
  only, deferred substantive content to future sub-wave.
- **v3 (this version, 2026-05-25)**: substantively strengthened body
  using the C1.1+C1.2 Finset-level Lagrangian-anyon-set content. The
  existential `∃ L₁ L₂ : Finset ToricAnyon, IsLagrangianAnyonSet L₁ ∧
  IsLagrangianAnyonSet L₂ ∧ L₁ ≠ L₂ ∧ classification` is NOT decide-
  able alone — it requires the C1.1+C1.2 substantive proofs that
  the Kitaev-Kong axioms hold on the electric/magnetic sets and that
  no other Finset of anyons satisfies the criterion (this is the
  Bombin-Martín-Delgado / Kitaev-Kong "exactly two gapped boundaries"
  classification).

**Honest scope distinction**: this ships substantive C1 content at
the *anyon-set level* via the Kitaev-Kong criterion. The concrete-
object construction of `lagrangian_electric = 𝟙 ⊕ e` as a
`MonObj`/`ComonObj`/`IsCommFrobeniusAlgebra` instance in `Center
(Discrete (ZMod 2))` (requiring direct-sum structure on Drinfeld
centers absent from Mathlib v4.29.1 at the right typeclass level)
remains for Phase 7+ Mathlib upstream. The two distinct anyon sets
correspond bijectively to the two gapped boundary conditions per
Kitaev-Kong 2012 Theorem 5.4 — substantively sound for the SymTFT-
boundary classification. -/
def IsToricCodeTwoLagrangianAlgebraStructure : Prop :=
  Is3DTQFT toricCodeBulk ∧
  ∃ L₁ L₂ : Finset ToricAnyon,
    IsLagrangianAnyonSet L₁ ∧ IsLagrangianAnyonSet L₂ ∧ L₁ ≠ L₂ ∧
    (∀ S : Finset ToricAnyon, IsLagrangianAnyonSet S → S = L₁ ∨ S = L₂)

/-! ## §3. The toric-code bulk is a 3D TQFT

**Phase 6r-prime A2 audit-remediation (2026-05-25)**: replaced
`IsBoundarySymTFTCorrespondence toricCodeBulk` (P5 alias for `Is3DTQFT`
per audit) with `Is3DTQFT toricCodeBulk` directly. -/

/-- The toric-code bulk satisfies `Is3DTQFT` by construction. -/
theorem toricCodeBulk_is3DTQFT_anchor :
    Is3DTQFT toricCodeBulk :=
  toricCodeBulk_is3DTQFT

/-- **C1.3 substantive discharge** (2026-05-25, A2-remediated): the
toric-code bulk has the two-Lagrangian-algebra structure, substantively
witnessed by the C1.1+C1.2 content. The existential is discharged using
`lagrangianElectricSet` and `lagrangianMagneticSet` from
`SymTFT/ToricCodeLagrangianAnyons.lean`; the universal classification
uses `isLagrangianAnyonSet_classification`. -/
theorem toricCodeBulk_isToricCodeTwoLagrangianAlgebraStructure :
    IsToricCodeTwoLagrangianAlgebraStructure :=
  ⟨toricCodeBulk_is3DTQFT_anchor,
   lagrangianElectricSet, lagrangianMagneticSet,
   isLagrangianAnyonSet_electric,
   isLagrangianAnyonSet_magnetic,
   lagrangianElectricSet_ne_magneticSet,
   isLagrangianAnyonSet_classification⟩

end SKEFTHawking.SymTFT
