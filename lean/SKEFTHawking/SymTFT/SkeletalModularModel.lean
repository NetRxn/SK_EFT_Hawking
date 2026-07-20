/-
# SymTFT S0/S1 — honest finite skeletal modular model + model-tied Lagrangian boundary support

This module opens the SymTFT semantic-strengthening lane (Fable-Targets packet
`temporary/working-docs/brainstorm/Fable-Targets/SymTFT/`). It ships the **honest
v2 statement layer** (S0 freeze) and the **first finite-model bricks** (S1) for
the toric-code condensable-boundary classification pilot, *beside* the legacy
Phase-6r façade (`SymTFT/Basic.lean`, `LagrangianAlgebra.lean`, `GappedBoundary.lean`)
— no legacy predicate is modified in place (packet §3.1 "versioned API first").

## The defect this repairs

The legacy `IsLagrangianAlgebraFPdimRefined L globalFPdimSquared`
(`SymTFT/LagrangianAlgebra.lean`) carries the global dimension as a **free
per-use parameter**, unrelated to the ambient model — the packet's kill
criterion "global dimension remains an arbitrary per-use argument"
(`SYMTFT_SEMANTIC_STRENGTHENING_ROADMAP.md` §7). Here the global FPdim² is
**derived model data**: `SkeletalModularModel.globalFPdimSquared` is *defined*
as `∑_{a simple} FPdim(a)²`, and the boundary datum's Lagrangian-dimension law
reads it from the model, so it cannot be supplied as an unrelated number.

## What is honest here

- `SkeletalModularModel` — an object-free (skeletal) finite abelian modular
  model: finite simple labels, an FPdim weight, a unital fusion, a mutual
  monodromy phase, with the FPdim axioms. Packet §2.1 "a concrete/skeletal
  carrier ... FPdim on simples/objects ... global dimension derived from the
  simple family". Instantiated concretely by `toricSkeletalModel` from the
  existing `ToricCodeCenter` substrate — the carrier is **non-vacuous**.
- `LagrangianSupport M` — the finite condensable-boundary datum: a fusion-closed,
  braiding-trivial, unit-containing set of simples whose FPdim² **equals the
  model's derived global dimension** (packet §2.1: the FPdim equality is
  mandatory and tied to the model, not passed at each use). The boundary carrier
  appears in *laws* (`fusion_closed`, `braiding_trivial`, `fpdim_lagrangian`),
  not as an unused parameter (repairing the `IsGappedTopologicalBoundary B C`
  defect where `C` is ignored).

## The falsifiers (both conditions load-bearing)

- `no_unitOnly_lagrangianSupport` — the vacuum-only "boundary" is **excluded**
  because its FPdim² = 1 ≠ 4 = global (the decisive unit falsifier; packet §1.5,
  §2.3 falsifier 1 — the regression test that the legacy weak predicate FAILS
  since `A5LagrangianCenterUnit` makes the unit weakly Lagrangian).
- `fermion_passes_fpdim_but_no_lagrangianSupport` — the `{1, ε}` candidate
  **passes** the FPdim condition (`fermionSet_passes_fpdim_lagrangian`) but is
  excluded by braiding-triviality (monodromy `ε,ε` = −1). Shows FPdim alone is
  insufficient; the braiding condition is independently load-bearing (packet
  §2.3 falsifier 2, and the `FrobeniusPerronDim.lean` note that the FPdim
  condition alone does not characterize Lagrangian algebras).
- `unit_not_isLagrangianAlgebraFPdimRefined` — the generic object-level negative:
  in *any* braided FPdim bulk of global dimension ≠ 1, the tensor unit fails the
  legacy FPdim-refined predicate (packet §1.5 "a new negative theorem for any
  bulk with global dimension not equal to 1").

## Non-vacuity + first classification

`toricElectricSupport`, `toricMagneticSupport` are honest `LagrangianSupport`
**terms** (not tracked Props). `toric_lagrangianSupport_classification` bridges
the honest FPdim-tied datum to the existing exhaustive anyon-set theorem
(`ToricCodeLagrangianAnyons.isLagrangianAnyonSet_classification`): the FPdim law
forces `card = 2`, then the two-element classification applies — every Lagrangian
support of the toric model is electric or magnetic.

## Scope boundary (packet §1 non-goals)

This is the finite pilot at the **support / skeletal** level. It does NOT ship a
functorial TQFT, a general fusion/modular tensor library, a general DMNO proof,
an object-level Frobenius-algebra construction (S2), or any Pin⁺/`ZMod 16` or
SM-boundary bridge. The object-level electric algebra (`A5VacuumPlusElectric`
componentwise multiplication) is a separate later milestone.

## References

- Kitaev-Kong, "Models for gapped boundaries and domain walls," Commun. Math.
  Phys. 313 (2012) 351; arXiv:1104.5047 (§3, Theorem 5.4).
- Davydov-Müger-Nikshych-Ostrik, J. Reine Angew. Math. 677 (2013) 135;
  arXiv:1009.2117 (Lagrangian algebra: FPdim(L)² = FPdim(B)).
- Substrate: `SKEFTHawking.ToricCodeCenter`, `SymTFT.FrobeniusPerronDim`,
  `SymTFT.ToricCodeLagrangianAnyons`, `SymTFT.LagrangianAlgebra`.
-/
import Mathlib
import SKEFTHawking.ToricCodeCenter
import SKEFTHawking.SymTFT.FrobeniusPerronDim
import SKEFTHawking.SymTFT.ToricCodeLagrangianAnyons
import SKEFTHawking.SymTFT.LagrangianAlgebra

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory
open SKEFTHawking

universe v u

/-! ## §1. The finite skeletal modular model (S0 carrier) -/

/-- **`SkeletalModularModel`** — an object-free finite abelian modular model:
a finite family of simple `Label`s, an FPdim weight `fpdim`, a unital `fusion`,
and a mutual `monodromy` phase, satisfying the FPdim unit/multiplicativity
axioms. This is the packet §2.1 "concrete/skeletal carrier" — the finite
truth-serum for the toric-boundary pilot, avoiding the Mathlib gap of a
category-level `FrobeniusPerronDim` instance while keeping FPdim tied to the
simple family. -/
structure SkeletalModularModel where
  /-- The finite type of simple-object labels. -/
  Label : Type
  [fintypeLabel : Fintype Label]
  [decEqLabel : DecidableEq Label]
  /-- The distinguished unit (vacuum) label. -/
  unit : Label
  /-- The Frobenius-Perron dimension weight on simples. -/
  fpdim : Label → NNReal
  /-- The (abelian) fusion operation on simples. -/
  fusion : Label → Label → Label
  /-- The mutual monodromy/braiding phase (abelian: a sign in `ℤ`). -/
  monodromy : Label → Label → ℤ
  /-- The unit is a left fusion identity. -/
  fusion_unit_left : ∀ a, fusion unit a = a
  /-- The unit is a right fusion identity. -/
  fusion_unit_right : ∀ a, fusion a unit = a
  /-- FPdim unit normalization. -/
  fpdim_unit : fpdim unit = 1
  /-- FPdim is multiplicative under fusion. -/
  fpdim_fusion : ∀ a b, fpdim (fusion a b) = fpdim a * fpdim b

attribute [instance] SkeletalModularModel.fintypeLabel SkeletalModularModel.decEqLabel

/-- **`SkeletalModularModel.globalFPdimSquared`** — the model's global FPdim²,
**derived** as the sum of squared FPdim weights over all simples (not a free
parameter). This is the packet §S0-task-5 "global dimension as derived model
data" and the antidote to the legacy free-`globalFPdimSquared` defect. -/
def SkeletalModularModel.globalFPdimSquared (M : SkeletalModularModel) : NNReal :=
  ∑ a : M.Label, M.fpdim a ^ 2

/-! ## §2. The model-tied Lagrangian boundary support (S0 boundary datum) -/

/-- **`LagrangianSupport M`** — the finite condensable-boundary datum on a
skeletal modular model `M`: a set of simples that contains the unit, is closed
under fusion, has trivial mutual monodromy, and whose FPdim² **equals the
model's derived global FPdim²**. The boundary carrier appears in the three laws
(not as an unused parameter), and the Lagrangian-dimension law reads the model's
own `globalFPdimSquared` — repairing both the unused-`C` defect of
`IsGappedTopologicalBoundary` and the free-`globalFPdimSquared` defect of
`IsLagrangianAlgebraFPdimRefined`. -/
structure LagrangianSupport (M : SkeletalModularModel) where
  /-- The set of condensed/boundary simples. -/
  carrier : Finset M.Label
  /-- The boundary contains the unit (the algebra has a unit object). -/
  unit_mem : M.unit ∈ carrier
  /-- The boundary is closed under bulk fusion (a law relating carrier to bulk). -/
  fusion_closed : ∀ a ∈ carrier, ∀ b ∈ carrier, M.fusion a b ∈ carrier
  /-- The boundary is mutually transparent (Müger-center condensability). -/
  braiding_trivial : ∀ a ∈ carrier, ∀ b ∈ carrier, M.monodromy a b = 1
  /-- The Lagrangian dimension law, tied to the MODEL's derived global FPdim²:
  `FPdim(L)² = FPdim(B)` in the DMNO/Kitaev-Kong sense. -/
  fpdim_lagrangian : (∑ a ∈ carrier, M.fpdim a) ^ 2 = M.globalFPdimSquared

/-! ## §3. The toric skeletal model (non-vacuity of the carrier) -/

/-- **`toricSkeletalModel`** — the concrete toric-code (`Z(Vec_{ℤ/2})`) instance
of `SkeletalModularModel`, built from the existing `ToricCodeCenter` +
`FrobeniusPerronDim` substrate. Demonstrates the carrier is non-vacuous. -/
def toricSkeletalModel : SkeletalModularModel where
  Label := ToricAnyon
  unit := ToricAnyon.vacuum
  fpdim := toricFPdim
  fusion := toricFusion
  monodromy := braidingPhase
  fusion_unit_left := fusion_vacuum_left
  fusion_unit_right := fusion_vacuum_right
  fpdim_unit := rfl
  fpdim_fusion := toricFPdim_fusion

/-- The toric model's derived global FPdim² is 4 — reusing the existing
`toricGlobalFPdimSquared_eq_sum` (`Σ FPdim² = 4`). The global dimension is
genuinely model-derived, not asserted. -/
theorem toricSkeletalModel_globalFPdimSquared_eq_four :
    toricSkeletalModel.globalFPdimSquared = 4 := by
  show (∑ a : ToricAnyon, toricFPdim a ^ 2) = 4
  exact toricGlobalFPdimSquared_eq_sum.symm

/-! ## §4. Positive fixtures — electric and magnetic boundary presentations -/

/-- **`toricElectricSupport`** — the electric condensable boundary `{1, e}` as an
honest `LagrangianSupport` **term** (not a tracked Prop). Reuses the proven
Kitaev-Kong witness for the fusion/braiding laws; the FPdim law is the new
model-tied content: `(1 + 1)² = 4 = globalFPdimSquared`. -/
def toricElectricSupport : LagrangianSupport toricSkeletalModel where
  carrier := lagrangianElectricSet
  unit_mem := isLagrangianAnyonSet_electric.vacuum_mem
  fusion_closed := isLagrangianAnyonSet_electric.fusion_closed
  braiding_trivial := isLagrangianAnyonSet_electric.braiding_trivial
  fpdim_lagrangian := by
    rw [toricSkeletalModel_globalFPdimSquared_eq_four]
    show (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.electric} : Finset ToricAnyon),
        toricFPdim a) ^ 2 = 4
    rw [Finset.sum_pair (by decide : ToricAnyon.vacuum ≠ ToricAnyon.electric)]
    show ((1 : NNReal) + 1) ^ 2 = 4
    norm_num

/-- **`toricMagneticSupport`** — the magnetic condensable boundary `{1, m}` as an
honest `LagrangianSupport` term. Symmetric to electric. -/
def toricMagneticSupport : LagrangianSupport toricSkeletalModel where
  carrier := lagrangianMagneticSet
  unit_mem := isLagrangianAnyonSet_magnetic.vacuum_mem
  fusion_closed := isLagrangianAnyonSet_magnetic.fusion_closed
  braiding_trivial := isLagrangianAnyonSet_magnetic.braiding_trivial
  fpdim_lagrangian := by
    rw [toricSkeletalModel_globalFPdimSquared_eq_four]
    show (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.magnetic} : Finset ToricAnyon),
        toricFPdim a) ^ 2 = 4
    rw [Finset.sum_pair (by decide : ToricAnyon.vacuum ≠ ToricAnyon.magnetic)]
    show ((1 : NNReal) + 1) ^ 2 = 4
    norm_num

/-! ## §5. Falsifier 1 — the unit-only boundary fails the FPdim law (decisive) -/

/-- The vacuum-only set fails the model-tied FPdim-Lagrangian law: `FPdim(1)² = 1
≠ 4`. This is the decisive regression test — the legacy weak predicate makes the
unit *weakly* Lagrangian (`A5LagrangianCenterUnit`), but the honest FPdim law
excludes it. -/
theorem unitOnly_fails_fpdim_lagrangian :
    (∑ a ∈ ({ToricAnyon.vacuum} : Finset ToricAnyon), toricSkeletalModel.fpdim a) ^ 2
      ≠ toricSkeletalModel.globalFPdimSquared := by
  rw [toricSkeletalModel_globalFPdimSquared_eq_four, Finset.sum_singleton]
  show (toricFPdim ToricAnyon.vacuum) ^ 2 ≠ 4
  rw [toricFPdim_eq_one]
  norm_num

/-- **Falsifier 1 (consumed)**: no `LagrangianSupport` of the toric model has the
unit-only carrier. The honest condensable-boundary datum excludes the trivial
boundary — the FPdim falsifier is genuinely load-bearing on the structure. -/
theorem no_unitOnly_lagrangianSupport (L : LagrangianSupport toricSkeletalModel) :
    L.carrier ≠ ({ToricAnyon.vacuum} : Finset ToricAnyon) := by
  intro hc
  apply unitOnly_fails_fpdim_lagrangian
  rw [← hc]
  exact L.fpdim_lagrangian

/-! ## §6. Falsifier 2 — the fermion boundary passes FPdim but fails braiding -/

/-- The `{1, ε}` candidate **passes** the model-tied FPdim law: `(1 + 1)² = 4`.
Shows the FPdim condition alone does not exclude the fermion. -/
theorem fermionSet_passes_fpdim_lagrangian :
    (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.fermion} : Finset ToricAnyon),
        toricSkeletalModel.fpdim a) ^ 2 = toricSkeletalModel.globalFPdimSquared := by
  rw [toricSkeletalModel_globalFPdimSquared_eq_four]
  show (∑ a ∈ ({ToricAnyon.vacuum, ToricAnyon.fermion} : Finset ToricAnyon),
      toricFPdim a) ^ 2 = 4
  rw [Finset.sum_pair (by decide : ToricAnyon.vacuum ≠ ToricAnyon.fermion)]
  show ((1 : NNReal) + 1) ^ 2 = 4
  norm_num

/-- **Falsifier 2 (consumed)**: despite passing FPdim, the fermion boundary is
excluded by braiding-triviality (`monodromy ε ε = −1 ≠ 1`). The braiding
condition is independently load-bearing — FPdim alone does not characterize
condensable boundaries. -/
theorem fermion_passes_fpdim_but_no_lagrangianSupport
    (L : LagrangianSupport toricSkeletalModel) :
    L.carrier ≠ ({ToricAnyon.vacuum, ToricAnyon.fermion} : Finset ToricAnyon) := by
  intro hc
  have hmem : ToricAnyon.fermion ∈ L.carrier := by rw [hc]; decide
  have hbraid : braidingPhase ToricAnyon.fermion ToricAnyon.fermion = 1 :=
    L.braiding_trivial _ hmem _ hmem
  rw [fermion_self_braiding] at hbraid
  exact absurd hbraid (by decide)

/-! ## §7. Generic object-level unit falsifier (packet §1.5) -/

/-- **`unit_not_isLagrangianAlgebraFPdimRefined`** — the generic negative: in
*any* braided FPdim bulk of global dimension ≠ 1, the tensor unit fails the
legacy `IsLagrangianAlgebraFPdimRefined` predicate, because `FPdim(1)² = 1`. This
is the packet §1.5 ask ("a new negative theorem for any bulk with global
dimension not equal to 1"), strengthening `A5LagrangianCenterUnit`'s weak
positive result at the FPdim-refined level. -/
theorem unit_not_isLagrangianAlgebraFPdimRefined
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
    [FrobeniusPerronDim C] [MonObj (𝟙_ C)] [ComonObj (𝟙_ C)]
    {g : NNReal} (hg : g ≠ 1) :
    ¬ IsLagrangianAlgebraFPdimRefined (𝟙_ C) g := by
  rintro ⟨_, hdim⟩
  rw [FrobeniusPerronDim.fpdim_unit, one_pow] at hdim
  exact hg hdim.symm

/-! ## §8. First classification — the honest support recovers electric/magnetic -/

/-- **`toric_lagrangianSupport_classification`** — every Lagrangian support of the
toric model is electric or magnetic. Bridges the honest FPdim-tied datum to the
existing exhaustive anyon-set theorem: the FPdim law forces `card = 2` (all toric
FPdims are 1), then `isLagrangianAnyonSet_classification` applies. This is the
S4-preview: the honest support classification lifts to exactly the two known
condensable boundaries. -/
theorem toric_lagrangianSupport_classification (L : LagrangianSupport toricSkeletalModel) :
    L.carrier = lagrangianElectricSet ∨ L.carrier = lagrangianMagneticSet := by
  apply isLagrangianAnyonSet_classification
  refine ⟨L.unit_mem, L.fusion_closed, L.braiding_trivial, ?_⟩
  -- card = 2 from the FPdim law: Σ_{a∈carrier} 1 = card, (card)² = 4 ⇒ card = 2
  have hsum : (∑ a ∈ L.carrier, toricSkeletalModel.fpdim a) = (L.carrier.card : NNReal) := by
    simp [toricSkeletalModel, toricFPdim]
  have hfp : ((L.carrier.card : NNReal)) ^ 2 = 4 := by
    rw [← hsum, ← toricSkeletalModel_globalFPdimSquared_eq_four]
    exact L.fpdim_lagrangian
  have hnat : L.carrier.card ^ 2 = 4 := by
    have hcast : ((L.carrier.card ^ 2 : ℕ) : NNReal) = ((4 : ℕ) : NNReal) := by
      push_cast
      rw [hfp]
    exact_mod_cast hcast
  have hmul : L.carrier.card * L.carrier.card = 4 := by rw [← pow_two]; exact hnat
  rcases Nat.lt_trichotomy L.carrier.card 2 with h | h | h
  · exfalso; nlinarith [hmul, h]
  · exact h
  · exfalso; nlinarith [hmul, h]

/-! ## §9. Pilot closure — non-vacuity + both falsifiers + classification -/

/-- **Toric boundary pilot closure** — the coherent S0/S1 deliverable:
(a) the honest boundary datum is non-vacuous (electric term exists);
(b) the unit-only boundary is excluded (FPdim falsifier load-bearing);
(c) the fermion boundary is excluded (braiding falsifier load-bearing);
(d) every honest boundary support is electric or magnetic (classification). -/
theorem toric_boundary_pilot_closure :
    Nonempty (LagrangianSupport toricSkeletalModel) ∧
    (∀ L : LagrangianSupport toricSkeletalModel,
      L.carrier ≠ ({ToricAnyon.vacuum} : Finset ToricAnyon)) ∧
    (∀ L : LagrangianSupport toricSkeletalModel,
      L.carrier ≠ ({ToricAnyon.vacuum, ToricAnyon.fermion} : Finset ToricAnyon)) ∧
    (∀ L : LagrangianSupport toricSkeletalModel,
      L.carrier = lagrangianElectricSet ∨ L.carrier = lagrangianMagneticSet) :=
  ⟨⟨toricElectricSupport⟩, no_unitOnly_lagrangianSupport,
   fermion_passes_fpdim_but_no_lagrangianSupport, toric_lagrangianSupport_classification⟩

end SKEFTHawking.SymTFT
