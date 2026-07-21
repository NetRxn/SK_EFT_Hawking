/-
# Phase 5q.H — the `b₂` residual as a **mod-2 count**: `|PairH2 / 2·PairH2| = 2¹⁶`

A third equivalent form of the last open input to `kummerK3_b2_target`, and the one a **mod-2**
computation can hit directly (this substrate's relative homology is mod-2-native).

The two banked facts do all the work:

* `KummerPairTubeSeparation.pairCoker_card` — `|PairH2 / im pairProj| = 2¹⁶` (the Euler-number pin);
* `KummerPairTubeSeparation.two_smul_mem_range_pairProj` — `2·PairH2 ⊆ im pairProj`;
* `KummerPairHalving.pairH2TwoTorsionFree_iff_range_eq_doubles` —
  the residual holds **iff** `im pairProj = 2·PairH2`.

Since `2·PairH2 ⊆ im pairProj` always, the quotient `PairH2 / 2·PairH2` always **surjects onto**
`PairH2 / im pairProj`, whose order is exactly `2¹⁶`. So the residual — equality of the two
submodules — is equivalent to the two quotients having the same order:

`pairH2TwoTorsionFree_iff_card_doubles : PairH2TwoTorsionFree ↔ Nat.card (PairH2 ⧸ 2·PairH2) = 2¹⁶`

with `2¹⁶ = 65536` (`card_doubles_pin`). A **falsifiable numeric** target: any extra `ℤ/2` summand in
`PairH2` doubles the count. And by the Bockstein/coefficient sequence `PairH2 / 2·PairH2` is the
`ℤ/2` relative group `H₂(eImage, collar; ℤ/2)` — i.e. this reduction says the `b₂` headline needs
only **`dim_{𝔽₂} H₂(E, ∂E; ℤ/2) = 1` per resolution piece**, a computation with no orientation, no
sign and no generator identification in it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerPieceCollarCyclicInt

open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerPairTubeSeparation
  (PairH2 PairH2TwoTorsionFree pairProj pairCoker_card two_smul_mem_range_pairProj)

namespace SKEFTHawking.KummerPieceCollarModTwoInt

noncomputable section

/-- The doubles submodule `2·PairH2`. -/
def pairDoubles : Submodule ℤ PairH2 :=
  LinearMap.range ((2 : ℤ) • LinearMap.id : PairH2 →ₗ[ℤ] PairH2)

/-- **The doubles always sit inside the free sublattice** (`two_smul_mem_range_pairProj`); the
residual is exactly the assertion that they fill it. -/
theorem pairDoubles_le_range : pairDoubles ≤ LinearMap.range pairProj := by
  rintro x ⟨y, rfl⟩
  exact two_smul_mem_range_pairProj y

/-- The comparison map `PairH2 / 2·PairH2 ↠ PairH2 / im pairProj`. -/
def compareQuot : (PairH2 ⧸ pairDoubles) →ₗ[ℤ] (PairH2 ⧸ LinearMap.range pairProj) :=
  Submodule.mapQ pairDoubles (LinearMap.range pairProj) LinearMap.id
    (by intro x hx; exact pairDoubles_le_range hx)

theorem compareQuot_mk (x : PairH2) :
    compareQuot (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

theorem compareQuot_surjective : Function.Surjective compareQuot := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- **The `b₂` residual as a mod-2 count.** `2·PairH2 ⊆ im pairProj` always, and the bigger quotient
has order `2¹⁶` (`pairCoker_card`), so the two submodules agree — which is the residual
(`pairH2TwoTorsionFree_iff_range_eq_doubles`) — exactly when the smaller quotient also has order
`2¹⁶`. -/
theorem pairH2TwoTorsionFree_iff_card_doubles :
    PairH2TwoTorsionFree ↔ Nat.card (PairH2 ⧸ pairDoubles) = 2 ^ 16 := by
  constructor
  · intro h
    have hrange : LinearMap.range pairProj = pairDoubles :=
      SKEFTHawking.KummerPairHalving.pairH2TwoTorsionFree_iff_range_eq_doubles.mp h
    rw [← hrange]
    exact pairCoker_card
  · intro hcard
    refine SKEFTHawking.KummerPairHalving.pairH2TwoTorsionFree_iff_range_eq_doubles.mpr ?_
    refine le_antisymm ?_ pairDoubles_le_range
    -- `compareQuot` is a surjection between finite modules of equal order, hence injective.
    haveI : Finite (PairH2 ⧸ pairDoubles) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    haveI : Fintype (PairH2 ⧸ pairDoubles) := Fintype.ofFinite _
    haveI : Fintype (PairH2 ⧸ LinearMap.range pairProj) := Fintype.ofFinite _
    have hc1 : Fintype.card (PairH2 ⧸ pairDoubles) = 2 ^ 16 := by
      rw [← Nat.card_eq_fintype_card]; exact hcard
    have hc2 : Fintype.card (PairH2 ⧸ LinearMap.range pairProj) = 2 ^ 16 := by
      rw [← Nat.card_eq_fintype_card]; exact pairCoker_card
    have hbij : Function.Bijective compareQuot :=
      (Fintype.bijective_iff_surjective_and_card _).mpr ⟨compareQuot_surjective, by
        rw [hc1, hc2]⟩
    intro x hx
    have h0 : compareQuot (Submodule.Quotient.mk x) = 0 := by
      rw [compareQuot_mk]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hx
    have h1 : (Submodule.Quotient.mk x : PairH2 ⧸ pairDoubles) = 0 :=
      hbij.1 (by rw [h0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).mp h1

/-- **Falsifiable numeric pin** — the target order is `65536`, not any other power of two. An extra
`ℤ/2` in any one of the sixteen per-piece groups would make it `2¹⁷ = 131072`. -/
theorem card_doubles_pin (h : PairH2TwoTorsionFree) : Nat.card (PairH2 ⧸ pairDoubles) = 65536 := by
  rw [pairH2TwoTorsionFree_iff_card_doubles.mp h]; norm_num

/-! ## §2. Descending the count to ONE resolution piece -/

section PerPiece

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerPieceCollarInt (outerE pairH2SplitOuter)

local notation "OuterH2" => RelHomologyInt (X := ResEtop) outerE 2

/-- The doubles submodule `2·H₂(E, {fiberNorm ≥ 1/2}; ℤ)` of the single per-piece group. -/
def outerDoubles : Submodule ℤ OuterH2 :=
  LinearMap.range ((2 : ℤ) • LinearMap.id : OuterH2 →ₗ[ℤ] OuterH2)

/-- The doubles submodule of the sixteen-fold product. -/
def piDoubles : Submodule ℤ (EIndex → OuterH2) :=
  LinearMap.range ((2 : ℤ) • LinearMap.id : (EIndex → OuterH2) →ₗ[ℤ] (EIndex → OuterH2))

theorem map_pairDoubles : Submodule.map pairH2SplitOuter.toLinearMap pairDoubles = piDoubles := by
  ext f
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    exact ⟨pairH2SplitOuter y, by simp⟩
  · rintro ⟨g, rfl⟩
    refine ⟨pairH2SplitOuter.symm ((2 : ℤ) • g), ⟨pairH2SplitOuter.symm g, ?_⟩, ?_⟩
    · show (2 : ℤ) • pairH2SplitOuter.symm g = pairH2SplitOuter.symm ((2 : ℤ) • g)
      rw [map_smul]
    · show pairH2SplitOuter (pairH2SplitOuter.symm ((2 : ℤ) • g)) = (2 : ℤ) • g
      rw [LinearEquiv.apply_symm_apply]

/-- Componentwise reduction `(EIndex → M) → (EIndex → M/2M)`. -/
def piRed : (EIndex → OuterH2) →ₗ[ℤ] (EIndex → OuterH2 ⧸ outerDoubles) :=
  LinearMap.pi fun i => outerDoubles.mkQ.comp (LinearMap.proj i)

theorem piRed_surjective : Function.Surjective piRed := by
  intro q
  choose g hg using fun i => Submodule.Quotient.mk_surjective outerDoubles (q i)
  exact ⟨g, funext fun i => hg i⟩

theorem ker_piRed : LinearMap.ker piRed = piDoubles := by
  ext f
  constructor
  · intro hf
    have hmem : ∀ i, f i ∈ outerDoubles := by
      intro i
      have : (outerDoubles.mkQ) (f i) = 0 := congrFun hf i
      exact (Submodule.Quotient.mk_eq_zero _).mp this
    choose g hg using fun i => hmem i
    refine ⟨fun i => g i, ?_⟩
    funext i
    show (2 : ℤ) • g i = f i
    exact hg i
  · rintro ⟨g, rfl⟩
    funext i
    show (outerDoubles.mkQ) ((2 : ℤ) • g i) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨g i, rfl⟩

/-- **The sixteen-fold count**: `|PairH2 / 2·PairH2| = |M / 2M|¹⁶` for the single per-piece group
`M = H₂(E, {fiberNorm ≥ 1/2}; ℤ)`. -/
theorem card_pairDoubles_eq_pow :
    Nat.card (PairH2 ⧸ pairDoubles) = (Nat.card (OuterH2 ⧸ outerDoubles)) ^ 16 := by
  have e1 : (PairH2 ⧸ pairDoubles) ≃ₗ[ℤ] ((EIndex → OuterH2) ⧸ piDoubles) :=
    Submodule.Quotient.equiv pairDoubles piDoubles pairH2SplitOuter map_pairDoubles
  have e2 : ((EIndex → OuterH2) ⧸ piDoubles) ≃ₗ[ℤ] (EIndex → OuterH2 ⧸ outerDoubles) :=
    (Submodule.quotEquivOfEq _ _ ker_piRed.symm).trans
      (piRed.quotKerEquivOfSurjective piRed_surjective)
  rw [Nat.card_congr (e1.trans e2).toEquiv, Nat.card_pi, Finset.prod_const, Finset.card_univ,
    SKEFTHawking.KummerWeld.eIndex_card]

/-- **The `b₂` residual as a count on ONE resolution piece**:
`H₂(K3;ℤ) ≅ ℤ²²` holds iff `H₂(E, {fiberNorm ≥ 1/2}; ℤ) / 2·(same)` has exactly **two** elements —
i.e. iff `dim_{𝔽₂}` of the mod-2 relative group of the single `𝒪(−2)` model pair is `1`. A genuine
`↔`: nothing is lost relative to `PairH2TwoTorsionFree`. -/
theorem pairH2TwoTorsionFree_iff_card_outerDoubles :
    PairH2TwoTorsionFree ↔ Nat.card (OuterH2 ⧸ outerDoubles) = 2 := by
  rw [pairH2TwoTorsionFree_iff_card_doubles, card_pairDoubles_eq_pow]
  constructor
  · intro h
    exact Nat.pow_left_injective (by norm_num) h
  · intro h; rw [h]

/-- **The headline consumer, per-piece mod-2 form.** -/
theorem kummerK3_b2_target_of_card_outerDoubles
    (h : Nat.card (OuterH2 ⧸ outerDoubles) = 2) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  SKEFTHawking.KummerPairHalving.kummerK3_b2_target_of_exceptional_halvable
    (SKEFTHawking.KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable.mp
      (pairH2TwoTorsionFree_iff_card_outerDoubles.mpr h))

end PerPiece

/-- **The headline consumer, mod-2 form** — a single count closes `H₂(K3;ℤ) ≅ ℤ²²`. -/
theorem kummerK3_b2_target_of_card_doubles (h : Nat.card (PairH2 ⧸ pairDoubles) = 2 ^ 16) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  SKEFTHawking.KummerPairHalving.kummerK3_b2_target_of_exceptional_halvable
    (SKEFTHawking.KummerPairHalving.pairH2TwoTorsionFree_iff_exceptional_halvable.mp
      (pairH2TwoTorsionFree_iff_card_doubles.mpr h))

end

end SKEFTHawking.KummerPieceCollarModTwoInt
