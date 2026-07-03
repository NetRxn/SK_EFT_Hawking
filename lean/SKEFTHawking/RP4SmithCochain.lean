import Mathlib
import SKEFTHawking.RP4Transfer
import SKEFTHawking.SingularCohomologyFunctoriality

/-!
# Phase 5q.G (B-arc, M3-a) — the cochain-level Smith transfer of the antipodal cover

The cochain dual of the M2 transfer: `τ^# : Cⁿ(S⁴) → Cⁿ(ℝP⁴)`, `(τ^#y)(σ) = y(σ₊) + y(σ₋)`
(sum over the two lifts). Together with the pullback `π^# = cochainPullback mkC` this opens the
**cohomological** Smith sequence, whose connecting map is the cup-ladder generator of
`H^*(ℝP⁴; ℤ/2)` (M3-c..i). The `δ`-commutation dualizes the M2-c face-pair combinatorics
(`face_pair_sum`): the faces of the two lifts are the two lifts of the faces, as a set.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Covering SKEFTHawking.RP4Transfer
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.RP4SmithCochain

/-! ## §1. The cochain transfer and its `δ`-commutation -/

/-- **The cochain transfer** `τ^# : Cⁿ(S⁴) → Cⁿ(ℝP⁴)` — evaluate on both lifts and add. -/
noncomputable def cochainTransfer (n : ℕ) :
    SingularCochain (TopCat.of S4) n →ₗ[ZMod 2] SingularCochain (TopCat.of RP4) n where
  toFun y := fun σ => y (liftPlus σ) + y (liftMinus σ)
  map_add' y z := by
    funext σ
    show (y + z) (liftPlus σ) + (y + z) (liftMinus σ) = _
    simp only [Pi.add_apply]
    abel
  map_smul' c y := by
    funext σ
    show (c • y) (liftPlus σ) + (c • y) (liftMinus σ) = _
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem cochainTransfer_apply {n : ℕ} (y : SingularCochain (TopCat.of S4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    cochainTransfer n y σ = y (liftPlus σ) + y (liftMinus σ) := rfl

/-- **The face-pair value identity** — the cochain shadow of `face_pair_sum`: evaluating any
cochain on the two faces-of-lifts equals evaluating it on the two lifts-of-faces. -/
theorem face_pair_value {n : ℕ} (y : SingularCochain (TopCat.of S4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk (n + 1))))
    (i : Fin (n + 2)) :
    y (face i (liftPlus σ)) + y (face i (liftMinus σ))
      = y (liftPlus (face i σ)) + y (liftMinus (face i σ)) := by
  have h := congrArg (Finsupp.linearCombination (ZMod 2) y) (face_pair_sum σ i)
  simpa only [map_add, Finsupp.linearCombination_single, one_smul] using h

/-- **The transfer is a cochain map**: `δ(τ^#y) = τ^#(δy)` — per-face, via `face_pair_value`. -/
theorem coboundary_cochainTransfer {n : ℕ} (y : SingularCochain (TopCat.of S4) n) :
    coboundary (TopCat.of RP4) n (cochainTransfer n y)
      = cochainTransfer (n + 1) (coboundary (TopCat.of S4) n y) := by
  funext σ
  show ∑ i : Fin (n + 2), (y (liftPlus (face i σ)) + y (liftMinus (face i σ)))
    = (∑ i : Fin (n + 2), y (face i (liftPlus σ)))
      + ∑ i : Fin (n + 2), y (face i (liftMinus σ))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (face_pair_value y σ i).symm)

/-- The transfer of a cocycle is a cocycle. -/
theorem cochainTransfer_mem_ker {n : ℕ} (y : LinearMap.ker (coboundaryₗ (TopCat.of S4) n)) :
    cochainTransfer n y.1 ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) n) := by
  rw [LinearMap.mem_ker]
  show coboundary (TopCat.of RP4) n (cochainTransfer n y.1) = 0
  rw [coboundary_cochainTransfer,
    show coboundary (TopCat.of S4) n y.1 = coboundaryₗ (TopCat.of S4) n y.1 from rfl,
    LinearMap.mem_ker.mp y.2, map_zero]

/-- **The cohomology transfer** `τ^* : Hⁿ(S⁴) → Hⁿ(ℝP⁴)` — the descended cochain transfer
(mirrors `cohomologyPullback`'s descent shape). -/
noncomputable def cohomologyTransfer (n : ℕ) :
    Cohomology (TopCat.of S4) n →ₗ[ZMod 2] Cohomology (TopCat.of RP4) n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cochainTransfer n).domRestrict (LinearMap.ker (coboundaryₗ (TopCat.of S4) n))).codRestrict
        (LinearMap.ker (coboundaryₗ (TopCat.of RP4) n)) fun y => cochainTransfer_mem_ker y))
    (by
      intro y hy
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hy
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
          have hy0 : (y.1 : SingularCochain (TopCat.of S4) 0) = 0 := by
            have h0 := hy
            rwa [show coboundaryRange (TopCat.of S4) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
              Submodule.mem_bot] at h0
          rw [show coboundaryRange (TopCat.of RP4) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
            Submodule.mem_bot, hy0, map_zero]
      | succ m =>
          obtain ⟨b, hb⟩ := hy
          refine ⟨cochainTransfer m b, ?_⟩
          show coboundaryₗ (TopCat.of RP4) m (cochainTransfer m b) = cochainTransfer (m + 1) y.1
          rw [show coboundaryₗ (TopCat.of RP4) m (cochainTransfer m b)
              = coboundary (TopCat.of RP4) m (cochainTransfer m b) from rfl,
            coboundary_cochainTransfer]
          rw [show coboundary (TopCat.of S4) m b = coboundaryₗ (TopCat.of S4) m b from rfl, hb])

/-- The computation rule for `cohomologyTransfer` on a representative cocycle. -/
@[simp] theorem cohomologyTransfer_mk {n : ℕ}
    (y : LinearMap.ker (coboundaryₗ (TopCat.of S4) n)) :
    cohomologyTransfer n (Cohomology.mk (TopCat.of S4) n y)
      = Cohomology.mk (TopCat.of RP4) n ⟨cochainTransfer n y.1, cochainTransfer_mem_ker y⟩ :=
  Submodule.liftQ_apply _ _ _

/-! ## §2. The cochain SES: `0 → Cⁿ(ℝP⁴) →π^# Cⁿ(S⁴) →τ^# Cⁿ(ℝP⁴) → 0` -/

open SKEFTHawking.SingularCohomologyFunctoriality

/-- **The pullback `π^#` is injective** — evaluate at the plus-lift. -/
theorem cochainPullback_injective (n : ℕ) :
    Function.Injective (cochainPullback (X := TopCat.of S4) (Y := TopCat.of RP4) mkC n) := by
  intro a b h
  funext σ
  have h1 := congrFun h (liftPlus σ)
  simpa only [cochainPullback_apply, mapSimplex_liftPlus] using h1

/-- **`τ^# ∘ π^# = 0`** — a pulled-back cochain takes equal values on the two lifts. -/
theorem cochainTransfer_cochainPullback (n : ℕ) (a : SingularCochain (TopCat.of RP4) n) :
    cochainTransfer n (cochainPullback mkC n a) = 0 := by
  funext σ
  show cochainPullback mkC n a (liftPlus σ) + cochainPullback mkC n a (liftMinus σ)
    = (0 : SingularCochain (TopCat.of RP4) n) σ
  rw [cochainPullback_apply, cochainPullback_apply, mapSimplex_liftPlus, mapSimplex_liftMinus,
    ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  rfl

/-- **The plus-values cochain** of an `S⁴`-cochain: `σ ↦ y(σ₊)` — the explicit descent witness
(and the raw connecting formula of M3-c). -/
noncomputable def plusValues (n : ℕ) :
    SingularCochain (TopCat.of S4) n →ₗ[ZMod 2] SingularCochain (TopCat.of RP4) n where
  toFun y := fun σ => y (liftPlus σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem plusValues_apply {n : ℕ} (y : SingularCochain (TopCat.of S4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    plusValues n y σ = y (liftPlus σ) := rfl

/-- Plus-values inverts the pullback: `plusValues (π^# a) = a`. -/
@[simp] theorem plusValues_cochainPullback {n : ℕ} (a : SingularCochain (TopCat.of RP4) n) :
    plusValues n (cochainPullback mkC n a) = a := by
  funext σ
  rw [plusValues_apply, cochainPullback_apply, mapSimplex_liftPlus]

/-- **The explicit descent**: a cochain killed by `τ^#` (equal values on the two lifts) is the
pullback of its plus-values. -/
theorem cochainPullback_plusValues {n : ℕ}
    (y : SingularCochain (TopCat.of S4) n) (hy : cochainTransfer n y = 0) :
    cochainPullback mkC n (plusValues n y) = y := by
  funext τ'
  rw [cochainPullback_apply, plusValues_apply]
  rcases mem_pair_of_pushforward τ' with h | h
  · exact (congrArg y h).symm
  · have h0 : y (liftPlus (mapSimplex mkC τ')) + y (liftMinus (mapSimplex mkC τ')) = 0 := by
      simpa using congrFun hy (mapSimplex mkC τ')
    have heq : y (liftPlus (mapSimplex mkC τ')) = y (liftMinus (mapSimplex mkC τ')) := by
      revert h0
      generalize y (liftPlus (mapSimplex mkC τ')) = p
      generalize y (liftMinus (mapSimplex mkC τ')) = q
      revert p q
      decide
    rw [heq]
    exact (congrArg y h).symm

/-- **`ker τ^# = im π^#`** — the existential corollary of the explicit descent. -/
theorem mem_range_cochainPullback_of_cochainTransfer_eq_zero {n : ℕ}
    (y : SingularCochain (TopCat.of S4) n) (hy : cochainTransfer n y = 0) :
    ∃ a, cochainPullback mkC n a = y :=
  ⟨plusValues n y, cochainPullback_plusValues y hy⟩

open Classical in
/-- **The extend-by-zero section of `τ^#`**: `s^#(g)(σ') = g(πσ')` when `σ'` is the plus-lift of
its pushforward, else `0`. A module section (`τ^# ∘ s^# = id` on the nose) but *not* a cochain
map — its `δ`-defect is the cohomological Smith connecting map (M3-c). -/
noncomputable def cochainSection (n : ℕ) :
    SingularCochain (TopCat.of RP4) n →ₗ[ZMod 2] SingularCochain (TopCat.of S4) n where
  toFun g := fun σ' =>
    if σ' = liftPlus (mapSimplex mkC σ') then g (mapSimplex mkC σ') else 0
  map_add' g h := by
    funext σ'
    simp only [Pi.add_apply]
    by_cases hσ : σ' = liftPlus (mapSimplex mkC σ')
    · rw [if_pos hσ, if_pos hσ, if_pos hσ]
    · rw [if_neg hσ, if_neg hσ, if_neg hσ, add_zero]
  map_smul' c g := by
    funext σ'
    simp only [Pi.smul_apply, RingHom.id_apply]
    by_cases hσ : σ' = liftPlus (mapSimplex mkC σ')
    · rw [if_pos hσ, if_pos hσ]
    · rw [if_neg hσ, if_neg hσ, smul_zero]

open Classical in
@[simp] theorem cochainSection_apply_plus {n : ℕ} (g : SingularCochain (TopCat.of RP4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    cochainSection n g (liftPlus σ) = g σ := by
  show (if liftPlus σ = liftPlus (mapSimplex mkC (liftPlus σ))
    then g (mapSimplex mkC (liftPlus σ)) else 0) = g σ
  rw [mapSimplex_liftPlus, if_pos rfl]

open Classical in
@[simp] theorem cochainSection_apply_minus {n : ℕ} (g : SingularCochain (TopCat.of RP4) n)
    (σ : (TopCat.toSSet.obj (TopCat.of RP4)).obj (op (SimplexCategory.mk n))) :
    cochainSection n g (liftMinus σ) = 0 := by
  show (if liftMinus σ = liftPlus (mapSimplex mkC (liftMinus σ))
    then g (mapSimplex mkC (liftMinus σ)) else 0) = 0
  rw [mapSimplex_liftMinus, if_neg (fun h => liftPlus_ne_liftMinus σ h.symm)]

/-- **`τ^# ∘ s^# = id` on the nose** — the transfer is (split-)surjective. -/
theorem cochainTransfer_cochainSection {n : ℕ} (g : SingularCochain (TopCat.of RP4) n) :
    cochainTransfer n (cochainSection n g) = g := by
  funext σ
  show cochainSection n g (liftPlus σ) + cochainSection n g (liftMinus σ) = g σ
  rw [cochainSection_apply_plus, cochainSection_apply_minus, add_zero]

/-! ## §3. The cohomological Smith connecting map `δS : Hⁿ(ℝP⁴) → Hⁿ⁺¹(ℝP⁴)` -/

/-- **The connecting cochain**: the plus-values of the `δ`-defect of the section,
`g ↦ plusValues(δ(s^# g))`. -/
noncomputable def connectingCochain (n : ℕ) :
    SingularCochain (TopCat.of RP4) n →ₗ[ZMod 2] SingularCochain (TopCat.of RP4) (n + 1) :=
  (plusValues (n + 1)) ∘ₗ (coboundaryₗ (TopCat.of S4) n) ∘ₗ (cochainSection n)

/-- For a cocycle `g`, the `δ`-defect of the section is killed by `τ^#`:
`τ^#(δ(s^#g)) = δ(τ^#(s^#g)) = δg = 0`. -/
theorem cochainTransfer_coboundary_cochainSection {n : ℕ}
    (g : SingularCochain (TopCat.of RP4) n) (hg : coboundaryₗ (TopCat.of RP4) n g = 0) :
    cochainTransfer (n + 1) (coboundaryₗ (TopCat.of S4) n (cochainSection n g)) = 0 := by
  rw [show (coboundaryₗ (TopCat.of S4) n) (cochainSection n g)
      = coboundary (TopCat.of S4) n (cochainSection n g) from rfl,
    ← coboundary_cochainTransfer, cochainTransfer_cochainSection]
  exact hg

/-- **The connecting pullback identity**: `π^#(connectingCochain g) = δ(s^# g)` for a cocycle
`g` — the defect is `τ^#`-killed, so it is the pullback of its plus-values. -/
theorem cochainPullback_connectingCochain {n : ℕ}
    (g : SingularCochain (TopCat.of RP4) n) (hg : coboundaryₗ (TopCat.of RP4) n g = 0) :
    cochainPullback mkC (n + 1) (connectingCochain n g)
      = coboundaryₗ (TopCat.of S4) n (cochainSection n g) :=
  cochainPullback_plusValues _ (cochainTransfer_coboundary_cochainSection g hg)

/-- **The connecting cochain of a cocycle is a cocycle** — `π^#`-inject `δδ(s^#g) = 0`. -/
theorem connectingCochain_mem_ker {n : ℕ}
    (g : SingularCochain (TopCat.of RP4) n) (hg : coboundaryₗ (TopCat.of RP4) n g = 0) :
    coboundaryₗ (TopCat.of RP4) (n + 1) (connectingCochain n g) = 0 := by
  apply cochainPullback_injective (n + 1 + 1)
  rw [map_zero,
    show cochainPullback mkC (n + 1 + 1)
        (coboundaryₗ (TopCat.of RP4) (n + 1) (connectingCochain n g))
      = coboundary (TopCat.of S4) (n + 1)
        (cochainPullback mkC (n + 1) (connectingCochain n g)) from
      (coboundary_cochainPullback mkC (n + 1) (connectingCochain n g)).symm,
    cochainPullback_connectingCochain g hg]
  exact coboundary_comp_coboundary (TopCat.of S4) n _

/-- **The connecting cochain of a coboundary is a coboundary**: the defect
`u := s^#(δb) + δ(s^#b)` is `τ^#`-killed, and `δ(π^# plusValues u) = δu = δ(s^#(δb))` exhibits
`connectingCochain (δb) = δ(plusValues u)`. -/
theorem connectingCochain_coboundary {n : ℕ} (b : SingularCochain (TopCat.of RP4) n) :
    ∃ c, coboundaryₗ (TopCat.of RP4) (n + 1) c
      = connectingCochain (n + 1) (coboundaryₗ (TopCat.of RP4) n b) := by
  set u := cochainSection (n + 1) (coboundaryₗ (TopCat.of RP4) n b)
    + coboundaryₗ (TopCat.of S4) n (cochainSection n b) with hu
  have hker : cochainTransfer (n + 1) u = 0 := by
    rw [hu, map_add, cochainTransfer_cochainSection,
      show (coboundaryₗ (TopCat.of S4) n) (cochainSection n b)
        = coboundary (TopCat.of S4) n (cochainSection n b) from rfl,
      ← coboundary_cochainTransfer, cochainTransfer_cochainSection]
    show coboundaryₗ (TopCat.of RP4) n b + coboundaryₗ (TopCat.of RP4) n b = 0
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
  refine ⟨plusValues (n + 1) u, ?_⟩
  apply cochainPullback_injective (n + 1 + 1)
  rw [show cochainPullback mkC (n + 1 + 1)
        (coboundaryₗ (TopCat.of RP4) (n + 1) (plusValues (n + 1) u))
      = coboundary (TopCat.of S4) (n + 1) (cochainPullback mkC (n + 1) (plusValues (n + 1) u))
      from (coboundary_cochainPullback mkC (n + 1) (plusValues (n + 1) u)).symm,
    cochainPullback_plusValues u hker,
    cochainPullback_connectingCochain (coboundaryₗ (TopCat.of RP4) n b)
      (coboundary_comp_coboundary (TopCat.of RP4) n b),
    hu]
  show coboundaryₗ (TopCat.of S4) (n + 1)
      (cochainSection (n + 1) (coboundaryₗ (TopCat.of RP4) n b)
        + coboundaryₗ (TopCat.of S4) n (cochainSection n b))
    = coboundaryₗ (TopCat.of S4) (n + 1)
        (cochainSection (n + 1) (coboundaryₗ (TopCat.of RP4) n b))
  rw [map_add,
    show (coboundaryₗ (TopCat.of S4) (n + 1))
        ((coboundaryₗ (TopCat.of S4) n) (cochainSection n b))
      = coboundary (TopCat.of S4) (n + 1) (coboundary (TopCat.of S4) n (cochainSection n b))
      from rfl,
    coboundary_comp_coboundary (TopCat.of S4) n, add_zero]

/-- **The cohomological Smith connecting map** `δS : Hⁿ(ℝP⁴; ℤ/2) → Hⁿ⁺¹(ℝP⁴; ℤ/2)` — the
descended connecting cochain. The cup-ladder generator of `H^*(ℝP⁴)` (M3-g..i). -/
noncomputable def smithCoConnecting (n : ℕ) :
    Cohomology (TopCat.of RP4) n →ₗ[ZMod 2] Cohomology (TopCat.of RP4) (n + 1) :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((connectingCochain n).domRestrict
          (LinearMap.ker (coboundaryₗ (TopCat.of RP4) n))).codRestrict
        (LinearMap.ker (coboundaryₗ (TopCat.of RP4) (n + 1)))
        fun g => LinearMap.mem_ker.mpr
          (connectingCochain_mem_ker g.1 (LinearMap.mem_ker.mp g.2))))
    (by
      intro g hg
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hg
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
          have hg0 : (g.1 : SingularCochain (TopCat.of RP4) 0) = 0 := by
            have h0 := hg
            rwa [show coboundaryRange (TopCat.of RP4) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
              Submodule.mem_bot] at h0
          exact ⟨0, by rw [map_zero, hg0, map_zero]⟩
      | succ m =>
          obtain ⟨b, hb⟩ := hg
          obtain ⟨c, hc⟩ := connectingCochain_coboundary b
          exact ⟨c, by rw [hc, hb]⟩)

/-- The computation rule for `δS` on a representative cocycle. -/
@[simp] theorem smithCoConnecting_mk {n : ℕ}
    (g : LinearMap.ker (coboundaryₗ (TopCat.of RP4) n)) :
    smithCoConnecting n (Cohomology.mk (TopCat.of RP4) n g)
      = Cohomology.mk (TopCat.of RP4) (n + 1)
          ⟨connectingCochain n g.1,
            LinearMap.mem_ker.mpr (connectingCochain_mem_ker g.1 (LinearMap.mem_ker.mp g.2))⟩ :=
  Submodule.liftQ_apply _ _ _

/-! ## §4. The exactness of the cohomological Smith triangle at the two `δS`-slots -/

private theorem cmk_eq_zero_iff {X : TopCat} {n : ℕ} (z : LinearMap.ker (coboundaryₗ X n)) :
    Cohomology.mk X n z = 0 ↔ (z : SingularCochain X n) ∈ coboundaryRange X n := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

private theorem sub_eq_add' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (a b : M) :
    a - b = a + b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (by
    rw [← two_smul (ZMod 2) b, show (2 : ZMod 2) = 0 by decide, zero_smul])]

/-- **`δS ∘ τ^* = 0`**: the defect `u := s^#(τ^#y) + y` is `τ^#`-killed, so
`conn(τ^#y) = plusValues(δu + δy) = δ(plusValues u)` — a coboundary. -/
theorem smithCoConnecting_cohomologyTransfer {n : ℕ} (y : Cohomology (TopCat.of S4) n) :
    smithCoConnecting n (cohomologyTransfer n y) = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show smithCoConnecting n (cohomologyTransfer n (Cohomology.mk (TopCat.of S4) n y)) = 0
  rw [cohomologyTransfer_mk, smithCoConnecting_mk, cmk_eq_zero_iff]
  set u := cochainSection n (cochainTransfer n y.1) + y.1 with hu
  have hker : cochainTransfer n u = 0 := by
    rw [hu, map_add, cochainTransfer_cochainSection, ← two_smul (ZMod 2),
      show (2 : ZMod 2) = 0 by decide, zero_smul]
  refine ⟨plusValues n u, ?_⟩
  show coboundaryₗ (TopCat.of RP4) n (plusValues n u) = connectingCochain n (cochainTransfer n y.1)
  apply cochainPullback_injective (n + 1)
  rw [show cochainPullback mkC (n + 1) (coboundaryₗ (TopCat.of RP4) n (plusValues n u))
      = coboundary (TopCat.of S4) n (cochainPullback mkC n (plusValues n u)) from
      (coboundary_cochainPullback mkC n (plusValues n u)).symm,
    cochainPullback_plusValues u hker,
    cochainPullback_connectingCochain (cochainTransfer n y.1)
      (cochainTransfer_mem_ker y |> LinearMap.mem_ker.mp), hu]
  show coboundaryₗ (TopCat.of S4) n (cochainSection n (cochainTransfer n y.1) + y.1)
    = coboundaryₗ (TopCat.of S4) n (cochainSection n (cochainTransfer n y.1))
  rw [map_add, LinearMap.mem_ker.mp y.2, add_zero]

/-- **Exactness at the `τ^*`-target `Hⁿ(ℝP⁴)`**: `ker δS = im τ^*`. Snake content: if
`conn g = δc`, then `y' := s^#g + π^#c` is an `S⁴`-cocycle with `τ^#y' = g` on the nose. -/
theorem exact_cohomologyTransfer_smithCoConnecting (n : ℕ) :
    Function.Exact (cohomologyTransfer n) (smithCoConnecting n) := by
  intro w₀
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w₀
  constructor
  · intro h
    have hb : connectingCochain n g.1 ∈ coboundaryRange (TopCat.of RP4) (n + 1) := by
      have h2 : smithCoConnecting n (Cohomology.mk (TopCat.of RP4) n g) = 0 := h
      rw [smithCoConnecting_mk, cmk_eq_zero_iff] at h2
      exact h2
    obtain ⟨c, hc⟩ := hb
    have hycyc : cochainSection n g.1 + cochainPullback mkC n c
        ∈ LinearMap.ker (coboundaryₗ (TopCat.of S4) n) := by
      rw [LinearMap.mem_ker, map_add,
        show (coboundaryₗ (TopCat.of S4) n) (cochainPullback mkC n c)
          = cochainPullback mkC (n + 1) (coboundaryₗ (TopCat.of RP4) n c) from
          coboundary_cochainPullback mkC n c,
        hc,
        show (coboundaryₗ (TopCat.of S4) n) (cochainSection n g.1)
          = cochainPullback mkC (n + 1) (connectingCochain n g.1) from
          (cochainPullback_connectingCochain g.1 (LinearMap.mem_ker.mp g.2)).symm,
        ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]
    refine ⟨Cohomology.mk (TopCat.of S4) n ⟨_, hycyc⟩, ?_⟩
    rw [cohomologyTransfer_mk]
    refine congrArg (Cohomology.mk (TopCat.of RP4) n) (Subtype.ext ?_)
    show cochainTransfer n (cochainSection n g.1 + cochainPullback mkC n c) = g.1
    rw [map_add, cochainTransfer_cochainSection, cochainTransfer_cochainPullback, add_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact smithCoConnecting_cohomologyTransfer y

/-- **`π^* ∘ δS = 0`**: `π^#(conn g) = δ(s^#g)` is a coboundary on the nose. -/
theorem cohomologyPullback_smithCoConnecting {n : ℕ} (w : Cohomology (TopCat.of RP4) n) :
    cohomologyPullback mkC (n + 1) (smithCoConnecting n w) = 0 := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show cohomologyPullback mkC (n + 1)
    (smithCoConnecting n (Cohomology.mk (TopCat.of RP4) n g)) = 0
  rw [smithCoConnecting_mk, cohomologyPullback_mk, cmk_eq_zero_iff]
  exact ⟨cochainSection n g.1,
    (cochainPullback_connectingCochain g.1 (LinearMap.mem_ker.mp g.2)).symm⟩

/-- **Exactness at the `δS`-target `Hⁿ⁺¹(ℝP⁴)`**: `ker π^* = im δS`. Snake content: if
`π^#x = δw`, then `g := τ^#w` is a cocycle with `conn g = x + δ(plusValues(s^#(τ^#w) + w))`. -/
theorem exact_smithCoConnecting_cohomologyPullback (n : ℕ) :
    Function.Exact (smithCoConnecting n) (cohomologyPullback mkC (n + 1)) := by
  intro x₀
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x₀
  constructor
  · intro h
    have hb : cochainPullback mkC (n + 1) x.1 ∈ coboundaryRange (TopCat.of S4) (n + 1) := by
      have h2 : cohomologyPullback mkC (n + 1)
          (Cohomology.mk (TopCat.of RP4) (n + 1) x) = 0 := h
      rw [cohomologyPullback_mk, cmk_eq_zero_iff] at h2
      exact h2
    obtain ⟨w, hw⟩ := hb
    have hgcyc : cochainTransfer n w ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) n) := by
      rw [LinearMap.mem_ker,
        show (coboundaryₗ (TopCat.of RP4) n) (cochainTransfer n w)
          = coboundary (TopCat.of RP4) n (cochainTransfer n w) from rfl,
        coboundary_cochainTransfer,
        show coboundary (TopCat.of S4) n w = coboundaryₗ (TopCat.of S4) n w from rfl,
        hw, cochainTransfer_cochainPullback]
    refine ⟨Cohomology.mk (TopCat.of RP4) n ⟨_, hgcyc⟩, ?_⟩
    rw [smithCoConnecting_mk]
    refine (Submodule.Quotient.eq _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    set u := cochainSection n (cochainTransfer n w) + w with hu
    have hker : cochainTransfer n u = 0 := by
      rw [hu, map_add, cochainTransfer_cochainSection, ← two_smul (ZMod 2),
        show (2 : ZMod 2) = 0 by decide, zero_smul]
    refine ⟨plusValues n u, ?_⟩
    show coboundaryₗ (TopCat.of RP4) n (plusValues n u)
      = connectingCochain n (cochainTransfer n w) - x.1
    apply cochainPullback_injective (n + 1)
    rw [map_sub,
      show cochainPullback mkC (n + 1) (coboundaryₗ (TopCat.of RP4) n (plusValues n u))
        = coboundary (TopCat.of S4) n (cochainPullback mkC n (plusValues n u)) from
        (coboundary_cochainPullback mkC n (plusValues n u)).symm,
      cochainPullback_plusValues u hker,
      cochainPullback_connectingCochain (cochainTransfer n w)
        (LinearMap.mem_ker.mp hgcyc), hu, ← hw]
    show coboundaryₗ (TopCat.of S4) n (cochainSection n (cochainTransfer n w) + w)
      = coboundaryₗ (TopCat.of S4) n (cochainSection n (cochainTransfer n w))
        - coboundaryₗ (TopCat.of S4) n w
    rw [map_add, sub_eq_add']
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact cohomologyPullback_smithCoConnecting g

end SKEFTHawking.RP4SmithCochain
