/-
# Phase 5q.H — the seam-lattice counting reduction of `QLatticeInSeamSpan`

`KummerK3H1Vanish.QLatticeInSeamSpan` — the ONE residual of the K3 `h1Free` chain — quantifies
over **all** of `H₁(T⁴°;ℤ)`. This module reduces it to a purely **finite** statement about the
16 seam classes alone, namely `Function.Injective seamClass`, by pinning the *size* of the lifted
subgroup `im p_* ≤ H₁(Q;ℤ)` from above by `16`:

* **`τ_* = −1` on `H₁(T⁴°;ℤ)`** (`tauStar_eq_neg`) — the norm `y + τ_* y` is `τ`-fixed, and
  `KummerPuncturedMV.x_H1_fixed_eq_zero` kills `τ`-fixed degree-1 classes.
* **`im p_*` is 2-torsion** (`two_zsmul_mapInt_qmkC`) — `p ∘ τ = p` (`qmkC_comp_tauC`) forces
  `p_* y = p_*(−y) = −p_* y`.
* **`H₁(T⁴°;ℤ)` is spanned by at most 4 elements** (`exists_spanning_family`) — the puncture
  window `H₁(T⁴°;ℤ) ↪ H₁(T⁴;ℤ) ≅ ℤ⁴` (`KummerPuncturedMV.puncture_hX1` +
  `KummerHomologyT4Full.torusFourH1EquivFin4`) plus the PID structure theorem
  (`Submodule.basisOfPid`).
* Hence **`im p_*` has at most `2⁴ = 16` elements** (every element is a `{0,1}`-combination of the
  four generators' images, `mem_range_boolSum`), while
* **the 16 seam differences `seamClass c − seamClass c₀` all lie in `im p_*`** (each is deck-even,
  `qDeck_qBdryMap` + `mem_range_qmk_of_qDeck_eq_zero`).

So as soon as the 16 seam classes are **pairwise distinct**, the 16 differences already exhaust
`im p_*` (pigeonhole `16 ≤ 16`), which is exactly `QLatticeInSeamSpan`.

**Honest scope.** `Function.Injective seamClass` is a *sufficient* condition, proved sufficient
here; the converse is **not** proved (it would need the matching lower bound `16 ≤ |im p_*|`,
i.e. surjectivity of the puncture window `H₁(T⁴°;ℤ) → H₁(T⁴;ℤ)`, which is not in the tree). It is
also **not vacuous**: it fails outright for a trivial `H₁(Q;ℤ)`, so no zero-geometric-input
discharge exists — separating the 16 seam classes is genuine geometry (the four lattice-parity
functionals of the `§5` discharge plan of `KummerK3H1Vanish`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3H1Vanish
import SKEFTHawking.KummerPuncturedMV
import SKEFTHawking.KummerHomologyT4Full

namespace SKEFTHawking.KummerK3H1SeamLattice

open SKEFTHawking.SingularHomologyInt (Homology chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp
  Homology.mapInt_id)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC tauC tauC_comp_self qmkC_comp_tauC)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerQuotientDeckFunctional (qDeck qDeck_qBdryMap)
open SKEFTHawking.KummerQuotientH2Solve (inclXC)
open SKEFTHawking.KummerPuncturedMV (x_H1_fixed_eq_zero puncture_hX1)
open SKEFTHawking.KummerHomologyT4Full (torusFourH1EquivFin4)
open SKEFTHawking.KummerK3H1Vanish

noncomputable section

/-! ## §1. `τ_* = −1` on `H₁(T⁴°;ℤ)`, and the 2-torsion of the lifted subgroup -/

/-- The deck action is involutive on `H₁(T⁴°;ℤ)` (functoriality + `τ ∘ τ = id`). -/
theorem tauStar_involutive (y : Homology PTtop 1) :
    Homology.mapInt tauC 1 (Homology.mapInt tauC 1 y) = y := by
  have h : (Homology.mapInt tauC 1).comp (Homology.mapInt tauC 1)
      = (LinearMap.id : Homology PTtop 1 →ₗ[ℤ] Homology PTtop 1) := by
    rw [← Homology.mapInt_comp, tauC_comp_self, Homology.mapInt_id]
  exact LinearMap.congr_fun h y

/-- **`τ_* = −1` on `H₁(T⁴°;ℤ)`** — the norm `y + τ_* y` is `τ`-fixed, and `H₁(T⁴°;ℤ)` has no
nonzero `τ`-fixed class (`KummerPuncturedMV.x_H1_fixed_eq_zero`). -/
theorem tauStar_eq_neg (y : Homology PTtop 1) : Homology.mapInt tauC 1 y = -y := by
  have hfix : Homology.mapInt tauC 1 (y + Homology.mapInt tauC 1 y)
      = y + Homology.mapInt tauC 1 y := by
    rw [map_add, tauStar_involutive]
    abel
  have h0 : y + Homology.mapInt tauC 1 y = 0 := x_H1_fixed_eq_zero _ hfix
  exact eq_neg_of_add_eq_zero_right h0

/-- **`p_* ∘ τ_* = p_*`** — the covering projection is `τ`-invariant (`qmkC_comp_tauC`). -/
theorem mapInt_qmkC_tauC (y : Homology PTtop 1) :
    Homology.mapInt qmkC 1 (Homology.mapInt tauC 1 y) = Homology.mapInt qmkC 1 y := by
  have h : (Homology.mapInt qmkC 1).comp (Homology.mapInt tauC 1)
      = Homology.mapInt qmkC 1 := by
    rw [← Homology.mapInt_comp, qmkC_comp_tauC]
  exact LinearMap.congr_fun h y

/-- **`im p_*` is 2-torsion**: `p_* y = p_*(τ_* y) = p_*(−y) = −p_* y`. -/
theorem two_zsmul_mapInt_qmkC (y : Homology PTtop 1) :
    (2 : ℤ) • Homology.mapInt qmkC 1 y = 0 := by
  have h := mapInt_qmkC_tauC y
  rw [tauStar_eq_neg, map_neg] at h
  rw [two_smul]
  nth_rewrite 1 [← h]
  abel

/-- A `ℤ`-multiple of a lifted class only sees the multiplier mod 2. -/
theorem zsmul_mapInt_qmkC (m : ℤ) (y : Homology PTtop 1) :
    m • Homology.mapInt qmkC 1 y = (m % 2) • Homology.mapInt qmkC 1 y := by
  conv_lhs => rw [← Int.mul_ediv_add_emod m 2]
  rw [add_zsmul, mul_zsmul, smul_comm, two_zsmul_mapInt_qmkC, smul_zero, zero_add]

/-! ## §2. `H₁(T⁴°;ℤ)` is spanned by at most four classes -/

/-- **The puncture window functional** `H₁(T⁴°;ℤ) → ℤ⁴` — the inclusion `T⁴° ↪ T⁴` followed by
the `H₁(T⁴;ℤ) ≅ ℤ⁴` identification. -/
def windowJ : Homology PTtop 1 →ₗ[ℤ] (Fin 4 → ℤ) :=
  (torusFourH1EquivFin4 : Homology (TopCat.of TorusFour) 1 ≃ₗ[ℤ] (Fin 4 → ℤ)).toLinearMap.comp
    (Homology.mapInt inclXC 1)

theorem windowJ_injective : Function.Injective windowJ :=
  (torusFourH1EquivFin4).injective.comp puncture_hX1

/-- **`H₁(T⁴°;ℤ)` is free of rank ≤ 4** — it embeds in `ℤ⁴` through the puncture window, and a
submodule of a finite-rank free module over a PID is free of no greater rank. -/
theorem exists_spanning_family :
    ∃ (n : ℕ) (b : Fin n → Homology PTtop 1),
      n ≤ 4 ∧ Submodule.span ℤ (Set.range b) = ⊤ := by
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin 4)) (LinearMap.range windowJ)
  let e : Homology PTtop 1 ≃ₗ[ℤ] ↥(LinearMap.range windowJ) :=
    LinearEquiv.ofInjective windowJ windowJ_injective
  refine ⟨n, ⇑(bN.map e.symm), ?_, (bN.map e.symm).span_eq⟩
  have h1 : Module.finrank ℤ ↥(LinearMap.range windowJ) = n := by
    rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
  have h2 : Module.finrank ℤ ↥(LinearMap.range windowJ) ≤ Module.finrank ℤ (Fin 4 → ℤ) :=
    Submodule.finrank_le _
  have h3 : Module.finrank ℤ (Fin 4 → ℤ) = 4 := by simp
  omega

/-! ## §3. The lifted subgroup has at most 16 elements -/

/-- The `{0,1}`-combinations of the images of a family of `H₁(T⁴°;ℤ)`-classes. -/
def boolSum {n : ℕ} (b : Fin n → Homology PTtop 1) (S : Finset (Fin n)) : Homology Qtop 1 :=
  ∑ i ∈ S, Homology.mapInt qmkC 1 (b i)

/-- **Every lifted class is a `{0,1}`-combination**: `im p_*` is 2-torsion, so an integer
coefficient only matters mod 2. -/
theorem mem_range_boolSum {n : ℕ} {b : Fin n → Homology PTtop 1}
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (y : Homology PTtop 1) :
    Homology.mapInt qmkC 1 y ∈ Set.range (boolSum b) := by
  classical
  have hy : y ∈ Submodule.span ℤ (Set.range b) := hb ▸ Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨c, hc⟩ := hy
  refine ⟨Finset.univ.filter (fun i => c i % 2 = 1), ?_⟩
  rw [boolSum, Finset.sum_filter, ← hc, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, zsmul_mapInt_qmkC]
  rcases Int.emod_two_eq_zero_or_one (c i) with h | h <;> simp [h]

/-! ## §4. The seam differences live in the lifted subgroup -/

/-- **The deck-even classes are exactly the lifted ones** (the `⊆` half): a class of deck value
`0` comes from `H₁(T⁴°;ℤ)`. Repackaging of `KummerK3H1Vanish.mem_range_projH_of_qDeckHml_eq_zero`
through the `Hml`/`Homology` bridge. -/
theorem mem_range_qmk_of_qDeck_eq_zero (x : Homology Qtop 1) (hx : qDeck x = 0) :
    ∃ y : Homology PTtop 1, Homology.mapInt qmkC 1 y = x := by
  obtain ⟨y, hy⟩ := mem_range_projH_of_qDeckHml_eq_zero
    (x := (x : Hml (chainBoundary Qtop) 1)) (by rw [← qDeck_eq_qDeckHml]; exact hx)
  rw [projH_eq_mapInt 0] at hy
  exact ⟨y, hy⟩

/-- **Every seam difference is lifted**: each seam class is deck-odd (`qDeck_qBdryMap`), so a
difference of two of them is deck-even, hence in `im p_*`. -/
theorem seam_diff_mem_range_qmk (c c' : EIndex) :
    ∃ y : Homology PTtop 1, Homology.mapInt qmkC 1 y = seamClass c - seamClass c' := by
  refine mem_range_qmk_of_qDeck_eq_zero _ ?_
  rw [map_sub, seamClass, seamClass, qDeck_qBdryMap, qDeck_qBdryMap, sub_self]

/-! ## §5. The reduction: seam-class injectivity discharges the residual -/

/-- **THE REDUCTION** — `QLatticeInSeamSpan` from the finite statement that the 16 seam classes
are pairwise distinct.

The 16 differences `seamClass c − seamClass c₀` are 16 distinct elements of `im p_*` (§4), and
`im p_*` has at most `2⁴ = 16` elements (§2 + §3); so the differences *exhaust* `im p_*`, and each
lies in `seamSpan`. -/
theorem qLatticeInSeamSpan_of_seamClass_injective
    (hinj : Function.Injective seamClass) : QLatticeInSeamSpan := by
  classical
  haveI : Nonempty EIndex :=
    Fintype.card_pos_iff.mp (by rw [SKEFTHawking.KummerWeld.eIndex_card]; omega)
  obtain ⟨n, b, hn, hb⟩ := exists_spanning_family
  set c₀ : EIndex := Classical.arbitrary EIndex with hc₀
  set Θ : EIndex → Homology Qtop 1 := fun c => seamClass c - seamClass c₀ with hΘ
  have hΘinj : Function.Injective Θ := by
    intro a a' haa
    exact hinj (sub_left_injective haa)
  have hΘmem : ∀ c : EIndex, Θ c ∈ Set.range (boolSum b) := by
    intro c
    obtain ⟨y, hy⟩ := seam_diff_mem_range_qmk c c₀
    show seamClass c - seamClass c₀ ∈ Set.range (boolSum b)
    rw [← hy]
    exact mem_range_boolSum hb y
  set T : Finset (Homology Qtop 1) := Finset.univ.image Θ with hT
  set U : Finset (Homology Qtop 1) := Finset.univ.image (boolSum b) with hU
  have hTU : T ⊆ U := by
    intro x hxT
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hxT
    obtain ⟨S, hS⟩ := hΘmem c
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ S, hS⟩
  have hTcard : T.card = 16 := by
    rw [hT, Finset.card_image_of_injective _ hΘinj, Finset.card_univ,
      SKEFTHawking.KummerWeld.eIndex_card]
  have hUcard : U.card ≤ 16 := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn
      _ = 16 := by norm_num
  have hTeq : T = U := Finset.eq_of_subset_of_card_le hTU (by omega)
  intro y
  have h1 : Homology.mapInt qmkC 1 y ∈ U := by
    obtain ⟨S, hS⟩ := mem_range_boolSum hb y
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ S, hS⟩
  rw [← hTeq] at h1
  obtain ⟨c, _, hc⟩ := Finset.mem_image.mp h1
  rw [← hc, hΘ]
  exact Submodule.sub_mem _ (seamClass_mem_seamSpan c) (seamClass_mem_seamSpan c₀)

/-! ## §6. Downstream: the `h1Free` atom under the finite residual -/

/-- **`H₁(K3;ℤ) = 0`** under the finite seam-distinctness residual. -/
theorem h1K3_eq_zero_of_seamClass_injective (hinj : Function.Injective seamClass)
    (x : Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) : x = 0 :=
  h1K3_eq_zero (qLatticeInSeamSpan_of_seamClass_injective hinj) x

/-- **The `h1Free` residual field of `KummerK3E1Package.KummerK3E1Residuals`**, now resting on the
finite seam-distinctness statement rather than on a quantifier over all of `H₁(T⁴°;ℤ)`. -/
theorem free_h1K3_of_seamClass_injective (hinj : Function.Injective seamClass) :
    Module.Free ℤ (Homology SKEFTHawking.KummerK7Opener.KummerK3top 1) :=
  free_h1K3 (qLatticeInSeamSpan_of_seamClass_injective hinj)

end

end SKEFTHawking.KummerK3H1SeamLattice
