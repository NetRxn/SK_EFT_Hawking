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
  window `H₁(T⁴°;ℤ) ↪ H₁(T⁴;ℤ) ≅ ℤ⁴` (`KummerPuncturedMV.puncture_hX1` + the four winding
  functionals `KummerT4CycleDetection.Phi1`, packaged here as `windowJ`) plus the PID structure
  theorem (`Submodule.basisOfPid`).
* Hence **`im p_*` has at most `2⁴ = 16` elements** (every element is a `{0,1}`-combination of the
  four generators' images, `mem_range_boolSum`), while
* **the 16 seam differences `seamClass c − seamClass c₀` all lie in `im p_*`** (each is deck-even,
  `qDeck_qBdryMap` + `mem_range_qmk_of_qDeck_eq_zero`).

So as soon as the 16 seam classes are **pairwise distinct**, the 16 differences already exhaust
`im p_*` (pigeonhole `16 ≤ 16`), which is exactly `QLatticeInSeamSpan`.

§6–§8 then push the residual one step further, off homology entirely and into **`ℤ⁴`
arithmetic**: `ker p_* = 2·H₁(T⁴°;ℤ)` **exactly** (`mapInt_qmkC_eq_zero_iff`, from SES-III
exactness at the middle plus `τ_* = −1`), so two seam classes agree **iff** their difference lift
is 2-divisible — and 2-divisibility is detected by the four winding functionals. The residual in
this form is `SeamWindingOdd`: *a lift of a difference of two distinct seam classes has an odd
winding coordinate.* Its parity vector is lift-independent
(`windowJ_sub_even_of_mapInt_qmkC_eq`), so no choice is hidden in it.

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
import SKEFTHawking.KummerT4CycleDetection

namespace SKEFTHawking.KummerK3H1SeamLattice

open SKEFTHawking.SingularHomologyInt (Homology chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt Homology.mapInt_comp
  Homology.mapInt_id)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC tauC tauC_comp_self qmkC_comp_tauC)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerQuotientDeckFunctional (qDeck qDeck_qBdryMap)
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.KummerQuotientH2Solve (inclXC tauH_eq_mapInt)
open SKEFTHawking.KummerPuncturedMV (x_H1_fixed_eq_zero puncture_hX1)
open SKEFTHawking.KummerT4CycleDetection (Phi1 Phi1_injective bCls fourStepC fourStepInvC
  fourStep_comp_inv fourStepInv_comp)
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

/-- The tower model `T⁴ ≅ (((S¹×S¹)×S¹)×S¹)` retraction is injective on homology (it is a
two-sided homeomorphism, `fourStep_comp_inv` / `fourStepInv_comp`). -/
theorem mapInt_fourStepInvC_injective (n : ℕ) :
    Function.Injective (Homology.mapInt fourStepInvC n) := by
  have h : (Homology.mapInt fourStepC n).comp (Homology.mapInt fourStepInvC n)
      = LinearMap.id := by
    rw [← Homology.mapInt_comp, fourStep_comp_inv, Homology.mapInt_id]
  intro a b hab
  have ha := LinearMap.congr_fun h a
  have hb := LinearMap.congr_fun h b
  simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at ha hb
  rw [← ha, ← hb, hab]

/-- **THE FOUR PUNCTURE-WINDOW WINDING FUNCTIONALS** `H₁(T⁴°;ℤ) → ℤ⁴` — push a class into `T⁴`
along the puncture inclusion (`inclXC`), transport to the tower model, and pair it with the four
coordinate winding cocycles (`KummerT4CycleDetection.Phi1`, the Kronecker pairing against
`bCls i`). These are exactly the "four winding functionals" of the `§5` discharge plan of
`KummerK3H1Vanish`. -/
def windowJ : Homology PTtop 1 →ₗ[ℤ] (Fin 4 → ℤ) :=
  Phi1.comp ((Homology.mapInt fourStepInvC 1).comp (Homology.mapInt inclXC 1))

theorem windowJ_apply (y : Homology PTtop 1) (i : Fin 4) :
    windowJ y i = SKEFTHawking.SingularHomologyInt.kroneckerHInt 1 (bCls i)
      (Homology.mapInt fourStepInvC 1 (Homology.mapInt inclXC 1 y)) := rfl

theorem windowJ_injective : Function.Injective windowJ := by
  intro a b hab
  exact puncture_hX1 (mapInt_fourStepInvC_injective 1 (Phi1_injective hab))

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

/-! ## §6. The kernel of the covering projection, exactly -/

/-- **SES-III exactness at `Hₙ(T⁴°)`**: `ker H(p₊) = im H(ι_B)` — the middle-term exactness of
the Smith SES-III long exact sequence, instantiated from the generic engine. -/
theorem exact_inclBH_projH (n : ℕ) : Function.Exact (inclBH n) (projH n) :=
  exact_Hmap_Hmap hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- **`ker p_* = 2·H₁(T⁴°;ℤ)`, exactly.**

`⊆`: SES-III exactness at `H₁(T⁴°)` puts a killed class in `im ι_B`; `D̄` is onto
(`diffH_one_surjective`), so the class is `u − τ_* u`, which is `2u` because `τ_* = −1` (§1).
`⊇`: `im p_*` is 2-torsion (§1).

This is the *sharp* statement — it turns "the two seam classes agree" into the **lattice**
statement "the difference lift is divisible by 2", which the winding functionals can test. -/
theorem mapInt_qmkC_eq_zero_iff (y : Homology PTtop 1) :
    Homology.mapInt qmkC 1 y = 0 ↔ ∃ u : Homology PTtop 1, y = (2 : ℤ) • u := by
  constructor
  · intro hy
    have hp : projH 1 y = 0 := by rw [projH_eq_mapInt 0]; exact hy
    obtain ⟨v, hv⟩ := (exact_inclBH_projH 1 y).mp hp
    obtain ⟨u, rfl⟩ := diffH_one_surjective v
    refine ⟨u, ?_⟩
    have h1 : inclBH 1 (diffH 1 u) = u - tauH 1 u := inclBH_diffH 1 u
    have h2 : tauH 1 u = -u := by rw [tauH_eq_mapInt 0]; exact tauStar_eq_neg u
    rw [h2, sub_neg_eq_add] at h1
    rw [← hv, h1, two_smul]
    rfl
  · rintro ⟨u, rfl⟩
    rw [map_zsmul]
    exact two_zsmul_mapInt_qmkC u

/-- **The winding parity of a lift is independent of the lift**: two lifts of the same class of
`H₁(Q;ℤ)` have puncture-window winding vectors congruent mod 2. So the residual `SeamWindingOdd`
below does not secretly depend on which lift is chosen. -/
theorem windowJ_sub_even_of_mapInt_qmkC_eq {y y' : Homology PTtop 1}
    (h : Homology.mapInt qmkC 1 y = Homology.mapInt qmkC 1 y') (i : Fin 4) :
    (2 : ℤ) ∣ (windowJ y i - windowJ y' i) := by
  have h0 : Homology.mapInt qmkC 1 (y - y') = 0 := by rw [map_sub, h, sub_self]
  obtain ⟨u, hu⟩ := (mapInt_qmkC_eq_zero_iff _).mp h0
  refine ⟨windowJ u i, ?_⟩
  have hk : windowJ y - windowJ y' = (2 : ℤ) • windowJ u := by
    rw [← map_sub, hu, map_zsmul]
  have := congrFun hk i
  simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using this

/-! ## §7. The residual in lattice form: one odd winding coordinate per seam difference -/

/-- **THE SHARP LATTICE RESIDUAL** — *a lift of any difference of two distinct seam classes has an
odd puncture-window winding coordinate.*

This is `KummerK3H1Vanish.QLatticeInSeamSpan` boiled down to arithmetic in `ℤ⁴`: no quantifier
over `H₁(T⁴°;ℤ)` survives, only the four integer winding numbers of the sixteen seam-difference
cycles. Geometrically it is the statement that the difference lift represents the lattice vector
`2v_c − 2v_{c'}` — which is odd in the coordinates where the two half-periods differ.

*Choice-independence*: by `windowJ_sub_even_of_mapInt_qmkC_eq` the parity vector of a lift is
independent of the lift, so the universal quantifier over `y` is not a strengthening.

*Non-vacuity*: it is refuted outright by any collapse of two seam classes (§8), so it carries the
whole geometric content — there is no zero-geometry discharge. -/
def SeamWindingOdd : Prop :=
  ∀ c c' : EIndex, c ≠ c' → ∀ y : Homology PTtop 1,
    Homology.mapInt qmkC 1 y = seamClass c - seamClass c' →
      ∃ i : Fin 4, ¬ ((2 : ℤ) ∣ windowJ y i)

/-! ## §8. `SeamWindingOdd → seamClass injective → QLatticeInSeamSpan` -/

/-- **The 16 seam classes are pairwise distinct** under the lattice residual: if two agreed, their
difference would lift to `0`, hence (by `mapInt_qmkC_eq_zero_iff`) to a class divisible by 2 —
whose winding coordinates are all even. -/
theorem seamClass_injective_of_seamWindingOdd (h : SeamWindingOdd) :
    Function.Injective seamClass := by
  intro c c' hcc
  by_contra hne
  obtain ⟨y, hy⟩ := seam_diff_mem_range_qmk c c'
  obtain ⟨i, hi⟩ := h c c' hne y hy
  refine hi ?_
  have h0 : Homology.mapInt qmkC 1 y = 0 := by rw [hy, hcc, sub_self]
  obtain ⟨u, rfl⟩ := (mapInt_qmkC_eq_zero_iff y).mp h0
  refine ⟨windowJ u i, ?_⟩
  rw [map_zsmul]
  simp

/-- **`QLatticeInSeamSpan` from the lattice residual** — §7 ∘ §5. -/
theorem qLatticeInSeamSpan_of_seamWindingOdd (h : SeamWindingOdd) : QLatticeInSeamSpan :=
  qLatticeInSeamSpan_of_seamClass_injective (seamClass_injective_of_seamWindingOdd h)

/-! ## §9. Downstream: the `h1Free` atom under the finite residual -/

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
