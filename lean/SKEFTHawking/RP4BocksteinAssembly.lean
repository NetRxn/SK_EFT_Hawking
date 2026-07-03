import Mathlib
import SKEFTHawking.SingularBocksteinLeibniz
import SKEFTHawking.RP4WuAssembly

/-!
# Phase 5q.G (B-arc, M4-c5..c6) — the Bockstein ladder on `ℝP⁴`: `Sq¹x = x²`, `Sq¹x² = 0`,
`Sq¹x³ = x⁴`

The class-level Bockstein computation on the `ℝP⁴` cup ladder, at pinned degrees (the
`(p+1)+q ≡ p+q+1` index seam is rfl only for literals):

* `Sq¹(xpow 1) = xpow 2` — the in-tree degree-1 Wu identity `Sq1_on_H1` + `xpow_two_eq_cupH`.
* `Sq¹(xpow 2) = xpow 3 + xpow 3 = 0` — Leibniz at `(1,1)` on the `[x ⌣ x]`-representative;
  both cross terms are `xpow 3` (left: the `(2,0)`-seeded Leibniz applied to the cup-shaped
  representative; right: the `(1,1)`-Leibniz form + a second-slot coboundary swap).
* `Sq¹(xpow 3) = x² ⌣ x² = xpow 4` — Leibniz at `(2,1)` on `[x² ⌣ x]`; the `Sq¹x²`-term dies.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4CohomologyLadder SKEFTHawking.RP4CupLadder
open SKEFTHawking.RP4SmithCochain
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularBocksteinLeibniz

namespace SKEFTHawking.RP4BocksteinAssembly

/-! ## §1. Pinned-degree cochain Leibniz + cup-coboundary helpers -/

/-- The Bockstein–Leibniz at `(1,1)` as a cochain-function identity (the Big/Small-vs-cup
face seams are one-`rfl` at literal degrees). -/
theorem Sq1cochain_cup_11 {X : TopCat} (a b : SingularCochain X 1)
    (ha : coboundary X 1 a = 0) (hb : coboundary X 1 b = 0) :
    Sq1cochain (cup a b) = cup (Sq1cochain a) b + cup a (Sq1cochain b) := by
  funext τ
  rw [Pi.add_apply, Sq1cochain_cup a ha b hb τ, cup_apply, cup_apply]
  rfl

/-- The Bockstein–Leibniz at `(2,1)` as a cochain-function identity. -/
theorem Sq1cochain_cup_21 {X : TopCat} (a : SingularCochain X 2) (b : SingularCochain X 1)
    (ha : coboundary X 2 a = 0) (hb : coboundary X 1 b = 0) :
    Sq1cochain (cup a b) = cup (Sq1cochain a) b + cup a (Sq1cochain b) := by
  funext τ
  rw [Pi.add_apply, Sq1cochain_cup a ha b hb τ, cup_apply, cup_apply]
  rfl

/-- **Right coboundary absorbs**: `a ⌣ δw = δ(a ⌣ w)` for a cocycle `a` (the `δa`-term of the
Leibniz rule dies) — at `(1,1)`: `a, w ∈ C¹`. -/
theorem cup_coboundary_right_11 {X : TopCat} (a w : SingularCochain X 1)
    (ha : coboundary X 1 a = 0) :
    cup a (coboundary X 1 w) = coboundary X (1 + 1) (cup a w) := by
  funext τ
  rw [cup_apply, coboundary_cup]
  have h1 : coboundary X 1 a (frontBig τ) = 0 := congrFun ha (frontBig τ)
  rw [h1, zero_mul, zero_add]
  rfl

/-- **Left coboundary absorbs**: `δw ⌣ b = δ(w ⌣ b)` for a cocycle `b` — at `(2→3, 1)`:
`w ∈ C²`, `b ∈ C¹`. -/
theorem cup_coboundary_left_31 {X : TopCat} (w : SingularCochain X 2) (b : SingularCochain X 1)
    (hb : coboundary X 1 b = 0) :
    cup (coboundary X 2 w) b = coboundary X (2 + 1) (cup w b) := by
  funext τ
  rw [cup_apply, coboundary_cup]
  have h1 : coboundary X 1 b (backSmall τ) = 0 := congrFun hb (backSmall τ)
  rw [h1, mul_zero, add_zero]
  rfl

/-! ## §2. The Bockstein on the ladder: `Sq¹(xpow 2) = 0` -/

private theorem cmk_eq_iff' {X : TopCat} {n : ℕ} (z w : LinearMap.ker (coboundaryₗ X n)) :
    (Submodule.Quotient.mk z : Cohomology X n) = Submodule.Quotient.mk w
      ↔ (z : SingularCochain X n) - w ∈ coboundaryRange X n := by
  refine (Submodule.Quotient.eq _).trans ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]

/-- The `x ⌣ x` cocycle (the cup-shaped representative of `xpow 2`). -/
noncomputable def xxRep : LinearMap.ker (coboundaryₗ (TopCat.of RP4) 2) :=
  ⟨cup xRep.1 xRep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 xRep.1
    (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp xRep.2))⟩

/-- `xpow 2` carried by the cup-shaped representative. -/
theorem xpow_two_eq_mk_xxRep : xpow 2 = Cohomology.mk (TopCat.of RP4) 2 xxRep := by
  rw [xpow_two_eq_cupH, xpow_one_eq]
  show cupH (Submodule.Quotient.mk xRep) (Submodule.Quotient.mk xRep) = _
  rw [cupH_mk_mk]
  rfl

/-- **`[(x⌣x) ⌣ x] = xpow 3`** — the `(2,0)`-seeded Leibniz applied to the cup-shaped
representative. -/
theorem mk_cup_xxRep_xRep : Cohomology.mk (TopCat.of RP4) 3
    ⟨cup (p := 2) (q := 1) xxRep.1 xRep.1, LinearMap.mem_ker.mpr (cup_cocycle xxRep.1 xRep.1
      (LinearMap.mem_ker.mp xxRep.2) (LinearMap.mem_ker.mp xRep.2))⟩ = xpow 3 := by
  have step := smithCoConnecting_cup xxRep ⟨oneC, oneC_mem_ker⟩
  have h1 : xpow 3 = smithCoConnecting 2 (Cohomology.mk (TopCat.of RP4) (2 + 0)
      ⟨cup (p := 2) (q := 0) xxRep.1 oneC, LinearMap.mem_ker.mpr (cup_cocycle xxRep.1 oneC
        (LinearMap.mem_ker.mp xxRep.2) (LinearMap.mem_ker.mp oneC_mem_ker))⟩) := by
    show smithCoConnecting 2 (xpow 2) = _
    rw [xpow_two_eq_mk_xxRep, mk_eq_mk_cup_one xxRep]
  rw [h1, step]
  rfl

/-- **`[x ⌣ x²] = xpow 3`** — the `(1,1)`-Leibniz form. -/
theorem mk_cup_xRep_x2Rep : Cohomology.mk (TopCat.of RP4) 3
    ⟨cup (p := 1) (q := 2) xRep.1 x2Rep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 x2Rep.1
      (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp x2Rep.2))⟩ = xpow 3 := by
  have step := smithCoConnecting_cup xRep xRep
  have h1 : xpow 3 = smithCoConnecting 2 (Cohomology.mk (TopCat.of RP4) (1 + 1)
      ⟨cup (p := 1) (q := 1) xRep.1 xRep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 xRep.1
        (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp xRep.2))⟩) := by
    show smithCoConnecting 2 (xpow 2) = _
    rw [xpow_two_eq_mk_xxRep]
    rfl
  rw [h1, step]
  rfl

/-- **The second-slot swap**: `[x ⌣ (x⌣x)] = xpow 3` — the two `xpow 2`-representatives differ
by a coboundary, which the cocycle-cup absorbs. -/
theorem mk_cup_xRep_xxRep : Cohomology.mk (TopCat.of RP4) 3
    ⟨cup (p := 1) (q := 2) xRep.1 xxRep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 xxRep.1
      (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp xxRep.2))⟩ = xpow 3 := by
  rw [← mk_cup_xRep_x2Rep]
  refine (cmk_eq_iff' _ _).mpr ?_
  have hdiff : (xxRep : SingularCochain (TopCat.of RP4) 2)
      - (x2Rep : SingularCochain (TopCat.of RP4) 2)
      ∈ coboundaryRange (TopCat.of RP4) 2 := by
    refine (cmk_eq_iff' xxRep x2Rep).mp ?_
    show Cohomology.mk (TopCat.of RP4) 2 xxRep = Cohomology.mk (TopCat.of RP4) 2 x2Rep
    rw [← xpow_two_eq_mk_xxRep, xpow_two_eq]
  obtain ⟨w, hw⟩ := hdiff
  refine ⟨cup xRep.1 w, ?_⟩
  show coboundary (TopCat.of RP4) (1 + 1) (cup xRep.1 w)
    = cup xRep.1 xxRep.1 - cup xRep.1 x2Rep.1
  rw [← cup_coboundary_right_11 xRep.1 w (LinearMap.mem_ker.mp xRep.2),
    show coboundary (TopCat.of RP4) 1 w = coboundaryₗ (TopCat.of RP4) 1 w from rfl, hw]
  have h := map_sub (cupₗ (X := TopCat.of RP4) 1 2 xRep.1)
    (xxRep : SingularCochain (TopCat.of RP4) 2) (x2Rep : SingularCochain (TopCat.of RP4) 2)
  simpa only [cupₗ_apply] using h

/-- **`Sq¹(xpow 2) = 0`** — Leibniz at `(1,1)` on the cup-shaped representative gives
`[x⌣x⌣x] + [x⌣x⌣x] = xpow 3 + xpow 3 = 0` (both association orders are `xpow 3`). -/
theorem Sq1_xpow_two : Sq1 (xpow 2) = 0 := by
  rw [xpow_two_eq_mk_xxRep]
  show Sq1 (Submodule.Quotient.mk xxRep) = 0
  rw [Sq1_apply]
  have hmem₁ : cup (p := 2) (q := 1) xxRep.1 xRep.1
      ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) 3) :=
    LinearMap.mem_ker.mpr (cup_cocycle _ _ (LinearMap.mem_ker.mp xxRep.2)
      (LinearMap.mem_ker.mp xRep.2))
  have hmem₂ : cup (p := 1) (q := 2) xRep.1 xxRep.1
      ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) 3) :=
    LinearMap.mem_ker.mpr (cup_cocycle _ _ (LinearMap.mem_ker.mp xRep.2)
      (LinearMap.mem_ker.mp xxRep.2))
  have hsplit : (⟨Sq1cochain (xxRep : SingularCochain (TopCat.of RP4) 2),
      Sq1cochain_cocycle _ xxRep.2⟩ : LinearMap.ker (coboundaryₗ (TopCat.of RP4) 3))
      = ⟨cup (p := 2) (q := 1) xxRep.1 xRep.1, hmem₁⟩
        + ⟨cup (p := 1) (q := 2) xRep.1 xxRep.1, hmem₂⟩ := by
    apply Subtype.ext
    show Sq1cochain (cup xRep.1 xRep.1) = _
    rw [Sq1cochain_cup_11 xRep.1 xRep.1 (LinearMap.mem_ker.mp xRep.2)
      (LinearMap.mem_ker.mp xRep.2),
      Sq1cochain_eq_cup_on_C1 xRep.1 xRep.2]
    rfl
  rw [hsplit]
  erw [Submodule.Quotient.mk_add]
  have h1 := mk_cup_xxRep_xRep
  have h2 := mk_cup_xRep_xxRep
  show Cohomology.mk (TopCat.of RP4) 3 ⟨cup (p := 2) (q := 1) xxRep.1 xRep.1, hmem₁⟩
    + Cohomology.mk (TopCat.of RP4) 3 ⟨cup (p := 1) (q := 2) xRep.1 xxRep.1, hmem₂⟩ = 0
  rw [h1, h2, ← two_smul (ZMod 2) (xpow 3), show (2 : ZMod 2) = 0 by decide, zero_smul]

/-! ## §3. `Sq¹(xpow 3) = xpow 4` and `μ(Sq¹ x³) = 1` -/

/-- **`[x² ⌣ (x⌣x)] = xpow 4`** — `cupH24` is class-level, so mixing the two `xpow 2`
representatives is free. -/
theorem mk_cup_x2Rep_xxRep : Cohomology.mk (TopCat.of RP4) 4
    ⟨cup (p := 2) (q := 2) x2Rep.1 xxRep.1, LinearMap.mem_ker.mpr (cup_cocycle x2Rep.1 xxRep.1
      (LinearMap.mem_ker.mp x2Rep.2) (LinearMap.mem_ker.mp xxRep.2))⟩ = xpow 4 := by
  rw [xpow_four_eq_cupH24]
  nth_rewrite 1 [xpow_two_eq]
  nth_rewrite 1 [xpow_two_eq_mk_xxRep]
  show _ = cupH24 (Submodule.Quotient.mk x2Rep) (Submodule.Quotient.mk xxRep)
  rw [cupH24_mk_mk]
  rfl

/-- **`Sq¹(xpow 3) = xpow 4`** — Leibniz at `(2,1)` on `[x² ⌣ x]`: the `Sq¹x²`-term is the cup
of a coboundary (`Sq¹(xpow 2) = 0`) and dies; the other term is `x² ⌣ x² = xpow 4`. -/
theorem Sq1_xpow_three : Sq1 (xpow 3) = xpow 4 := by
  rw [xpow_three_eq]
  show Sq1 (Submodule.Quotient.mk
    (⟨cup (p := 2) (q := 1) x2Rep.1 xRep.1, LinearMap.mem_ker.mpr
      (cup_cocycle x2Rep.1 xRep.1 (LinearMap.mem_ker.mp x2Rep.2)
        (LinearMap.mem_ker.mp xRep.2))⟩ : LinearMap.ker (coboundaryₗ (TopCat.of RP4) 3)))
    = xpow 4
  rw [Sq1_apply]
  -- the Sq¹x²-term: Sq1cochain x2Rep is a coboundary
  have hzero : Sq1cochain (x2Rep : SingularCochain (TopCat.of RP4) 2)
      ∈ coboundaryRange (TopCat.of RP4) 3 := by
    have h0 : Sq1 (xpow 2) = 0 := Sq1_xpow_two
    rw [xpow_two_eq] at h0
    have h1 : Sq1 (Submodule.Quotient.mk x2Rep) = 0 := h0
    rw [Sq1_apply] at h1
    have h2 := (Submodule.Quotient.mk_eq_zero _).mp h1
    simpa only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using h2
  obtain ⟨w, hw⟩ := hzero
  have hmem₁ : cup (p := 3) (q := 1) (Sq1cochain (x2Rep : SingularCochain (TopCat.of RP4) 2))
      xRep.1 ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) 4) :=
    LinearMap.mem_ker.mpr (cup_cocycle _ _
      (Sq1cochain_cocycle _ x2Rep.2) (LinearMap.mem_ker.mp xRep.2))
  have hmem₂ : cup (p := 2) (q := 2) x2Rep.1 xxRep.1
      ∈ LinearMap.ker (coboundaryₗ (TopCat.of RP4) 4) :=
    LinearMap.mem_ker.mpr (cup_cocycle _ _ (LinearMap.mem_ker.mp x2Rep.2)
      (LinearMap.mem_ker.mp xxRep.2))
  have hsplit : (⟨Sq1cochain (cup (p := 2) (q := 1) x2Rep.1 xRep.1),
      Sq1cochain_cocycle _ (LinearMap.mem_ker.mpr (cup_cocycle x2Rep.1 xRep.1
        (LinearMap.mem_ker.mp x2Rep.2) (LinearMap.mem_ker.mp xRep.2)))⟩ :
      LinearMap.ker (coboundaryₗ (TopCat.of RP4) 4))
      = ⟨_, hmem₁⟩ + ⟨_, hmem₂⟩ := by
    apply Subtype.ext
    show Sq1cochain (cup x2Rep.1 xRep.1) = _
    rw [Sq1cochain_cup_21 x2Rep.1 xRep.1 (LinearMap.mem_ker.mp x2Rep.2)
      (LinearMap.mem_ker.mp xRep.2),
      Sq1cochain_eq_cup_on_C1 xRep.1 xRep.2]
    rfl
  rw [hsplit]
  erw [Submodule.Quotient.mk_add]
  -- first term: cup (δw) x = δ(w ⌣ x), a coboundary → class 0
  have hfirst : (Submodule.Quotient.mk (⟨_, hmem₁⟩ :
      LinearMap.ker (coboundaryₗ (TopCat.of RP4) 4)) : Cohomology (TopCat.of RP4) 4) = 0 := by
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    refine ⟨cup w xRep.1, ?_⟩
    show coboundary (TopCat.of RP4) 3 (cup w xRep.1)
      = cup (Sq1cochain (x2Rep : SingularCochain (TopCat.of RP4) 2)) xRep.1
    rw [← cup_coboundary_left_31 w xRep.1 (LinearMap.mem_ker.mp xRep.2),
      show coboundary (TopCat.of RP4) 2 w = coboundaryₗ (TopCat.of RP4) 2 w from rfl, hw]
  rw [hfirst, zero_add]
  exact mk_cup_x2Rep_xxRep

/-- **`μ(Sq¹(xpow 3)) = 1`** — the Bockstein value that certifies `v₁ = x` (M4-c7). -/
theorem mu_Sq1_xpow_three :
    (SKEFTHawking.SingularPD4Instances.poincareDual4Mid_of_closed (M := RP4)).mu
      (Sq1 (xpow 3)) = 1 := by
  rw [Sq1_xpow_three]
  exact SKEFTHawking.RP4WuAssembly.mu_xpow_four

/-! ## §4. `v₁ = x` (M4-c7) -/

open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWuFormula

/-- The canonical `δS`-representative of `xpow 3`. -/
noncomputable def x3Rep : LinearMap.ker (coboundaryₗ (TopCat.of RP4) 3) :=
  ⟨connectingCochain 2 x2Rep.1, LinearMap.mem_ker.mpr
    (connectingCochain_mem_ker _ (LinearMap.mem_ker.mp x2Rep.2))⟩

theorem xpow_three_eq_mk_x3Rep : xpow 3 = Cohomology.mk (TopCat.of RP4) 3 x3Rep := by
  show smithCoConnecting 2 (xpow 2) = _
  rw [xpow_two_eq, smithCoConnecting_mk]
  rfl

/-- **`[x ⌣ x³] = xpow 4`** — the `(1,3)`-cup against the canonical `xpow 3` representative. -/
theorem mk_cup_xRep_x3Rep : Cohomology.mk (TopCat.of RP4) 4
    ⟨cup (p := 1) (q := 3) xRep.1 x3Rep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 x3Rep.1
      (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp x3Rep.2))⟩ = xpow 4 := by
  have step := smithCoConnecting_cup xRep x2Rep
  have h1 : xpow 4 = smithCoConnecting 3 (Cohomology.mk (TopCat.of RP4) (1 + 2)
      ⟨cup (p := 1) (q := 2) xRep.1 x2Rep.1, LinearMap.mem_ker.mpr (cup_cocycle xRep.1 x2Rep.1
        (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp x2Rep.2))⟩) := by
    show smithCoConnecting 3 (xpow 3) = _
    rw [mk_cup_xRep_x2Rep]
  rw [h1, step]
  rfl

/-- **`μ(x ⌣₁₃ x³) = 1`** — the `(1,3)` pairing value of the generators. -/
theorem mu_cupH13_xpow1_xpow3 :
    (poincareDual4Mid_of_closed (M := RP4)).mu (cupH13 (xpow 1) (xpow 3)) = 1 := by
  rw [xpow_one_eq, xpow_three_eq_mk_x3Rep]
  show (poincareDual4Mid_of_closed (M := RP4)).mu
    (cupH13 (Submodule.Quotient.mk xRep) (Submodule.Quotient.mk x3Rep)) = 1
  rw [cupH13_mk_mk]
  have h := mk_cup_xRep_x3Rep
  show (poincareDual4Mid_of_closed (M := RP4)).mu (Cohomology.mk (TopCat.of RP4) 4 _) = 1
  rw [show (Cohomology.mk (TopCat.of RP4) 4 ⟨cup xRep.1 x3Rep.1, cup_cocycle xRep.1 x3Rep.1
      (LinearMap.mem_ker.mp xRep.2) (LinearMap.mem_ker.mp x3Rep.2) |> LinearMap.mem_ker.mpr⟩ :
      Cohomology (TopCat.of RP4) 4) = xpow 4 from h]
  exact SKEFTHawking.RP4WuAssembly.mu_xpow_four

/-- **`v₁ = x`** — the first Wu class of `ℝP⁴` is the ladder generator: both classes induce
the same `(1,3)`-pairing functional (tested on the one-dimensional `H³`: the cup value is `1`
by `mu_cupH13_xpow1_xpow3` and the Bockstein value is `1` by `mu_Sq1_xpow_three`), and the
pairing is injective. -/
theorem wuClass1_eq_xpow1 :
    wuClass1 (poincareDual4Lo_of_closed (M := RP4)) = xpow 1 := by
  apply (poincareDual4Lo_of_closed (M := RP4)).nondeg₁₃
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply]
  have hv := wu_relation_v1 (poincareDual4Lo_of_closed (M := RP4)) y
  rw [show ((poincareDual4Lo_of_closed (M := RP4)).cup13
      (wuClass1 (poincareDual4Lo_of_closed (M := RP4)))) y
      = (poincareDual4Lo_of_closed (M := RP4)).cup13
        (wuClass1 (poincareDual4Lo_of_closed (M := RP4))) y from rfl, hv]
  obtain ⟨c, rfl⟩ := cohomology_eq_smul_xpow (by norm_num) y
  rw [map_smul, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  congr 1
  · show (poincareDual4Mid_of_closed (M := RP4)).mu (Sq1 (xpow 3)) = _
    rw [mu_Sq1_xpow_three]
    show _ = (poincareDual4Mid_of_closed (M := RP4)).mu (cupH13 (xpow 1) (xpow 3))
    rw [mu_cupH13_xpow1_xpow3]

end SKEFTHawking.RP4BocksteinAssembly
