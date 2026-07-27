/-
# The mod-2 detection of `∂₃[T⁴]`: discharging the degree-3 puncture crux

`KummerPunctureH3Saturation` reduced the 2-torsion-freeness of `H₃(T⁴°;ℤ)` to the single statement
`redHomology (∂₃[T⁴]) ≠ 0`. This module proves that statement, and so ships
`H₃(T⁴°;ℤ)` 2-torsion-freeness UNCONDITIONALLY.

**Why the mod-2 side is the cheap side.** Over `ℤ/2` every closed manifold is orientable: the local
groups `H₄(M|x;ℤ/2) ≅ ℤ/2` have a unique generator, so the on-main tower supplies the fundamental
class `[M]₂` and the *bijectivity* of the point restriction `ρ_x` unconditionally
(`SingularFundamentalClass.localDegree_bijective`, Hatcher 3.26). That bijectivity is exactly the
statement that a class of `H₄(T⁴;ℤ/2)` is detected at ANY single point — so a subset `S ⊆ T⁴` that
misses one point `y` has `im(H₄(S;ℤ/2) → H₄(T⁴;ℤ/2)) = 0` (§3): the composite through
`H₄(T⁴, T⁴∖y;ℤ/2)` is `homProj ∘ homIncl = 0`, and `ρ_y` is injective.

Both pieces of the puncture cover miss a point:
* `thickA` misses every fixed point (it is the complement of the open half-balls, §2);
* `ballsV` misses `witnessPoint = (i,1,1,1)`, which is at distance `≥ 1` from every point of `{±1}⁴`
  while each closed chart ball has metric radius `≤ 1/2` (§2).

So the mod-2 MV sum `Σ₄ : H₄(thickA;ℤ/2) ⊕ H₄(ballsV;ℤ/2) → H₄(T⁴;ℤ/2)` is the ZERO map, and mod-2
MV exactness at `H₄(T⁴)` makes `δ₃` injective (§4). Since `redHomology (T⁴) 4` is surjective — the
rank-UCT core `SphereProdHTwoMod2.redHomology_surjective` fed by the banked
`torusFourH3_twoTorsionFree` — the reduction of `[T⁴]` generates `H₄(T⁴;ℤ/2) ∋ [T⁴]₂ ≠ 0`, hence is
itself nonzero (§5). Transporting along the `δ`-reduction square
(`SingularMayerVietorisRedCompatInt.redHomology_mvDeltaInt`) gives `red(∂₃[T⁴]) ≠ 0` (§6).

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1** `torusFourChartedE4` — `T⁴` as a `ChartedSpace (𝓔⁴)`, the model the closed-manifold mod-2
  fundamental-class tower requires (Mathlib's product atlas lands on `ModelProd`, which carries no
  norm; transported along a model homeomorphism).
* **§2** `fixedOne_not_mem_thickA`, `witnessPoint_not_mem_ballsV` — the two missed points.
* **§3** `topMap_eq_zero_of_subset_compl` — a subset missing a point has zero image in `H₄(T⁴;ℤ/2)`.
* **§4** `puncMvDelta3_mod2_injective` — the mod-2 puncture connecting map is injective.
* **§5** `redHomology_torusFourFundamentalClass_ne_zero` — `[T⁴]` survives reduction.
* **§6** `red_puncDelta3_fundamentalClass_ne_zero` and the headline
  `thickA_H3_twoTorsionFree` — `H₃(T⁴°;ℤ) = H₃(thickA;ℤ)` is 2-torsion-free, UNCONDITIONALLY.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureH3Saturation
import SKEFTHawking.SingularMayerVietorisRedCompatInt
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish
import SKEFTHawking.SphereProdHTwoMod2
import SKEFTHawking.KummerFreeQuotient

namespace SKEFTHawking.KummerPunctureH3Mod2

open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus (fixedSet mem_fixedSet_iff centeredChartParam
  centeredChartParam_zero sqNorm le_dist_c1)
open SKEFTHawking.KummerInvolution (negOne coe_negOne)
open SKEFTHawking.KummerPunctureBalls (thickA ballsV halfBall halfD4o closedBallT
  dist_le_of_mem_closedBallT punc_hcov)
open SKEFTHawking.KummerFreeQuotient (witnessPoint circleI coe_circleI)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl mvHomSum mvDelta mv_exact_ambient)
open SKEFTHawking.SingularFundamentalClass (fundamentalClass restrictHomologyToPoint)
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish
  (restrictHomologyToPoint_eq_homProj homProj_localPoint_injective)

noncomputable section

/-! ## §1. `T⁴` as a charted space on `𝓔⁴` -/

/-- **Transport of a charted structure along a homeomorphism of models.** `ChartedSpace` is data:
composing every chart with a model homeomorphism produces a charted structure on the new model. Needed
because Mathlib's product atlas for `T⁴ = (S¹)⁴` lands on `ModelProd 𝓔¹ (ModelProd 𝓔¹ (ModelProd 𝓔¹ 𝓔¹))`,
a type synonym carrying no normed structure — so the project's `ManifoldModelTransport`
(continuous-linear-equiv) transport does not apply, while a plain homeomorphism does. -/
@[reducible] def transportChartedSpaceHomeo {H H' M : Type*} [TopologicalSpace H]
    [TopologicalSpace H'] [TopologicalSpace M] [ChartedSpace H M] (e : H ≃ₜ H') :
    ChartedSpace H' M where
  atlas := (fun c : OpenPartialHomeomorph M H => c.trans e.toOpenPartialHomeomorph) '' (atlas H M)
  chartAt x := (chartAt H x).trans e.toOpenPartialHomeomorph
  mem_chart_source x := by simp [mem_chart_source]
  chart_mem_atlas x := ⟨chartAt H x, chart_mem_atlas H x, rfl⟩

/-- The product model of the `T⁴` atlas. -/
abbrev T4Model : Type :=
  ModelProd (EuclideanSpace ℝ (Fin 1))
    (ModelProd (EuclideanSpace ℝ (Fin 1))
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))))

/-- **The model homeomorphism `𝓔¹ × 𝓔¹ × 𝓔¹ × 𝓔¹ ≃ₜ 𝓔⁴`** — any two real normed spaces of equal
finite dimension are continuously linearly isomorphic (`1 + 1 + 1 + 1 = 4`). -/
def torusFourModelHomeo : T4Model ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  (Classical.choice (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
    (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) ×
      EuclideanSpace ℝ (Fin 1))
    (F := EuclideanSpace ℝ (Fin 4)) (by simp))).toHomeomorph

/-- **`T⁴` as a `𝓔⁴`-charted space** — the structure the closed-manifold mod-2 fundamental-class
tower (`SingularFundamentalClass`) consumes. Scoped, so it cannot collide with the ambient product
atlas elsewhere. -/
scoped instance torusFourChartedE4 : ChartedSpace (EuclideanSpace ℝ (Fin 4)) TorusFour :=
  transportChartedSpaceHomeo (H := T4Model) (M := TorusFour) torusFourModelHomeo

/-- The same charted structure in the `m' + 2` spelling the mod-2 fundamental-class tower states its
hypotheses with (`m' = 2`). Instance search does not reduce the literal `2 + 2` to `4`, so the
`Fin (2 + 2)` form is registered separately; the two are definitionally the same structure. -/
scoped instance torusFourChartedE4' :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) TorusFour :=
  torusFourChartedE4

/-- `T⁴` is preconnected (it is path-connected, `KummerH0T4.torusFour_pathConnected`). -/
scoped instance torusFourPreconnected : PreconnectedSpace TorusFour :=
  haveI := SKEFTHawking.KummerH0T4.torusFour_pathConnected
  inferInstance

/-! ## §2. Each cover piece misses a point -/

/-- `(1,1,1,1)` is one of the sixteen `τ`-fixed points. -/
theorem fixedOne_mem_fixedSet : ((1, 1, 1, 1) : TorusFour) ∈ fixedSet :=
  (mem_fixedSet_iff _).mpr ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- **`thickA` misses the fixed point `(1,1,1,1)`** — `thickA` is the complement of the open
half-balls, and each fixed point is the centre of its own half-ball (`centeredChartParam c 0 = c`,
`sqNorm 0 = 0 < 1/16`). -/
theorem fixedOne_not_mem_thickA : ((1, 1, 1, 1) : TorusFour) ∉ thickA := by
  intro hmem
  refine (SKEFTHawking.KummerPunctureBalls.mem_thickA_iff.mp hmem) _ fixedOne_mem_fixedSet ?_
  refine ⟨0, ?_, centeredChartParam_zero _⟩
  show sqNorm (0 : ℝ × ℝ × ℝ × ℝ) < 1 / 16
  simp [sqNorm]

/-- **`i` is at distance `≥ 1` from each square root of unity** — the imaginary part of `i − (±1)`
is `1`, and `|im| ≤ ‖·‖`. (The banked `half_le_dist_circleI` only records the `≥ 1/2` consequence,
which is too weak to escape the CLOSED chart balls of radius `1/2`.) -/
theorem one_le_dist_circleI {z : Circle} (hz : z = 1 ∨ z = negOne) : (1 : ℝ) ≤ dist circleI z := by
  show (1 : ℝ) ≤ dist ((circleI : Circle) : ℂ) ((z : Circle) : ℂ)
  rw [coe_circleI, Complex.dist_eq]
  rcases hz with rfl | rfl
  · rw [Circle.coe_one]
    calc (1 : ℝ) = |(Complex.I - 1).im| := by simp
      _ ≤ ‖Complex.I - 1‖ := Complex.abs_im_le_norm _
  · rw [coe_negOne]
    calc (1 : ℝ) = |(Complex.I - (-1)).im| := by simp
      _ ≤ ‖Complex.I - (-1)‖ := Complex.abs_im_le_norm _

/-- **`ballsV` misses `witnessPoint = (i,1,1,1)`** — every point of a closed chart ball is within
metric distance `1/2` of its centre (`dist_le_of_mem_closedBallT`), while `witnessPoint` is at
distance `≥ 1` from every fixed centre (its first coordinate already is). -/
theorem witnessPoint_not_mem_ballsV : witnessPoint ∉ ballsV := by
  intro hmem
  obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp hmem
  have hd : dist witnessPoint c ≤ 1 / 2 := dist_le_of_mem_closedBallT hxc
  have hc1 : c.1 = 1 ∨ c.1 = negOne := ((mem_fixedSet_iff c).mp hc).1
  have h1 : (1 : ℝ) ≤ dist witnessPoint.1 c.1 := one_le_dist_circleI hc1
  have hle : dist witnessPoint.1 c.1 ≤ dist witnessPoint c :=
    le_dist_c1 witnessPoint c
  linarith

/-! ## §3. A subset missing a point has zero image in `H₄(T⁴;ℤ/2)` -/

/-- **`S ⊆ {y}ᶜ` ⟹ `H₄(S;ℤ/2) → H₄(T⁴;ℤ/2)` is the zero map.** The inclusion factors through
`{y}ᶜ`, and the pair-LES composite `homProj_{(T⁴,{y}ᶜ)} ∘ homIncl_{{y}ᶜ}` vanishes; since the
point restriction `homProj {y}ᶜ` is INJECTIVE in the top degree (Hatcher 3.26 kernel-triviality,
`homProj_localPoint_injective` — unconditional over `ℤ/2`), the class itself vanishes. -/
theorem topMap_eq_zero_of_subset_compl {S : Set TorusFour} {y : TorusFour}
    (hS : S ⊆ ({y}ᶜ : Set TorusFour))
    (u : SKEFTHawking.SingularHomologyMod2.Homology
      (sub (X := TopCat.of TorusFour) S) 4) :
    SKEFTHawking.SingularFunctoriality.Homology.map
        (ambIncl (X := TopCat.of TorusFour) S) 4 u = 0 := by
  have hfac : ambIncl (X := TopCat.of TorusFour) S
      = (ambIncl (X := TopCat.of TorusFour) ({y}ᶜ : Set TorusFour)).comp (subIncl hS) :=
    ContinuousMap.ext fun _ => rfl
  rw [hfac, SKEFTHawking.SingularFunctoriality.Homology.map_comp]
  set v := SKEFTHawking.SingularFunctoriality.Homology.map
    (subIncl (X := TopCat.of TorusFour) hS) 4 u with hv
  show SKEFTHawking.SingularFunctoriality.Homology.map
      (ambIncl (X := TopCat.of TorusFour) ({y}ᶜ : Set TorusFour)) 4 v = 0
  rw [SKEFTHawking.SingularMayerVietorisLES.Homology.map_ambIncl]
  refine homProj_localPoint_injective (m' := 2) (M := TorusFour) y ?_
  rw [SKEFTHawking.SingularPairLES.homProj_homIncl, map_zero]

/-! ## §4. The mod-2 puncture connecting map is injective -/

/-- **The mod-2 MV sum `Σ₄` of the puncture cover is ZERO.** Both pieces miss a point of `T⁴`
(`thickA` misses `(1,1,1,1)`, `ballsV` misses `witnessPoint`), so §3 kills each summand. -/
theorem puncMvHomSum4_mod2_eq_zero
    (p : SKEFTHawking.SingularHomologyMod2.Homology (sub (X := TopCat.of TorusFour) thickA) 4 ×
      SKEFTHawking.SingularHomologyMod2.Homology (sub (X := TopCat.of TorusFour) ballsV) 4) :
    mvHomSum (X := TopCat.of TorusFour) thickA ballsV 4 p = 0 := by
  show SKEFTHawking.SingularFunctoriality.Homology.map
      (ambIncl (X := TopCat.of TorusFour) thickA) 4 p.1
    + SKEFTHawking.SingularFunctoriality.Homology.map
      (ambIncl (X := TopCat.of TorusFour) ballsV) 4 p.2 = 0
  rw [topMap_eq_zero_of_subset_compl (y := ((1, 1, 1, 1) : TorusFour))
      (fun _ hx => fun hy => fixedOne_not_mem_thickA (hy ▸ hx)),
    topMap_eq_zero_of_subset_compl (y := witnessPoint)
      (fun _ hx => fun hy => witnessPoint_not_mem_ballsV (hy ▸ hx)),
    add_zero]

/-- **The mod-2 degree-3 puncture connecting map `δ₃` is INJECTIVE.** MV exactness at `H₄(T⁴;ℤ/2)`
gives `ker δ₃ = im Σ₄`, and `Σ₄ = 0` (`puncMvHomSum4_mod2_eq_zero`). This is the mod-2 shadow of
"`H₄(T⁴°) = 0`" — obtained without any open-manifold top-vanishing theorem, purely from the fact that
each cover piece is detected at a point it misses. -/
theorem puncMvDelta3_mod2_ne_zero
    {w : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of TorusFour) 4} (hw : w ≠ 0) :
    mvDelta (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov w ≠ 0 := by
  intro h0
  obtain ⟨p, hp⟩ := (mv_exact_ambient (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov w).mp h0
  exact hw (by rw [← hp]; exact puncMvHomSum4_mod2_eq_zero p)

/-! ## §5. `[T⁴]` survives the mod-2 reduction -/

/-- **`redHomology [T⁴] ≠ 0`.** `H₃(T⁴;ℤ)` is 2-torsion-free (`torusFourH3_twoTorsionFree`, banked),
so the rank-UCT core `SphereProdHTwoMod2.redHomology_surjective` makes `redHomology (T⁴) 4`
surjective; and `H₄(T⁴;ℤ)` is generated by `[T⁴]`, so its reduction generates the whole of
`H₄(T⁴;ℤ/2)`. That group is nonzero — it contains the on-main mod-2 fundamental class
(`fundamentalClass_ne_zero`) — hence `red [T⁴] ≠ 0`. -/
theorem redHomology_torusFourFundamentalClass_ne_zero :
    SKEFTHawking.SingularHomologyInt.redHomology (TopCat.of TorusFour) 4
      SKEFTHawking.KummerHomologyT4Full.torusFourFundamentalClass ≠ 0 := by
  intro hzero
  have hsurj := SKEFTHawking.SphereProdHTwoMod2.redHomology_surjective
    (X := TopCat.of TorusFour) 3 SKEFTHawking.KummerPunctureH3.torusFourH3_twoTorsionFree
  have hall : ∀ y : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of TorusFour) 4, y = 0 := by
    intro y
    obtain ⟨c, hc⟩ := hsurj y
    obtain ⟨k, hk⟩ :=
      Submodule.mem_span_singleton.mp
        (show c ∈ Submodule.span ℤ
            {SKEFTHawking.KummerHomologyT4Full.torusFourFundamentalClass} by
          rw [SKEFTHawking.KummerHomologyT4Full.torusFourFundamentalClass_generates]; trivial)
    rw [← hc, ← hk, map_zsmul, hzero, smul_zero]
  exact SKEFTHawking.SingularFundamentalClass.fundamentalClass_ne_zero
    (m := 2) (M := TorusFour) ((1, 1, 1, 1) : TorusFour) (hall _)

/-! ## §6. The crux, discharged -/

/-- **THE CRUX: `red(∂₃[T⁴]) ≠ 0`.** Transport `[T⁴]`'s surviving reduction (§5) across the
Mayer–Vietoris `δ`-reduction square (`redHomology_mvDeltaInt`), then apply mod-2 injectivity of `δ₃`
(§4). This is exactly the input `KummerPunctureH3Saturation` isolated. -/
theorem red_puncDelta3_fundamentalClass_ne_zero :
    SKEFTHawking.SingularHomologyInt.redHomology
        (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3
        (SKEFTHawking.KummerPunctureH3Saturation.puncDelta3
          SKEFTHawking.KummerHomologyT4Full.torusFourFundamentalClass) ≠ 0 := by
  rw [SKEFTHawking.SingularMayerVietorisRedCompatInt.redHomology_mvDeltaInt
    (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov]
  exact puncMvDelta3_mod2_ne_zero redHomology_torusFourFundamentalClass_ne_zero

/-- **`H₃(T⁴°;ℤ) = H₃(thickA;ℤ) IS 2-TORSION-FREE — UNCONDITIONALLY.** The degree-3 puncture
residual of `KummerPunctureH3` is discharged: the banked reduction
(`thickA_H3_twoTorsionFree_of_delta3_saturated`) + the cyclic-image saturation criterion
(`KummerPunctureH3Saturation`) + the mod-2 detection of `∂₃[T⁴]` (§6). -/
theorem thickA_H3_twoTorsionFree
    (x : SKEFTHawking.SingularHomologyInt.Homology (sub (X := TopCat.of TorusFour) thickA) 3)
    (hx : (2 : ℤ) • x = 0) : x = 0 :=
  SKEFTHawking.KummerPunctureH3Saturation.thickA_H3_twoTorsionFree_of_red_delta3_ne_zero
    red_puncDelta3_fundamentalClass_ne_zero x hx

end

end SKEFTHawking.KummerPunctureH3Mod2
