/-
# Phase 5q.H — K6′a Leg 2 FINISHER: `IsManifold` for the E-piece `ResE`

Completes `KummerResolutionPieceBoundary.lean`: the remaining 20/36 atlas transition pairs — the
**annulus-annulus** quadrant (4 pairs, product transitions through the single equatorial
trivialization) and the **annulus↔base** classes (16 pairs, whose fiber coordinate change is the
base-dependent unit twist `ζ = regDir(z)·w`) — and the final 6×6 dispatch
`isManifold_resE : IsManifold ((𝓡 3).prod (𝓡∂ 1)) k ResE`, the E-side smooth
manifold-with-boundary certificate that K6′b (the smooth weld) consumes opposite the T⁴°-side
`KummerShellChart` certificate.

## Architecture

* §1 — the `ℂ ≅ 𝓔²` bridge upgraded to `C^∞` (`contDiff_toE2`/`contDiff_ofE2`) and the
  **rotation** `rotE2 u = toE2 ∘ (u·) ∘ ofE2` with its bilinear smoothness; the two twist
  functions `twistU = regDir ∘ ofE2` (forward) and `twistUConj` (inverse), `C^∞` on the annulus.
* §2 — `contDiffOn_reshapeConjTwist`: the `contDiffOn_reshapeConj` generalization whose fiber
  block may depend on the base coordinate (the twist forces this).
* §3 — the four **twisted fiber transition classes** `contDiffOn_twistFiberTrans_{II,IC,CI,CC}`:
  recover through `D₀`, rotate by the unit `U b`, chart through `D₁` — `C^k` in the joint
  (base, fiber) model coordinates.
* §4 — the three **general transition theorems**: annulus-annulus (`gBase = id`, untwisted §O
  fiber), chart0/chart1→annulus and annulus→chart0/chart1 (`gBase ∈ {id, toE2∘regInv∘ofE2}`,
  twisted fiber).
* §5 — the 20 pair instantiations and **`isManifold_resE`**, the 6×6 dispatch.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerResolutionPieceBoundary

namespace SKEFTHawking.KummerResolutionPieceManifold

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open Metric Set
open scoped Manifold

open SKEFTHawking.DiskChartGeneric (NDisk NSphere ballClamp diskDir assemble splitLo
  diskCollarChart diskInteriorChart ballClamp_coe_of_norm_le diskDir_coe diskDir_scaled
  collar_invFun_mem toLp_ofLp_fin_one)

noncomputable section

/-! ## §1. The `C^∞` bridge and the unit twist -/

/-- `toE2` is `C^m` (it is `ℝ`-linear). -/
theorem contDiff_toE2 {m : WithTop ℕ∞} : ContDiff ℝ m toE2 := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  -- v4.32: `simpa`'s closing step no longer unifies the bundled coercion `⇑Complex.reCLM` with the
  -- goal's eta-expanded `fun x => x.re` (defeq only through `ContinuousLinearMap`'s `DFunLike`
  -- structure, which it will not unfold). Hand simp the funext-derived equation for the UNAPPLIED
  -- coercion so the term is rewritten into the goal's shape before the close.
  · simpa [show (⇑Complex.reCLM : ℂ → ℝ) = fun x => x.re from funext Complex.reCLM_apply] using
      Complex.reCLM.contDiff
  · simpa [show (⇑Complex.imCLM : ℂ → ℝ) = fun x => x.im from funext Complex.imCLM_apply] using
      Complex.imCLM.contDiff

/-- `ofE2` is `C^m` (it is `ℝ`-linear). -/
theorem contDiff_ofE2 {m : WithTop ℕ∞} : ContDiff ℝ m ofE2 := by
  have heq : ofE2 = fun v : EuclideanSpace ℝ (Fin 2) =>
      ((v.ofLp 0 : ℝ) : ℂ) + ((v.ofLp 1 : ℝ) : ℂ) * Complex.I := by
    funext v
    apply Complex.ext <;> simp [ofE2]
  rw [heq]
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 0).comp PiLp.contDiff_ofLp)).add
    ((Complex.ofRealCLM.contDiff.comp ((contDiff_apply ℝ ℝ 1).comp PiLp.contDiff_ofLp)).mul
      contDiff_const)

/-- The `ofE2` unpacking is norm-faithful (the `norm_toE2` mirror). -/
theorem norm_ofE2 (v : EuclideanSpace ℝ (Fin 2)) : ‖ofE2 v‖ = ‖v‖ := by
  rw [← norm_toE2, toE2_ofE2]

/-- **Rotation by `u ∈ ℂ` on `𝓔²`** — complex multiplication transported through the bridge. For
`‖u‖ = 1` this is the rotation implementing the annulus trivialization's fiber twist. -/
def rotE2 (u : ℂ) (a : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  toE2 (u * ofE2 a)

theorem norm_rotE2 (u : ℂ) (a : EuclideanSpace ℝ (Fin 2)) : ‖rotE2 u a‖ = ‖u‖ * ‖a‖ := by
  rw [rotE2, norm_toE2, norm_mul, norm_ofE2]

/-- The rotation is jointly `C^m` in `(u, a)` (bilinear through the linear bridge). -/
theorem contDiff_rotE2 {m : WithTop ℕ∞} :
    ContDiff ℝ m (fun p : ℂ × EuclideanSpace ℝ (Fin 2) => rotE2 p.1 p.2) :=
  contDiff_toE2.comp ((contDiff_fst (E := ℂ) (F := EuclideanSpace ℝ (Fin 2))).mul
    (contDiff_ofE2.comp contDiff_snd))

theorem ofE2_smul (c : ℝ) (a : EuclideanSpace ℝ (Fin 2)) : ofE2 (c • a) = c • ofE2 a := by
  apply Complex.ext <;> simp [ofE2, Complex.real_smul]

theorem toE2_smul (c : ℝ) (z : ℂ) : toE2 (c • z) = c • toE2 z := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> simp [toE2, Complex.real_smul]

/-- The rotation is `ℝ`-homogeneous in its vector argument. -/
theorem rotE2_smul (u : ℂ) (c : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    rotE2 u (c • a) = c • rotE2 u a := by
  rw [rotE2, ofE2_smul, mul_smul_comm, toE2_smul, rotE2]

/-- **The forward unit twist** `b ↦ regDir (ofE2 b)` — the annulus trivialization's fiber rotation
factor, as a function of the base model coordinate. -/
def twistU (b : EuclideanSpace ℝ (Fin 2)) : ℂ := regDir (ofE2 b)

/-- **The inverse unit twist** `b ↦ conj (regDir (ofE2 b))` — the fiber rotation of the inverse
trivialization (`recoverFiber0`). -/
def twistUConj (b : EuclideanSpace ℝ (Fin 2)) : ℂ := (starRingEnd ℂ) (regDir (ofE2 b))

theorem norm_twistU {b : EuclideanSpace ℝ (Fin 2)} (hb : 1 / 2 ≤ ‖b‖) : ‖twistU b‖ = 1 :=
  norm_regDir_of (by rw [norm_ofE2]; exact hb)

theorem norm_twistUConj {b : EuclideanSpace ℝ (Fin 2)} (hb : 1 / 2 ≤ ‖b‖) : ‖twistUConj b‖ = 1 := by
  rw [twistUConj, Complex.norm_conj]
  exact norm_twistU hb

theorem contDiffOn_twistU {k : WithTop ℕ∞} :
    ContDiffOn ℝ k twistU {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} :=
  (contDiffOn_regDir.of_le le_top).comp contDiff_ofE2.contDiffOn
    (fun b hb => by rw [Set.mem_setOf_eq, norm_ofE2]; exact hb)

theorem contDiffOn_twistUConj {k : WithTop ℕ∞} :
    ContDiffOn ℝ k twistUConj {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} :=
  Complex.conjCLE.contDiff.comp_contDiffOn contDiffOn_twistU

/-- **The annulus base coordinate change** `toE2 ∘ regInv ∘ ofE2` (the `chart1`-side base map),
`C^k` on the annulus `{1/2 < ‖b‖}`. -/
theorem contDiffOn_toE2_regInv_ofE2 {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (fun b : EuclideanSpace ℝ (Fin 2) => toE2 (regInv (ofE2 b)))
      {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} :=
  contDiff_toE2.comp_contDiffOn ((contDiffOn_regInv.of_le le_top).comp contDiff_ofE2.contDiffOn
    (fun b hb => by rw [Set.mem_setOf_eq, norm_ofE2]; exact hb))

/-- A `chart0` point of the annulus region has base-annulus norm `1/2 < ‖z‖` (the welded partner
forces `‖z‖ = 1`, still in the annulus). -/
theorem mem_annulusRegion_chart0_norm {p : ResChart} (h : chart0 p ∈ annulusRegion) :
    1 / 2 < ‖(p.1 : ℂ)‖ := by
  rcases h with ⟨p', hp', hmk⟩ | ⟨q', hq', hmk⟩
  · rwa [chart0_inj_iff.mp hmk.symm]
  · have hg : glued p q' := chart0_eq_chart1_iff.mp hmk.symm
    rw [hg.1]; norm_num

/-- The `chart1` mirror of `mem_annulusRegion_chart0_norm`. -/
theorem mem_annulusRegion_chart1_norm {q : ResChart} (h : chart1 q ∈ annulusRegion) :
    1 / 2 < ‖(q.1 : ℂ)‖ := by
  rcases h with ⟨p', hp', hmk⟩ | ⟨q', hq', hmk⟩
  · have hg : glued p' q := chart0_eq_chart1_iff.mp hmk
    rw [hg.2.1, norm_inv, hg.1, inv_one]; norm_num
  · rwa [chart1_inj_iff.mp hmk.symm]

/-! ## §2. The base-coupled reshape conjugation wrapper

`contDiffOn_reshapeConj` (§P.0 of the Boundary module) assumed the fiber coordinate change is a pure
fiber map. The annulus↔base transitions violate this: their fiber change is the rotation by
`regDir z`, a function of the base coordinate. This wrapper generalizes: `gFiber` receives the base
model coordinate `splitLo 2 m.1` alongside the fiber block. -/

/-- **The base-coupled `reshapeModel`-conjugation smoothness wrapper.** Like
`contDiffOn_reshapeConj`, but the fiber coordinate change `gFiber` may depend on the (source) base
coordinate — as the annulus twist requires. -/
theorem contDiffOn_reshapeConjTwist {k : WithTop ℕ∞}
    {gBase : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {gFiber : EuclideanSpace ℝ (Fin 2) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)}
    {S : Set (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1))}
    {baseSet : Set (EuclideanSpace ℝ (Fin 2))}
    {fiberSet : Set (EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))}
    (hBase : ContDiffOn ℝ k gBase baseSet) (hFiber : ContDiffOn ℝ k gFiber fiberSet)
    (hmapBase : Set.MapsTo (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        splitLo 2 m.1) S baseSet)
    (hmapFiber : Set.MapsTo (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
        (splitLo 2 m.1, (WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp (Fin.last 2)), m.2))) S
        fiberSet) :
    ContDiffOn ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      ((assemble 2 (gBase (splitLo 2 m.1))
          ((gFiber (splitLo 2 m.1,
            (WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp (Fin.last 2)), m.2))).1.ofLp 0),
        (gFiber (splitLo 2 m.1,
          (WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp (Fin.last 2)), m.2))).2) :
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1))) S := by
  have hfibIn : ContDiff ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      ((splitLo 2 m.1, (WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp (Fin.last 2)), m.2)) :
        EuclideanSpace ℝ (Fin 2) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))) :=
    ContDiff.prodMk (contDiff_splitLo.comp contDiff_fst)
      (ContDiff.prodMk
        (PiLp.contDiff_toLp.comp (contDiff_pi.mpr fun _ =>
          (contDiff_apply ℝ ℝ (Fin.last 2)).comp (PiLp.contDiff_ofLp.comp contDiff_fst)))
        contDiff_snd)
  have hGF : ContDiffOn ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      gFiber (splitLo 2 m.1, (WithLp.toLp 2 (fun _ : Fin 1 => m.1.ofLp (Fin.last 2)), m.2))) S :=
    hFiber.comp hfibIn.contDiffOn hmapFiber
  have hGB : ContDiffOn ℝ k (fun m : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 1) =>
      gBase (splitLo 2 m.1)) S :=
    hBase.comp (contDiff_splitLo.comp contDiff_fst).contDiffOn hmapBase
  refine ContDiffOn.prodMk ?_ (contDiff_snd.comp_contDiffOn hGF)
  exact contDiff_assemble.comp_contDiffOn (hGB.prodMk
    (((contDiff_apply ℝ ℝ 0).comp (PiLp.contDiff_ofLp.comp contDiff_fst)).comp_contDiffOn hGF))

/-! ## §3. The twisted fiber transition classes

The annulus↔base fiber coordinate change: recover the fiber disk point through `D₀`, rotate by the
base-dependent unit `U b`, chart through `D₁` — in `(𝓡 1).prod (𝓡∂ 1)` model coordinates,
junk-totalized by `ballClamp`. The four classes (`D₀`, `D₁` ∈ {interior, collar}) mirror §O of the
Boundary module with the rotation inserted. -/

/-- **The twisted fiber transition function** (junk-totalized): recover through `D₀`, rotate by
`U b`, chart through `D₁`. -/
def twistFiberTrans (U : EuclideanSpace ℝ (Fin 2) → ℂ)
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (p : EuclideanSpace ℝ (Fin 2) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) :=
  ((𝓡 1).prod (𝓡∂ 1)) (D₁ (ballClamp 1 (rotE2 (U p.1)
    ((D₀.symm (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2)))))

/-- **The twisted fiber transition domain**: base coordinate in `bSet`, fiber block in the model
range, recovered point in `D₀.target`-position, rotated point in `D₁.source`. -/
def twistFiberSet (U : EuclideanSpace ℝ (Fin 2) → ℂ) (bSet : Set (EuclideanSpace ℝ (Fin 2)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1))) :
    Set (EuclideanSpace ℝ (Fin 2) × (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :=
  {p | p.1 ∈ bSet ∧ p.2 ∈ Set.range ↑((𝓡 1).prod (𝓡∂ 1)) ∧
    (((𝓡 1).prod (𝓡∂ 1)).symm p.2) ∈ D₀.target ∧
    ballClamp 1 (rotE2 (U p.1)
      ((D₀.symm (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2)))
      ∈ D₁.source}

/-- **Interior-target normal form is smooth**: `p ↦ (splitLo (G p), (G p)ₗₐₛₜ + 2)` is `C^k`
whenever `G` is. -/
theorem contDiffOn_interiorTargetForm {k : WithTop ℕ∞} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : Set E} {G : E → EuclideanSpace ℝ (Fin 2)}
    (hG : ContDiffOn ℝ k G T) :
    ContDiffOn ℝ k (fun p => ((splitLo 1 (G p),
      (WithLp.toLp 2 (fun _ : Fin 1 => (G p).ofLp (Fin.last 1) + 2) :
        EuclideanSpace ℝ (Fin 1))) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) T := by
  refine ContDiffOn.prodMk (contDiff_splitLo1.comp_contDiffOn hG) ?_
  have htoLp : ContDiff ℝ k (fun r : ℝ =>
      (WithLp.toLp 2 (fun _ : Fin 1 => r) : EuclideanSpace ℝ (Fin 1))) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => contDiff_id))
  exact htoLp.comp_contDiffOn
    ((((contDiff_apply ℝ ℝ (Fin.last 1)).comp PiLp.contDiff_ofLp).comp_contDiffOn hG).add
      contDiffOn_const)

/-- **Collar-target normal form is smooth**: `p ↦ (repr (stereoToFun (−u₁) (G p / ‖G p‖)), 1 − ‖G p‖)`
is `C^k` whenever `G` is, `G ≠ 0`, and the normalized image avoids the north pole. -/
theorem contDiffOn_collarTargetForm {k : WithTop ℕ∞} (u₁ : NSphere 1) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T : Set E} {G : E → EuclideanSpace ℝ (Fin 2)}
    (hG : ContDiffOn ℝ k G T) (hne : ∀ p ∈ T, G p ≠ 0)
    (hinner : ∀ p ∈ T, innerSL ℝ ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
      (‖G p‖⁻¹ • G p) ≠ 1) :
    ContDiffOn ℝ k (fun p => (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₁))).repr
        (stereoToFun ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1))) (‖G p‖⁻¹ • G p)),
      (WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖G p‖) : EuclideanSpace ℝ (Fin 1))) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) T := by
  refine ContDiffOn.prodMk ?_ ?_
  · exact (contDiffOn_reprStereoNormalize u₁).comp hG (fun p hp => ⟨hne p hp, hinner p hp⟩)
  · have htoLp : ContDiff ℝ k (fun r : ℝ =>
        (WithLp.toLp 2 (fun _ : Fin 1 => r) : EuclideanSpace ℝ (Fin 1))) :=
      PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun _ => contDiff_id))
    have hnorm : ContDiffOn ℝ k (fun p => ‖G p‖) T := fun p hp =>
      ((contDiffAt_norm ℝ (hne p hp)).comp_contDiffWithinAt p (hG p hp))
    exact htoLp.comp_contDiffOn (contDiffOn_const.sub hnorm)

/-- **Twisted fiber class II (interior → interior)**: the recovered interior point, rotated by the
unit `U b`, re-charted through the interior chart — `C^k` (fully polynomial modulo the twist). -/
theorem contDiffOn_twistFiberTrans_II {k : WithTop ℕ∞} {U : EuclideanSpace ℝ (Fin 2) → ℂ}
    {bSet : Set (EuclideanSpace ℝ (Fin 2))} (hU : ContDiffOn ℝ k U bSet)
    (hUnorm : ∀ b ∈ bSet, ‖U b‖ = 1) :
    ContDiffOn ℝ k
      (twistFiberTrans U (DiskChartGeneric.diskInteriorChart 1)
        (DiskChartGeneric.diskInteriorChart 1))
      (twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (DiskChartGeneric.diskInteriorChart 1)) := by
  have key : ∀ p ∈ twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (DiskChartGeneric.diskInteriorChart 1),
      ‖assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)‖ < 1 ∧ p.1 ∈ bSet := by
    intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have h : ‖assemble 1 p.2.1 (((𝓡∂ 1).symm p.2.2).val.ofLp 0 - 2)‖ < 1 := h3
    rw [hzval] at h
    exact ⟨h, h1⟩
  have hR : ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 2) ×
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
      rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)))
      (twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (DiskChartGeneric.diskInteriorChart 1)) :=
    contDiff_rotE2.comp_contDiffOn
      ((hU.comp contDiffOn_fst (fun p hp => (key p hp).2)).prodMk
        (contDiff_assembleShift1.comp contDiff_snd).contDiffOn)
  apply ContDiffOn.congr (f := fun p : EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
    ((splitLo 1 (rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))),
      (WithLp.toLp 2 (fun _ : Fin 1 =>
        (rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))).ofLp (Fin.last 1) + 2) :
        EuclideanSpace ℝ (Fin 1))) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  · exact contDiffOn_interiorTargetForm hR
  · intro p hp
    obtain ⟨hA, h1⟩ := key p hp
    obtain ⟨-, h2, -, -⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hrec : ((DiskChartGeneric.diskInteriorChart 1).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : EuclideanSpace ℝ (Fin (1 + 1)))
        = assemble 1 p.2.1 (p.2.2.ofLp 0 - 2) := by
      show (ballClamp 1 (assemble 1 p.2.1 (((𝓡∂ 1).symm p.2.2).val.ofLp 0 - 2)) :
          EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, ballClamp_coe_of_norm_le (le_of_lt hA)]
    have hRlt : ‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖ < 1 := by
      rw [norm_rotE2, hUnorm p.1 h1, one_mul]
      exact hA
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)) := by
      rw [hrec]
      exact ballClamp_coe_of_norm_le (le_of_lt hRlt)
    show (splitLo 1 ((ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))),
      WithLp.toLp 2 (fun _ : Fin 1 => ((ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))).ofLp (Fin.last 1) + 2)) = _
    rw [hcl]

/-- **Twisted fiber class CI (collar `u₀` → interior)**: the collar-recovered scaled sphere point,
rotated by the unit `U b`, re-charted through the interior chart — `C^k` (no denominators). -/
theorem contDiffOn_twistFiberTrans_CI {k : WithTop ℕ∞} (u₀ : NSphere 1)
    {U : EuclideanSpace ℝ (Fin 2) → ℂ}
    {bSet : Set (EuclideanSpace ℝ (Fin 2))} (hU : ContDiffOn ℝ k U bSet)
    (hUnorm : ∀ b ∈ bSet, ‖U b‖ = 1) :
    ContDiffOn ℝ k
      (twistFiberTrans U (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1))
      (twistFiberSet U bSet (diskCollarChart 1 u₀)
        (DiskChartGeneric.diskInteriorChart 1)) := by
  have key : ∀ p ∈ twistFiberSet U bSet (diskCollarChart 1 u₀)
        (DiskChartGeneric.diskInteriorChart 1),
      (0 ≤ p.2.2.ofLp 0 ∧ p.2.2.ofLp 0 < 1) ∧ p.1 ∈ bSet := by
    intro p hp
    obtain ⟨h1, h2, h3, -⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hge : (0 : ℝ) ≤ p.2.2.ofLp 0 := by
      have h := h2.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    have h : ((𝓡∂ 1).symm p.2.2).val.ofLp 0 < 1 := h3
    rw [hzval] at h
    exact ⟨⟨hge, h⟩, h1⟩
  have hR : ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 2) ×
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
      rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1)))))
      (twistFiberSet U bSet (diskCollarChart 1 u₀)
        (DiskChartGeneric.diskInteriorChart 1)) :=
    contDiff_rotE2.comp_contDiffOn
      ((hU.comp contDiffOn_fst (fun p hp => (key p hp).2)).prodMk
        ((contDiff_const.sub ((contDiff_apply ℝ ℝ 0).comp
            (PiLp.contDiff_ofLp.comp (contDiff_snd.comp contDiff_snd)))).smul
          ((contDiff_chartSymm_coe u₀).comp (contDiff_fst.comp contDiff_snd))).contDiffOn)
  apply ContDiffOn.congr (f := fun p : EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
    ((splitLo 1 (rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))))),
      (WithLp.toLp 2 (fun _ : Fin 1 =>
        (rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))))).ofLp (Fin.last 1) + 2) :
        EuclideanSpace ℝ (Fin 1))) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  · exact contDiffOn_interiorTargetForm hR
  · intro p hp
    obtain ⟨⟨hge, hlt⟩, h1⟩ := key p hp
    obtain ⟨-, h2, -, -⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hrec : (((diskCollarChart 1 u₀).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = (1 - p.2.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))) := by
      show max 0 (1 - ((𝓡∂ 1).symm p.2.2).val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, max_eq_right (by linarith)]
    have hRle : ‖rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))))‖ ≤ 1 := by
      rw [norm_rotE2, hUnorm p.1 h1, one_mul, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith),
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1).2,
        mul_one]
      linarith
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1)))) := by
      rw [hrec]
      exact ballClamp_coe_of_norm_le hRle
    show (splitLo 1 ((ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))),
      WithLp.toLp 2 (fun _ : Fin 1 => ((ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))).ofLp (Fin.last 1) + 2)) = _
    rw [hcl]

/-- **Twisted fiber class IC (interior → collar `u₁`)**: the recovered interior point, rotated by
the unit `U b`, re-charted through the `u₁`-polar collar — `C^k` on the twisted domain. -/
theorem contDiffOn_twistFiberTrans_IC {k : WithTop ℕ∞} (u₁ : NSphere 1)
    {U : EuclideanSpace ℝ (Fin 2) → ℂ}
    {bSet : Set (EuclideanSpace ℝ (Fin 2))} (hU : ContDiffOn ℝ k U bSet)
    (hUnorm : ∀ b ∈ bSet, ‖U b‖ = 1) :
    ContDiffOn ℝ k
      (twistFiberTrans U (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁))
      (twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (diskCollarChart 1 u₁)) := by
  have key : ∀ p ∈ twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (diskCollarChart 1 u₁),
      p.1 ∈ bSet ∧ ‖assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)‖ < 1 ∧
        rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)) ≠ 0 ∧
        innerSL ℝ ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖⁻¹ •
            rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))) ≠ 1 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hA : ‖assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)‖ < 1 := by
      have h : ‖assemble 1 p.2.1 (((𝓡∂ 1).symm p.2.2).val.ofLp 0 - 2)‖ < 1 := h3
      rwa [hzval] at h
    have hrec : (((DiskChartGeneric.diskInteriorChart 1).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = assemble 1 p.2.1 (p.2.2.ofLp 0 - 2) := by
      show (ballClamp 1 (assemble 1 p.2.1 (((𝓡∂ 1).symm p.2.2).val.ofLp 0 - 2)) :
          EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, ballClamp_coe_of_norm_le (le_of_lt hA)]
    have hRlt : ‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖ < 1 := by
      rw [norm_rotE2, hUnorm p.1 h1, one_mul]
      exact hA
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)) := by
      rw [hrec]
      exact ballClamp_coe_of_norm_le (le_of_lt hRlt)
    obtain ⟨hne0, hchart⟩ := h4
    refine ⟨h1, hA, ?_, ?_⟩
    · rw [← hcl]
      exact hne0
    · have h := innerSL_ne_one_of_mem_source hchart
      rw [diskDir_coe hne0, hcl] at h
      exact h
  have hR : ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 2) ×
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
      rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)))
      (twistFiberSet U bSet (DiskChartGeneric.diskInteriorChart 1)
        (diskCollarChart 1 u₁)) :=
    contDiff_rotE2.comp_contDiffOn
      ((hU.comp contDiffOn_fst (fun p hp => (key p hp).1)).prodMk
        (contDiff_assembleShift1.comp contDiff_snd).contDiffOn)
  apply ContDiffOn.congr (f := fun p : EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
    (((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₁))).repr
        (stereoToFun ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖⁻¹ •
            rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)))),
      (WithLp.toLp 2 (fun _ : Fin 1 =>
        1 - ‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖) :
        EuclideanSpace ℝ (Fin 1))) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  · exact contDiffOn_collarTargetForm u₁ hR (fun p hp => (key p hp).2.2.1)
      (fun p hp => (key p hp).2.2.2)
  · intro p hp
    obtain ⟨h1, hA, hRne, -⟩ := key p hp
    obtain ⟨-, h2, -, -⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hrec : (((DiskChartGeneric.diskInteriorChart 1).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = assemble 1 p.2.1 (p.2.2.ofLp 0 - 2) := by
      show (ballClamp 1 (assemble 1 p.2.1 (((𝓡∂ 1).symm p.2.2).val.ofLp 0 - 2)) :
          EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, ballClamp_coe_of_norm_le (le_of_lt hA)]
    have hRlt : ‖rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2))‖ < 1 := by
      rw [norm_rotE2, hUnorm p.1 h1, one_mul]
      exact hA
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = rotE2 (U p.1) (assemble 1 p.2.1 (p.2.2.ofLp 0 - 2)) := by
      rw [hrec]
      exact ballClamp_coe_of_norm_le (le_of_lt hRlt)
    have hne' : ((ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))) ≠ 0 := by
      rw [hcl]
      exact hRne
    show (chartAt (EuclideanSpace ℝ (Fin 1)) u₁ (diskDir 1 (ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))))),
      WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖((ballClamp 1 (rotE2 (U p.1)
        (((DiskChartGeneric.diskInteriorChart 1).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))‖)) = _
    rw [chartAt_oneSphere_apply, diskDir_coe hne', hcl]

/-- **Twisted fiber class CC (collar `u₀` → collar `u₁`)**: the collar-recovered scaled sphere
point, rotated by the unit `U b`, re-charted through the `u₁`-polar collar. The radial coordinate
is untouched (the rotation is an isometry); the sphere block is the `S¹` chart transition composed
with the rotation. -/
theorem contDiffOn_twistFiberTrans_CC {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1)
    {U : EuclideanSpace ℝ (Fin 2) → ℂ}
    {bSet : Set (EuclideanSpace ℝ (Fin 2))} (hU : ContDiffOn ℝ k U bSet)
    (hUnorm : ∀ b ∈ bSet, ‖U b‖ = 1) :
    ContDiffOn ℝ k
      (twistFiberTrans U (diskCollarChart 1 u₀) (diskCollarChart 1 u₁))
      (twistFiberSet U bSet (diskCollarChart 1 u₀) (diskCollarChart 1 u₁)) := by
  have hrotunit : ∀ p : EuclideanSpace ℝ (Fin 2) ×
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)), p.1 ∈ bSet →
      ‖rotE2 (U p.1) ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
        EuclideanSpace ℝ (Fin (1 + 1)))‖ = 1 := by
    intro p h1
    rw [norm_rotE2, hUnorm p.1 h1, one_mul,
      mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1).2]
  have key : ∀ p ∈ twistFiberSet U bSet (diskCollarChart 1 u₀) (diskCollarChart 1 u₁),
      (p.1 ∈ bSet ∧ (0 ≤ p.2.2.ofLp 0 ∧ p.2.2.ofLp 0 < 1)) ∧
        innerSL ℝ ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (rotE2 (U p.1) ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1)))) ≠ 1 := by
    intro p hp
    obtain ⟨h1, h2, h3, h4⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hge : (0 : ℝ) ≤ p.2.2.ofLp 0 := by
      have h := h2.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    have hlt : p.2.2.ofLp 0 < 1 := by
      have h : ((𝓡∂ 1).symm p.2.2).val.ofLp 0 < 1 := h3
      rwa [hzval] at h
    have hcpos : (0 : ℝ) < 1 - p.2.2.ofLp 0 := by linarith
    have hrec : (((diskCollarChart 1 u₀).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = (1 - p.2.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))) := by
      show max 0 (1 - ((𝓡∂ 1).symm p.2.2).val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, max_eq_right (by linarith)]
    have hRval : rotE2 (U p.1) ((1 - p.2.2.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))))
        = (1 - p.2.2.ofLp 0) • rotE2 (U p.1)
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) := rotE2_smul _ _ _
    have hnormR : ‖(1 - p.2.2.ofLp 0) • rotE2 (U p.1)
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1)))‖ = 1 - p.2.2.ofLp 0 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hrotunit p h1, mul_one]
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = (1 - p.2.2.ofLp 0) • rotE2 (U p.1)
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) := by
      rw [hrec, hRval]
      exact ballClamp_coe_of_norm_le (by rw [hnormR]; linarith)
    obtain ⟨hne0, hchart⟩ := h4
    have h := innerSL_ne_one_of_mem_source hchart
    rw [diskDir_coe hne0, hcl, hnormR, inv_smul_smul₀ (ne_of_gt hcpos)] at h
    exact ⟨⟨h1, hge, hlt⟩, h⟩
  have hG : ContDiffOn ℝ k (fun p : EuclideanSpace ℝ (Fin 2) ×
        (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
      rotE2 (U p.1) ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
        EuclideanSpace ℝ (Fin (1 + 1))))
      (twistFiberSet U bSet (diskCollarChart 1 u₀) (diskCollarChart 1 u₁)) :=
    contDiff_rotE2.comp_contDiffOn
      ((hU.comp contDiffOn_fst (fun p hp => (key p hp).1.1)).prodMk
        ((contDiff_chartSymm_coe u₀).comp (contDiff_fst.comp contDiff_snd)).contDiffOn)
  apply ContDiffOn.congr (f := fun p : EuclideanSpace ℝ (Fin 2) ×
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =>
    ((((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₁))).repr
        (stereoToFun ((-u₁ : NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
          (rotE2 (U p.1) ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1)))))),
      p.2.2) :
      EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)))
  · refine ContDiffOn.prodMk ?_ (contDiff_snd.comp contDiff_snd).contDiffOn
    exact ((OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 1
        (ne_zero_of_mem_unit_sphere (-u₁))).repr.contDiff.comp_contDiffOn
        contDiffOn_stereoToFun).comp hG (fun p hp => (key p hp).2)
  · intro p hp
    obtain ⟨⟨h1, hge, hlt⟩, -⟩ := key p hp
    obtain ⟨-, h2, -, h4⟩ := hp
    rw [ModelWithCorners.range_prod] at h2
    have hzval : ((𝓡∂ 1).symm p.2.2).val = p.2.2 := ModelWithCorners.right_inv (𝓡∂ 1) h2.2
    have hcpos : (0 : ℝ) < 1 - p.2.2.ofLp 0 := by linarith
    have hrec : (((diskCollarChart 1 u₀).symm
        (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = (1 - p.2.2.ofLp 0) • ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))) := by
      show max 0 (1 - ((𝓡∂ 1).symm p.2.2).val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) = _
      rw [hzval, max_eq_right (by linarith)]
    have hnormR : ‖(1 - p.2.2.ofLp 0) • rotE2 (U p.1)
        ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1)))‖ = 1 - p.2.2.ofLp 0 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hrotunit p h1, mul_one]
    have hcl : (ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        EuclideanSpace ℝ (Fin (1 + 1)))
        = (1 - p.2.2.ofLp 0) • rotE2 (U p.1)
          ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
            EuclideanSpace ℝ (Fin (1 + 1))) := by
      rw [hrec, rotE2_smul]
      exact ballClamp_coe_of_norm_le (by rw [hnormR]; linarith)
    have hne' : ((ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
        NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1))) ≠ 0 := h4.1
    have hdir : ((diskDir 1 (ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2)))) :
        NSphere 1) : EuclideanSpace ℝ (Fin (1 + 1)))
        = rotE2 (U p.1) ((chartAt (EuclideanSpace ℝ (Fin 1)) u₀).symm p.2.1 :
          EuclideanSpace ℝ (Fin (1 + 1))) := by
      rw [diskDir_coe hne', hcl, hnormR, inv_smul_smul₀ (ne_of_gt hcpos)]
    show (chartAt (EuclideanSpace ℝ (Fin 1)) u₁ (diskDir 1 (ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))))),
      WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖((ballClamp 1 (rotE2 (U p.1)
        (((diskCollarChart 1 u₀).symm
          (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
          NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))‖)) = _
    refine Prod.ext ?_ ?_
    · rw [chartAt_oneSphere_apply, hdir]
    · show WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖((ballClamp 1 (rotE2 (U p.1)
          (((diskCollarChart 1 u₀).symm
            (((𝓡 1).prod (𝓡∂ 1)).symm p.2) : NDisk 1) : EuclideanSpace ℝ (Fin 2))) :
            NDisk 1) : EuclideanSpace ℝ (Fin (1 + 1)))‖) = p.2.2
      rw [hcl, hnormR, sub_sub_cancel]
      exact toLp_ofLp_fin_one p.2.2

/-! ## §4. The general transition theorems for the annulus quadrants -/

/-- **The annulus-annulus transition class.** Two equatorial charts share the single `annulusTriv`
prefix, which cancels on the overlap (`right_inv`); the base block is the exact `toE2Homeo`
round-trip (`gBase = id`), the fiber block the untwisted §O transition `D₀.symm ≫ₕ D₁`. -/
theorem contDiffOn_transition_annulusFam_gen {k : WithTop ℕ∞}
    (F₀ F₁ : OpenPartialHomeomorph Disk
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hF₀ : F₀ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)
    (hF₁ : F₁ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)
    (A₀ A₁ : OpenPartialHomeomorph ResE Model)
    (hA₀ : A₀ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₀).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hA₁ : A₁ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₁).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hfiber : ContDiffOn ℝ k
      (↑((𝓡 1).prod (𝓡∂ 1)) ∘ ↑(D₀.symm ≫ₕ D₁) ∘ ↑((𝓡 1).prod (𝓡∂ 1)).symm)
      (↑((𝓡 1).prod (𝓡∂ 1)).symm ⁻¹' (D₀.symm ≫ₕ D₁).source ∩
        range ↑((𝓡 1).prod (𝓡∂ 1)))) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(A₀.symm ≫ₕ A₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (A₀.symm ≫ₕ A₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  subst hF₀ hF₁ hA₀ hA₁
  set BF₀ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₀
  set BF₁ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₁
  refine (contDiffOn_reshapeConj (gBase := id) (baseSet := Set.univ) contDiffOn_id
      hfiber (Set.mapsTo_univ _ _) ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hAt⟩ := htgt
    have hD0tgt : (reshapeModel.symm y).2 ∈ D₀.target := by
      have h := hBt
      rw [hBF₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      have h2 := h.2
      rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at h2
      exact h2.1
    have hBsrc : BF₀.symm y ∈ BF₁.source := by
      rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff] at hsrc
      have h2 := hsrc.2
      rw [Set.mem_preimage] at h2
      have hco : (annulusTriv.trans BF₀).symm y = annulusTriv.symm (BF₀.symm y) := rfl
      rw [hco] at h2
      rwa [annulusTriv.right_inv hAt] at h2
    have hDsrc : D₀.symm ((reshapeModel.symm y).2) ∈ D₁.source := by
      rw [hBF₀, hBF₁] at hBsrc
      simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
        Set.mem_preimage, OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_symm_apply,
        OpenPartialHomeomorph.prod_source, Set.mem_prod,
        Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, and_true, true_and,
        Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.apply_symm_apply] at hBsrc
      exact hBsrc
    have hrange2 : (0 : ℝ) ≤ x.2.ofLp 0 := by
      rw [ModelWithCorners.range_prod, Set.mem_prod] at hxrange
      have h := hxrange.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    refine ⟨?_, ?_⟩
    · rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
        Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨hD0tgt, hDsrc⟩
    · rw [ModelWithCorners.range_prod, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact Set.mem_univ _
      · rw [range_modelWithCornersEuclideanHalfSpace]; exact hrange2
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, -⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨-, hAt⟩ := htgt
    have hval : annulusTriv ((annulusTriv.trans BF₀).symm y) = BF₀.symm y := by
      have hco : (annulusTriv.trans BF₀).symm y = annulusTriv.symm (BF₀.symm y) := rfl
      rw [hco]
      exact annulusTriv.right_inv hAt
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [hval, hBF₀, hBF₁]
    simp only [OpenPartialHomeomorph.coe_trans,
      OpenPartialHomeomorph.coe_trans_symm, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
      OpenPartialHomeomorph.prod_apply, OpenPartialHomeomorph.prod_symm_apply, id_eq,
      Homeomorph.apply_symm_apply]
    rfl

/-- **The forward twist in `NDisk` coordinates**: `diskHomeoNDisk1 (trivFiber z w)` is the clamped
`regDir z`-rotation of `diskHomeoNDisk1 w`. -/
theorem diskHomeo_trivFiber (z : ℂ) (w : Disk) :
    diskHomeoNDisk1 (trivFiber z w)
      = ballClamp 1 (rotE2 (regDir z)
          ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2))) := by
  apply Subtype.ext
  have hco : rotE2 (regDir z) ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2))
      = toE2 (regDir z * (w : ℂ)) := by
    rw [show ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (w : ℂ) from rfl,
      rotE2, ofE2_toE2]
  rw [hco, ballClamp_coe_of_norm_le (by rw [norm_toE2]; exact (trivFiber z w).2)]
  rfl

/-- **The inverse twist in `NDisk` coordinates**: `diskHomeoNDisk1 (recoverFiber0 z w)` is the
clamped `conj (regDir z)`-rotation of `diskHomeoNDisk1 w`. -/
theorem diskHomeo_recoverFiber0 (z : ℂ) (w : Disk) :
    diskHomeoNDisk1 (recoverFiber0 z w)
      = ballClamp 1 (rotE2 ((starRingEnd ℂ) (regDir z))
          ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2))) := by
  apply Subtype.ext
  have hco : rotE2 ((starRingEnd ℂ) (regDir z))
        ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2))
      = toE2 ((starRingEnd ℂ) (regDir z) * (w : ℂ)) := by
    rw [show ((diskHomeoNDisk1 w : NDisk 1) : EuclideanSpace ℝ (Fin 2)) = toE2 (w : ℂ) from rfl,
      rotE2, ofE2_toE2]
  rw [hco, ballClamp_coe_of_norm_le (by rw [norm_toE2]; exact (recoverFiber0 z w).2)]
  rfl

theorem annulusTriv_coe : ⇑annulusTriv = annulusTrivFun := rfl

theorem annulusTriv_symm_coe : ⇑annulusTriv.symm = annulusTrivInv := rfl

theorem toE2Homeo_coe : ⇑toE2Homeo = toE2 := rfl

/-- **The chart0-family → annulus-family transition class.** The source chart is a `chart0`-lift of
the base-interior product chart; the target the equatorial annulus chart. On the overlap the base
coordinate is unchanged (`gBase = id` — the annulus base coordinate over the `chart0` side IS `z`)
and the fiber block is the `twistU`-rotated `D₀ → D₁` change (`ζ = regDir z · w`). -/
theorem contDiffOn_transition_chart0_annulus_gen {k : WithTop ℕ∞}
    (F₀ F₁ : OpenPartialHomeomorph Disk
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hF₀ : F₀ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)
    (hF₁ : F₁ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)
    (C₀ A₁ : OpenPartialHomeomorph ResE Model)
    (hC₀ : C₀ = ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans
        ((baseDiskChart.prod F₀).trans reshapeModel.toOpenPartialHomeomorph)).lift_openEmbedding
        isOpenEmbedding_chart0_baseInterior)
    (hA₁ : A₁ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₁).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hfiber : ContDiffOn ℝ k (twistFiberTrans twistU D₀ D₁)
      (twistFiberSet twistU {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} D₀ D₁)) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(C₀.symm ≫ₕ A₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (C₀.symm ≫ₕ A₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  subst hF₀ hF₁ hC₀ hA₁
  set B₀ := (baseDiskChart.prod (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)).trans
      reshapeModel.toOpenPartialHomeomorph with hB₀
  set BF₁ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₁
  set Cin := (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : ↥baseInterior → ResChart)
      isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans B₀ with hCin
  refine (contDiffOn_reshapeConjTwist (gBase := id) (baseSet := Set.univ) contDiffOn_id
      hfiber (Set.mapsTo_univ _ _) ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.lift_openEmbedding_target, hCin,
      OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hvt⟩ := htgt
    have hbaseInt : B₀.symm y ∈ Set.range (Subtype.val : ↥baseInterior → ResChart) := by
      rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hvt
    have hbtgt : (reshapeModel.symm y).1 ∈ baseDiskChart.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      exact h.1
    have hD0tgt : (reshapeModel.symm y).2 ∈ D₀.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      have h2 := h.2
      rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at h2
      exact h2.1
    have hpstar : ((Cin.symm y : ↥baseInterior) : ResChart) = B₀.symm y :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal hbaseInt
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hsrc
    obtain ⟨hreg, himg⟩ := hsrc
    have hreg' : chart0 ((Cin.symm y : ↥baseInterior) : ResChart) ∈ annulusRegion := hreg
    have himg' : annulusTrivFun (chart0 ((Cin.symm y : ↥baseInterior) : ResChart))
        ∈ BF₁.source := himg
    rw [hpstar] at hreg' himg'
    have hnorm : 1 / 2 < ‖(((B₀.symm y).1 : Disk) : ℂ)‖ := mem_annulusRegion_chart0_norm hreg'
    have hp1 : (((B₀.symm y).1 : Disk) : ℂ) = ofE2 ((reshapeModel.symm y).1) := by
      show ofE2 ((ballClamp 1 ((reshapeModel.symm y).1) : NDisk 1) :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [ballClamp_coe_of_norm_le (le_of_lt hbtgt)]
    have hw : diskHomeoNDisk1 ((B₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    rw [annulusTrivFun_chart0, hBF₁] at himg'
    simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.prod_source, Set.mem_prod,
      Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, true_and, and_true,
      Homeomorph.toOpenPartialHomeomorph_apply] at himg'
    have hDim : diskHomeoNDisk1 (trivFiber (((B₀.symm y).1 : Disk) : ℂ) ((B₀.symm y).2))
        ∈ D₁.source := himg'
    rw [diskHomeo_trivFiber, hw, hp1] at hDim
    have hrange2 : (0 : ℝ) ≤ x.2.ofLp 0 := by
      rw [ModelWithCorners.range_prod, Set.mem_prod] at hxrange
      have h := hxrange.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 / 2 < ‖splitLo 2 x.1‖
      rw [hp1, norm_ofE2] at hnorm
      exact hnorm
    · rw [ModelWithCorners.range_prod, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact Set.mem_univ _
      · rw [range_modelWithCornersEuclideanHalfSpace]; exact hrange2
    · exact hD0tgt
    · exact hDim
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, -⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.lift_openEmbedding_target, hCin,
      OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hvt⟩ := htgt
    have hbaseInt : B₀.symm y ∈ Set.range (Subtype.val : ↥baseInterior → ResChart) := by
      rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hvt
    have hbtgt : (reshapeModel.symm y).1 ∈ baseDiskChart.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      exact h.1
    have hpstar : ((Cin.symm y : ↥baseInterior) : ResChart) = B₀.symm y :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal hbaseInt
    have hp1 : (((B₀.symm y).1 : Disk) : ℂ) = ofE2 ((reshapeModel.symm y).1) := by
      show ofE2 ((ballClamp 1 ((reshapeModel.symm y).1) : NDisk 1) :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [ballClamp_coe_of_norm_le (le_of_lt hbtgt)]
    have hw : diskHomeoNDisk1 ((B₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    have hCsy : (Cin.lift_openEmbedding isOpenEmbedding_chart0_baseInterior).symm y
        = chart0 ((Cin.symm y : ↥baseInterior) : ResChart) := rfl
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [← hy, hCsy, hpstar, annulusTriv_coe, annulusTrivFun_chart0, hBF₁]
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, OpenPartialHomeomorph.prod_apply]
    rw [diskHomeo_trivFiber, hw, hp1, toE2Homeo_coe, toE2_ofE2]
    rfl

/-- **The chart1-family → annulus-family transition class.** As `chart0 → annulus`, but over the
`chart1` base disk the annulus base coordinate is `β = z'⁻¹` — `gBase = toE2 ∘ regInv ∘ ofE2` —
while the fiber twist is still `regDir z'` in the source coordinate (`twistU`). -/
theorem contDiffOn_transition_chart1_annulus_gen {k : WithTop ℕ∞}
    (F₀ F₁ : OpenPartialHomeomorph Disk
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hF₀ : F₀ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)
    (hF₁ : F₁ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)
    (C₀ A₁ : OpenPartialHomeomorph ResE Model)
    (hC₀ : C₀ = ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans
        ((baseDiskChart.prod F₀).trans reshapeModel.toOpenPartialHomeomorph)).lift_openEmbedding
        isOpenEmbedding_chart1_baseInterior)
    (hA₁ : A₁ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₁).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hfiber : ContDiffOn ℝ k (twistFiberTrans twistU D₀ D₁)
      (twistFiberSet twistU {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} D₀ D₁)) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(C₀.symm ≫ₕ A₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (C₀.symm ≫ₕ A₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  subst hF₀ hF₁ hC₀ hA₁
  set B₀ := (baseDiskChart.prod (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)).trans
      reshapeModel.toOpenPartialHomeomorph with hB₀
  set BF₁ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₁
  set Cin := (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : ↥baseInterior → ResChart)
      isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans B₀ with hCin
  refine (contDiffOn_reshapeConjTwist
      (gBase := fun b : EuclideanSpace ℝ (Fin 2) => toE2 (regInv (ofE2 b)))
      (baseSet := {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖})
      contDiffOn_toE2_regInv_ofE2 hfiber ?_ ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.lift_openEmbedding_target, hCin,
      OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hvt⟩ := htgt
    have hbaseInt : B₀.symm y ∈ Set.range (Subtype.val : ↥baseInterior → ResChart) := by
      rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hvt
    have hbtgt : (reshapeModel.symm y).1 ∈ baseDiskChart.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      exact h.1
    have hpstar : ((Cin.symm y : ↥baseInterior) : ResChart) = B₀.symm y :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal hbaseInt
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hsrc
    obtain ⟨hreg, -⟩ := hsrc
    have hreg' : chart1 ((Cin.symm y : ↥baseInterior) : ResChart) ∈ annulusRegion := hreg
    rw [hpstar] at hreg'
    have hnorm : 1 / 2 < ‖(((B₀.symm y).1 : Disk) : ℂ)‖ := mem_annulusRegion_chart1_norm hreg'
    have hp1 : (((B₀.symm y).1 : Disk) : ℂ) = ofE2 ((reshapeModel.symm y).1) := by
      show ofE2 ((ballClamp 1 ((reshapeModel.symm y).1) : NDisk 1) :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [ballClamp_coe_of_norm_le (le_of_lt hbtgt)]
    show 1 / 2 < ‖splitLo 2 x.1‖
    rw [hp1, norm_ofE2] at hnorm
    exact hnorm
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.lift_openEmbedding_target, hCin,
      OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hvt⟩ := htgt
    have hbaseInt : B₀.symm y ∈ Set.range (Subtype.val : ↥baseInterior → ResChart) := by
      rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hvt
    have hbtgt : (reshapeModel.symm y).1 ∈ baseDiskChart.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      exact h.1
    have hD0tgt : (reshapeModel.symm y).2 ∈ D₀.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      have h2 := h.2
      rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at h2
      exact h2.1
    have hpstar : ((Cin.symm y : ↥baseInterior) : ResChart) = B₀.symm y :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal hbaseInt
    rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at hsrc
    obtain ⟨hreg, himg⟩ := hsrc
    have hreg' : chart1 ((Cin.symm y : ↥baseInterior) : ResChart) ∈ annulusRegion := hreg
    have himg' : annulusTrivFun (chart1 ((Cin.symm y : ↥baseInterior) : ResChart))
        ∈ BF₁.source := himg
    rw [hpstar] at hreg' himg'
    have hnorm : 1 / 2 < ‖(((B₀.symm y).1 : Disk) : ℂ)‖ := mem_annulusRegion_chart1_norm hreg'
    have hp1 : (((B₀.symm y).1 : Disk) : ℂ) = ofE2 ((reshapeModel.symm y).1) := by
      show ofE2 ((ballClamp 1 ((reshapeModel.symm y).1) : NDisk 1) :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [ballClamp_coe_of_norm_le (le_of_lt hbtgt)]
    have hw : diskHomeoNDisk1 ((B₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    rw [annulusTrivFun_chart1, hBF₁] at himg'
    simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.prod_source, Set.mem_prod,
      Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, true_and, and_true,
      Homeomorph.toOpenPartialHomeomorph_apply] at himg'
    have hDim : diskHomeoNDisk1 (trivFiber (((B₀.symm y).1 : Disk) : ℂ) ((B₀.symm y).2))
        ∈ D₁.source := himg'
    rw [diskHomeo_trivFiber, hw, hp1] at hDim
    have hrange2 : (0 : ℝ) ≤ x.2.ofLp 0 := by
      rw [ModelWithCorners.range_prod, Set.mem_prod] at hxrange
      have h := hxrange.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 / 2 < ‖splitLo 2 x.1‖
      rw [hp1, norm_ofE2] at hnorm
      exact hnorm
    · rw [ModelWithCorners.range_prod, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact Set.mem_univ _
      · rw [range_modelWithCornersEuclideanHalfSpace]; exact hrange2
    · exact hD0tgt
    · exact hDim
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, -⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.lift_openEmbedding_target, hCin,
      OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hvt⟩ := htgt
    have hbaseInt : B₀.symm y ∈ Set.range (Subtype.val : ↥baseInterior → ResChart) := by
      rwa [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target] at hvt
    have hbtgt : (reshapeModel.symm y).1 ∈ baseDiskChart.target := by
      have h := hBt
      rw [hB₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      exact h.1
    have hpstar : ((Cin.symm y : ↥baseInterior) : ResChart) = B₀.symm y :=
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal hbaseInt
    have hp1 : (((B₀.symm y).1 : Disk) : ℂ) = ofE2 ((reshapeModel.symm y).1) := by
      show ofE2 ((ballClamp 1 ((reshapeModel.symm y).1) : NDisk 1) :
        EuclideanSpace ℝ (Fin 2)) = _
      rw [ballClamp_coe_of_norm_le (le_of_lt hbtgt)]
    have hw : diskHomeoNDisk1 ((B₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    have hCsy : (Cin.lift_openEmbedding isOpenEmbedding_chart1_baseInterior).symm y
        = chart1 ((Cin.symm y : ↥baseInterior) : ResChart) := rfl
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [← hy, hCsy, hpstar, annulusTriv_coe, annulusTrivFun_chart1, hBF₁]
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, OpenPartialHomeomorph.prod_apply]
    rw [diskHomeo_trivFiber, hw, hp1, toE2Homeo_coe]
    rfl

/-- **The annulus-family → chart0-family transition class.** On the overlap the inverse
trivialization takes its `chart0` branch (the `chart1` branch would weld a base-interior `chart0`
point to a `chart1` point, forcing `‖z‖ = 1`); the base is unchanged (`gBase = id`) and the fiber
is the `twistUConj`-rotated change (`w = conj (regDir β) · ζ`). -/
theorem contDiffOn_transition_annulus_chart0_gen {k : WithTop ℕ∞}
    (F₀ F₁ : OpenPartialHomeomorph Disk
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hF₀ : F₀ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)
    (hF₁ : F₁ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)
    (A₀ C₁ : OpenPartialHomeomorph ResE Model)
    (hA₀ : A₀ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₀).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hC₁ : C₁ = ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans
        ((baseDiskChart.prod F₁).trans reshapeModel.toOpenPartialHomeomorph)).lift_openEmbedding
        isOpenEmbedding_chart0_baseInterior)
    (hfiber : ContDiffOn ℝ k (twistFiberTrans twistUConj D₀ D₁)
      (twistFiberSet twistUConj {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} D₀ D₁)) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(A₀.symm ≫ₕ C₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (A₀.symm ≫ₕ C₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  subst hF₀ hF₁ hA₀ hC₁
  set BF₀ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₀
  set B₁ := (baseDiskChart.prod (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)).trans
      reshapeModel.toOpenPartialHomeomorph with hB₁
  set Cin := (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : ↥baseInterior → ResChart)
      isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans B₁ with hCin
  refine (contDiffOn_reshapeConjTwist (gBase := id) (baseSet := Set.univ) contDiffOn_id
      hfiber (Set.mapsTo_univ _ _) ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hAt⟩ := htgt
    have hD0tgt : (reshapeModel.symm y).2 ∈ D₀.target := by
      have h := hBt
      rw [hBF₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      have h2 := h.2
      rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at h2
      exact h2.1
    have hAt' : 1 / 2 < ‖(BF₀.symm y).1‖ ∧ ‖(BF₀.symm y).1‖ < 2 := hAt
    have hβ : (BF₀.symm y).1 = ofE2 ((reshapeModel.symm y).1) := rfl
    have hsrc' : annulusTrivInv (BF₀.symm y)
        ∈ (fun p : ↥baseInterior => chart0 p.1) '' Cin.source := hsrc
    obtain ⟨a, ha, heq⟩ := hsrc'
    have hble : ‖(BF₀.symm y).1‖ ≤ 1 := by
      by_contra hgt
      have heq2 : chart0 (a : ResChart) = annulusTrivInv (BF₀.symm y) := heq
      have heq' : chart0 (a : ResChart)
          = chart1 (clampBall (regInv (BF₀.symm y).1),
              trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
        rw [heq2]
        simp only [annulusTrivInv, if_neg hgt]
      have hg := chart0_eq_chart1_iff.mp heq'
      exact absurd hg.1 (ne_of_lt a.2)
    have hinv : annulusTrivInv (BF₀.symm y)
        = chart0 (clampBall (BF₀.symm y).1,
            recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
      simp only [annulusTrivInv, if_pos hble]
    have ha' : (a : ResChart)
        = (clampBall (BF₀.symm y).1, recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
      apply chart0_inj_iff.mp
      rw [← hinv]
      exact heq
    have haB : ((a : ResChart)) ∈ B₁.source := by
      rw [hCin, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at ha
      exact ha.2
    rw [ha', hB₁] at haB
    simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.prod_source, Set.mem_prod,
      Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, and_true, true_and,
      Homeomorph.toOpenPartialHomeomorph_apply] at haB
    have hDim : diskHomeoNDisk1 (recoverFiber0 (BF₀.symm y).1 ((BF₀.symm y).2))
        ∈ D₁.source := haB.2
    have hw : diskHomeoNDisk1 ((BF₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    rw [diskHomeo_recoverFiber0, hw, hβ] at hDim
    have hrange2 : (0 : ℝ) ≤ x.2.ofLp 0 := by
      rw [ModelWithCorners.range_prod, Set.mem_prod] at hxrange
      have h := hxrange.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 / 2 < ‖splitLo 2 x.1‖
      have h1 := hAt'.1
      rw [hβ, norm_ofE2] at h1
      exact h1
    · rw [ModelWithCorners.range_prod, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact Set.mem_univ _
      · rw [range_modelWithCornersEuclideanHalfSpace]; exact hrange2
    · exact hD0tgt
    · exact hDim
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hAt⟩ := htgt
    have hAt' : 1 / 2 < ‖(BF₀.symm y).1‖ ∧ ‖(BF₀.symm y).1‖ < 2 := hAt
    have hβ : (BF₀.symm y).1 = ofE2 ((reshapeModel.symm y).1) := rfl
    have hsrc' : annulusTrivInv (BF₀.symm y)
        ∈ (fun p : ↥baseInterior => chart0 p.1) '' Cin.source := hsrc
    obtain ⟨a, ha, heq⟩ := hsrc'
    have hble : ‖(BF₀.symm y).1‖ ≤ 1 := by
      by_contra hgt
      have heq2 : chart0 (a : ResChart) = annulusTrivInv (BF₀.symm y) := heq
      have heq' : chart0 (a : ResChart)
          = chart1 (clampBall (regInv (BF₀.symm y).1),
              trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
        rw [heq2]
        simp only [annulusTrivInv, if_neg hgt]
      have hg := chart0_eq_chart1_iff.mp heq'
      exact absurd hg.1 (ne_of_lt a.2)
    have hinv : annulusTrivInv (BF₀.symm y)
        = chart0 (clampBall (BF₀.symm y).1,
            recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
      simp only [annulusTrivInv, if_pos hble]
    have ha' : (a : ResChart)
        = (clampBall (BF₀.symm y).1, recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
      apply chart0_inj_iff.mp
      rw [← hinv]
      exact heq
    have hpv : ((clampBall (BF₀.symm y).1,
        recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) : ResChart) ∈ baseInterior := ha' ▸ a.2
    have hw : diskHomeoNDisk1 ((BF₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    have hAsy : (annulusTriv.trans BF₀).symm y = annulusTrivInv (BF₀.symm y) := rfl
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [← hy, hAsy, hinv]
    have happ := OpenPartialHomeomorph.lift_openEmbedding_apply Cin
      isOpenEmbedding_chart0_baseInterior
      (x := (⟨(clampBall (BF₀.symm y).1, recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩ :
        ↥baseInterior))
    have hCapp : (Cin.lift_openEmbedding isOpenEmbedding_chart0_baseInterior)
        (chart0 (clampBall (BF₀.symm y).1, recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2))
        = Cin ⟨(clampBall (BF₀.symm y).1,
            recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩ := happ
    rw [hCapp]
    have hCin1app : Cin ⟨(clampBall (BF₀.symm y).1,
        recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩
        = B₁ (clampBall (BF₀.symm y).1,
            recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := rfl
    rw [hCin1app, hB₁]
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, OpenPartialHomeomorph.prod_apply]
    rw [diskHomeo_recoverFiber0, hw, hβ]
    have hbase : baseDiskChart (clampBall (ofE2 ((reshapeModel.symm y).1)))
        = (reshapeModel.symm y).1 := by
      show toE2 ((clampBall (ofE2 ((reshapeModel.symm y).1)) : Disk) : ℂ) = _
      rw [clampBall_eq (hβ ▸ hble), toE2_ofE2]
    rw [hbase]
    rfl

/-- **The annulus-family → chart1-family transition class.** On the overlap the inverse
trivialization takes its `chart1` branch (`‖β‖ > 1`; the `chart0` branch would weld to a
base-interior `chart1` point, forcing norm one); the base map is `β ↦ β⁻¹`
(`gBase = toE2 ∘ regInv ∘ ofE2`) and the fiber the `twistU`-rotated change. -/
theorem contDiffOn_transition_annulus_chart1_gen {k : WithTop ℕ∞}
    (F₀ F₁ : OpenPartialHomeomorph Disk
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (D₀ D₁ : OpenPartialHomeomorph (NDisk 1)
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 1)))
    (hF₀ : F₀ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)
    (hF₁ : F₁ = diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)
    (A₀ C₁ : OpenPartialHomeomorph ResE Model)
    (hA₀ : A₀ = annulusTriv.trans ((toE2Homeo.toOpenPartialHomeomorph.prod F₀).trans
      reshapeModel.toOpenPartialHomeomorph))
    (hC₁ : C₁ = ((Topology.IsOpenEmbedding.toOpenPartialHomeomorph
        (Subtype.val : ↥baseInterior → ResChart)
        isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans
        ((baseDiskChart.prod F₁).trans reshapeModel.toOpenPartialHomeomorph)).lift_openEmbedding
        isOpenEmbedding_chart1_baseInterior)
    (hfiber : ContDiffOn ℝ k (twistFiberTrans twistU D₀ D₁)
      (twistFiberSet twistU {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖} D₀ D₁)) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(A₀.symm ≫ₕ C₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (A₀.symm ≫ₕ C₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) := by
  subst hF₀ hF₁ hA₀ hC₁
  set BF₀ := (toE2Homeo.toOpenPartialHomeomorph.prod
      (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₀)).trans
      reshapeModel.toOpenPartialHomeomorph with hBF₀
  set B₁ := (baseDiskChart.prod (diskHomeoNDisk1.toOpenPartialHomeomorph.trans D₁)).trans
      reshapeModel.toOpenPartialHomeomorph with hB₁
  set Cin := (Topology.IsOpenEmbedding.toOpenPartialHomeomorph
      (Subtype.val : ↥baseInterior → ResChart)
      isOpen_baseInterior.isOpenEmbedding_subtypeVal).trans B₁ with hCin
  refine (contDiffOn_reshapeConjTwist
      (gBase := fun b : EuclideanSpace ℝ (Fin 2) => toE2 (regInv (ofE2 b)))
      (baseSet := {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖})
      contDiffOn_toE2_regInv_ofE2 hfiber ?_ ?_).congr ?_
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, -⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨-, hAt⟩ := htgt
    have hAt' : 1 / 2 < ‖(BF₀.symm y).1‖ ∧ ‖(BF₀.symm y).1‖ < 2 := hAt
    have hβ : (BF₀.symm y).1 = ofE2 ((reshapeModel.symm y).1) := rfl
    show 1 / 2 < ‖splitLo 2 x.1‖
    have h1 := hAt'.1
    rw [hβ, norm_ofE2] at h1
    exact h1
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hAt⟩ := htgt
    have hD0tgt : (reshapeModel.symm y).2 ∈ D₀.target := by
      have h := hBt
      rw [hBF₀, OpenPartialHomeomorph.trans_target,
        Homeomorph.toOpenPartialHomeomorph_target, Set.univ_inter, Set.mem_preimage,
        Homeomorph.toOpenPartialHomeomorph_symm_apply, OpenPartialHomeomorph.prod_target] at h
      have h2 := h.2
      rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff] at h2
      exact h2.1
    have hAt' : 1 / 2 < ‖(BF₀.symm y).1‖ ∧ ‖(BF₀.symm y).1‖ < 2 := hAt
    have hβ : (BF₀.symm y).1 = ofE2 ((reshapeModel.symm y).1) := rfl
    have hsrc' : annulusTrivInv (BF₀.symm y)
        ∈ (fun p : ↥baseInterior => chart1 p.1) '' Cin.source := hsrc
    obtain ⟨a, ha, heq⟩ := hsrc'
    have heq2 : chart1 (a : ResChart) = annulusTrivInv (BF₀.symm y) := heq
    have hnle : ¬ ‖(BF₀.symm y).1‖ ≤ 1 := by
      intro hble
      have heq' : chart1 (a : ResChart)
          = chart0 (clampBall (BF₀.symm y).1,
              recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
        rw [heq2]
        simp only [annulusTrivInv, if_pos hble]
      have hg := chart0_eq_chart1_iff.mp heq'.symm
      have h1 : ‖((a : ResChart)).1.1‖ = 1 := by
        rw [hg.2.1, norm_inv, hg.1, inv_one]
      exact absurd h1 (ne_of_lt a.2)
    have hinv : annulusTrivInv (BF₀.symm y)
        = chart1 (clampBall (regInv (BF₀.symm y).1),
            trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
      simp only [annulusTrivInv, if_neg hnle]
    have ha' : (a : ResChart)
        = (clampBall (regInv (BF₀.symm y).1), trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
      apply chart1_inj_iff.mp
      rw [← hinv]
      exact heq2
    have haB : ((a : ResChart)) ∈ B₁.source := by
      rw [hCin, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage] at ha
      exact ha.2
    rw [ha', hB₁] at haB
    simp only [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff, Set.mem_preimage,
      OpenPartialHomeomorph.prod_source, Set.mem_prod,
      Homeomorph.toOpenPartialHomeomorph_source, Set.mem_univ, and_true, true_and,
      Homeomorph.toOpenPartialHomeomorph_apply] at haB
    have hDim : diskHomeoNDisk1 (trivFiber (BF₀.symm y).1 ((BF₀.symm y).2))
        ∈ D₁.source := haB.2
    have hw : diskHomeoNDisk1 ((BF₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    rw [diskHomeo_trivFiber, hw, hβ] at hDim
    have hrange2 : (0 : ℝ) ≤ x.2.ofLp 0 := by
      rw [ModelWithCorners.range_prod, Set.mem_prod] at hxrange
      have h := hxrange.2
      rwa [range_modelWithCornersEuclideanHalfSpace] at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 / 2 < ‖splitLo 2 x.1‖
      have h1 := hAt'.1
      rw [hβ, norm_ofE2] at h1
      exact h1
    · rw [ModelWithCorners.range_prod, Set.mem_prod]
      refine ⟨?_, ?_⟩
      · rw [ModelWithCorners.Boundaryless.range_eq_univ]; exact Set.mem_univ _
      · rw [range_modelWithCornersEuclideanHalfSpace]; exact hrange2
    · exact hD0tgt
    · exact hDim
  · intro x hx
    obtain ⟨hxsrc, hxrange⟩ := hx
    rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source, Set.mem_inter_iff, Set.mem_preimage] at hxsrc
    obtain ⟨htgt, hsrc⟩ := hxsrc
    set y := ((𝓡 3).prod (𝓡∂ 1)).symm x with hy
    rw [OpenPartialHomeomorph.trans_target, Set.mem_inter_iff, Set.mem_preimage] at htgt
    obtain ⟨hBt, hAt⟩ := htgt
    have hAt' : 1 / 2 < ‖(BF₀.symm y).1‖ ∧ ‖(BF₀.symm y).1‖ < 2 := hAt
    have hβ : (BF₀.symm y).1 = ofE2 ((reshapeModel.symm y).1) := rfl
    have hsrc' : annulusTrivInv (BF₀.symm y)
        ∈ (fun p : ↥baseInterior => chart1 p.1) '' Cin.source := hsrc
    obtain ⟨a, ha, heq⟩ := hsrc'
    have heq2 : chart1 (a : ResChart) = annulusTrivInv (BF₀.symm y) := heq
    have hnle : ¬ ‖(BF₀.symm y).1‖ ≤ 1 := by
      intro hble
      have heq' : chart1 (a : ResChart)
          = chart0 (clampBall (BF₀.symm y).1,
              recoverFiber0 (BF₀.symm y).1 (BF₀.symm y).2) := by
        rw [heq2]
        simp only [annulusTrivInv, if_pos hble]
      have hg := chart0_eq_chart1_iff.mp heq'.symm
      have h1 : ‖((a : ResChart)).1.1‖ = 1 := by
        rw [hg.2.1, norm_inv, hg.1, inv_one]
      exact absurd h1 (ne_of_lt a.2)
    have hinv : annulusTrivInv (BF₀.symm y)
        = chart1 (clampBall (regInv (BF₀.symm y).1),
            trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
      simp only [annulusTrivInv, if_neg hnle]
    have ha' : (a : ResChart)
        = (clampBall (regInv (BF₀.symm y).1), trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := by
      apply chart1_inj_iff.mp
      rw [← hinv]
      exact heq2
    have hpv : ((clampBall (regInv (BF₀.symm y).1),
        trivFiber (BF₀.symm y).1 (BF₀.symm y).2) : ResChart) ∈ baseInterior := ha' ▸ a.2
    have hw : diskHomeoNDisk1 ((BF₀.symm y).2) = D₀.symm ((reshapeModel.symm y).2) := by
      show diskHomeoNDisk1 (diskHomeoNDisk1.symm (D₀.symm ((reshapeModel.symm y).2))) = _
      exact Homeomorph.apply_symm_apply _ _
    have hrpos : (0 : ℝ) < ‖(BF₀.symm y).1‖ := lt_trans (by norm_num) hAt'.1
    have hle1 : ‖regInv (BF₀.symm y).1‖ ≤ 1 := by
      rw [regInv_eq (le_of_lt hAt'.1), norm_inv, inv_le_one₀ hrpos]
      exact (not_le.mp hnle).le
    have hAsy : (annulusTriv.trans BF₀).symm y = annulusTrivInv (BF₀.symm y) := rfl
    simp only [Function.comp_apply, OpenPartialHomeomorph.coe_trans]
    rw [← hy, hAsy, hinv]
    have happ := OpenPartialHomeomorph.lift_openEmbedding_apply Cin
      isOpenEmbedding_chart1_baseInterior
      (x := (⟨(clampBall (regInv (BF₀.symm y).1),
        trivFiber (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩ : ↥baseInterior))
    have hCapp : (Cin.lift_openEmbedding isOpenEmbedding_chart1_baseInterior)
        (chart1 (clampBall (regInv (BF₀.symm y).1),
          trivFiber (BF₀.symm y).1 (BF₀.symm y).2))
        = Cin ⟨(clampBall (regInv (BF₀.symm y).1),
            trivFiber (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩ := happ
    rw [hCapp]
    have hCin1app : Cin ⟨(clampBall (regInv (BF₀.symm y).1),
        trivFiber (BF₀.symm y).1 (BF₀.symm y).2), hpv⟩
        = B₁ (clampBall (regInv (BF₀.symm y).1),
            trivFiber (BF₀.symm y).1 (BF₀.symm y).2) := rfl
    rw [hCin1app, hB₁]
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      Homeomorph.toOpenPartialHomeomorph_apply, OpenPartialHomeomorph.prod_apply]
    rw [diskHomeo_trivFiber, hw, hβ]
    have hbase : baseDiskChart (clampBall (regInv (ofE2 ((reshapeModel.symm y).1))))
        = toE2 (regInv (ofE2 ((reshapeModel.symm y).1))) := by
      show toE2 ((clampBall (regInv (ofE2 ((reshapeModel.symm y).1))) : Disk) : ℂ) = _
      rw [clampBall_eq (hβ ▸ hle1)]
    rw [hbase]
    rfl

/-! ## §5. The pair instantiations and the `IsManifold` certificate -/

/-- The `chart1`-family → `chart0`-family mirror of `contDiffOn_transition_cross` (disjointness is
symmetric). -/
theorem contDiffOn_transition_cross' {k : WithTop ℕ∞}
    {e e' : OpenPartialHomeomorph ResE Model}
    (he : e.source ⊆ Set.range (fun p : ↥baseInterior => chart1 p.1))
    (he' : e'.source ⊆ Set.range (fun p : ↥baseInterior => chart0 p.1)) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘ ↑(e.symm ≫ₕ e') ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (e.symm ≫ₕ e').source ∩ range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_vacuous_of_disjoint he he' disjoint_chart0_chart1_baseInterior.symm

/-- The twisted fiber smoothness inputs, `twistU`-side. -/
private theorem hUn : ∀ b ∈ {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖}, ‖twistU b‖ = 1 :=
  fun _ hb => norm_twistU (le_of_lt hb)

/-- The twisted fiber smoothness inputs, `twistUConj`-side. -/
private theorem hUnConj : ∀ b ∈ {b : EuclideanSpace ℝ (Fin 2) | 1 / 2 < ‖b‖},
    ‖twistUConj b‖ = 1 :=
  fun _ hb => norm_twistUConj (le_of_lt hb)

/-! ### §5.1. The annulus-annulus quadrant (4 pairs) -/

/-- **annulus interior → annulus interior**. -/
theorem contDiffOn_transition_annulusInterior_II {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (annulusInteriorChart.symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulusFam_gen fiberInteriorChart fiberInteriorChart
    (DiskChartGeneric.diskInteriorChart 1) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    annulusInteriorChart annulusInteriorChart rfl rfl
    (mem_groupoid_of_pregroupoid.mp
      (symm_trans_mem_contDiffGroupoid (DiskChartGeneric.diskInteriorChart 1))).1

/-- **annulus interior → annulus collar**. -/
theorem contDiffOn_transition_annulusInterior_annulusCollar {k : WithTop ℕ∞} (u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          (annulusInteriorChart.symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulusFam_gen fiberInteriorChart (fiberCollarChart u₁)
    (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁) rfl rfl
    annulusInteriorChart (annulusCollarChart u₁) rfl rfl
    (contDiffOn_transition_fiber_IC u₁)

/-- **annulus collar → annulus interior**. -/
theorem contDiffOn_transition_annulusCollar_annulusInterior {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((annulusCollarChart u₀).symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulusFam_gen (fiberCollarChart u₀) fiberInteriorChart
    (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    (annulusCollarChart u₀) annulusInteriorChart rfl rfl
    (contDiffOn_transition_fiber_CI u₀)

/-- **annulus collar → annulus collar**. -/
theorem contDiffOn_transition_annulusCollar_CC {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((annulusCollarChart u₀).symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulusFam_gen (fiberCollarChart u₀) (fiberCollarChart u₁)
    (diskCollarChart 1 u₀) (diskCollarChart 1 u₁) rfl rfl
    (annulusCollarChart u₀) (annulusCollarChart u₁) rfl rfl
    (contDiffOn_transition_fiber_CC u₀ u₁)

/-! ### §5.2. The chart0-family ↔ annulus-family classes (8 pairs) -/

/-- **chart0 interior → annulus interior**. -/
theorem contDiffOn_transition_interiorChart_annulusInterior {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(interiorChart.symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (interiorChart.symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart0_annulus_gen fiberInteriorChart fiberInteriorChart
    (DiskChartGeneric.diskInteriorChart 1) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    interiorChart annulusInteriorChart rfl rfl
    (contDiffOn_twistFiberTrans_II contDiffOn_twistU hUn)

/-- **chart0 interior → annulus collar**. -/
theorem contDiffOn_transition_interiorChart_annulusCollar {k : WithTop ℕ∞} (u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(interiorChart.symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (interiorChart.symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart0_annulus_gen fiberInteriorChart (fiberCollarChart u₁)
    (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁) rfl rfl
    interiorChart (annulusCollarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_IC u₁ contDiffOn_twistU hUn)

/-- **chart0 collar → annulus interior**. -/
theorem contDiffOn_transition_collarChart_annulusInterior {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((collarChart u₀).symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((collarChart u₀).symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart0_annulus_gen (fiberCollarChart u₀) fiberInteriorChart
    (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    (collarChart u₀) annulusInteriorChart rfl rfl
    (contDiffOn_twistFiberTrans_CI u₀ contDiffOn_twistU hUn)

/-- **chart0 collar → annulus collar**. -/
theorem contDiffOn_transition_collarChart_annulusCollar {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((collarChart u₀).symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((collarChart u₀).symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart0_annulus_gen (fiberCollarChart u₀) (fiberCollarChart u₁)
    (diskCollarChart 1 u₀) (diskCollarChart 1 u₁) rfl rfl
    (collarChart u₀) (annulusCollarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_CC u₀ u₁ contDiffOn_twistU hUn)

/-- **annulus interior → chart0 interior**. -/
theorem contDiffOn_transition_annulusInterior_interiorChart {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ interiorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (annulusInteriorChart.symm ≫ₕ interiorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart0_gen fiberInteriorChart fiberInteriorChart
    (DiskChartGeneric.diskInteriorChart 1) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    annulusInteriorChart interiorChart rfl rfl
    (contDiffOn_twistFiberTrans_II contDiffOn_twistUConj hUnConj)

/-- **annulus interior → chart0 collar**. -/
theorem contDiffOn_transition_annulusInterior_collarChart {k : WithTop ℕ∞} (u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ collarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (annulusInteriorChart.symm ≫ₕ collarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart0_gen fiberInteriorChart (fiberCollarChart u₁)
    (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁) rfl rfl
    annulusInteriorChart (collarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_IC u₁ contDiffOn_twistUConj hUnConj)

/-- **annulus collar → chart0 interior**. -/
theorem contDiffOn_transition_annulusCollar_interiorChart {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ interiorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((annulusCollarChart u₀).symm ≫ₕ interiorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart0_gen (fiberCollarChart u₀) fiberInteriorChart
    (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    (annulusCollarChart u₀) interiorChart rfl rfl
    (contDiffOn_twistFiberTrans_CI u₀ contDiffOn_twistUConj hUnConj)

/-- **annulus collar → chart0 collar**. -/
theorem contDiffOn_transition_annulusCollar_collarChart {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ collarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' ((annulusCollarChart u₀).symm ≫ₕ collarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart0_gen (fiberCollarChart u₀) (fiberCollarChart u₁)
    (diskCollarChart 1 u₀) (diskCollarChart 1 u₁) rfl rfl
    (annulusCollarChart u₀) (collarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_CC u₀ u₁ contDiffOn_twistUConj hUnConj)

/-! ### §5.3. The chart1-family ↔ annulus-family classes (8 pairs) -/

/-- **chart1 interior → annulus interior**. -/
theorem contDiffOn_transition_interiorChart1_annulusInterior {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(interiorChart1.symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (interiorChart1.symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart1_annulus_gen fiberInteriorChart fiberInteriorChart
    (DiskChartGeneric.diskInteriorChart 1) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    interiorChart1 annulusInteriorChart rfl rfl
    (contDiffOn_twistFiberTrans_II contDiffOn_twistU hUn)

/-- **chart1 interior → annulus collar**. -/
theorem contDiffOn_transition_interiorChart1_annulusCollar {k : WithTop ℕ∞} (u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(interiorChart1.symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (interiorChart1.symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart1_annulus_gen fiberInteriorChart (fiberCollarChart u₁)
    (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁) rfl rfl
    interiorChart1 (annulusCollarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_IC u₁ contDiffOn_twistU hUn)

/-- **chart1 collar → annulus interior**. -/
theorem contDiffOn_transition_collarChart1_annulusInterior {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((collarChart1 u₀).symm ≫ₕ annulusInteriorChart) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((collarChart1 u₀).symm ≫ₕ annulusInteriorChart).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart1_annulus_gen (fiberCollarChart u₀) fiberInteriorChart
    (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    (collarChart1 u₀) annulusInteriorChart rfl rfl
    (contDiffOn_twistFiberTrans_CI u₀ contDiffOn_twistU hUn)

/-- **chart1 collar → annulus collar**. -/
theorem contDiffOn_transition_collarChart1_annulusCollar {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((collarChart1 u₀).symm ≫ₕ annulusCollarChart u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((collarChart1 u₀).symm ≫ₕ annulusCollarChart u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_chart1_annulus_gen (fiberCollarChart u₀) (fiberCollarChart u₁)
    (diskCollarChart 1 u₀) (diskCollarChart 1 u₁) rfl rfl
    (collarChart1 u₀) (annulusCollarChart u₁) rfl rfl
    (contDiffOn_twistFiberTrans_CC u₀ u₁ contDiffOn_twistU hUn)

/-- **annulus interior → chart1 interior**. -/
theorem contDiffOn_transition_annulusInterior_interiorChart1 {k : WithTop ℕ∞} :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ interiorChart1) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (annulusInteriorChart.symm ≫ₕ interiorChart1).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart1_gen fiberInteriorChart fiberInteriorChart
    (DiskChartGeneric.diskInteriorChart 1) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    annulusInteriorChart interiorChart1 rfl rfl
    (contDiffOn_twistFiberTrans_II contDiffOn_twistU hUn)

/-- **annulus interior → chart1 collar**. -/
theorem contDiffOn_transition_annulusInterior_collarChart1 {k : WithTop ℕ∞} (u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑(annulusInteriorChart.symm ≫ₕ collarChart1 u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹' (annulusInteriorChart.symm ≫ₕ collarChart1 u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart1_gen fiberInteriorChart (fiberCollarChart u₁)
    (DiskChartGeneric.diskInteriorChart 1) (diskCollarChart 1 u₁) rfl rfl
    annulusInteriorChart (collarChart1 u₁) rfl rfl
    (contDiffOn_twistFiberTrans_IC u₁ contDiffOn_twistU hUn)

/-- **annulus collar → chart1 interior**. -/
theorem contDiffOn_transition_annulusCollar_interiorChart1 {k : WithTop ℕ∞} (u₀ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ interiorChart1) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((annulusCollarChart u₀).symm ≫ₕ interiorChart1).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart1_gen (fiberCollarChart u₀) fiberInteriorChart
    (diskCollarChart 1 u₀) (DiskChartGeneric.diskInteriorChart 1) rfl rfl
    (annulusCollarChart u₀) interiorChart1 rfl rfl
    (contDiffOn_twistFiberTrans_CI u₀ contDiffOn_twistU hUn)

/-- **annulus collar → chart1 collar**. -/
theorem contDiffOn_transition_annulusCollar_collarChart1 {k : WithTop ℕ∞} (u₀ u₁ : NSphere 1) :
    ContDiffOn ℝ k (↑((𝓡 3).prod (𝓡∂ 1)) ∘
        ↑((annulusCollarChart u₀).symm ≫ₕ collarChart1 u₁) ∘ ↑((𝓡 3).prod (𝓡∂ 1)).symm)
      (↑((𝓡 3).prod (𝓡∂ 1)).symm ⁻¹'
          ((annulusCollarChart u₀).symm ≫ₕ collarChart1 u₁).source ∩
        range ↑((𝓡 3).prod (𝓡∂ 1))) :=
  contDiffOn_transition_annulus_chart1_gen (fiberCollarChart u₀) (fiberCollarChart u₁)
    (diskCollarChart 1 u₀) (diskCollarChart 1 u₁) rfl rfl
    (annulusCollarChart u₀) (collarChart1 u₁) rfl rfl
    (contDiffOn_twistFiberTrans_CC u₀ u₁ contDiffOn_twistU hUn)

/-! ### §5.4. The `IsManifold` certificate -/

/-- **`ResE` is a smooth manifold-with-boundary** on `ModelProd (𝓔 3) (EuclideanHalfSpace 1)` — the
K6′a Leg-2 E-side certificate, at every regularity `k` (including `C^∞` and `C^ω`). The full 6×6
atlas dispatch: cross-side pairs are vacuous (disjoint sources), same-side base-interior pairs are
`contDiffOn_transition_baseInterior_gen` (§P.1 of the Boundary module), annulus-annulus pairs are
the untwisted product transitions, annulus↔base pairs the `regDir`-twisted classes. Kernel-pure
`{propext, Classical.choice, Quot.sound}`. -/
theorem isManifold_resE {k : WithTop ℕ∞} :
    IsManifold ((𝓡 3).prod (𝓡∂ 1)) k ResE := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  have he2 : e ∈ atlasE := he
  have he'2 : e' ∈ atlasE := he'
  simp only [atlasE, Set.union_assoc, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_range] at he2 he'2
  obtain (rfl | rfl | rfl) | ⟨u₀, rfl⟩ | ⟨u₀, rfl⟩ | ⟨u₀, rfl⟩ := he2 <;>
    obtain (rfl | rfl | rfl) | ⟨u₁, rfl⟩ | ⟨u₁, rfl⟩ | ⟨u₁, rfl⟩ := he'2
  · exact contDiffOn_transition_interiorChart_II
  · exact contDiffOn_transition_cross interiorChart_source_subset interiorChart1_source_subset
  · exact contDiffOn_transition_interiorChart_annulusInterior
  · exact contDiffOn_transition_interiorChart_collarChart u₁
  · exact contDiffOn_transition_cross interiorChart_source_subset (collarChart1_source_subset u₁)
  · exact contDiffOn_transition_interiorChart_annulusCollar u₁
  · exact contDiffOn_transition_cross' interiorChart1_source_subset interiorChart_source_subset
  · exact contDiffOn_transition_interiorChart1_II
  · exact contDiffOn_transition_interiorChart1_annulusInterior
  · exact contDiffOn_transition_cross' interiorChart1_source_subset
      (collarChart_source_subset u₁)
  · exact contDiffOn_transition_interiorChart1_collarChart1 u₁
  · exact contDiffOn_transition_interiorChart1_annulusCollar u₁
  · exact contDiffOn_transition_annulusInterior_interiorChart
  · exact contDiffOn_transition_annulusInterior_interiorChart1
  · exact contDiffOn_transition_annulusInterior_II
  · exact contDiffOn_transition_annulusInterior_collarChart u₁
  · exact contDiffOn_transition_annulusInterior_collarChart1 u₁
  · exact contDiffOn_transition_annulusInterior_annulusCollar u₁
  · exact contDiffOn_transition_collarChart_interiorChart u₀
  · exact contDiffOn_transition_cross (collarChart_source_subset u₀)
      interiorChart1_source_subset
  · exact contDiffOn_transition_collarChart_annulusInterior u₀
  · exact contDiffOn_transition_collarChart_CC u₀ u₁
  · exact contDiffOn_transition_cross (collarChart_source_subset u₀)
      (collarChart1_source_subset u₁)
  · exact contDiffOn_transition_collarChart_annulusCollar u₀ u₁
  · exact contDiffOn_transition_cross' (collarChart1_source_subset u₀)
      interiorChart_source_subset
  · exact contDiffOn_transition_collarChart1_interiorChart1 u₀
  · exact contDiffOn_transition_collarChart1_annulusInterior u₀
  · exact contDiffOn_transition_cross' (collarChart1_source_subset u₀)
      (collarChart_source_subset u₁)
  · exact contDiffOn_transition_collarChart1_CC u₀ u₁
  · exact contDiffOn_transition_collarChart1_annulusCollar u₀ u₁
  · exact contDiffOn_transition_annulusCollar_interiorChart u₀
  · exact contDiffOn_transition_annulusCollar_interiorChart1 u₀
  · exact contDiffOn_transition_annulusCollar_annulusInterior u₀
  · exact contDiffOn_transition_annulusCollar_collarChart u₀ u₁
  · exact contDiffOn_transition_annulusCollar_collarChart1 u₀ u₁
  · exact contDiffOn_transition_annulusCollar_CC u₀ u₁

/-- The certificate as a typeclass instance (any regularity `k`), so Mathlib's
boundary-manifold API finds the smooth structure on `ResE` by instance resolution. -/
instance instIsManifoldResE {k : WithTop ℕ∞} : IsManifold ((𝓡 3).prod (𝓡∂ 1)) k ResE :=
  isManifold_resE

/-! ## §Z. STATUS — the E-side `IsManifold` certificate COMPLETE

**GREEN — task #288's residual fully closed: all 36/36 atlas transition pairs + the dispatch.**

* §1 — the `C^∞` bridge (`contDiff_toE2`/`contDiff_ofE2`), the rotation `rotE2` (jointly smooth,
  norm-multiplicative, `ℝ`-homogeneous), the unit twists `twistU`/`twistUConj` (`C^∞` on the
  annulus `{1/2 < ‖b‖}`), and the annulus-region norm extraction lemmas.
* §2 — `contDiffOn_reshapeConjTwist`: the base-coupled generalization of the Boundary module's
  `contDiffOn_reshapeConj` (the fiber block may read the base coordinate — the twist forces this;
  the product-form wrapper cannot express the annulus↔base classes).
* §3 — the four **twisted fiber classes** `contDiffOn_twistFiberTrans_{II,CI,IC,CC}` (recover
  through `D₀`, rotate by the unit `U b`, chart through `D₁`), plus the interior/collar-target
  normal-form smoothness helpers and the `diskHomeo_trivFiber`/`diskHomeo_recoverFiber0` bridges
  (the `Disk`-level twist IS the clamped `rotE2` rotation on `NDisk 1`).
* §4 — the five **general transition theorems**: `annulusFam` (annulus-annulus, untwisted §O
  fiber, `annulusTriv` cancels by `right_inv`), `chart0_annulus`/`chart1_annulus` (val-lift source,
  annulus target; `gBase = id` resp. `toE2∘regInv∘ofE2`; fiber `twistU`), and
  `annulus_chart0`/`annulus_chart1` (annulus source, val-lift target; the `annulusTrivInv` branch
  is FORCED by the weld-disjointness — the wrong branch would equate a base-interior `chart0`
  point with a `chart1` point, impossible off the equator; fiber `twistUConj` resp. `twistU`).
* §5 — the 20 pair instantiations (4 annulus-annulus + 16 annulus↔base), the cross-mirror
  `contDiffOn_transition_cross'`, and **`isManifold_resE : IsManifold ((𝓡 3).prod (𝓡∂ 1)) k ResE`**
  (+ the instance form `instIsManifoldResE`) — the 6×6 `isManifold_of_contDiffOn` dispatch over
  `atlasE`: 8 cross-side (vacuous) + 8 same-side base-interior (§P.1, Boundary) + 4
  annulus-annulus + 16 annulus↔base pairs.

**This is the E-side smooth manifold-with-boundary certificate K6′b (the smooth weld) consumes**
opposite the T⁴°-side `KummerShellChart` exterior certificate. Remaining K6′b-side work (not this
module): the smooth `∂E ≅ ℝP³` upgrade of `bdryHomeoRP3` in these charts, and the weld itself.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom. -/

end

end SKEFTHawking.KummerResolutionPieceManifold
