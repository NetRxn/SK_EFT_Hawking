/-
# Phase 5q.H (N6 + orientation) — FIRING the σ÷16 leg at S⁴: spin discharged, orientation isolated

`SphereWitnessTowerInt.sixteen_dvd_latticeSig_sphere4` fires the kron-free σ÷16 leg at the first
witness with exactly two open binders: the spin certificate `hv2 : wuClass2 (…) = 0` and the
orientation datum `d : IntOrientationData SphereFour` (normalised `orient ≡ 1`). This module closes
that gap to a SINGLE named geometric Prop:

* §1 — the SPIN binder is DISCHARGED (`sphere4_wuClass2_eq_zero`): the Wu class `v₂ ∈ H²(S⁴;ℤ/2)`
  vanishes because the whole group does — mod-2 middle vanishing (`sphere_homology_middle` at
  `(2,4)`) flipped through the mod-2 (field) universal-coefficients Kronecker non-degeneracy
  (`cohomology_eq_zero_of_kroneckerH`), packaged as the general
  `cohomologyMod2_subsingleton_of_homology` (the ℤ/2 mirror of
  `SphereWitnessTowerInt.cohomology_subsingleton_of_homology`, instance-free — field coefficients).
* §2 — the ORIENTATION binder is reduced to the honest single-Prop freeze
  `Sphere4ChartBallsOriented`: the constant `+1` section is realisable on every chart ball of S⁴
  (the `hballs` residual of the 18h constructor `intOrientationDataOfOrientation`, verbatim at
  `M = SphereFour`, `orient ≡ 1`). Given it, `sphere4IntOrientationData` assembles the full
  `IntOrientationData SphereFour` (global `[S⁴]` + per-point restrictions + mod-2 `redCompat`)
  through the proved 18e–18h chain.
* §3 — the freeze is SHRUNK to a strictly local statement
  (`sphere4ChartBallsOriented_of_locallyConstant`): chart balls are preconnected
  (`chartBall_isPreconnected` — continuous image of a convex closed ball), and a locally constant
  `±1` sign section on a preconnected ball normalises to the constant `+1` realisation
  (`hasOrientedFundClassInt_const_one_of_isLocallyConstant` — flip the witness class by `-1` if
  needed). Since `hasOrientedFundClassInt_chartBall` already produces a per-ball `±1` realisation,
  the ONLY remaining geometric content of the freeze is the LOCAL CONSTANCY of the per-ball sign
  section — the atlas transition-degree coherence (stereographic charts at nearby poles compare
  with local degree `+1`). Discharge plan: a moving-puncture local-degree continuity device on the
  `chartLocalIsoInt` tower (brick 14f), applied to the S⁴ stereographic atlas — a future arc.
* §4 — **the σ÷16 leg FIRES at S⁴ modulo ONLY the freeze**
  (`sixteen_dvd_latticeSig_sphere4_of_chartBallsOriented`): every other input of the leg —
  the full instance package (N5), the basis datum, `htopo` (N2), and now the spin certificate
  (N6) and the orientation packaging — is a THEOREM. This is the closest-to-unconditional
  Rokhlin-leg instantiation in the tree: one named geometric Prop from zero-binder firing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereWitnessTowerInt
import SKEFTHawking.SingularIntOrientationDataConstruct
import SKEFTHawking.SingularIntFundClassChartBall
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularSphereMiddle

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularIntFundamentalClassExist
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.SphereWitnessTowerInt

namespace SKEFTHawking.SphereWitnessFiringInt

/-! ## §1. The spin binder: `v₂(S⁴) = 0` from mod-2 middle vanishing + field UCT -/

/-- **Mod-2 cohomology vanishes where mod-2 homology does** (field universal coefficients,
packaged): if `Hₙ₊₁(X;ℤ/2) = 0` then `Hⁿ⁺¹(X;ℤ/2) = 0` — every class pairs to `0` with every
homology class, so it is `0` by the Kronecker non-degeneracy
(`SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH`). The ℤ/2 mirror of
`SphereWitnessTowerInt.cohomology_subsingleton_of_homology`; over the field NO freeness /
projectivity instances are needed. -/
theorem cohomologyMod2_subsingleton_of_homology (X : TopCat) (N : ℕ)
    [Subsingleton (SKEFTHawking.SingularHomologyMod2.Homology X (N + 1))] :
    Subsingleton (SKEFTHawking.SingularCohomologyMod2.Cohomology X (N + 1)) :=
  subsingleton_of_forall_eq 0 fun ω =>
    SKEFTHawking.SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH N ω fun β => by
      rw [Subsingleton.elim β 0, map_zero]

/-- **`H₂(S⁴;ℤ/2) = 0`** — the mod-2 sphere tower's middle vanishing at `(2, 4)`. -/
instance : Subsingleton (SKEFTHawking.SingularHomologyMod2.Homology (Sph 4) 2) :=
  subsingleton_of_forall_eq 0
    (SKEFTHawking.SingularSphereMiddle.sphere_homology_middle 2 4 two_pos (by norm_num))

/-- **`H²(S⁴;ℤ/2) = 0`** — the field-UCT flip of the mod-2 middle vanishing. The group the Wu
class `v₂` lives in is trivial at the first witness. -/
instance : Subsingleton (SKEFTHawking.SingularCohomologyMod2.Cohomology (Sph 4) 2) :=
  haveI : Subsingleton (SKEFTHawking.SingularHomologyMod2.Homology (Sph 4) (1 + 1)) :=
    inferInstanceAs (Subsingleton (SKEFTHawking.SingularHomologyMod2.Homology (Sph 4) 2))
  cohomologyMod2_subsingleton_of_homology (Sph 4) 1

/-- **The σ÷16 leg's SPIN binder DISCHARGED at S⁴ (N6)**: the Wu class `v₂` of the genuine
Poincaré-duality datum vanishes, because `H²(S⁴;ℤ/2) = 0` outright. This is the exact `hv2` input
of `SphereWitnessTowerInt.sixteen_dvd_latticeSig_sphere4` — S⁴ is spin through the same Wu
formalism the leg consumes, with no hypothesis. -/
theorem sphere4_wuClass2_eq_zero :
    wuClass2 (poincareDual4Mid_of_closed (M := SphereFour)) = 0 :=
  haveI : Subsingleton (SKEFTHawking.SingularCohomologyMod2.Cohomology (TopCat.of SphereFour) 2) :=
    inferInstanceAs (Subsingleton (SKEFTHawking.SingularCohomologyMod2.Cohomology (Sph 4) 2))
  Subsingleton.elim _ _

/-! ## §2. The orientation binder: the honest single-Prop freeze + the datum it buys -/

/-- **The S⁴ chart-ball orientation coherence — the honest single-Prop freeze.** The constant `+1`
orientation section is realisable on every chart ball of S⁴: this is the `hballs` residual of the
18h constructor `intOrientationDataOfOrientation`, verbatim at `M = SphereFour`, `orient ≡ 1`.

The TRUE geometric content (see §3 for the reduction): the per-point local generators
`orientedLocalGenerator y 1` are pinned to the chart AT `y` (`intLocalHomologyIso_of_manifold' y`,
via `chartAt y` = stereographic projection from `-y`), so realising a single constant section on a
whole ball is exactly the orientation coherence of the stereographic atlas — nearby-pole chart
transitions have local degree `+1`. Mathematically true (the all-poles stereographic atlas is an
oriented atlas); NOT yet provable in-tree: the mod-2 agreement device
(`localComposite_agree_chartBall`, unique iso to `ℤ/2`) has no ℤ analogue, and no integral
local-degree comparison across DIFFERENT charts exists. Discharge plan: §3 reduces this to local
constancy of the per-ball sign section; the future arc builds a moving-puncture local-degree
continuity device on the `chartLocalIsoInt` tower and evaluates it on the stereographic atlas. -/
def Sphere4ChartBallsOriented : Prop :=
  ∀ (x : SphereFour) (ρ : ℝ), 0 ≤ ρ →
    Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
      ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
    hasOrientedFundClassInt (fun _ => (1 : ℤ))
      ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ)

/-- S⁴ is preconnected (path-connected: `isPathConnected_sphere` in rank `5 > 1`) — the
`[PreconnectedSpace]` input of the 18h `redCompat` (mod-2 uniqueness at a basepoint). -/
instance : PreconnectedSpace SphereFour := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 5)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < 5)
  have hpc : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 5)) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  haveI : PathConnectedSpace SphereFour := isPathConnected_iff_pathConnectedSpace.mp hpc
  infer_instance

/-- **The S⁴ orientation datum from the freeze**: given `Sphere4ChartBallsOriented`, the full
`IntOrientationData SphereFour` with the constant `+1` section — the global `[S⁴] ∈ H₄(S⁴;ℤ)`
(`intFundClass` over the univ witness glued by `hasOrientedFundClassInt_univ`), its per-point
restriction to the `+1` local generator, and the mod-2 `redCompat`. Everything here is the proved
18e–18h chain; the freeze is the only hypothesis. -/
noncomputable def sphere4IntOrientationData (h : Sphere4ChartBallsOriented) :
    IntOrientationData SphereFour :=
  haveI hUniv := SKEFTHawking.SingularIntFundClassUnivInt.hasOrientedFundClassInt_univ
    (M := SphereFour) (fun _ => 1) h
  { orient := fun _ => 1
    orient_unit := fun _ => Or.inl rfl
    fundClass := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass hUniv
    restricts := SKEFTHawking.SingularIntOrientationDataConstruct.intFundClass_restricts hUniv
    redCompat := SKEFTHawking.SingularIntOrientationDataConstruct.redCompat_intFundClass hUniv
      (fun _ => Or.inl rfl) }

/-! ## §3. Shrinking the freeze: connected balls normalise locally constant signs -/

section FreezeReduction

variable {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

omit [T1Space M] in
/-- **Chart balls are preconnected** — the continuous (`continuousOn_symm`) image of a convex
closed ball. The topological half of the freeze reduction: on a preconnected ball a locally
constant sign section is constant. -/
theorem chartBall_isPreconnected (x : M) {ρ : ℝ}
    (hsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
      ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target) :
    IsPreconnected ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ) :=
  (convex_closedBall _ _).isPreconnected.image _
    ((chartAt (EuclideanSpace ℝ (Fin 4)) x).continuousOn_symm.mono hsub)

/-- The oriented local generator is `ℤ`-odd in the sign: `orientedLocalGenerator x (-s)
= -orientedLocalGenerator x s` (`neg_smul` through the definition `s • localGenerator x`). -/
theorem orientedLocalGenerator_neg (x : M) (s : ℤ) :
    orientedLocalGenerator x (-s) = -orientedLocalGenerator x s :=
  neg_smul s _

/-- **A locally constant `±1` realisation on a preconnected set normalises to the constant `+1`
realisation.** If some `±1`-valued section `orient` (locally constant as a function on `↥K`,
`K` preconnected) is realised by an oriented fundamental class on `K`, then so is the constant
section `+1`: local constancy + preconnectedness force `orient` to be a constant `ε ∈ {±1}` on
`K`, and for `ε = -1` the negated witness class realises `+1`
(`orientedLocalGenerator_neg`). This is the general-`M` reduction that shrinks the orientation
freeze from a whole-ball coherence statement to a strictly LOCAL one. -/
theorem hasOrientedFundClassInt_const_one_of_isLocallyConstant
    {K : Set M} (hKconn : IsPreconnected K) {x₀ : M} (hx₀ : x₀ ∈ K)
    {orient : M → ℤ} (horient : ∀ x ∈ K, orient x = 1 ∨ orient x = -1)
    (hlc : IsLocallyConstant (K.restrict orient))
    (h : hasOrientedFundClassInt orient K) :
    hasOrientedFundClassInt (fun _ => (1 : ℤ)) K := by
  obtain ⟨α, hα⟩ := h
  haveI : PreconnectedSpace ↑K := Subtype.preconnectedSpace hKconn
  have hconst : ∀ x, ∀ hx : x ∈ K, orient x = orient x₀ := fun x hx =>
    hlc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨x₀, hx₀⟩
  rcases horient x₀ hx₀ with h1 | hm1
  · exact ⟨α, fun x hx => by rw [hα x hx, hconst x hx, h1]⟩
  · refine ⟨-α, fun x hx => ?_⟩
    rw [map_neg, hα x hx, hconst x hx, hm1, show (-1 : ℤ) = -(1 : ℤ) from rfl,
      orientedLocalGenerator_neg]
    exact neg_neg _

/-- **The S⁴ orientation freeze follows from per-ball LOCALLY CONSTANT sign sections.** If every
chart ball of S⁴ carries an oriented fundamental class w.r.t. some `±1` section that is locally
constant on the ball, then `Sphere4ChartBallsOriented` holds — chart balls are preconnected
(`chartBall_isPreconnected`), so the section normalises to the constant `+1`
(`hasOrientedFundClassInt_const_one_of_isLocallyConstant`). Combined with the base case
`hasOrientedFundClassInt_chartBall` (which already produces a per-ball `±1` realisation), the
ONLY remaining content of the freeze is the local constancy of the per-ball sign section — the
atlas transition-degree coherence, the named discharge target. -/
theorem sphere4ChartBallsOriented_of_locallyConstant
    (h : ∀ (x : SphereFour) (ρ : ℝ), 0 ≤ ρ →
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ
        ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) x).target →
      ∃ orient : SphereFour → ℤ,
        (∀ y ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
            Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ,
          orient y = 1 ∨ orient y = -1) ∧
        IsLocallyConstant (((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
            Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ).restrict orient) ∧
        hasOrientedFundClassInt orient ((chartAt (EuclideanSpace ℝ (Fin 4)) x).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) x x) ρ)) :
    Sphere4ChartBallsOriented := by
  intro x ρ hρ hsub
  obtain ⟨orient, hpm, hlc, hK⟩ := h x ρ hρ hsub
  exact hasOrientedFundClassInt_const_one_of_isLocallyConstant
    (chartBall_isPreconnected x hsub)
    ⟨chartAt (EuclideanSpace ℝ (Fin 4)) x x, Metric.mem_closedBall_self hρ,
      (chartAt (EuclideanSpace ℝ (Fin 4)) x).left_inv (mem_chart_source _ x)⟩
    hpm hlc hK

end FreezeReduction

/-! ## §4. THE FIRING: the σ÷16 leg at S⁴, conditional on ONLY the freeze -/

/-- **The σ÷16 leg FIRES at S⁴ modulo ONLY the chart-ball orientation freeze.** Every other input
of `SphereWitnessTowerInt.sixteen_dvd_latticeSig_sphere4` is a THEOREM: the N5 instance package
and basis datum (computed sphere tower), `htopo` (`sphere4_interMatrix_htopo`, N2), the spin
certificate (`sphere4_wuClass2_eq_zero`, N6 — §1), and the orientation packaging
(`sphere4IntOrientationData`, 18e–18h). This is the FIRST Rokhlin-leg instantiation in the tree
with a single named geometric Prop between it and a zero-binder firing; at the consistency witness
the conclusion is `16 ∣ 0` (`b₂(S⁴) = 0`), and the value of the theorem is that the WHOLE leg
pipeline — orientation → intersection form → even unimodularity → σ÷16 — type-checks and fires
end-to-end on computed inputs. -/
theorem sixteen_dvd_latticeSig_sphere4_of_chartBallsOriented (h : Sphere4ChartBallsOriented) :
    (16 : ℤ) ∣ latticeSig (interMatrix
      (intFundamentalClassOfHomology (sphere4IntOrientationData h).fundClass)
      sphere4IntH2Basis) :=
  sixteen_dvd_latticeSig_sphere4 (sphere4IntOrientationData h) (fun _ => rfl)
    sphere4_wuClass2_eq_zero (sphere4_interMatrix_htopo _)

end SKEFTHawking.SphereWitnessFiringInt
