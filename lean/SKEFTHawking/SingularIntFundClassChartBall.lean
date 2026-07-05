import Mathlib
import SKEFTHawking.SingularIntFundamentalClassExist
import SKEFTHawking.SingularChartBallBijectiveInt

/-!
# The oriented fundamental-class base case on a chart ball (brick 18e)

The base case of the ℤ chart-cover fundamental-class induction: on a chart ball `K` (a closed-ball
chart neighbourhood), the oriented fundamental class exists — there is a `±1` orientation section
`orient` on `K` and a class `α ∈ Hₙ(M|K;ℤ)` restricting, at every `x ∈ K`, to the ORIENTED local
generator `orientedLocalGenerator x (orient x)`.

The construction (cleaner than the mod-2 `hasFundClass_chartBall`, which needed a locally-constant
`localComposite`): the chart-ball restriction `restrictToPointInt hx` is bijective at every `x ∈ K`
(brick 18-chartBall `restrictToPointInt_chartBall_bijective`), so `perEquivInt x hx :
Hₙ(M|K;ℤ) ≃+ ℤ` is the composite with the local iso `iso_x`. Set `α := (perEquivInt y₀).symm 1`
(normalise at the centre) and `orient x := perEquivInt x α`. Then:
* `restrictsToOrientedGeneratorInt orient α` holds **definitionally** (`iso.symm_apply_apply` + the
  ℤ-linearity of `iso.symm`), NO local-constancy needed — the sign is tracked by `orient`;
* `orient x = ±1` because `orient x = ((perEquivInt y₀).symm.trans (perEquivInt x)) 1` and an
  additive automorphism of `ℤ` sends `1` to a unit.

Orientation COHERENCE across overlapping balls is NOT a base-case concern (each ball carries its own
`orient` from its chart); it is the union step's obligation. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.IntOrientationSection (orientedLocalGenerator restrictToPointInt)
open SKEFTHawking.SingularIntFundamentalClassExist

namespace SKEFTHawking.SingularIntFundClassChartBall

/-- **An additive automorphism of `ℤ` sends `1` to a unit** (hence to `±1`): `e.symm (e 1) = 1`
expands by `map_zsmul` to `e 1 • e.symm 1 = 1`, i.e. `e 1 * e.symm 1 = 1`. -/
theorem intAddEquiv_apply_one_isUnit (e : ℤ ≃+ ℤ) : IsUnit (e 1) := by
  let e' : ℤ ≃ₗ[ℤ] ℤ := { e with map_smul' := fun r x => map_zsmul e r x }
  have hee : e' 1 = e 1 := rfl
  rw [← hee]
  have h : e' 1 * e'.symm 1 = 1 := by
    have hk := e'.symm_apply_apply 1
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    exact hk
  exact ⟨Units.mkOfMulEqOne (e' 1) (e'.symm 1) h, rfl⟩

/-- `n • iso.symm 1 = iso.symm n` for an additive iso to `ℤ` (ℤ-linearity of `iso.symm`). -/
theorem smul_symm_one {A : Type*} [AddCommGroup A] (iso : A ≃+ ℤ) (n : ℤ) :
    n • iso.symm 1 = iso.symm n := by simpa using (map_zsmul iso.symm n 1).symm

variable {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- The per-point composite additive iso `Hₙ(M|K;ℤ) ≃+ ℤ` at a point `x` of a chart ball `K`, where
the restriction `restrictToPointInt hx` is bijective (brick 18-chartBall) and `iso_x` is the local
iso `H₄(M|x;ℤ) ≃+ ℤ`. -/
noncomputable def perEquivInt (y₀ : M) {r : ℝ}
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).target)
    {x : M} (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
      Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r) :
    RelHomologyInt (X := TopCat.of M)
        ((chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r)ᶜ 4 ≃+ ℤ :=
  ((LinearEquiv.ofBijective (restrictToPointInt (X := TopCat.of M) hx 4)
      (SKEFTHawking.SingularChartBallBijectiveInt.restrictToPointInt_chartBall_bijective
        y₀ hrsub hx)).toAddEquiv).trans
    (SKEFTHawking.SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold' x).iso

/-- **The oriented fundamental class exists on a chart ball** (base case of the ℤ chart-cover
induction): for a closed-ball chart neighbourhood `K = (chartAt y₀).symm '' B̄(chartAt y₀·y₀, r)`
(`0 ≤ r`, `B̄ ⊆ target`) there is a `±1` orientation section `orient` on `K` and a class realising the
oriented fundamental class on `K` (`hasOrientedFundClassInt orient K`).

Construction: `α := (perEquivInt y₀).symm 1` (centre-normalised), `orient x := perEquivInt x α`.
`orient x = ((perEquivInt y₀).symm.trans (perEquivInt x)) 1 = ±1` (additive-aut-of-`ℤ` sends `1` to a
unit); `restrictsToOrientedGeneratorInt orient α` is `iso.symm_apply_apply` after `smul_symm_one`. No
local-constancy / connectivity needed — the sign is carried by `orient`. -/
theorem hasOrientedFundClassInt_chartBall (y₀ : M) {r : ℝ} (hr : 0 ≤ r)
    (hrsub : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r
      ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).target) :
    ∃ orient : M → ℤ,
      (∀ x ∈ (chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
          Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r,
        orient x = 1 ∨ orient x = -1) ∧
      hasOrientedFundClassInt orient ((chartAt (EuclideanSpace ℝ (Fin 4)) y₀).symm ''
        Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 4)) y₀ y₀) r) := by
  classical
  set c := chartAt (EuclideanSpace ℝ (Fin 4)) y₀ with hc
  set K : Set M := c.symm '' Metric.closedBall (c y₀) r with hKdef
  have hy₀K : y₀ ∈ K := ⟨c y₀, Metric.mem_closedBall_self hr, c.left_inv (mem_chart_source _ y₀)⟩
  set α := (perEquivInt y₀ hrsub hy₀K).symm 1 with hα
  refine ⟨fun x => if hx : x ∈ K then perEquivInt y₀ hrsub hx α else 1, ?_, α, ?_⟩
  · intro x hx
    simp only [dif_pos hx]
    have hunit : perEquivInt y₀ hrsub hx α
        = ((perEquivInt y₀ hrsub hy₀K).symm.trans (perEquivInt y₀ hrsub hx)) 1 := by
      rw [AddEquiv.trans_apply, hα]
    rw [hunit]
    exact Int.isUnit_iff.mp (intAddEquiv_apply_one_isUnit _)
  · intro x hx
    simp only [dif_pos hx]
    -- `restrictToPointInt hx α = orientedLocalGenerator x (perEquivInt x α)`
    have hval : perEquivInt y₀ hrsub hx α
        = (SKEFTHawking.SingularReducedGeneratorInt.intLocalHomologyIso_of_manifold' x).iso
            (restrictToPointInt hx 4 α) := by
      simp only [perEquivInt, AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
      congr 1
    rw [hval, SKEFTHawking.IntOrientationSection.orientedLocalGenerator,
      SKEFTHawking.SingularRelHomologyInt.localGenerator, smul_symm_one, AddEquiv.symm_apply_apply]

end SKEFTHawking.SingularIntFundClassChartBall
