import SKEFTHawking.QuantumNetwork.GaussianWick
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar change of variables on `EuclideanSpace` (Phase 6AG, Ask 4 — brick 3)

The generalised polar-coordinate change of variables for the Lebesgue (`volume`) measure on
`EuclideanSpace ℝ (Fin N)`, the analytic bridge between the Gaussian moment integrals (brick 2)
and the uniform measure on the unit sphere (brick 4). Mathlib's
`Measure.measurePreserving_homeomorphUnitSphereProd` exhibits `volume` (an additive Haar measure)
as the pushforward of `volume.toSphere ⊗ volumeIoiPow (N-1)` under the homeomorphism
`x ↦ (x/‖x‖, ‖x‖)`. Adapting the radial-only `integral_fun_norm_addHaar` template to an arbitrary
integrand, we obtain the full polar identity below, in which the integrand is reparametrised by
direction `ω ∈ S` and radius `r > 0` as `g (r • ω)`.

For a *homogeneous* integrand `g = P·exp(-‖·‖²/2)` the reparametrised integrand factorises as a
product `(direction part)·(radial part)`, so `MeasureTheory.integral_prod_mul` splits the integral
into a sphere integral times a radial Gamma integral — the route used in brick 4.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory Set Metric

/-- **Polar change of variables on `EuclideanSpace ℝ (Fin N)`** (`N ≠ 0`). The Lebesgue integral
of any `g` equals the integral over `S × (0,∞)` of `g (r • ω)` against the product of the unit-sphere
surface measure `volume.toSphere` and the radial measure `volumeIoiPow (N-1)` (Lebesgue with density
`r^{N-1}`):
`∫ x, g x = ∫ (ω, r), g (r • ω) ∂(volume.toSphere ⊗ volumeIoiPow (N-1))`. -/
theorem polar_change {N : ℕ} [NeZero N] (g : EuclideanSpace ℝ (Fin N) → ℝ) :
    ∫ x, g x
      = ∫ z : (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) × Ioi (0 : ℝ),
          g ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N)))
          ∂((volume.toSphere).prod
              (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1))) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin N)) := by
    have : Nonempty (Fin N) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩⟩
    infer_instance
  rw [show (∫ x, g x)
        = ∫ x : ({(0 : EuclideanSpace ℝ (Fin N))}ᶜ : Set (EuclideanSpace ℝ (Fin N))),
            g (x : EuclideanSpace ℝ (Fin N)) ∂(Measure.comap Subtype.val volume) from by
        rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]]
  rw [show (∫ x : ({(0 : EuclideanSpace ℝ (Fin N))}ᶜ : Set (EuclideanSpace ℝ (Fin N))),
            g (x : EuclideanSpace ℝ (Fin N)) ∂(Measure.comap Subtype.val volume))
        = ∫ x : ({(0 : EuclideanSpace ℝ (Fin N))}ᶜ : Set (EuclideanSpace ℝ (Fin N))),
            (fun z : (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) × Ioi (0 : ℝ) =>
              g ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N))))
              (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin N)) x)
            ∂(Measure.comap Subtype.val volume) from by
        apply integral_congr_ae; apply Filter.Eventually.of_forall; intro x
        have hx : (x : EuclideanSpace ℝ (Fin N)) ≠ 0 := x.2
        simp only [homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]]
  exact (volume.measurePreserving_homeomorphUnitSphereProd).integral_comp
    (Homeomorph.measurableEmbedding _)
    (fun z : (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) × Ioi (0 : ℝ) =>
      g ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N))))

/-- **Homogeneous polar split.** For an integrand of the form `P·exp(-‖·‖²/2)` with `P` positively
homogeneous of degree `k` (`P (r • ω) = r^k · P ω` for `r > 0`, `‖ω‖ = 1`), the Gaussian integral
factorises into a unit-sphere integral times a radial Gamma integral:
`∫ x, P x·exp(-‖x‖²/2) = (∫_S P dσ) · (∫_{r>0} r^k·exp(-r²/2) ∂volumeIoiPow (N-1))`.
This is `polar_change` specialised: on `S × (0,∞)` the integrand becomes the product
`P(ω) · (r^k·exp(-r²/2))` (using `‖r • ω‖ = r`), split by `integral_prod_mul`. -/
theorem polar_split {N : ℕ} [NeZero N] (P : EuclideanSpace ℝ (Fin N) → ℝ) (k : ℕ)
    (hP : ∀ (r : ℝ) (ω : EuclideanSpace ℝ (Fin N)), 0 < r → ‖ω‖ = 1 → P (r • ω) = r ^ k * P ω) :
    ∫ x, P x * Real.exp (-‖x‖ ^ 2 / 2)
      = (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1, P (ω : EuclideanSpace ℝ (Fin N))
            ∂volume.toSphere)
        * (∫ r : Ioi (0 : ℝ), (r : ℝ) ^ k * Real.exp (-(r : ℝ) ^ 2 / 2)
            ∂Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)) := by
  rw [polar_change (fun x => P x * Real.exp (-‖x‖ ^ 2 / 2))]
  rw [show (∫ z : (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) × Ioi (0 : ℝ),
            P ((z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N)))
              * Real.exp (-‖(z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N))‖ ^ 2 / 2)
            ∂((volume.toSphere).prod (Measure.volumeIoiPow _)))
        = ∫ z : (sphere (0 : EuclideanSpace ℝ (Fin N)) 1) × Ioi (0 : ℝ),
            (fun ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 => P (ω : EuclideanSpace ℝ (Fin N))) z.1
              * (fun r : Ioi (0 : ℝ) => (r : ℝ) ^ k * Real.exp (-(r : ℝ) ^ 2 / 2)) z.2
            ∂((volume.toSphere).prod (Measure.volumeIoiPow _)) from by
        apply integral_congr_ae; apply Filter.Eventually.of_forall; intro z
        simp only []
        have hr : (0 : ℝ) < (z.2 : ℝ) := z.2.2
        have hω : ‖(z.1 : EuclideanSpace ℝ (Fin N))‖ = 1 := mem_sphere_zero_iff_norm.1 z.1.2
        have hnorm : ‖(z.2 : ℝ) • (z.1 : EuclideanSpace ℝ (Fin N))‖ = (z.2 : ℝ) := by
          rw [norm_smul, hω, mul_one, Real.norm_eq_abs, abs_of_pos hr]
        rw [hP (z.2 : ℝ) (z.1 : EuclideanSpace ℝ (Fin N)) hr hω, hnorm]
        ring]
  rw [integral_prod_mul
        (fun ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1 => P (ω : EuclideanSpace ℝ (Fin N)))
        (fun r : Ioi (0 : ℝ) => (r : ℝ) ^ k * Real.exp (-(r : ℝ) ^ 2 / 2))]

end SKEFTHawking.QuantumNetwork
