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

end SKEFTHawking.QuantumNetwork
