import SKEFTHawking.QuantumNetwork.GaussianPolar
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Uniform sphere moments via the Gaussian (Phase 6AG, Ask 4 — brick 4)

The degree-4 moment of the uniform probability measure on the unit sphere, assembled from the
Gaussian moment tensor (brick 2) and the polar split (brick 3). This file builds the **radial
infrastructure** first:

* `halfline_moment` / `halfline_rec` — the half-line Gaussian moments `∫_{r>0} r^m·exp(-r²/2)` in
  closed Gamma form and the two-step recurrence `∫ r^{m+2} = (m+1)·∫ r^m`;
* `radial_ratio` — `∫ r^{N+3}·exp = N(N+2)·∫ r^{N-1}·exp`, the ratio `M₀/M₄ = 1/(N(N+2))`
  (`= 1/(4d(d+1))` for `N = 2d`) that supplies the `1/(d(d+1))` normalisation of the sphere moment;
* `radial_volumeIoiPow` — unfolds the `volumeIoiPow` radial measure (from `polar_split`) into a
  Lebesgue integral on `(0,∞)`;
* `gaussInt_one` — the `P = 1` normalisation `∫ exp(-‖x‖²/2) = (√(2π))^N`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open MeasureTheory ProbabilityTheory Real Set Finset Metric

/-- **Half-line Gaussian moment in closed Gamma form:**
`∫_{r>0} r^m·exp(-r²/2) = (1/2)^{-(m+1)/2}·(1/2)·Γ((m+1)/2)`. -/
theorem halfline_moment (m : ℕ) :
    (∫ a in Ioi (0 : ℝ), a ^ m * Real.exp (-a ^ 2 / 2))
      = (1 / 2 : ℝ) ^ (-((m : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((m : ℝ) + 1) / 2) := by
  have hconv : (∫ a in Ioi (0 : ℝ), a ^ m * Real.exp (-a ^ 2 / 2))
      = ∫ a in Ioi (0 : ℝ), a ^ ((m : ℝ)) * Real.exp (-(1 / 2) * a ^ (2 : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
    simp only []
    rw [Real.rpow_natCast x m, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    push_cast; rw [show (-(1 / 2 : ℝ) * x ^ 2) = -x ^ 2 / 2 by ring]
  rw [hconv, integral_rpow_mul_exp_neg_mul_rpow (by norm_num)
        (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith) (by norm_num)]

/-- **Two-step moment recurrence:** `∫_{r>0} r^{m+2}·exp(-r²/2) = (m+1)·∫_{r>0} r^m·exp(-r²/2)`,
from `Γ(z+1) = z·Γ(z)`. -/
theorem halfline_rec (m : ℕ) :
    (∫ a in Ioi (0 : ℝ), a ^ (m + 2) * Real.exp (-a ^ 2 / 2))
      = ((m : ℝ) + 1) * ∫ a in Ioi (0 : ℝ), a ^ m * Real.exp (-a ^ 2 / 2) := by
  rw [halfline_moment (m + 2), halfline_moment m]
  push_cast
  rw [show (((m : ℝ) + 2) + 1) / 2 = ((m : ℝ) + 1) / 2 + 1 by ring,
      Real.Gamma_add_one (ne_of_gt (by positivity)),
      show (-(((m : ℝ) + 2) + 1) / 2) = (-((m : ℝ) + 1) / 2) + (-1) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg_one]
  ring

/-- **Radial ratio:** `∫_{r>0} r^{N+3}·exp(-r²/2) = N(N+2)·∫_{r>0} r^{N-1}·exp(-r²/2)` (`N ≥ 1`).
Hence `M₀/M₄ = 1/(N(N+2))`, which is `1/(4d(d+1))` for `N = 2d`. -/
theorem radial_ratio (N : ℕ) [NeZero N] :
    (∫ a in Ioi (0 : ℝ), a ^ (N + 3) * Real.exp (-a ^ 2 / 2))
      = (N : ℝ) * ((N : ℝ) + 2) * ∫ a in Ioi (0 : ℝ), a ^ (N - 1) * Real.exp (-a ^ 2 / 2) := by
  rcases Nat.exists_eq_succ_of_ne_zero (NeZero.ne N) with ⟨M, rfl⟩
  simp only [Nat.succ_sub_one]
  rw [show M + 1 + 3 = (M + 2) + 2 by omega, halfline_rec (M + 2), halfline_rec M]
  push_cast
  ring

/-- Unfold the `volumeIoiPow n` radial measure (the radial factor of `polar_split`) into a Lebesgue
integral on `(0,∞)`: `∫ r, r^k·exp(-r²/2) ∂volumeIoiPow n = ∫_{a>0} a^{n+k}·exp(-a²/2)`. -/
theorem radial_volumeIoiPow (n k : ℕ) :
    (∫ r : Ioi (0 : ℝ), (r : ℝ) ^ k * Real.exp (-(r : ℝ) ^ 2 / 2) ∂Measure.volumeIoiPow n)
      = ∫ a in Ioi (0 : ℝ), a ^ (n + k) * Real.exp (-a ^ 2 / 2) := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul (by fun_prop),
      integral_subtype_comap measurableSet_Ioi
        (fun a => Real.toNNReal (a ^ n) • (a ^ k * Real.exp (-a ^ 2 / 2)))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only []
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
  ring

/-- **Gaussian normalisation:** `∫ 1·exp(-‖x‖²/2) = (√(2π))^N` over `EuclideanSpace ℝ (Fin N)`. -/
theorem gaussInt_one (N : ℕ) :
    ∫ x : EuclideanSpace ℝ (Fin N), (1 : ℝ) * Real.exp (-‖x‖ ^ 2 / 2) = Real.sqrt (2 * π) ^ N := by
  have h := gaussInt_monomial N (fun _ => 0)
  simp only [pow_zero, Finset.prod_const_one] at h
  rw [h, Finset.prod_congr rfl (fun i _ => by simp only [one_mul]; exact integral_gaussian_weight),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### The real degree-4 sphere moment

Combining the polar split (brick 3) for the degree-4 monomial `P = x_a x_b x_c x_d` and for the
constant `1`, evaluated through brick 2 (`gaussRealFourTensor`) / `gaussInt_one`, and the radial
ratio, the unit-sphere surface integral of the monomial against `volume.toSphere` is the Wick
coefficient up to the `N(N+2)` normalisation. -/

/-- Polar split of the degree-4 monomial: `realWick·(√2π)^N = (∫_S x_a x_b x_c x_d dσ)·(∫ r^{N+3}·exp)`. -/
theorem sphere_polar_monomial {N : ℕ} [NeZero N] (a b c d : Fin N) :
    realWick a b c d * Real.sqrt (2 * π) ^ N
      = (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
            (ω : EuclideanSpace ℝ (Fin N)) a * (ω : EuclideanSpace ℝ (Fin N)) b
              * (ω : EuclideanSpace ℝ (Fin N)) c * (ω : EuclideanSpace ℝ (Fin N)) d ∂volume.toSphere)
        * (∫ aa in Ioi (0 : ℝ), aa ^ (N + 3) * Real.exp (-aa ^ 2 / 2)) := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := by simp
  have hhom : ∀ (r : ℝ) (ω : EuclideanSpace ℝ (Fin N)), 0 < r → ‖ω‖ = 1 →
      (fun x : EuclideanSpace ℝ (Fin N) => x a * x b * x c * x d) (r • ω)
        = r ^ 4 * (fun x : EuclideanSpace ℝ (Fin N) => x a * x b * x c * x d) ω := by
    intro r ω _ _; simp only [PiLp.smul_apply, smul_eq_mul]; ring
  have hsplit := polar_split (fun x : EuclideanSpace ℝ (Fin N) => x a * x b * x c * x d) 4 hhom
  rw [← gaussRealFourTensor a b c d, hsplit, hfin, radial_volumeIoiPow (N - 1) 4,
      show N - 1 + 4 = N + 3 by omega]

/-- Polar split of the constant `1`: `(√2π)^N = (toSphere.real univ)·(∫ r^{N-1}·exp)`. -/
theorem sphere_polar_one {N : ℕ} [NeZero N] :
    Real.sqrt (2 * π) ^ N
      = ((volume.toSphere (E := EuclideanSpace ℝ (Fin N))).real univ)
        * (∫ aa in Ioi (0 : ℝ), aa ^ (N - 1) * Real.exp (-aa ^ 2 / 2)) := by
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := by simp
  have hhom : ∀ (r : ℝ) (ω : EuclideanSpace ℝ (Fin N)), 0 < r → ‖ω‖ = 1 →
      (fun _ : EuclideanSpace ℝ (Fin N) => (1 : ℝ)) (r • ω)
        = r ^ 0 * (fun _ : EuclideanSpace ℝ (Fin N) => (1 : ℝ)) ω := by
    intro r ω _ _; simp
  have hsplit := polar_split (fun _ : EuclideanSpace ℝ (Fin N) => (1 : ℝ)) 0 hhom
  rw [← gaussInt_one N, hsplit, hfin, radial_volumeIoiPow (N - 1) 0, Nat.add_zero,
      integral_const, smul_eq_mul, mul_one]

/-- **Real degree-4 sphere moment** (division-free form): for the surface measure `volume.toSphere`
on the unit sphere of `EuclideanSpace ℝ (Fin N)` (`N ≥ 1`),
`N(N+2)·∫_S x_a x_b x_c x_d dσ = realWick(a,b,c,d)·(toSphere.real univ)`.
Dividing by the (positive) total mass gives the normalised moment `realWick/(N(N+2))`. -/
theorem sphere_moment_real {N : ℕ} [NeZero N] (a b c d : Fin N) :
    (N : ℝ) * ((N : ℝ) + 2)
        * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
            (ω : EuclideanSpace ℝ (Fin N)) a * (ω : EuclideanSpace ℝ (Fin N)) b
              * (ω : EuclideanSpace ℝ (Fin N)) c * (ω : EuclideanSpace ℝ (Fin N)) d ∂volume.toSphere)
      = realWick a b c d * (volume.toSphere (E := EuclideanSpace ℝ (Fin N))).real univ := by
  have hM0 : 0 < ∫ aa in Ioi (0 : ℝ), aa ^ (N - 1) * Real.exp (-aa ^ 2 / 2) := by
    rw [halfline_moment (N - 1)]; positivity
  have key : (realWick a b c d * (volume.toSphere (E := EuclideanSpace ℝ (Fin N))).real univ)
        * (∫ aa in Ioi (0 : ℝ), aa ^ (N - 1) * Real.exp (-aa ^ 2 / 2))
      = ((N : ℝ) * ((N : ℝ) + 2)
          * (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
              (ω : EuclideanSpace ℝ (Fin N)) a * (ω : EuclideanSpace ℝ (Fin N)) b
                * (ω : EuclideanSpace ℝ (Fin N)) c
                * (ω : EuclideanSpace ℝ (Fin N)) d ∂volume.toSphere))
          * (∫ aa in Ioi (0 : ℝ), aa ^ (N - 1) * Real.exp (-aa ^ 2 / 2)) := by
    have h1 := sphere_polar_monomial a b c d
    rw [sphere_polar_one, radial_ratio N] at h1
    linear_combination h1
  exact (mul_right_cancel₀ (ne_of_gt hM0) key).symm

end SKEFTHawking.QuantumNetwork
