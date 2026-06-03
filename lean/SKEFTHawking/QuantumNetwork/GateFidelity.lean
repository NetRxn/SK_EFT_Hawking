import SKEFTHawking.QuantumNetwork.GaussianComplexTensor
import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# Average gate fidelity ↔ entanglement fidelity (Phase 6AG, Ask 4 — bricks 5/6)

The headline identity of the bench-data→worst-case bridge: for a CPTP (Kraus) channel `Φ` on a
`d`-dimensional system,

`F_avg(Φ) = (d · F_e(Φ) + 1) / (d + 1)`,

where `F_avg` is the Haar-average of the input-output overlap over pure states and `F_e` is the
entanglement fidelity. The analytic engine is the degree-4 complex sphere moment
`complexSphereTensor` (brick 4): contracting it against the Kraus matrices yields

`∫_S |⟨ψ|K|ψ⟩|² dσ = (|tr K|² + tr(Kᴴ K)) · S₁/(d(d+1))`,

and summing over the Kraus operators with the trace-preservation condition `∑ₖ Kₖᴴ Kₖ = 1`
(so `∑ₖ tr(Kₖᴴ Kₖ) = d`) collapses the dimension factor. Obtained constructively from the Gaussian→
sphere route — no Weingarten / unitary-2-design machinery.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Complex MeasureTheory Set Metric Matrix

variable {d : ℕ}

/-- The sphere-measure constant `S₁ = σ(S^{2d-1})` (total surface measure), abbreviated for the
contraction identities below. -/
noncomputable def sphereTotal (d : ℕ) : ℝ :=
  (volume.toSphere (E := EuclideanSpace ℝ (Fin d ⊕ Fin d))).real univ

@[fun_prop]
theorem continuous_psiC (p : Fin d) :
    Continuous (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1 =>
      psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) := by
  unfold psiC; fun_prop

/-- **Per-term contraction.** A single `(p,q,r,s)` summand of `|⟨ψ|K|ψ⟩|²` integrates to
`K_pq · conj(K_rs) · complexSphereTensor(p,q,s,r)` — the matrix entries pull out of the integral and
the surviving sphere integral is the degree-4 complex moment. -/
theorem sphere_qform_term [NeZero d] (K : Matrix (Fin d) (Fin d) ℂ) (p q r s : Fin d) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) * K p q
            * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
          * (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r * (starRingEnd ℂ) (K r s)
            * (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s))
        ∂volume.toSphere)
      = K p q * (starRingEnd ℂ) (K r s)
          * (((((if p = q then (1 : ℝ) else 0) * (if s = r then 1 else 0)
                + (if p = r then 1 else 0) * (if q = s then 1 else 0))
              * (sphereTotal d / ((d : ℝ) * ((d : ℝ) + 1))) : ℝ)) : ℂ) := by
  calc (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
          ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) * K p q
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
            * (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r * (starRingEnd ℂ) (K r s)
              * (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s))
          ∂volume.toSphere)
      = ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
          (K p q * (starRingEnd ℂ) (K r s)) *
            ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
                * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
                * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)
                    * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r))
          ∂volume.toSphere := by
        apply integral_congr_ae; filter_upwards with ω; ring
    _ = (K p q * (starRingEnd ℂ) (K r s)) *
          ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
            ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
                * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
                * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)
                    * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r))
          ∂volume.toSphere := integral_const_mul _ _
    _ = _ := by rw [complexSphereTensor p q s r]; simp only [sphereTotal]

/-- **Delta contraction.** Contracting the degree-4 delta tensor `δ_pq δ_sr + δ_pr δ_qs` against
`K_pq conj(K_rs)` yields `|tr K|² + tr(Kᴴ K)`: the first delta forces the trace-square term
`(∑ K_pp)(∑ conj K_pp)`, the second the Hilbert–Schmidt term `∑ K_pq conj(K_pq)`. -/
theorem delta_contraction (K : Matrix (Fin d) (Fin d) ℂ) :
    (∑ r, ∑ s, ∑ p, ∑ q,
        K p q * (starRingEnd ℂ) (K r s)
          * ((if p = q then (1:ℂ) else 0) * (if s = r then 1 else 0)
              + (if p = r then 1 else 0) * (if q = s then 1 else 0)))
      = (∑ p, K p p) * (starRingEnd ℂ) (∑ p, K p p) + ∑ p, ∑ q, K p q * (starRingEnd ℂ) (K p q) := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1
  · -- Sum1: trace-square term
    have hfac : (∑ r, ∑ s, ∑ p, ∑ q,
            K p q * (starRingEnd ℂ) (K r s) * ((if p = q then (1:ℂ) else 0) * (if s = r then 1 else 0)))
          = (∑ r, ∑ s, (starRingEnd ℂ) (K r s) * (if s = r then (1:ℂ) else 0))
            * (∑ p, ∑ q, K p q * (if p = q then (1:ℂ) else 0)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [hfac,
      show (∑ p, ∑ q, K p q * (if p = q then (1:ℂ) else 0)) = ∑ p, K p p by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true],
      show (∑ r, ∑ s, (starRingEnd ℂ) (K r s) * (if s = r then (1:ℂ) else 0))
            = ∑ r, (starRingEnd ℂ) (K r r) by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true],
      map_sum, mul_comm]
  · -- Sum2: Hilbert–Schmidt term
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Sphere contraction of `|⟨ψ|K|ψ⟩|²`.** Integrating the squared bra-ket overlap of a fixed matrix
`K` over the uniform measure on the unit sphere of `ℂ^d` gives `(|tr K|² + tr(Kᴴ K))·S₁/(d(d+1))`.
This is the degree-4 complex sphere moment (`complexSphereTensor`) contracted against the matrix
entries — the analytic engine of the average-gate-fidelity identity. -/
theorem sphere_braKet_normSq [NeZero d] (K : Matrix (Fin d) (Fin d) ℂ) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        Complex.normSq (∑ p, ∑ q, (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
            * K p q * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
        ∂volume.toSphere)
      = (Complex.normSq (∑ p, K p p) + ∑ p, ∑ q, Complex.normSq (K p q))
          * (sphereTotal d / ((d : ℝ) * ((d : ℝ) + 1))) := by
  refine Complex.ofReal_injective ?_
  refine integral_ofReal.symm.trans ?_
  have hI : ∀ g : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1 → ℂ,
      Continuous g → Integrable g volume.toSphere :=
    fun g hg => hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1 =>
        ((Complex.normSq (∑ p, ∑ q, (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
            * K p q * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q) : ℝ) : ℂ))
      =ᵐ[volume.toSphere] (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1 =>
          ∑ r, ∑ s, ∑ p, ∑ q,
          ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) * K p q
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
            * (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r * (starRingEnd ℂ) (K r s)
              * (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s))) := by
    filter_upwards with ω
    rw [← Complex.mul_conj, map_sum]
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
  refine (integral_congr_ae hpt).trans ?_
  rw [show (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        (∑ r, ∑ s, ∑ p, ∑ q,
          ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) * K p q
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
            * (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r * (starRingEnd ℂ) (K r s)
              * (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)))
          ∂volume.toSphere)
      = ∑ r, ∑ s, ∑ p, ∑ q, ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
          ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p) * K p q
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q)
            * (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r * (starRingEnd ℂ) (K r s)
              * (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s))
          ∂volume.toSphere from by
      rw [integral_finset_sum _ (fun r _ => hI _ (by fun_prop))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [integral_finset_sum _ (fun s _ => hI _ (by fun_prop))]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [integral_finset_sum _ (fun p _ => hI _ (by fun_prop))]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [integral_finset_sum _ (fun q _ => hI _ (by fun_prop))]]
  simp_rw [sphere_qform_term K]
  set C : ℂ := ((sphereTotal d / ((d : ℝ) * ((d : ℝ) + 1)) : ℝ) : ℂ) with hC
  rw [show (((Complex.normSq (∑ p, K p p) + ∑ p, ∑ q, Complex.normSq (K p q))
          * (sphereTotal d / ((d : ℝ) * ((d : ℝ) + 1))) : ℝ) : ℂ)
        = ((∑ p, K p p) * (starRingEnd ℂ) (∑ p, K p p)
            + ∑ p, ∑ q, K p q * (starRingEnd ℂ) (K p q)) * C from by
      rw [hC]; push_cast
      simp_rw [← Complex.mul_conj]]
  rw [← delta_contraction K]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hC]; push_cast
  simp only [apply_ite (Complex.ofReal), Complex.ofReal_one, Complex.ofReal_zero]
  ring

end SKEFTHawking.QuantumNetwork
