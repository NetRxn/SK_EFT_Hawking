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

end SKEFTHawking.QuantumNetwork
