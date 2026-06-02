import SKEFTHawking.QuantumNetwork.GaussianComplexMoment

/-!
# Degree-4 complex sphere moment — assembly (Phase 6AG, Ask 4 — brick 4)

Assembles the degree-(2,2) complex sphere moment

`∫_S conj(ψ_p) ψ_q conj(ψ_r) ψ_s dσ = (δ_pq δ_rs + δ_ps δ_qr)·(toSphere.real univ)/(d(d+1))`

from the real/imaginary bilinear split `conjPsi_mul_psi`, the real part `tensor_realPart`
(`= 4(δ_pq δ_rs + δ_ps δ_qr)·C`), and the vanishing imaginary part `tensor_imagPart`. The complex
integral is decomposed via `integral_re_add_im` into its real and imaginary integral parts, each
identified (pointwise, through `conjPsi_mul_psi`) with the real degree-4 monomial sums of
`tensor_realPart`/`tensor_imagPart`. The radial normalisation `4·S1/(2d(2d+2)) = S1/(d(d+1))`
collapses the dimension factor. This is the unitary-2-design second moment, obtained constructively
without Weingarten/t-design machinery.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Complex MeasureTheory Set Metric

/-- **Degree-4 complex sphere moment.** For the uniform surface measure on the unit sphere of
`ℂ^d ≅ EuclideanSpace ℝ (Fin d ⊕ Fin d)` (`d ≥ 1`),
`∫_S conj(ψ_p) ψ_q conj(ψ_r) ψ_s dσ = (δ_pq δ_rs + δ_ps δ_qr)·(toSphere.real univ)/(d(d+1))`. -/
theorem complexSphereTensor {d : ℕ} [NeZero d] (p q r s : Fin d) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
          * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
          * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r)
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)
        ∂volume.toSphere)
      = ((((if p = q then (1 : ℝ) else 0) * (if r = s then 1 else 0)
            + (if p = s then 1 else 0) * (if q = r then 1 else 0))
          * ((volume.toSphere (E := EuclideanSpace ℝ (Fin d ⊕ Fin d))).real univ
              / ((d : ℝ) * ((d : ℝ) + 1))) : ℝ) : ℂ) := by
  have hpoint : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
      (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
          * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
          * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r)
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)
        = (( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inl s)
          + coordMono4 ω (.inl p) (.inl q) (.inr r) (.inr s)
          + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inl s)
          + coordMono4 ω (.inr p) (.inr q) (.inr r) (.inr s)
          - coordMono4 ω (.inl p) (.inr q) (.inl r) (.inr s)
          + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inl s)
          + coordMono4 ω (.inr p) (.inl q) (.inl r) (.inr s)
          - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inl s) : ℝ) : ℂ)
        + Complex.I *
          (( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inr s)
          - coordMono4 ω (.inl p) (.inl q) (.inr r) (.inl s)
          + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inr s)
          - coordMono4 ω (.inr p) (.inr q) (.inr r) (.inl s)
          + coordMono4 ω (.inl p) (.inr q) (.inl r) (.inl s)
          + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inr s)
          - coordMono4 ω (.inr p) (.inl q) (.inl r) (.inl s)
          - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inr s) : ℝ) : ℂ) := by
    intro ω; rw [conjPsi_mul_psi, conjPsi_mul_psi]; simp only [coordMono4]; push_cast; ring_nf
    rw [Complex.I_sq]; ring
  have hint : Integrable (fun ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1 =>
      (starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
        * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
        * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r)
            * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)) volume.toSphere := by
    apply Continuous.integrable_of_hasCompactSupport
    · simp only [psiC]; fun_prop
    · exact HasCompactSupport.of_compactSpace _
  refine (integral_re_add_im hint).symm.trans ?_
  rw [show (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        RCLike.re ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
          * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
          * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r)
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)) ∂volume.toSphere)
      = (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
          ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inl s)
          + coordMono4 ω (.inl p) (.inl q) (.inr r) (.inr s)
          + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inl s)
          + coordMono4 ω (.inr p) (.inr q) (.inr r) (.inr s)
          - coordMono4 ω (.inl p) (.inr q) (.inl r) (.inr s)
          + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inl s)
          + coordMono4 ω (.inr p) (.inl q) (.inl r) (.inr s)
          - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inl s) ) ∂volume.toSphere)
      from by apply integral_congr_ae; filter_upwards with ω; rw [hpoint]; simp]
  rw [show (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        RCLike.im ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) p)
          * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) q
          * ((starRingEnd ℂ) (psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) r)
              * psiC (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) s)) ∂volume.toSphere)
      = (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
          ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inr s)
          - coordMono4 ω (.inl p) (.inl q) (.inr r) (.inl s)
          + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inr s)
          - coordMono4 ω (.inr p) (.inr q) (.inr r) (.inl s)
          + coordMono4 ω (.inl p) (.inr q) (.inl r) (.inl s)
          + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inr s)
          - coordMono4 ω (.inr p) (.inl q) (.inl r) (.inl s)
          - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inr s) ) ∂volume.toSphere)
      from by apply integral_congr_ae; filter_upwards with ω; rw [hpoint]; simp]
  rw [show (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inl s)
        + coordMono4 ω (.inl p) (.inl q) (.inr r) (.inr s)
        + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inl s)
        + coordMono4 ω (.inr p) (.inr q) (.inr r) (.inr s)
        - coordMono4 ω (.inl p) (.inr q) (.inl r) (.inr s)
        + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inl s)
        + coordMono4 ω (.inr p) (.inl q) (.inl r) (.inr s)
        - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inl s) ) ∂volume.toSphere) = _
      from tensor_realPart p q r s]
  rw [show (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
        ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inr s)
        - coordMono4 ω (.inl p) (.inl q) (.inr r) (.inl s)
        + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inr s)
        - coordMono4 ω (.inr p) (.inr q) (.inr r) (.inl s)
        + coordMono4 ω (.inl p) (.inr q) (.inl r) (.inl s)
        + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inr s)
        - coordMono4 ω (.inr p) (.inl q) (.inl r) (.inl s)
        - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inr s) ) ∂volume.toSphere) = (0 : ℝ)
      from tensor_imagPart p q r s]
  have hcard : Fintype.card (Fin d ⊕ Fin d) = 2 * d := by simp [Fintype.card_sum]; ring
  rw [hcard]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  simp only [RCLike.ofReal_zero, zero_mul, add_zero,
             show (RCLike.ofReal : ℝ → ℂ) = Complex.ofReal from rfl]
  rw [Complex.ofReal_inj]
  push_cast
  field_simp
  ring

end SKEFTHawking.QuantumNetwork
