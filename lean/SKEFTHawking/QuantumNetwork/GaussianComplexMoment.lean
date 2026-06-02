import SKEFTHawking.QuantumNetwork.GaussianSphere

/-!
# Degree-4 complex sphere moment (Phase 6AG, Ask 4 — brick 4, complex part)

The complex unit sphere `S^{2d-1} ⊂ ℂ^d` is the real unit sphere of `EuclideanSpace ℝ (Fin d ⊕ Fin d)`
under the isometry `ψ ↦ (Re ψ, Im ψ)`. A point `ω` of the real sphere gives the complex vector
`psiC ω p = ω(inl p) + i·ω(inr p)`. The degree-(2,2) complex moment

`∫_S conj(ψ_p) ψ_q conj(ψ_r) ψ_s dσ = (δ_pq δ_rs + δ_ps δ_qr)/(d(d+1))`

is obtained by expanding each `conj(ψ_·) ψ_·` into its real bilinear pieces and applying the real
degree-4 sphere moment `sphere_moment_real` (brick 4) per monomial; the cross `δ_pr δ_qs` term cancels
under the complex pairing. This is the analytic heart of the average-gate-fidelity identity.

Real/imag coordinates use the index `Fin d ⊕ Fin d` so coordinate coincidences reduce to
`Sum.inl_injective` / `Sum.inr_injective` / `Sum.inl ≠ Sum.inr` (no `Fin (2d)` arithmetic).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Complex

/-- The complex coordinate vector built from a real point of the sphere in `ℝ^{2d}` indexed by
`Fin d ⊕ Fin d`: `psiC ω p = ω(inl p) + i·ω(inr p)`, i.e. `inl` carries the real parts and `inr`
the imaginary parts. -/
noncomputable def psiC {d : ℕ} (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) (p : Fin d) : ℂ :=
  (ω (Sum.inl p) : ℂ) + Complex.I * (ω (Sum.inr p) : ℂ)

/-- **Sesquilinear building block.** `conj(ψ_p)·ψ_q = (a_p a_q + b_p b_q) + i·(a_p b_q − b_p a_q)`,
where `a_· = ω(inl ·)` (real parts) and `b_· = ω(inr ·)` (imaginary parts). The real part is the
symmetric bilinear form, the imaginary part the antisymmetric one. -/
theorem conjPsi_mul_psi {d : ℕ} (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) (p q : Fin d) :
    (starRingEnd ℂ) (psiC ω p) * psiC ω q
      = ((ω (Sum.inl p) * ω (Sum.inl q) + ω (Sum.inr p) * ω (Sum.inr q) : ℝ) : ℂ)
        + Complex.I
          * ((ω (Sum.inl p) * ω (Sum.inr q) - ω (Sum.inr p) * ω (Sum.inl q) : ℝ) : ℂ) := by
  simp only [psiC, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end SKEFTHawking.QuantumNetwork
