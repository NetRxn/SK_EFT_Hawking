import SKEFTHawking.QuantumNetwork.GaussianSphere

/-!
# Degree-4 complex sphere moment (Phase 6AG, Ask 4 — brick 4, complex part)

The complex unit sphere `S^{2d-1} ⊂ ℂ^d` is the real unit sphere of `EuclideanSpace ℝ (Fin d ⊕ Fin d)`
under the isometry `ψ ↦ (Re ψ, Im ψ)`. A point `ω` of the real sphere gives the complex vector
`psiC ω p = ω(inl p) + i·ω(inr p)`. The degree-(2,2) complex moment

`∫_S conj(ψ_p) ψ_q conj(ψ_r) ψ_s dσ = (δ_pq δ_rs + δ_ps δ_qr)·(toSphere.real univ)/(d(d+1))`

is obtained by expanding each `conj(ψ_·) ψ_·` into its real bilinear pieces and applying the real
degree-4 sphere moment `sphere_moment_norm` (brick 4) per monomial; the cross `δ_pr δ_qs` term
cancels under the complex pairing. This is the analytic heart of the average-gate-fidelity identity,
the unitary-2-design second moment obtained constructively without Weingarten/t-design machinery.

Real/imaginary coordinates use the index `Fin d ⊕ Fin d` so coordinate coincidences reduce to
`Sum.inl_injective` / `Sum.inr_injective` / `Sum.inl ≠ Sum.inr` (no `Fin (2d)` arithmetic).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Complex MeasureTheory Set Metric

/-- The degree-4 coordinate monomial on the real sphere; a (semireducible) `def` keeps the long
`EuclideanSpace` coercions out of the term-by-term expansions below while giving it a stable opaque
form under `rw`/`simp` matching. -/
def coordMono4 {ι : Type*} [Fintype ι] (ω : sphere (0 : EuclideanSpace ℝ ι) 1) (i j k l : ι) : ℝ :=
  (ω : EuclideanSpace ℝ ι) i * (ω : EuclideanSpace ℝ ι) j
    * (ω : EuclideanSpace ℝ ι) k * (ω : EuclideanSpace ℝ ι) l

@[fun_prop]
theorem continuous_coordMono4 {ι : Type*} [Fintype ι] (i j k l : ι) :
    Continuous (fun ω : sphere (0 : EuclideanSpace ℝ ι) 1 => coordMono4 ω i j k l) := by
  unfold coordMono4; fun_prop

/-- The complex coordinate vector built from a real point of the sphere in `ℝ^{2d}` indexed by
`Fin d ⊕ Fin d`: `psiC ω p = ω(inl p) + i·ω(inr p)`, i.e. `inl` carries the real parts and `inr`
the imaginary parts. -/
noncomputable def psiC {d : ℕ} (ω : EuclideanSpace ℝ (Fin d ⊕ Fin d)) (p : Fin d) : ℂ :=
  (ω (Sum.inl p) : ℂ) + Complex.I * (ω (Sum.inr p) : ℂ)

/-- **Sesquilinear building block.** `conj(ψ_p)·ψ_q = (a_p a_q + b_p b_q) + i·(a_p b_q − b_p a_q)`,
where `a_· = ω(inl ·)` (real parts) and `b_· = ω(inr ·)` (imaginary parts). -/
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

/-- **Real part of the degree-4 complex tensor.** `X_pq X_rs − Y_pq Y_rs` integrates to
`4(δ_pq δ_rs + δ_ps δ_qr)·C` (`C = S1/(n(n+2))`, `n = 2d`); the cross `δ_pr δ_qs` term cancels. -/
theorem tensor_realPart {d : ℕ} [NeZero d] (p q r s : Fin d) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
      ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inl s)
      + coordMono4 ω (.inl p) (.inl q) (.inr r) (.inr s)
      + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inl s)
      + coordMono4 ω (.inr p) (.inr q) (.inr r) (.inr s)
      - coordMono4 ω (.inl p) (.inr q) (.inl r) (.inr s)
      + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inl s)
      + coordMono4 ω (.inr p) (.inl q) (.inl r) (.inr s)
      - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inl s) ) ∂volume.toSphere)
      = (4 * ((if p = q then (1 : ℝ) else 0) * (if r = s then 1 else 0)
              + (if p = s then 1 else 0) * (if q = r then 1 else 0)))
          * ((volume.toSphere (E := EuclideanSpace ℝ (Fin d ⊕ Fin d))).real univ
              / ((Fintype.card (Fin d ⊕ Fin d) : ℝ) * ((Fintype.card (Fin d ⊕ Fin d) : ℝ) + 2))) := by
  rw [integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))]
  simp only [coordMono4]
  rw [sphere_moment_norm, sphere_moment_norm, sphere_moment_norm, sphere_moment_norm,
      sphere_moment_norm, sphere_moment_norm, sphere_moment_norm, sphere_moment_norm]
  simp only [realWick, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false, mul_zero,
             add_zero, zero_add]
  ring

/-- **Imaginary part of the degree-4 complex tensor vanishes.** `X_pq Y_rs + Y_pq X_rs` integrates
to `0`: every monomial mixes three coordinates of one real/imaginary parity with one of the other,
so its Wick coefficient is `0`. -/
theorem tensor_imagPart {d : ℕ} [NeZero d] (p q r s : Fin d) :
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d ⊕ Fin d)) 1,
      ( coordMono4 ω (.inl p) (.inl q) (.inl r) (.inr s)
      - coordMono4 ω (.inl p) (.inl q) (.inr r) (.inl s)
      + coordMono4 ω (.inr p) (.inr q) (.inl r) (.inr s)
      - coordMono4 ω (.inr p) (.inr q) (.inr r) (.inl s)
      + coordMono4 ω (.inl p) (.inr q) (.inl r) (.inl s)
      + coordMono4 ω (.inl p) (.inr q) (.inr r) (.inr s)
      - coordMono4 ω (.inr p) (.inl q) (.inl r) (.inl s)
      - coordMono4 ω (.inr p) (.inl q) (.inr r) (.inr s) ) ∂volume.toSphere)
      = 0 := by
  rw [integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_add
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)),
      integral_sub
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))
        (Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _))]
  simp only [coordMono4]
  rw [sphere_moment_norm, sphere_moment_norm, sphere_moment_norm, sphere_moment_norm,
      sphere_moment_norm, sphere_moment_norm, sphere_moment_norm, sphere_moment_norm]
  simp [realWick, Sum.inl.injEq, Sum.inr.injEq]

end SKEFTHawking.QuantumNetwork
