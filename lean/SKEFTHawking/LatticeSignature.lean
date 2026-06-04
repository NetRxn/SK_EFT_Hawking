/-
Phase 5q.B Wave B5: the genuine signature of an integer symmetric form, grounded in Mathlib.

Until now the Rokhlin leg (`AlgebraicRokhlin.lean`, `SpinRokhlinInterface.lean`) carried the
signature only as a *free* integer parameter `sigma`/`sig`, unconnected to the form `M`. This module
closes that gap: it defines `latticeSig M` as the actual signature `sigPos − sigNeg` of the real
quadratic form obtained by casting `M : Matrix (Fin n) (Fin n) ℤ` to ℝ, using Mathlib's
`QuadraticMap.sigPos`/`sigNeg` (Sylvester's law of inertia, `Mathlib.LinearAlgebra.QuadraticForm.Signature`).

This is real infrastructure, not a proxy: `latticeSig` is the topologist's/number-theorist's
signature, and the lemmas below are its genuine structural laws — orientation reversal
`σ(−M) = −σ(M)` and the rank bound `|σ(M)| ≤ n`. All proofs are kernel-pure
(`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no `maxHeartbeats`, no axiom.

WHAT THIS DOES NOT (YET) DO. It does not prove van der Blij (`IsEvenUnimodular M → 8 ∣ latticeSig M`).
That divisibility is the one genuinely arithmetic input remaining on the leg; per the deep-research
note (`Lit-Search/Phase-5c/Rokhlin/…`) and a direct Mathlib scout (2026-06-03), it requires either
the Hasse–Minkowski classification of indefinite unimodular forms or Milgram–Gauss-sum reciprocity,
neither of which is in Mathlib (no Witt group, no p-adic quadratic-form theory, no lattice Gauss-sum
reciprocity). The finite Arf/Gauss-sum machinery in `ArfInvariant.lean`/`EvenLatticeForm.lean`
captures the *mod-2* layer (the second factor of two, `σ/8 mod 2 = Arf(q̄)`), which is genuinely a
different and more elementary layer than van der Blij's mod-8 statement. See the roadmap
`docs/roadmaps/Phase5qB_SpectraFreeSpinBordism_Roadmap.md` (Wave B1) for the discharge options.

See also `AlgebraicRokhlin.lean` (the `8 ∣ σ` algebra, conditional on the characteristic-square
identity) and `SpinRokhlinInterface.lean` (the wired `16 ∣ σ`).
-/

import Mathlib

namespace SKEFTHawking

open QuadraticMap

/-- The **signature** of an integer symmetric form `M`, defined as `sigPos − sigNeg` of the real
quadratic form obtained by casting `M` to ℝ. This is the genuine (Sylvester-invariant) signature:
the number of positive minus the number of negative eigenvalues, counted with multiplicity. -/
noncomputable def latticeSig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  (sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)
    - (sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ)

/-- **Orientation reversal:** `σ(−M) = −σ(M)`. Negating the form swaps the positive and negative
inertia indices, so the signature flips sign. (Topologically: reversing the orientation of a
4-manifold negates its signature.) -/
theorem latticeSig_neg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    latticeSig (-M) = - latticeSig M := by
  have hmap : ((-M).map (Int.cast : ℤ → ℝ)) = -(M.map (Int.cast : ℤ → ℝ)) := by
    ext i j; simp
  have hqm : ((-M).map (Int.cast : ℤ → ℝ)).toQuadraticMap'
      = -((M.map (Int.cast : ℤ → ℝ)).toQuadraticMap') := by
    rw [hmap]; simp [Matrix.toQuadraticMap']
  unfold latticeSig
  rw [hqm]
  show (sigPos (-_) : ℤ) - (sigNeg (-_) : ℤ) = _
  rw [sigNeg, sigNeg, neg_neg]
  ring

/-- **Upper rank bound:** `σ(M) ≤ n`. The positive inertia index never exceeds the rank. -/
theorem latticeSig_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    latticeSig M ≤ (n : ℤ) := by
  have h : sigPos (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' ≤ n := by
    simpa using sigPos_le_finrank (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'
  have hneg : (0 : ℤ) ≤ (sigNeg (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' : ℤ) := by positivity
  unfold latticeSig; omega

/-- **Lower rank bound:** `−n ≤ σ(M)`, obtained from the upper bound via orientation reversal. -/
theorem latticeSig_ge {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    -(n : ℤ) ≤ latticeSig M := by
  have h := latticeSig_le (-M)
  rw [latticeSig_neg] at h
  omega

/-- **Signature is bounded by rank:** `|σ(M)| ≤ n`. -/
theorem abs_latticeSig_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    |latticeSig M| ≤ (n : ℤ) :=
  abs_le.mpr ⟨latticeSig_ge M, latticeSig_le M⟩

/-! ## Definite forms: the signature is `±rank`

These are the `latticeSig = ±n` facts for (positive/negative) definite forms — a stepping stone for the
frontier-build sub-wave that handles the *definite* even-unimodular case (where `σ = ±rank`, so `8 ∣ σ ⟺
8 ∣ rank`). The two `sigPos`/`sigNeg` helpers are general (any finite-dimensional real quadratic form) and
reusable. -/

/-- For a positive-definite quadratic form on a finite-dimensional real space, the positive inertia index is
the full dimension. -/
theorem sigPos_eq_finrank_of_posDef {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : Q.PosDef) :
    sigPos Q = Module.finrank ℝ M := by
  refine le_antisymm (sigPos_le_finrank Q) ?_
  have hr : (Q.restrict (⊤ : Submodule ℝ M)).PosDef := by
    intro x hx
    have hxv : (x : M) ≠ 0 := by rwa [Ne, Submodule.coe_eq_zero]
    rw [QuadraticMap.restrict_apply]; exact hQ _ hxv
  simpa using le_sigPos_of_posDef Q hr

/-- For a positive-definite quadratic form, the negative inertia index vanishes. -/
theorem sigNeg_eq_zero_of_posDef {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : Q.PosDef) : sigNeg Q = 0 := by
  rw [sigNeg]
  obtain ⟨V, hV, hVpos⟩ := exists_finrank_eq_sigPos_and_posDef (-Q)
  have hVbot : V = ⊥ := by
    by_contra hne
    obtain ⟨x, hxV, hx0⟩ := V.exists_mem_ne_zero_of_ne_bot hne
    have hpos : (0 : ℝ) < (-Q) x := by
      have := hVpos ⟨x, hxV⟩ (by simpa [Subtype.ext_iff] using hx0)
      rwa [QuadraticMap.restrict_apply] at this
    have hQx : Q x < 0 := by simpa using hpos
    exact absurd hQx (not_lt.mpr (le_of_lt (hQ x hx0)))
  rw [← hV, hVbot]; simp

/-- **Positive-definite ⟹ `σ(M) = rank`.** -/
theorem latticeSig_of_posDef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : (M.map (Int.cast : ℤ → ℝ)).PosDef) : latticeSig M = (n : ℤ) := by
  have hQ := hM.toQuadraticForm'
  unfold latticeSig
  rw [sigPos_eq_finrank_of_posDef _ hQ, sigNeg_eq_zero_of_posDef _ hQ]
  simp

/-- **Negative-definite ⟹ `σ(M) = -rank`** (the negation of `M` is positive-definite). -/
theorem latticeSig_of_negDef {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ((-M).map (Int.cast : ℤ → ℝ)).PosDef) : latticeSig M = -(n : ℤ) := by
  have h := latticeSig_of_posDef (-M) hM
  rw [latticeSig_neg] at h
  omega

end SKEFTHawking
