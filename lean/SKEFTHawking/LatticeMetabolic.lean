/-
# Phase 5q.H close-out — the metabolic (Lagrangian) signature-vanishing lattice lemma

The **banked-algebra half** of the σ-descent's last atom `hbord` (Thom bordism-invariance of the
signature). Classical Novikov additivity says: a closed oriented 4-manifold `M = ∂W` that BOUNDS has
signature `σ(M) = 0`, because the restriction `L = im(H²(W;ℝ) → H²(M;ℝ))` is a **Lagrangian** of `M`'s
intersection form — a half-dimensional totally-isotropic subspace. The purely algebraic core of that
statement is proved here, at the level of `latticeSig` on integer forms:

  **`latticeSig M = 0`** whenever the real form of `M` (rank `n = 2m`) is nondegenerate (`radical = ⊥`)
  and carries an isotropic subspace `L` of dimension `m` (the quadratic form vanishes on `L`).

The proof is pure Sylvester inertia, from Mathlib's `sigPos`/`sigNeg` API:
* `sigPos_add_finrank_le_of_nonpos` on `L` (isotropic ⟹ `Q ≤ 0` on `L`) gives `sigPos Q ≤ m`;
* the same on `-Q` (isotropic ⟹ `-Q ≤ 0` on `L`) gives `sigNeg Q ≤ m`;
* `sigPos_add_sigNeg_add_radical` with `radical = ⊥` gives `sigPos Q + sigNeg Q = 2m`;
* so `sigPos Q = sigNeg Q = m`, hence `latticeSig M = sigPos Q − sigNeg Q = 0`.

This is the "form with a Lagrangian ⟹ σ = 0" lattice lemma (half (a) of the Novikov route). The
geometric half — that a bounding manifold's boundary form actually HAS such a Lagrangian (isotropy from
cup-functoriality + `[W,∂W]`; half-dimensionality from Poincaré–Lefschetz duality) — stays a disclosed
geometric atom, consumed downstream (`PinPlusKTSpinSigmaHbord`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HyperbolicNormalForm

namespace SKEFTHawking

open QuadraticMap Module

/-- **The metabolic (Lagrangian) signature-vanishing lemma.** If a rank-`n = 2m` integer form `M` has a
nondegenerate real form (`radical = ⊥`) and an isotropic subspace `L` of dimension `m` — the real
quadratic form vanishes identically on `L` — then `latticeSig M = 0`.

This is the algebraic core of Novikov additivity: a form with a half-dimensional totally-isotropic
subspace (a Lagrangian) has zero signature. The three inputs are Sylvester inertia
(`sigPos + sigNeg + radical = finrank`) plus the two isotropic bounds (`sigPos ≤ m`, `sigNeg ≤ m`). -/
theorem latticeSig_eq_zero_of_lagrangian {n m : ℕ} (hn : n = 2 * m)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hrad : (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (L : Submodule ℝ (Fin n → ℝ))
    (hLdim : Module.finrank ℝ L = m)
    (hLiso : ∀ x ∈ L, (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0) :
    latticeSig M = 0 := by
  set Q := (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' with hQ
  -- The ambient space has dimension `n`.
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by
    simp
  -- `sigPos Q ≤ m` from the isotropic subspace being negative-semidefinite.
  have hpos : sigPos Q + m ≤ n := by
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) (V := L)
      (fun x hx => le_of_eq (hLiso x hx))
    rwa [hdim, hLdim] at h
  -- `sigNeg Q ≤ m` from the isotropic subspace being nonnegative-semidefinite (apply to `-Q`).
  have hneg : sigNeg Q + m ≤ n := by
    have h := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := -Q) (V := L)
      (fun x hx => by simp [hLiso x hx])
    rwa [sigPos_neg, hdim, hLdim] at h
  -- Sylvester: `sigPos + sigNeg + finrank radical = n`, and `radical = ⊥`.
  have hsum : sigPos Q + sigNeg Q + Module.finrank ℝ Q.radical = n := by
    rw [QuadraticForm.sigPos_add_sigNeg_add_radical, hdim]
  rw [hrad, finrank_bot] at hsum
  -- Combine: `sigPos = m`, `sigNeg = m`.
  have hpe : sigPos Q = m := by omega
  have hne : sigNeg Q = m := by omega
  unfold latticeSig
  -- v4.32: `toQuadraticMap'` is a deprecated *alias* of `toQuadraticForm'`, so the two spellings
  -- are defeq but not syntactically equal. `set … with hQ` captured the OLD spelling while
  -- `latticeSig` unfolds to the NEW one, so `rw [← hQ]` cannot see its pattern. Bridge by
  -- restating hQ in the goal's own spelling (typechecks by defeq); statements stay on the old
  -- name per the standing whole-component boundary.
  rw [show (M.map (Int.cast : ℤ → ℝ)).toQuadraticForm' = Q from hQ.symm, hpe, hne]
  simp

/-- **The metabolic lemma keyed on even-unimodularity** — the directly-consumable form. An even-unimodular
integer form (`IsEvenUnimodular`, hence nondegenerate over `ℝ` by `radical_eq_bot`) of rank `n = 2m` with a
half-dimensional isotropic subspace has `latticeSig = 0`. This is the shape the σ-descent's disclosed
intersection matrices consume: their even-unimodularity is free from the bundle's `wu`/`pd`, so the only
geometric input is the half-dimensional isotropic Lagrangian. -/
theorem latticeSig_eq_zero_of_lagrangian_of_evenUnimodular {n m : ℕ} (hn : n = 2 * m)
    (M : Matrix (Fin n) (Fin n) ℤ) (heu : IsEvenUnimodular M)
    (L : Submodule ℝ (Fin n → ℝ))
    (hLdim : Module.finrank ℝ L = m)
    (hLiso : ∀ x ∈ L, (M.map (Int.cast : ℤ → ℝ)).toQuadraticMap' x = 0) :
    latticeSig M = 0 :=
  latticeSig_eq_zero_of_lagrangian hn M heu.radical_eq_bot L hLdim hLiso
