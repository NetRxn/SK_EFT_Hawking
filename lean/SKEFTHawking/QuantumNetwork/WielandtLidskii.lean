import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Wielandt min-max toward arbitrary-index Lidskii (Phase 6AL, Wave 4, item F1b core ∃P)

The genuine arbitrary-index Lidskii–Wielandt content underlying the trace-norm Mirsky inequality. The
top-level target (numerically validated, `mirsky_of_proj_exists` consumes it) is **single-frame existence**:
for every subset `S` there is a rank-`|S|` orthogonal projection simultaneously high for `A` and low for `B`.
We build toward it via the Courant–Fischer / Wielandt subspace machinery (Mathlib has only the *extreme*
eigenvalues via `hasEigenvalue_iSup/iInf`; the indexed min-max is absent).

This file starts with the **subspace-intersection dimension lemma** — the load-bearing technique for both the
single-eigenvalue Courant–Fischer "≤" direction and the Wielandt frame construction: two subspaces whose
dimensions sum past the ambient dimension meet in a nonzero vector.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

/-- **Subspace-intersection dimension lemma.** Two finite-dimensional subspaces whose dimensions sum to
strictly more than the ambient dimension intersect in a nonzero vector. This is the core counting step of
the Courant–Fischer min-max (a candidate subspace meets a complementary eigenspace) and of the Wielandt
frame construction. -/
theorem exists_mem_inf_ne_zero {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (s t : Submodule K V)
    (h : Module.finrank K V < Module.finrank K s + Module.finrank K t) :
    ∃ x ∈ s ⊓ t, x ≠ 0 := by
  have hsup : Module.finrank K (s ⊔ t : Submodule K V) ≤ Module.finrank K V := Submodule.finrank_le _
  have hkey : Module.finrank K (s ⊔ t : Submodule K V) + Module.finrank K (s ⊓ t : Submodule K V)
      = Module.finrank K s + Module.finrank K t := Submodule.finrank_sup_add_finrank_inf_eq s t
  have hpos : 0 < Module.finrank K (s ⊓ t : Submodule K V) := by omega
  have hnt : Nontrivial (s ⊓ t : Submodule K V) := Module.finrank_pos_iff.mp hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : (s ⊓ t : Submodule K V))
  exact ⟨y, y.2, fun h0 => hy (Subtype.ext h0)⟩

end SKEFTHawking.QuantumNetwork
