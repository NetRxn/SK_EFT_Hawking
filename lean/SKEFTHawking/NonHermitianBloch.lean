import Mathlib

/-!
# Phase 6CD, Wave 1 — Non-Hermitian Bloch Hamiltonian and the exceptional point

A **PT-symmetric non-Hermitian** two-band Bloch Hamiltonian

  `H(g) = ⎡ i g   1   ⎤`
  `       ⎣ 1    −i g ⎦`   (gain/loss strength `g : ℝ`),

the canonical model of non-Hermitian band physics. Its characteristic polynomial is `X² + (g² − 1)`,
so its eigenvalues are `±√(1 − g²)`: **real** for `|g| < 1` (PT-unbroken), **coalescing to 0** at the
**exceptional point** `g = 1`, and **imaginary** for `|g| > 1` (PT-broken).

## Wave-1 headline (`exceptional_point_defective`)

At the exceptional point `g = 1`, `H(1) = [[i,1],[1,−i]]` is a genuinely **defective** (non-diagonalisable)
degeneracy — the defining feature of an EP, distinct from an ordinary Hermitian degeneracy:

* `H(1)` is **nilpotent** (`H(1)² = 0`), so its only eigenvalue is `0` with **algebraic multiplicity 2**
  (the whole 2-d space is the generalised eigenspace);
* yet its ordinary **eigenspace is the single line** `ℂ·(1, −i)` — every null vector is a multiple of
  `(1, −i)` — so the **geometric multiplicity is 1**;
* and `(1, 0)` is **not** an eigenvector, witnessing geometric mult `1 < 2` algebraic mult.

Eigenvalue *and* eigenvector coalesce: that simultaneous collapse is exactly what makes `g = 1` an
exceptional point rather than a diagonalisable (e.g. Hermitian) crossing.

**Two-layer honesty.** The Bloch-operator algebra and the defectiveness are Lean-verified. Identifying
`H(g)` with a specific photonic/acoustic gain-loss device stays literature-cited (cf. non-Hermitian
photonics reviews, e.g. El-Ganainy et al., Nat. Phys. 14, 11 (2018)).
-/

namespace SKEFTHawking.NonHermitian

open Complex Matrix

/-- The PT-symmetric non-Hermitian 2-band Bloch Hamiltonian `H(g) = [[ig, 1], [1, −ig]]`. -/
noncomputable def ptBloch (g : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![I * (g : ℂ), 1; 1, -(I * (g : ℂ))]

/-- The Hamiltonian at the exceptional point `g = 1`, `H(1) = [[i, 1], [1, −i]]`. -/
noncomputable def ptBlochEP : Matrix (Fin 2) (Fin 2) ℂ := ptBloch 1

/-- At the EP the Hamiltonian is **nilpotent**: `H(1)² = 0`. Hence its sole eigenvalue is `0`, with
algebraic multiplicity `2` (the entire space is the generalised eigenspace). -/
lemma ptBlochEP_nilpotent : ptBlochEP * ptBlochEP = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptBlochEP, ptBloch, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

/-- `(1, −i)` is an eigenvector of `H(1)` for the eigenvalue `0`: it spans the (1-dimensional)
eigenspace. -/
lemma ptBlochEP_eigenvector : ptBlochEP.mulVec ![1, -I] = 0 := by
  funext i
  fin_cases i <;>
    simp [ptBlochEP, ptBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.I_mul_I]

/-- **Geometric multiplicity 1.** Every null vector of `H(1)` lies on the line `ℂ·(1, −i)`: its
second component is forced to be `−i` times its first. The eigenspace is exactly that one line. -/
lemma ptBlochEP_kernel_line (v : Fin 2 → ℂ) (hv : ptBlochEP.mulVec v = 0) :
    v 1 = -I * v 0 := by
  have h0 := congrFun hv 0
  simp [ptBlochEP, ptBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  -- h0 : I * v 0 + v 1 = 0
  linear_combination h0

/-- `(1, 0)` is **not** an eigenvector for eigenvalue `0` — so the geometric multiplicity is strictly
below the algebraic multiplicity `2`. -/
lemma ptBlochEP_not_eigenvector : ptBlochEP.mulVec ![1, 0] ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp [ptBlochEP, ptBloch, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

/-- **Exceptional point is defective (Phase 6CD W1).** At `g = 1` the non-Hermitian Bloch Hamiltonian
`H(1)` is nilpotent (so `0` is its only eigenvalue, with algebraic multiplicity `2`), yet its
eigenspace is the single line `ℂ·(1, −i)` (geometric multiplicity `1`) and `(1, 0)` is not an
eigenvector — eigenvalue and eigenvector coalesce, the hallmark of an exceptional point. -/
theorem exceptional_point_defective :
    ptBlochEP * ptBlochEP = 0 ∧
    ptBlochEP.mulVec ![1, -I] = 0 ∧
    (∀ v : Fin 2 → ℂ, ptBlochEP.mulVec v = 0 → v 1 = -I * v 0) ∧
    ptBlochEP.mulVec ![1, 0] ≠ 0 :=
  ⟨ptBlochEP_nilpotent, ptBlochEP_eigenvector, ptBlochEP_kernel_line, ptBlochEP_not_eigenvector⟩

end SKEFTHawking.NonHermitian
