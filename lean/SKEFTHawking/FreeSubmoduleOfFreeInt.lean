/-
# Phase 5q.H (E1 CSC-PD tower) — Kaplansky: a submodule of a free ℤ-module is free

`Module.Free ℤ ↥N` for any submodule `N` of a free ℤ-module (arbitrary, possibly infinite, rank).
Mathlib has only the `[Finite ι]` PID theory (`Submodule.basisOfPid` / `smithNormalForm`); the
infinite-rank case (Kaplansky, `infer_instance` FAILS for `Submodule ℤ (ℕ →₀ ℤ)`) is absent, yet it is
exactly what the integral UCT needs to discharge `hproj` (`relBoundariesInt` projective) and `hfree`
(top relative homology free) — both are submodules/subquotients of the free `RelativeChainInt`
(`free_relChainInt`).

**Method** (classical well-ordered leading-term descent): well-order the basis index `ι`; every
`f ≠ 0 : ι →₀ ℤ` has a max-support index `leadIdx f` with a nonzero leading coefficient and zero above
it. The leading coefficients at each index form an ideal `dᵢℤ`; choosing generators gives a basis of
`N` (linear independence from distinct leading indices; spanning by well-founded descent on `leadIdx`).

This file: the leading-term infrastructure (green foundation). Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib

namespace SKEFTHawking.FreeSubmoduleInt

variable {ι : Type*} [LinearOrder ι]

/-- **The leading index** of a nonzero finitely-supported function: the maximum element of its
support (w.r.t. the linear order on `ι`). -/
noncomputable def leadIdx (f : ι →₀ ℤ) (hf : f ≠ 0) : ι :=
  f.support.max' (Finsupp.support_nonempty_iff.mpr hf)

/-- The leading coefficient `f (leadIdx f)` is nonzero. -/
theorem lead_coeff_ne_zero (f : ι →₀ ℤ) (hf : f ≠ 0) : f (leadIdx f hf) ≠ 0 := by
  have hmem : leadIdx f hf ∈ f.support := f.support.max'_mem _
  exact Finsupp.mem_support_iff.mp hmem

/-- `f` vanishes strictly above its leading index. -/
theorem eq_zero_of_gt_leadIdx (f : ι →₀ ℤ) (hf : f ≠ 0) {j : ι} (hj : leadIdx f hf < j) :
    f j = 0 := by
  by_contra hfj
  have hmem : j ∈ f.support := Finsupp.mem_support_iff.mpr hfj
  exact absurd (f.support.le_max' j hmem) (not_le.mpr hj)

/-- The leading index is `≤` any index at which `f` is nonzero (it is the max of the support). -/
theorem leadIdx_le_of_ne_zero (f : ι →₀ ℤ) (hf : f ≠ 0) {j : ι} (hj : f j ≠ 0) :
    j ≤ leadIdx f hf :=
  f.support.le_max' j (Finsupp.mem_support_iff.mpr hj)

/-- A function `f` is **`i`-truncated** if it vanishes strictly above `i`. -/
def IsTrunc (i : ι) (f : ι →₀ ℤ) : Prop := ∀ j, i < j → f j = 0

/-- **The leading-coefficient ideal at `i`**: the coefficients `f i` for `i`-truncated `f ∈ N`.
A submodule of `ℤ` (hence, `ℤ` a PID, a principal ideal `(dᵢ)`); `dᵢ` is the leading coefficient
that generates the `i`-th step of the basis. -/
def leadIdeal (N : Submodule ℤ (ι →₀ ℤ)) (i : ι) : Submodule ℤ ℤ where
  carrier := {c | ∃ f ∈ N, IsTrunc i f ∧ f i = c}
  add_mem' := by
    rintro _ _ ⟨f, hfN, hf, rfl⟩ ⟨g, hgN, hg, rfl⟩
    exact ⟨f + g, N.add_mem hfN hgN,
      fun j hj => by rw [Finsupp.add_apply, hf j hj, hg j hj, add_zero], Finsupp.add_apply _ _ _⟩
  zero_mem' := ⟨0, N.zero_mem, fun _ _ => rfl, rfl⟩
  smul_mem' := by
    rintro a _ ⟨f, hfN, hf, rfl⟩
    exact ⟨a • f, N.smul_mem a hfN,
      fun j hj => by rw [Finsupp.smul_apply, hf j hj, smul_zero], Finsupp.smul_apply _ _ _⟩

/-- Membership in `leadIdeal`: `c` is a leading coefficient at `i` iff some `i`-truncated `f ∈ N` has
`f i = c`. -/
theorem mem_leadIdeal {N : Submodule ℤ (ι →₀ ℤ)} {i : ι} {c : ℤ} :
    c ∈ leadIdeal N i ↔ ∃ f ∈ N, IsTrunc i f ∧ f i = c := Iff.rfl

end SKEFTHawking.FreeSubmoduleInt
