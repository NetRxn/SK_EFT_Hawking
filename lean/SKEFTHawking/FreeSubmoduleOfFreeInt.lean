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

variable (N : Submodule ℤ (ι →₀ ℤ))

/-- **The principal generator** of the leading-coefficient ideal at `i` (`ℤ` a PID). The `i`-th step
of the basis exists exactly when `genCoeff N i ≠ 0`. -/
noncomputable def genCoeff (i : ι) : ℤ :=
  Submodule.IsPrincipal.generator (leadIdeal N i)

theorem genCoeff_mem (i : ι) : genCoeff N i ∈ leadIdeal N i :=
  Submodule.IsPrincipal.generator_mem _

/-- `genCoeff` generates the leading ideal: every leading coefficient at `i` is a `ℤ`-multiple of it. -/
theorem genCoeff_dvd {i : ι} {c : ℤ} (hc : c ∈ leadIdeal N i) : genCoeff N i ∣ c :=
  (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp hc

/-- **A chosen `i`-truncated witness** in `N` realizing the leading coefficient `genCoeff N i`. -/
noncomputable def gVec (i : ι) : ι →₀ ℤ := (mem_leadIdeal.mp (genCoeff_mem N i)).choose

theorem gVec_mem (i : ι) : gVec N i ∈ N := (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.1

theorem gVec_trunc (i : ι) : IsTrunc i (gVec N i) :=
  (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.2.1

theorem gVec_apply (i : ι) : (gVec N i) i = genCoeff N i :=
  (mem_leadIdeal.mp (genCoeff_mem N i)).choose_spec.2.2

/-- Above `i`, `gVec N i` vanishes (it is `i`-truncated). -/
theorem gVec_eq_zero_of_gt {i j : ι} (hj : i < j) : (gVec N i) j = 0 := gVec_trunc N i j hj

/-- **Evaluation of a `gVec`-combination at its top index reads off the leading coefficient.** For a
finite index set `s` with maximum `k`, `(∑ i ∈ s, g i • gVec N i) k = g k • genCoeff N k` — every lower
`gVec` is `i`-truncated hence vanishes at `k`. The triangular structure driving linear independence. -/
theorem sum_gVec_apply_max {s : Finset ι} (g : ι → ℤ) {k : ι} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≤ k) :
    (∑ i ∈ s, g i • gVec N i) k = g k • genCoeff N k := by
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single_of_mem k hk]
  · rw [Finsupp.smul_apply, gVec_apply]
  · intro i hi hik
    rw [Finsupp.smul_apply, gVec_eq_zero_of_gt N (lt_of_le_of_ne (hmax i hi) hik), smul_zero]

/-- **Triangular linear independence (finite-support core).** Any `ℤ`-combination of `gVec`s over a
finite set of indices with nonzero leading coefficients that sums to `0` has all coefficients `0` —
evaluate at the top nonzero index (`sum_gVec_apply_max`); its coefficient is `g k • genCoeff N k`, a
product of two nonzeros in the domain `ℤ`. -/
theorem gVec_indep_core {s : Finset ι} (g : ι → ℤ) (hs : ∀ i ∈ s, genCoeff N i ≠ 0)
    (hsum : ∑ i ∈ s, g i • gVec N i = 0) : ∀ i ∈ s, g i = 0 := by
  intro i₀ hi₀s
  by_contra hi₀
  set t := s.filter (fun i => g i ≠ 0) with ht
  have htne : t.Nonempty := ⟨i₀, Finset.mem_filter.mpr ⟨hi₀s, hi₀⟩⟩
  set k := t.max' htne with hkdef
  have hkt : k ∈ t := t.max'_mem htne
  have hks : k ∈ s := (Finset.mem_filter.mp hkt).1
  have hkg : g k ≠ 0 := (Finset.mem_filter.mp hkt).2
  have hsum_t : ∑ i ∈ t, g i • gVec N i = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i his hit
    have hgi : g i = 0 := by by_contra hgi; exact hit (Finset.mem_filter.mpr ⟨his, hgi⟩)
    rw [hgi, zero_smul]
  have hmax : ∀ j ∈ t, j ≤ k := fun j hj => t.le_max' j hj
  have hzero : g k • genCoeff N k = 0 := by
    rw [← sum_gVec_apply_max N g hkt hmax, hsum_t, Finsupp.coe_zero, Pi.zero_apply]
  rw [smul_eq_mul] at hzero
  exact mul_ne_zero hkg (hs k hks) hzero

end SKEFTHawking.FreeSubmoduleInt
