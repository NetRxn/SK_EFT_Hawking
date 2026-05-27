/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g-substrate — n-parameter exp product

The d-generic n-parameter exp product map
`Φ_n(t_1, …, t_n) := ∏_{i=0}^{n-1} exp(t_i • X_i)`,
parameterized by a finite family `X : Fin n → Matrix (Fin d) (Fin d) ℂ`.

This is the structural foundation for the multi-parameter IFT
discharge of S.2g unconditional. The full derivative formula
`t ↦ ∑ t_i • X_i` is heavy work (see GenericSUdTwoDirExpProduct
abandoned-attempt notes for the n=2 instance-pollution walls); this
module ships only the structural piece — definition + base properties +
SU(d)-image preservation + H-image preservation.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (substrate part —
n-parameter exp product structural foundation).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdLocalDiffeoRestriction

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. The n-parameter exp product definition -/

/-- **n-parameter exp product** `multiDirExpProduct X t :=
exp(t_0 • X_0) · exp(t_1 • X_1) · … · exp(t_{n-1} • X_{n-1})`.

The product is taken in natural index order via `List.prod` over
`List.finRange n` (since `Matrix (Fin d) (Fin d) ℂ` is non-commutative,
we cannot use `Finset.prod` which requires CommMonoid).
At `t = 0` (zero vector), gives `1` (each exp factor is `exp(0) = 1`). -/
noncomputable def multiDirExpProduct {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (t : Fin n → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  ((List.finRange n).map (fun i => NormedSpace.exp ((t i : ℂ) • X i))).prod

/-- **`multiDirExpProduct X 0 = 1`** (identity at zero parameter vector). -/
@[simp]
theorem multiDirExpProduct_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    multiDirExpProduct X (fun _ => 0) = 1 := by
  unfold multiDirExpProduct
  -- Each factor: exp((0:ℂ) • X i) = exp 0 = 1.
  have h_each : ∀ i ∈ List.finRange n,
      NormedSpace.exp (((0 : ℝ) : ℂ) • X i : Matrix (Fin d) (Fin d) ℂ) = 1 := by
    intro i _
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  rw [List.map_congr_left (fun i hi => h_each i hi)]
  -- Goal: ((List.finRange n).map (fun _ => 1)).prod = 1
  rw [show (fun i : Fin n => (1 : Matrix (Fin d) (Fin d) ℂ)) =
      Function.const (Fin n) 1 from rfl]
  rw [List.map_const]
  exact List.prod_replicate _ _ |>.trans (one_pow _)

/-! ## 2. SU(d) image preservation -/

/-- **n-parameter exp product preserves SU(d) membership**: if every
generator `X i ∈ 𝔰𝔲(d)` (skew-Hermitian + traceless), then
`multiDirExpProduct X t ∈ SU(d)` for any parameter vector `t`.

Each factor `exp(t i • X i) ∈ SU(d)` (since `t i • X i` is skew-Hermitian
with trace 0, so `exp_of_su_d_mem_SUd` applies). Product of SU(d)
elements is in SU(d). -/
theorem multiDirExpProduct_mem_SUd {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ i, (X i).IsSkewHermitian ∧ (X i).trace = 0)
    (t : Fin n → ℝ) :
    multiDirExpProduct X t ∈ Matrix.specialUnitaryGroup (Fin d) ℂ := by
  -- Show by induction: the partial product over any Finset s is in SU(d).
  -- Actually: SU(d) is a Subgroup (which is a Submonoid + closed under
  -- inverse). Finset.prod of elements in a Submonoid is in the Submonoid.
  unfold multiDirExpProduct
  -- Goal: (List.finRange n).map (fun i => exp(...)).prod ∈ SU(d).
  -- Each factor is in SU(d). SU(d) is a Submonoid; List.prod over a Submonoid stays in it.
  have h_factor_mem : ∀ i,
      (NormedSpace.exp ((t i : ℂ) • X i) : Matrix (Fin d) (Fin d) ℂ) ∈
        Matrix.specialUnitaryGroup (Fin d) ℂ := by
    intro i
    -- t i • X i is skew-Hermitian (real scalar of skew-Hermitian).
    have h_smul_sh : ((t i : ℂ) • X i :
        Matrix (Fin d) (Fin d) ℂ).IsSkewHermitian := by
      have h_X_sh : (X i).IsSkewHermitian := (hX i).1
      show ((t i : ℂ) • X i).conjTranspose = -((t i : ℂ) • X i)
      rw [Matrix.conjTranspose_smul, h_X_sh]
      have h_star : star ((t i : ℂ) : ℂ) = (t i : ℂ) := Complex.conj_ofReal _
      rw [h_star, smul_neg]
    have h_smul_tr : ((t i : ℂ) • X i :
        Matrix (Fin d) (Fin d) ℂ).trace = 0 := by
      rw [Matrix.trace_smul, (hX i).2, smul_zero]
    exact exp_of_su_d_mem_SUd h_smul_sh h_smul_tr
  -- Lift to product membership via Submonoid closure of List.prod.
  -- specialUnitaryGroup is a Submonoid; `Submonoid.list_prod_mem` applies directly.
  apply Submonoid.list_prod_mem
  intro m hm
  -- m : Matrix (Fin d) (Fin d) ℂ is in the map's image; find the i.
  rw [List.mem_map] at hm
  obtain ⟨i, _, h_eq⟩ := hm
  rw [← h_eq]
  exact h_factor_mem i

/-! ## 3. H-image preservation (consumer hypothesis form)

If every factor's flow line lies in a subgroup H ≤ SU(d), then the
n-parameter exp product also lies in H. Formally: given the witness
hypothesis from `CartanFinalStep_SUd_v4` (per-direction flow lines),
the multi-parameter product map lands in H.val. -/

/-- **n-parameter exp product preserves H-membership** (consumer form).

Given:
  * `X : Fin n → 𝔰𝔲(d)` traceless skew-Hermitian;
  * For each `i` and `t i : ℝ`, an element `M ∈ H` with
    `M.val = NormedSpace.exp ((t i : ℂ) • X i)` (per-direction flow
    line in H);

then `multiDirExpProduct X t ∈ (H : Set _)` viewed at the matrix level
(actually: the product LIVES in SU(d) and projects to H as a subgroup
element). The substantive content is: H, being a subgroup of SU(d),
is closed under product, so the product of the per-direction flow
points stays in H. -/
theorem multiDirExpProduct_mem_H {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (h_flow : ∀ i, ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
        M ∈ H ∧ M.val = NormedSpace.exp ((t : ℂ) • X i))
    (t : Fin n → ℝ) :
    ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      M ∈ H ∧ M.val = multiDirExpProduct X t := by
  -- Pick one witness M_i ∈ H for each i.
  choose M_i hM_i_mem hM_i_val using
    (fun i => h_flow i (t i))
  -- The list-product (∏ in List.finRange order) of M_i is in H (Subgroup.list_prod_mem)
  -- and projects to multiDirExpProduct X t.
  let M_prod := ((List.finRange n).map M_i).prod
  refine ⟨M_prod, ?_, ?_⟩
  · -- M_prod ∈ H via Subgroup.list_prod_mem.
    apply Subgroup.list_prod_mem
    intro m hm
    rw [List.mem_map] at hm
    obtain ⟨i, _, h_eq⟩ := hm
    rw [← h_eq]
    exact hM_i_mem i
  · -- M_prod.val = multiDirExpProduct X t.
    show (((List.finRange n).map M_i).prod).val = multiDirExpProduct X t
    -- (∏ list).val = ∏ list.map (·.val) via Submonoid.coe_list_prod.
    rw [Submonoid.coe_list_prod]
    unfold multiDirExpProduct
    -- Goal: (list.map M_i).map (·.val).prod = (list.map (fun i => exp(...))).prod
    rw [List.map_map]
    -- Goal: (list.map ((·.val) ∘ M_i)).prod = (list.map (fun i => exp((t i : ℂ) • X i))).prod
    congr 1
    apply List.map_congr_left
    intro i _
    -- ((·.val) ∘ M_i) i = (M_i i).val = exp((t i : ℂ) • X i)
    exact hM_i_val i

end SKEFTHawking.FKLW.GenericSUd
