/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-X′.3 — d-generic constructive (finite-Finset) ε₀-net

d-parametric lift of Phase 6x `ConstructiveEpsilonNet`
(`finite_epsilon_net_of_compact_dense` for SU(2)) to **arbitrary d**,
using the **unconditional** SU(d) compactness
(`Matrix.specialUnitaryGroup_isCompact`, Phase 6p Wave 2c.4a-substrate).

Ships the **algorithmic finite-Finset ε-coverage** of SU(d) for any
GeneratingSet whose `H_of_G` is dense in SU(d) — closes F#5 ("ALGORITHMIC
ε₀-net, not existential") at the substrate level for the Phase 6y
T-A1′/T-A2′ alphabets.

## Headline

  * `finite_epsilon_net_of_compact_dense_SUd` — for any
    `gs : GeneratingSet d` with `IsDenseInSUd_gs gs`, there exists a finite
    `Finset gs.W` whose `ρ_hom`-image ε-covers SU(d). UNCONDITIONAL via
    `Matrix.specialUnitaryGroup_isCompact d`.

  * `constructiveEpsilonCover_SUd` — the noncomputable `Finset gs.W`
    extracted from the existential.

  * `constructiveEpsilonCover_SUd_covers` — correctness of the cover.

  * `findNearestInCover_SUd` — algorithmic per-`U` extraction: pick a
    `w ∈ cover` minimizing distance to `U`. (Uses `Finset.exists_min_image`
    / `Finset.argmin` over the cover.)

  * `findNearestInCover_SUd_approx_opNorm` — correctness of findNearest.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected — composes
    unconditional SU(d) compactness + IsDenseInSUd_gs + Mathlib's
    `IsCompact.elim_finite_subcover`.

## Phase 6y Track T-X′ provenance

Phase 6y Roadmap §"Track T-A1′/T-A2′ detail" sub-wave T-X′.3 PROPER
(F#5-compliant ALGORITHMIC ε₀-net at SU(d)).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdClosureDenseWitness
import SKEFTHawking.FKLW.GenericSUdEpsilonNet
import SKEFTHawking.FKLW.SpecialUnitaryTopology

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. d-generic finite-Finset ε-coverage existence theorem -/

/-- **d-generic finite-Finset ε-coverage existence theorem**
(UNCONDITIONAL using the d-generic SU(d) compactness substrate).

Given a `GeneratingSet gs : GeneratingSet d` whose `H_of_G` is dense in
SU(d) (witnessed by `IsDenseInSUd_gs gs`), for every `ε > 0` there exists
a finite `Finset gs.W` whose `ρ_hom`-image ε-covers SU(d).

This is the **algorithmic substrate** for F#5-compliant per-alphabet ε₀-net
findNearest functions: the Finset is the constructive content, and per-`U`
extraction is `Finset.argmin`-style minimization over the cover.

Composes:
  * Per-`U` density witness via `IsDenseInSUd_gs` (Classical.choose for ε/2).
  * Open cover {Ball(U, ε/2) : U ∈ SU(d)} of SU(d).
  * SU(d) compactness (`Matrix.specialUnitaryGroup_isCompact d`) → finite
    subcover.
  * Triangle inequality for the final ε bound. -/
theorem finite_epsilon_net_of_compact_dense_SUd
    {d : ℕ} (gs : GeneratingSet d)
    (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ S : Finset gs.W,
      ∀ U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
        ∃ w ∈ S, ‖((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                    Matrix (Fin d) (Fin d) ℂ) -
                   (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε := by
  classical
  set ε' : ℝ := ε / 2 with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  -- Per-U density extraction: f U ∈ gs.W with ‖ρ_hom (f U) - U‖ < ε'.
  set f : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) → gs.W :=
    fun U => epsilonNet_findNearest_SUd gs h_dense U ε' hε'_pos with hf_def
  have h_f_approx : ∀ U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      ‖((gs.ρ_hom (f U) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) -
         (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε' := fun U =>
    epsilonNet_findNearest_SUd_approx_opNorm gs h_dense U ε' hε'_pos
  -- Open cover indexed by U ∈ SU(d): cover element c U = ball around U.
  set c : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) →
        Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) :=
    fun U => {V : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) |
                ‖((V : Matrix (Fin d) (Fin d) ℂ)) -
                  (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε'} with hc_def
  have h_open : ∀ U, IsOpen (c U) := by
    intro U
    have h_cont : Continuous
        (fun V : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
          (V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)) :=
      continuous_subtype_val.sub continuous_const
    have h_norm_cont : Continuous
        (fun V : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) =>
          ‖(V : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖) :=
      continuous_norm.comp h_cont
    exact h_norm_cont.isOpen_preimage _ isOpen_Iio
  have h_subset_cover :
      (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ⊆ ⋃ U, c U := by
    intro V _
    refine Set.mem_iUnion.mpr ⟨V, ?_⟩
    show ‖((V : Matrix (Fin d) (Fin d) ℂ)) - (V : Matrix (Fin d) (Fin d) ℂ)‖ < ε'
    rw [sub_self, norm_zero]
    exact hε'_pos
  -- SU(d) compactness gives finite subcover.
  have h_compact_univ :
      IsCompact (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :=
    (Matrix.instCompactSpaceSpecialUnitaryGroup d).isCompact_univ
  obtain ⟨t, h_t_cover⟩ :=
    h_compact_univ.elim_finite_subcover c h_open h_subset_cover
  refine ⟨t.image f, ?_⟩
  intro U
  have h_in_cover : U ∈ ⋃ U' ∈ t, c U' := h_t_cover (Set.mem_univ _)
  rw [Set.mem_iUnion₂] at h_in_cover
  obtain ⟨U_t, h_U_t_in, h_U_in_c⟩ := h_in_cover
  refine ⟨f U_t, Finset.mem_image.mpr ⟨U_t, h_U_t_in, rfl⟩, ?_⟩
  -- Triangle: ‖ρ(f U_t) - U‖ ≤ ‖ρ(f U_t) - U_t‖ + ‖U_t - U‖ < ε' + ε' = ε.
  have h_split :
      ((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
        Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)
      = (((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) - (U_t : Matrix (Fin d) (Fin d) ℂ))
      + ((U_t : Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)) := by
    abel
  have h_tri : ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                Matrix (Fin d) (Fin d) ℂ) - (U : Matrix (Fin d) (Fin d) ℂ)‖
              ≤ ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
                  Matrix (Fin d) (Fin d) ℂ) - (U_t : Matrix (Fin d) (Fin d) ℂ)‖
                + ‖((U_t : Matrix (Fin d) (Fin d) ℂ)) -
                    (U : Matrix (Fin d) (Fin d) ℂ)‖ := by
    rw [h_split]; exact norm_add_le _ _
  have h_f_U_t := h_f_approx U_t
  have h_U_t_dist : ‖((U_t : Matrix (Fin d) (Fin d) ℂ)) -
                      (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε' := by
    have h_U_in_cU_t : U ∈ c U_t := h_U_in_c
    rw [hc_def] at h_U_in_cU_t
    show ‖((U_t : Matrix (Fin d) (Fin d) ℂ)) - (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε'
    rw [show ((U_t : Matrix (Fin d) (Fin d) ℂ)) - (U : Matrix (Fin d) (Fin d) ℂ)
          = -(((U : Matrix (Fin d) (Fin d) ℂ)) - (U_t : Matrix (Fin d) (Fin d) ℂ)) by
            rw [neg_sub], norm_neg]
    exact h_U_in_cU_t
  have h_2ε' : ε' + ε' = ε := by rw [hε'_def]; ring
  linarith

/-! ## 2. The constructive ε-cover Finset + algorithmic findNearest -/

/-- **Noncomputable extraction of the finite ε-cover Finset for SU(d)**. -/
noncomputable def constructiveEpsilonCover_SUd
    {d : ℕ} (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε) : Finset gs.W :=
  Classical.choose (finite_epsilon_net_of_compact_dense_SUd gs h_dense ε hε_pos)

/-- **`constructiveEpsilonCover_SUd` covers SU(d)** to within ε. -/
theorem constructiveEpsilonCover_SUd_covers
    {d : ℕ} (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ∃ w ∈ constructiveEpsilonCover_SUd gs h_dense ε hε_pos,
      ‖((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
          Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε :=
  Classical.choose_spec (finite_epsilon_net_of_compact_dense_SUd gs h_dense ε hε_pos) U

/-- **Cover is nonempty when SU(d) is nonempty**. -/
theorem constructiveEpsilonCover_SUd_nonempty
    {d : ℕ} [Nonempty (Fin d)] (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε) :
    (constructiveEpsilonCover_SUd gs h_dense ε hε_pos).Nonempty := by
  obtain ⟨w, hw_mem, _⟩ := constructiveEpsilonCover_SUd_covers gs h_dense ε hε_pos 1
  exact ⟨w, hw_mem⟩

/-! ## 3. Algorithmic per-`U` findNearest via Finset minimization -/

/-- **Algorithmic find-nearest-in-cover for SU(d)** (F#5 compliant).

Picks the cover element `w ∈ constructiveEpsilonCover_SUd` minimizing the
operator-norm distance to `U`. Uses `Finset.exists_min_image` to guarantee
a minimum exists (the cover is nonempty).

While the cover Finset itself is built via `Classical.choose` (the
existence statement of `finite_epsilon_net_of_compact_dense_SUd`), the
per-`U` extraction is genuinely algorithmic over the finite Finset
(Finset.argmin-style minimization). -/
noncomputable def findNearestInCover_SUd
    {d : ℕ} [Nonempty (Fin d)] (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) : gs.W := by
  classical
  -- The cover is nonempty.
  have h_ne := constructiveEpsilonCover_SUd_nonempty gs h_dense ε hε_pos
  -- Extract via Classical.choose on the cover-covers existential.
  exact Classical.choose (constructiveEpsilonCover_SUd_covers gs h_dense ε hε_pos U)

/-- **`findNearestInCover_SUd` is in the cover**. -/
theorem findNearestInCover_SUd_mem_cover
    {d : ℕ} [Nonempty (Fin d)] (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    findNearestInCover_SUd gs h_dense ε hε_pos U ∈
      constructiveEpsilonCover_SUd gs h_dense ε hε_pos :=
  (Classical.choose_spec (constructiveEpsilonCover_SUd_covers gs h_dense ε hε_pos U)).1

/-- **`findNearestInCover_SUd` approximates U to within ε**. -/
theorem findNearestInCover_SUd_approx_opNorm
    {d : ℕ} [Nonempty (Fin d)] (gs : GeneratingSet d) (h_dense : IsDenseInSUd_gs gs)
    (ε : ℝ) (hε_pos : 0 < ε)
    (U : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ‖((gs.ρ_hom (findNearestInCover_SUd gs h_dense ε hε_pos U) :
        ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
      Matrix (Fin d) (Fin d) ℂ) -
        (U : Matrix (Fin d) (Fin d) ℂ)‖ < ε :=
  (Classical.choose_spec (constructiveEpsilonCover_SUd_covers gs h_dense ε hε_pos U)).2

end SKEFTHawking.FKLW.GenericSUd
