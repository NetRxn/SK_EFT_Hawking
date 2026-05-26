/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-S′ — Constructive ε₀-net for Clifford+T (and any alphabet with dense closure in SU(2))

Ships the **finite-Finset ε₀-coverage** existence theorem for any
`GeneratingSet` whose `H_of_G` is dense in `SU(2)`. This strengthens
the Phase 6u Wave 3 existential ε₀-net (per-`U` `Classical.choose`)
to: there *exists a single finite `Finset`* of words that ε₀-covers
all of SU(2).

For Clifford+T specifically (the canonical Phase 6u Track T-S ε₀-net),
this gives a uniform finite-Finset of words whose `ρ_CliffT` images
ε₀-cover SU(2). The downstream `cliffordTBaseFinder` can then be
recast as `Finset.argmin`-style minimization over this Finset (a
genuinely runnable algorithm modulo decidable real-norm comparison
substrate).

## Headline (parameterized by SU(2)-compactness)

  * `finite_epsilon_net_of_compact_dense` — generic statement: if
    `(SU(2) : Set _).IsCompact` and the generating set's `H_of_G` is
    `IsDenseInSU2_gs`, then there exists a finite `Finset` of words
    that ε-covers SU(2) for any `ε > 0`.

  * `cliffordT_finite_epsilon_net_of_compact` — instantiation at the
    Clifford+T generating set (assuming SU(2) compactness).

## SU(2) compactness substrate

The hypothesis `IsCompact (SU(2) : Set (Matrix (Fin 2) (Fin 2) ℂ))` is
standard (SU(2) is closed and bounded in the finite-dimensional Banach
space `Matrix (Fin 2) (Fin 2) ℂ`; Heine-Borel gives compactness). It
is **not currently a direct typeclass instance** in Mathlib4 v4.29.1
for `Matrix.specialUnitaryGroup`; the SU(2) compactness proof is a
separate Mathlib-upstream-PR candidate (Phase 6x follow-on or T-A2.0
absorption).

This file ships the **substantive ε₀-net coverage theorem** assuming
SU(2) compactness as an explicit hypothesis, factoring out the missing
substrate.

## Ross-Selinger 2014 algorithmic refinement (Lit-Search dependency)

The Ross-Selinger 2014 (arXiv:1403.2975) algorithm for exact Clifford+T
synthesis over the ring `ℤ[ω][1/√2]` (where `ω = exp(iπ/4)` is a
primitive 8th root of unity) provides a *computationally efficient*
ε₀-net via symbolic algebraic-number-theoretic enumeration. Mathlib4
v4.29.1 has `CyclotomicRing` substrate but not the `ℤ[ω][1/√2]`-
specific Ross-Selinger enumeration.

A Lit-Search task drop for the Ross-Selinger formalization is queued
at `Lit-Search/tasks/T-S-prime-ross-selinger.md` (Phase 6x deep
research task). The finite-Finset coverage shipped here is the
generic-substrate intermediate result that the Ross-Selinger refinement
will eventually optimize.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.GenericEpsilonNet
import SKEFTHawking.FKLW.GenericClosureDenseWitness
import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.CliffordTV4WitnessUnconditional
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW

/-! ## 1. Finite-Finset ε-coverage (existence) -/

/-- **Finite-Finset ε-coverage existence theorem**.

Given a `GeneratingSet gs` whose `H_of_G` is dense in `SU(2)` (witnessed
by `IsDenseInSU2_gs gs`), and given that `SU(2)` is compact as a subset
of `Matrix (Fin 2) (Fin 2) ℂ`, for every `ε > 0` there exists a finite
`Finset` of words `S : Finset gs.W` such that `gs.ρ_hom '' S` is an
ε-cover of SU(2): every `U ∈ SU(2)` lies within ε of some
`gs.ρ_hom w` for `w ∈ S`.

This strengthens `epsilonNet_findNearest` (which gives a per-`U`
existence via `Classical.choose`) to a uniform finite-Finset cover.
The Finset is the constructive content; per-`U` extraction of a
specific witness `w ∈ S` can be done by direct minimization over `S`.

**Proof sketch**:
  1. By density, for each `U ∈ SU(2)`, there exists `w_U ∈ gs.W` with
     `‖gs.ρ_hom w_U - U‖ < ε/2`. The balls `Ball(gs.ρ_hom w_U, ε/2)`
     for `U ∈ SU(2)` thus cover SU(2).
  2. By compactness of SU(2) (the hypothesis), there exists a finite
     subcover. The corresponding finite set of words is `S`.
  3. For any `U ∈ SU(2)`, the finite subcover places some `w_U` with
     `‖gs.ρ_hom w_{U} - U‖ < ε`. -/
theorem finite_epsilon_net_of_compact_dense
    (gs : GeneratingSet)
    (h_dense : IsDenseInSU2_gs gs)
    (h_compact : IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ S : Finset gs.W,
      ∀ U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        ∃ w ∈ S, ‖((gs.ρ_hom w : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
                   (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε := by
  -- Step 1: per-U existence via density, packaged as a Choice function.
  classical
  set ε' : ℝ := ε / 2 with hε'_def
  have hε'_pos : 0 < ε' := by positivity
  -- For each U ∈ SU(2), extract a word w_U with ‖gs.ρ_hom w_U - U‖ < ε'.
  set f : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) → gs.W :=
    fun U => epsilonNet_findNearest gs h_dense U ε' hε'_pos with hf_def
  have h_f_approx : ∀ U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
      ‖((gs.ρ_hom (f U) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) -
         (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε' := by
    intro U
    exact epsilonNet_findNearest_approx_opNorm gs h_dense U ε' hε'_pos
  -- Step 2: open cover indexed by U ∈ SU(2). The cover element at U is the
  -- open ball around U of radius ε'.
  set c : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    fun U => {V : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) |
                ‖((V : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε'}
    with hc_def
  have h_open : ∀ U, IsOpen (c U) := by
    intro U
    -- {V | ‖V - U‖ < ε'} is open in the subtype topology (preimage of an open
    -- ball under the continuous coercion V ↦ V.val).
    have h_cont : Continuous
        (fun V : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
          (V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
      exact (continuous_subtype_val.sub continuous_const)
    have h_norm_cont : Continuous
        (fun V : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) =>
          ‖(V : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖) :=
      continuous_norm.comp h_cont
    exact h_norm_cont.isOpen_preimage _ isOpen_Iio
  have h_subset_cover : (Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
      ⊆ ⋃ U, c U := by
    intro V _
    refine Set.mem_iUnion.mpr ⟨V, ?_⟩
    -- ‖V - V‖ = 0 < ε'.
    show ‖((V : Matrix (Fin 2) (Fin 2) ℂ)) - (V : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε'
    rw [sub_self, norm_zero]
    exact hε'_pos
  -- Step 3: apply IsCompact.elim_finite_subcover.
  obtain ⟨t, h_t_cover⟩ :=
    h_compact.elim_finite_subcover c h_open h_subset_cover
  -- t : Finset of indices, and SU(2) ⊆ ⋃ U ∈ t, c U.
  -- The finite Finset of words S := { f U | U ∈ t }.
  refine ⟨t.image f, ?_⟩
  intro U
  have h_in : U ∈ Set.univ := Set.mem_univ _
  have h_in_cover : U ∈ ⋃ U' ∈ t, c U' := h_t_cover h_in
  rw [Set.mem_iUnion₂] at h_in_cover
  obtain ⟨U_t, h_U_t_in, h_U_in_c⟩ := h_in_cover
  -- U ∈ c U_t means ‖U - U_t‖ < ε'. Triangle inequality with f U_t.
  refine ⟨f U_t, Finset.mem_image.mpr ⟨U_t, h_U_t_in, rfl⟩, ?_⟩
  -- ‖ρ(f U_t) - U‖ ≤ ‖ρ(f U_t) - U_t‖ + ‖U_t - U‖ < ε' + ε' = ε.
  have h_tri : ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖
              ≤ ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                  Matrix (Fin 2) (Fin 2) ℂ) - (U_t : Matrix (Fin 2) (Fin 2) ℂ)‖
                + ‖((U_t : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ := by
    have h_split :
        ((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)
        = (((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
            Matrix (Fin 2) (Fin 2) ℂ) - (U_t : Matrix (Fin 2) (Fin 2) ℂ))
        + ((U_t : Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)) := by abel
    rw [h_split]
    exact norm_add_le _ _
  have h_f_U_t : ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) - (U_t : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε' := h_f_approx U_t
  have h_U_t_dist : ‖((U_t : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε' := by
    -- U ∈ c U_t means ‖U - U_t‖ < ε'. Norm symmetric.
    have h_U_in_cU_t : U ∈ c U_t := h_U_in_c
    rw [hc_def] at h_U_in_cU_t
    show ‖((U_t : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε'
    rw [show ((U_t : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)
          = -(((U : Matrix (Fin 2) (Fin 2) ℂ)) - (U_t : Matrix (Fin 2) (Fin 2) ℂ)) by
            rw [neg_sub], norm_neg]
    exact h_U_in_cU_t
  -- Combine.
  have h_sum : ‖((gs.ρ_hom (f U_t) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                Matrix (Fin 2) (Fin 2) ℂ) - (U_t : Matrix (Fin 2) (Fin 2) ℂ)‖
              + ‖((U_t : Matrix (Fin 2) (Fin 2) ℂ)) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖
              < ε' + ε' := by linarith
  have h_2ε' : ε' + ε' = ε := by rw [hε'_def]; ring
  linarith

/-! ## 2. Clifford+T instantiation -/

/-- **Clifford+T finite-Finset ε-cover existence** (conditional on
SU(2) compactness).

Specializes `finite_epsilon_net_of_compact_dense` at
`cliffordTGeneratingSet` and consumes the unconditional
`cliffordT_density_unconditional` (Phase 6u T-S.2 substantive
discharge).

The Finset of `FreeGroup (Fin 2)` words is the constructive
ε₀-coverage. Per-`U` minimization over this Finset (with respect to
the operator-norm distance to `ρ_CliffT(w)`) gives the
`cliffordTBaseFinder`-replacement that consumes the existential
ε-net **without** invoking `Classical.choose` on each query (the
Finset itself was chosen once via Classical at construction). -/
theorem cliffordT_finite_epsilon_net_of_compact
    (h_compact : IsCompact ((Set.univ : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))))
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ S : Finset (FreeGroup (Fin 2)),
      ∀ U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ),
        ∃ w ∈ S, ‖((cliffordTGeneratingSet.ρ_hom w :
                    ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
                    Matrix (Fin 2) (Fin 2) ℂ) -
                   (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε :=
  finite_epsilon_net_of_compact_dense
    cliffordTGeneratingSet cliffordT_density_unconditional h_compact ε hε_pos

end SKEFTHawking.FKLW.GenericSU2
