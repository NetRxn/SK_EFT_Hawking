/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4a — abstract "irreducible ⟹ orbit spans"

The load-bearing **assembly** step of Phase 6z Wave 4 (`hX_spans`): the Clifford-conjugation orbit of the
seed tangent `X₀ ≠ 0` spans `𝔰𝔲(8)` *because* the Clifford adjoint representation on `𝔰𝔲(8)` is
irreducible. This module ships the abstract engine — a general representation-theoretic fact, independent
of the Clifford/Pauli specifics:

> For a linear representation `ρ : G →* (V →ₗ[ℝ] V)` whose only `ρ`-invariant submodules are `⊥` and `⊤`
> (irreducibility), the ℝ-span of the orbit `{ρ g v : g}` of any nonzero `v` is all of `V`.

The Clifford-specific irreducibility (Pauli-conjugation eigenvectors `Ad_{P_w}(P_v) = (−1)^⟨w,v⟩ P_v`,
distinct characters ⟹ coordinate subspaces, Clifford transitivity on the 63 Pauli lines) is built in the
companion Wave-4 modules and fed into `hirr` here.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 4 increment 4a (abstract orbit-spans engine). 2026-05-28.
-/

import Mathlib

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

/-- **Orbit of a nonzero vector spans, under an irreducible linear representation.**

If `ρ : G →* (V →ₗ[ℝ] V)` is a linear representation of a monoid `G` on an ℝ-module `V` whose only
`ρ`-invariant submodules are `⊥` and `⊤` (irreducibility, stated as the `hirr` hypothesis), then the
ℝ-span of the orbit `{ρ g v : g}` of any nonzero `v` is all of `V`.

Proof: `span (orbit v)` is `ρ`-invariant (each `ρ g` maps the spanning set `{ρ h v}` into itself via
`ρ g (ρ h v) = ρ (g*h) v`) and contains `v = ρ 1 v ≠ 0`; irreducibility forces it to be `⊤`. -/
theorem span_orbit_eq_top_of_irreducible
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {G : Type*} [Monoid G] (ρ : G →* (V →ₗ[ℝ] V))
    (hirr : ∀ W : Submodule ℝ V,
      (∀ g : G, ∀ w : V, w ∈ W → ρ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {v : V} (hv : v ≠ 0) :
    Submodule.span ℝ (Set.range (fun g : G => ρ g v)) = ⊤ := by
  set S : Set V := Set.range (fun g : G => ρ g v) with hS
  -- `span S` is `ρ`-invariant.
  have h_inv : ∀ g : G, ∀ w : V, w ∈ Submodule.span ℝ S → ρ g w ∈ Submodule.span ℝ S := by
    intro g w hw
    have hsub : (ρ g) '' S ⊆ S := by
      rintro x ⟨a, ⟨h, rfl⟩, rfl⟩
      exact ⟨g * h, by simp only [map_mul]; rfl⟩
    have hmem : ρ g w ∈ Submodule.map (ρ g) (Submodule.span ℝ S) :=
      Submodule.mem_map_of_mem hw
    rw [Submodule.map_span] at hmem
    exact Submodule.span_mono hsub hmem
  -- Irreducibility: `span S` is `⊥` or `⊤`; it contains `v ≠ 0`, so it is `⊤`.
  rcases hirr (Submodule.span ℝ S) h_inv with h_bot | h_top
  · exfalso
    apply hv
    have hv_mem : v ∈ Submodule.span ℝ S := Submodule.subset_span ⟨1, by simp⟩
    rw [h_bot, Submodule.mem_bot] at hv_mem
    exact hv_mem
  · exact h_top

end SKEFTHawking.FKLW.CliffordCCZSU8
