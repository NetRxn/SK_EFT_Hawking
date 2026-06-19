import Mathlib
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-C0a) — the `{W, Kᶜ}` excisive cover of a compact in an open

The first step of the **fund-cycle-in-an-open** representation (`C0`): a relative cycle for `(M, Kᶜ)`
(a representative of the fundamental class `μ_K ∈ Hₙ(M|K)`) has, after subdivision, a representative
**supported in any open `W ⊇ K`**. This needs the two-set cover `𝒰 = {W, Kᶜ}` to be **excisive** — its
interiors cover `M` — which holds exactly because a compact `K` in a Hausdorff space is closed (so
`Kᶜ` is open, `interior Kᶜ = Kᶜ`) and `K ⊆ W` open (so `interior W = W` and `W ∪ Kᶜ = univ`).

This is the geometric input that makes `relativeDualityK` instantiable in the inductive open-cover
Poincaré-duality proof (Hatcher 3.36): the fund cycle of `K` lives in `C(W)` for the open `W`, so the
cap lands in `H_{n-k}(sub W)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularExcision SKEFTHawking.SingularSubdivision

namespace SKEFTHawking.SingularFundCycleOpen

variable {X : TopCat} [T2Space ↑X]

/-- **The `{W, Kᶜ}` interiors cover `M`** when `K` is compact and `K ⊆ W` with `W` open: `interior W = W`
(open), `interior Kᶜ = Kᶜ` (`K` compact ⟹ closed ⟹ `Kᶜ` open), and `W ∪ Kᶜ = univ` (from `K ⊆ W`). This
is the excisiveness needed by `exists_iterate_smallChains` to subdivide a relative cycle into one
supported in `W`. -/
theorem interiors_cover_of_compact_subset_open {K W : Set ↑X} (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) :
    (⋃ U ∈ ({W, Kᶜ} : Set (Set ↑X)), interior U) = Set.univ := by
  have hKcl : IsClosed K := hK.isClosed
  rw [Set.biUnion_insert, Set.biUnion_singleton, hW.interior_eq, hKcl.isOpen_compl.interior_eq]
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ K
  · exact Set.mem_union_left _ (hKW hx)
  · exact Set.mem_union_right _ hx

/-- **The fundamental cycle of a compact in an open** (`C0`): a relative cycle `z` for `(M, Kᶜ)` (its
boundary `∂z ∈ C(Kᶜ)` — the condition a `hasFundClass` representative `μ_K` satisfies) has, after
subdivision, a representative **supported in any open `W ⊇ K`**: `z_W ∈ subspaceChains W`, still a
relative cycle (`∂z_W ∈ C(Kᶜ)`), and rel-homologous to `z`
(`mk z + mk z_W ∈ relBoundaries`). The subdivision `Sdᵐ z` is small for `{W, Kᶜ}`
(`exists_iterate_smallChains` + `interiors_cover_of_compact_subset_open`), so splits as `z_W + z_{Kᶜ}`
(`smallChains_two_le`); the `W`-part is the representative, with `∂z_W ∈ C(Kᶜ)` because `∂(Sdᵐ z) =
Sdᵐ(∂z) ∈ C(Kᶜ)` (`singularSd` preserves `C(Kᶜ)`) and `∂z_{Kᶜ} ∈ C(Kᶜ)`, and rel-homologous because
`mk z + mk(Sdᵐ z) ∈ relBoundaries` (`relative_add_singularSd_iterate_mem_relBoundaries`) with
`mk(Sdᵐ z) = mk z_W` (`z_{Kᶜ}` vanishes in the relative chain). This is what makes `relativeDualityK`
instantiable in the open-cover induction: the fund cycle of `K` lives in `C(W)`. -/
theorem exists_fundCycle_in_open {K W : Set ↑X} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    {n : ℕ} {z : SingularChain X (n + 1)} (hz : chainBoundary X n z ∈ subspaceChains Kᶜ n) :
    ∃ zW : SingularChain X (n + 1), zW ∈ subspaceChains W (n + 1) ∧
      chainBoundary X n zW ∈ subspaceChains Kᶜ n ∧
      RelativeChain.mk Kᶜ (n + 1) z + RelativeChain.mk Kᶜ (n + 1) zW
        ∈ relBoundaries Kᶜ (n + 1) := by
  obtain ⟨m, hm⟩ :=
    exists_iterate_smallChains (interiors_cover_of_compact_subset_open hK hW hKW) z
  obtain ⟨zW, hzW, zKc, hzKc, hsplit⟩ := Submodule.mem_sup.mp (smallChains_two_le W Kᶜ (n + 1) hm)
  refine ⟨zW, hzW, ?_, ?_⟩
  · -- `∂z_W ∈ C(Kᶜ)`: `∂z_W = ∂(Sdᵐ z) - ∂z_{Kᶜ}`, both in `C(Kᶜ)`.
    have hbd_sd : chainBoundary X n ((⇑(singularSd X (n + 1)))^[m] z) ∈ subspaceChains Kᶜ n := by
      rw [singularSd_iterate_chainBoundary]
      exact singularSd_iterate_mem_subspaceChains hz m
    have heq : chainBoundary X n zW
        = chainBoundary X n ((⇑(singularSd X (n + 1)))^[m] z) - chainBoundary X n zKc :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [heq]
    exact Submodule.sub_mem _ hbd_sd (chainBoundary_mem_subspaceChains Kᶜ n zKc hzKc)
  · -- rel-homologous: `mk z + mk(Sdᵐ z) ∈ relBoundaries` and `mk(Sdᵐ z) = mk z_W`.
    have hrel := relative_add_singularSd_iterate_mem_relBoundaries (A := Kᶜ) hz m
    have hmk : RelativeChain.mk Kᶜ (n + 1) ((⇑(singularSd X (n + 1)))^[m] z)
        = RelativeChain.mk Kᶜ (n + 1) zW := by
      rw [← hsplit]
      refine (Submodule.Quotient.eq _).mpr ?_
      rw [add_sub_cancel_left]
      exact hzKc
    rwa [hmk] at hrel

end SKEFTHawking.SingularFundCycleOpen
