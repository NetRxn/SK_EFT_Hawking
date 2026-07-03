import Mathlib
import SKEFTHawking.SingularSphereBottom
import SKEFTHawking.SingularSphereHighDegree
import SKEFTHawking.SingularH0PathConnected

/-!
# Phase 5q.G (G1 PD-induction, base-case substrate) — the middle sphere homology vanishes

`H_j(Sⁿ) = 0` for `0 < j < n` — the missing middle band between the library's
`sphere_homology_high` (above-dimension vanishing) and `topSphereIso`/`circleH1Equiv` (the top).

* `sphere_homology_one` (B1a): `H₁(Sⁿ) = 0` for `n ≥ 2` — the bottom-suspension embedding
  `bottomSuspEquiv : H₁(Sⁿ) ≃ H̃₀(Sⁿ∖{v,-v})` composed with the vanishing of reduced `H̃₀` of the
  doubly-punctured sphere, which is PATH-CONNECTED for `n ≥ 2`: under the stereographic
  homeomorphism `Sⁿ∖{-v} ≃ₜ ℝⁿ` the double puncture is the complement of ONE point of `ℝⁿ`,
  path-connected by `isPathConnected_compl_singleton_of_one_lt_rank` (rank `n ≥ 2 > 1`).
* `sphere_homology_middle` (B1b): the full band, by downward `dimReductionEquiv` induction
  (`H_{k+2}(Sⁿ⁺¹) ≅ H_{k+1}(Sⁿ)`) terminating at B1a.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularH0
open SKEFTHawking.SingularSphereAcyclic SKEFTHawking.SingularSphereBottom
open SKEFTHawking.SingularSphereHighDegree SKEFTHawking.SingularEuclideanAcyclic

namespace SKEFTHawking.SingularSphereMiddle

/-- **The doubly-punctured sphere is path-connected for `n ≥ 2`** (as the `restr`-subset of the
`(-v)`-punctured subspace): under `puncturedHomeo n (antipode v) : Sⁿ∖{-v} ≃ₜ ℝⁿ` the set is the
complement of a single point of `ℝⁿ`, path-connected since `rank ℝ ℝⁿ = n > 1`. -/
theorem restr_doubly_punctured_pathConnected (n : ℕ) (hn : 2 ≤ n)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsPathConnected (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
    rw [← Module.finrank_eq_rank, hfr]
    exact_mod_cast hn
  have hvmem : (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
      ∈ ({antipode v}ᶜ : Set ↑(Sph n)) := by
    simpa using ne_antipode v
  set φ := puncturedHomeo n (antipode v) with hφ
  have hpcE : IsPathConnected ({φ ⟨v, hvmem⟩}ᶜ : Set ↑(Eucl n)) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank (φ ⟨v, hvmem⟩)
  have himg : (φ.symm '' ({φ ⟨v, hvmem⟩}ᶜ : Set ↑(Eucl n)))
      = (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) := by
    ext x
    simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_singleton_iff, restr,
      Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      show ¬((↑(φ.symm y) : ↑(Sph n)) ∈ ({v} : Set ↑(Sph n)))
      rw [Set.mem_singleton_iff]
      intro hxv
      refine hy ?_
      have heq : φ.symm y = ⟨v, hvmem⟩ := Subtype.ext hxv
      rw [show y = φ (φ.symm y) from (φ.apply_symm_apply y).symm, heq]
    · intro hx
      refine ⟨φ x, ?_, φ.symm_apply_apply x⟩
      intro hcontra
      have hxeq : x = ⟨v, hvmem⟩ := φ.injective (by rw [hcontra])
      exact hx (by rw [hxeq])
  rw [← himg]
  exact hpcE.image (map_continuous φ.symm)

/-- **B1a: `H₁(Sⁿ) = 0` for `n ≥ 2`.** The bottom suspension embeds `H₁(Sⁿ)` into reduced
`H̃₀` of the doubly-punctured sphere, which vanishes by path-connectedness
(`SingularH0PathConnected.augH_injective`). -/
theorem sphere_homology_one (n : ℕ) (hn : 2 ≤ n) (x : Homology (Sph n) 1) : x = 0 := by
  set v := basePoint n with hv
  have hpc : IsPathConnected (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) :=
    restr_doubly_punctured_pathConnected n hn v
  haveI hpcs : PathConnectedSpace
      ↑(sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) :=
    isPathConnected_iff_pathConnectedSpace.mp hpc
  have hker : LinearMap.ker (augH (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) = ⊥ :=
    LinearMap.ker_eq_bot.mpr (SKEFTHawking.SingularH0PathConnected.augH_injective)
  have h0 : bottomSuspMap n v x = 0 := by
    have hmem : bottomSuspMap n v x
        ∈ LinearMap.ker (augH (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) := by
      rw [← bottomSuspMap_range]
      exact ⟨x, rfl⟩
    rw [hker] at hmem
    exact hmem
  exact bottomSuspMap_injective (by rw [h0, map_zero])

/-- **B1b: the middle sphere homology vanishes** — `H_j(Sⁿ) = 0` for `0 < j < n`, by downward
`dimReductionEquiv` induction terminating at `sphere_homology_one`. -/
theorem sphere_homology_middle :
    ∀ (j n : ℕ), 0 < j → j < n → ∀ x : Homology (Sph n) j, x = 0 := by
  intro j
  induction j with
  | zero => intro n h0 _ _; exact absurd h0 (lt_irrefl 0)
  | succ k ih =>
    intro n _ hlt x
    match k, n, hlt with
    | 0, n, hlt =>
      exact sphere_homology_one n (by omega) x
    | k + 1, n + 1, hlt =>
      have hred := dimReductionEquiv (n := n + 1) (basePoint (n + 1)) k
      rw [← LinearEquiv.map_eq_zero_iff hred]
      exact ih n (Nat.succ_pos k) (by omega) (hred x)

end SKEFTHawking.SingularSphereMiddle
