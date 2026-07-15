/-
# Phase 5q.H (W-A arm 4) — the OPEN-manifold top vanishing `H_{m'+2}(M∖σ) = 0`

Route-B δ-closer keystone. The overlap-pair anatomy
(`…PuncturedOverlapPair`/`…PuncturedOverlap`) leaves the punctured-product local homology's δ-content
resting on ONE global fact that the plain ⊔-additive subspace bookkeeping cannot supply — the top
homology of the punctured base VANISHES:

  `H_{m'+2}(M∖σ) = 0`   (M a closed connected charted `(m'+2)`-manifold, σ ∈ M).

This is the manifold analogue of "a non-compact connected `n`-manifold has no fundamental class", and
is exactly the deep input `…PuncturedOverlap`'s docstring names ("`ι_* : H(M∖σ) → H(M)` not onto in
top degree"). It is proved here from IN-TREE closed-manifold theory alone, via the pair-LES of
`({σ}ᶜ ⊆ M)` at degree `m'+2`:

  `H_{m'+3}(M, M∖σ) —[δ]→ H_{m'+2}(M∖σ) —[i_*]→ H_{m'+2}(M) —[j_*]→ H_{m'+2}(M, M∖σ)`,

where
* `j_* = homProj = restrictHomologyToPoint σ` is INJECTIVE (Hatcher 3.26 kernel-triviality,
  `restrictHomologyToPoint_injective`), so `im i_* = ker j_* = 0`, hence `i_* = 0` and
  `H_{m'+2}(M∖σ) = ker i_* = im δ`;
* `H_{m'+3}(M, M∖σ) = 0` above top (`manifoldLocalHom_above_eq_zero`), so `im δ = 0`.

Therefore `H_{m'+2}(M∖σ) = 0`.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the `homProj = restrictHomologyToPoint` bridge** `restrictHomologyToPoint_eq_homProj`
  (degree-general; re-proved locally to avoid the heavy `Int` orientation import).
* **§2 — `homProj` injectivity at a point** `homProj_localPoint_injective` (from
  `restrictHomologyToPoint_injective`).
* **§3 — the open-manifold top vanishing** `openManifold_top_homology_eq_zero`:
  `H_{m'+2}(M∖σ) = 0`, and its finrank corollary `finrank_openManifold_top_homology`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFundamentalClass
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.SingularPairLES
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedTopVanish

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish

noncomputable section

/-! ## §1. The `homProj = restrictHomologyToPoint` bridge -/

/-- **`homProj S ∘ relHomologyEmptyEquiv = relIncl (∅ ⊆ S)`** (degree-general): the pair-projection of
the empty-subspace class is the pair-inclusion `(X, ∅) → (X, S)`. Re-proved locally (matches
`SingularIntOrientationDataConstruct.homProj_relHomologyEmptyEquiv`, without the `Int` import). -/
theorem homProj_relHomologyEmptyEquiv {X : TopCat} (S : Set ↑X) (n : ℕ)
    (w : RelativeHomology (∅ : Set ↑X) n) :
    homProj S n (relHomologyEmptyEquiv (X := X) n w)
      = relIncl (Set.empty_subset S) n w := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [show (Submodule.Quotient.mk u : RelativeHomology (∅ : Set ↑X) n)
        = RelativeHomology.mk (∅ : Set ↑X) n u from rfl,
    relHomologyEmptyEquiv_mk, homProj_mk]
  simp only [relIncl]
  congr 1
  apply Subtype.ext
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (u : RelativeChain (∅ : Set ↑X) n)
  simp only [SKEFTHawking.SingularRelativeFunctoriality.relCyclesMap_coe,
    SKEFTHawking.SingularRelativeEmpty.cyclesEmptyEquiv_coe, ← hc,
    show (Submodule.Quotient.mk c : RelativeChain (∅ : Set ↑X) n)
      = RelativeChain.mk (∅ : Set ↑X) n c from rfl,
    SKEFTHawking.SingularRelativeEmpty.chainEmptyEquiv_mk,
    SKEFTHawking.SingularRelativeFunctoriality.relMapChain_mk,
    SKEFTHawking.SingularFunctoriality.mapChain_id]

/-- **`restrictHomologyToPoint x = homProj {x}ᶜ`** (degree-general): the local-restriction of an
absolute class is the pair-projection to `(X, {x}ᶜ)`. -/
theorem restrictHomologyToPoint_eq_homProj {X : TopCat} (x : ↑X) (n : ℕ) (α : Homology X n) :
    restrictHomologyToPoint (X := X) x n α = homProj ({x}ᶜ : Set ↑X) n α := by
  simp only [restrictHomologyToPoint, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← homProj_relHomologyEmptyEquiv, LinearEquiv.apply_symm_apply]

/-! ## §2. `homProj` injectivity at a point -/

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **`homProj {σ}ᶜ` is injective at top degree** (Hatcher 3.26 kernel-triviality): a class of
`H_{m'+2}(M)` whose pair-projection to `(M, M∖σ)` vanishes is `0`
(`restrictHomologyToPoint_injective`). -/
theorem homProj_localPoint_injective (σ : M) :
    Function.Injective (homProj (X := TopCat.of M) ({σ}ᶜ : Set ↑(TopCat.of M)) (m' + 2)) := by
  intro a b hab
  refine sub_eq_zero.mp (restrictHomologyToPoint_injective (x₀ := σ) ?_)
  rw [restrictHomologyToPoint_eq_homProj, map_sub, hab, sub_self]

/-! ## §3. The open-manifold top vanishing `H_{m'+2}(M∖σ) = 0` -/

/-- **The top homology of the punctured base vanishes**: `H_{m'+2}(M∖σ) = 0` for `M` a closed
connected charted `(m'+2)`-manifold. Pair-LES of `({σ}ᶜ ⊆ M)`: `j_* = homProj` injective forces
`i_* = 0`, so `H_{m'+2}(M∖σ) = ker i_* = im δ`; and `H_{m'+3}(M, M∖σ) = 0`
(`manifoldLocalHom_above_eq_zero`) makes `im δ = 0`. The deep δ-content input the punctured-product
overlap pair (`…PuncturedOverlap`/`…PuncturedOverlapPair`) rests on. -/
theorem openManifold_top_homology_eq_zero (σ : M)
    (w : Homology (sub ({σ}ᶜ : Set ↑(TopCat.of M))) (m' + 2)) : w = 0 := by
  haveI : T1Space M := inferInstance
  -- `i_* w = 0`: it projects to `0` (`homProj_homIncl`) and `homProj` is injective.
  have hincl0 : homIncl (X := TopCat.of M) ({σ}ᶜ : Set ↑(TopCat.of M)) (m' + 2) w = 0 :=
    homProj_localPoint_injective σ (by
      rw [homProj_homIncl, map_zero])
  -- `w ∈ ker i_* = im δ`.
  obtain ⟨y, hy⟩ := (exact_connecting_homIncl (X := TopCat.of M)
    ({σ}ᶜ : Set ↑(TopCat.of M)) (m' + 2) w).mp hincl0
  -- `y : H_{m'+3}(M, M∖σ) = 0` above top.
  have hy0 : y = 0 := manifoldLocalHom_above_eq_zero (M := M) σ y
  rw [← hy, hy0, map_zero]

/-- **`dim H_{m'+2}(M∖σ) = 0`** — the finrank form of the open-manifold top vanishing, the value the
overlap-pair δ-count (`…PuncturedOverlapPair.overlap_pair_finrank_le`) plugs in for the base
top-degree `M∖σ` Betti number. -/
theorem finrank_openManifold_top_homology (σ : M) :
    Module.finrank (ZMod 2) (Homology (sub ({σ}ᶜ : Set ↑(TopCat.of M))) (m' + 2)) = 0 := by
  have : Subsingleton (Homology (sub ({σ}ᶜ : Set ↑(TopCat.of M))) (m' + 2)) :=
    ⟨fun a b => by rw [openManifold_top_homology_eq_zero σ a,
      openManifold_top_homology_eq_zero σ b]⟩
  exact Module.finrank_zero_of_subsingleton

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderOpenTopVanish
