import Mathlib
import SKEFTHawking.SingularLocalDuality
import SKEFTHawking.SingularRelativeUC
import SKEFTHawking.SingularPointComplement
import SKEFTHawking.SingularH0PathConnected

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4f-b3) — the local Poincaré-duality map is injective

The base case of the Poincaré-duality induction: at a point `x` of a `T1` charted manifold there is a
local fundamental cycle `z` (an absolute representative of the generator of `Hₙ(M|x)`) for which the
degree-0 duality map `D_x = relativeDuality0 (M∖x) (m+1) z` is **injective**. Post-composing with the
augmentation `augH` recovers the relative Kronecker pairing against the local generator
`g = (manifoldLocalIsoPC x).symm 1`; since `g` spans the one-dimensional `Hₙ(M|x)`, that pairing is
injective (the relative universal coefficients `relCohomology_eq_zero_of_relKroneckerH`, PD-4d), so `D_x`
is injective. The whole assembly is routed through the named set `pointComplement x` so the cross-context
`{y ≠ x}` coercion heartbeat wall never forms (see `SingularPointComplement`).

`D_x` is a full isomorphism once `H₀(M) ≅ ℤ/2` (connected `M`, `SingularH0PathConnected`) supplies the
surjective half — used in the MV/compactness induction (PD-5/PD-6).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeDuality0
open SKEFTHawking.SingularLocalDuality SKEFTHawking.SingularRelativeUC
open SKEFTHawking.SingularPointComplement SKEFTHawking.SingularH0PathConnected

namespace SKEFTHawking.SingularLocalDualityInjective

/-- **The local Poincaré-duality map is injective.** There is a local fundamental cycle `z` at `x` for
which `D_x = relativeDuality0 (pointComplement x) (m+1) z` is injective. -/
theorem exists_localDuality_injective {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    ∃ (z : SingularChain (TopCat.of M) (m + 2))
      (hz : chainBoundary (TopCat.of M) (m + 1) z ∈ subspaceChains (pointComplement (m := m) x) (m + 1)),
      Function.Injective (relativeDuality0 (pointComplement (m := m) x) (m + 1) z hz) := by
  obtain ⟨z, hz, hgen⟩ := exists_relCycle_chain_rep (k := m + 1) (pointComplement (m := m) x)
    ((manifoldLocalIsoPC x).symm 1)
  refine ⟨z, hz, fun u v huv => ?_⟩
  -- `augH (D_x w) = ⟨w, g⟩` for `g = (manifoldLocalIsoPC x).symm 1` (descended bridge + `[z] = g`).
  have key : ∀ w, augH (TopCat.of M) (relativeDuality0 (pointComplement (m := m) x) (m + 1) z hz w)
      = relKroneckerH (pointComplement (m := m) x) w ((manifoldLocalIsoPC x).symm 1) := by
    intro w
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [show (Submodule.Quotient.mk a : RelativeCohomology (pointComplement (m := m) x) (m + 1 + 1))
        = RelativeCohomology.mk (pointComplement (m := m) x) (m + 1 + 1) a from rfl,
      augH_relativeDuality0_eq_relKroneckerH, hgen]
  -- `D_x u = D_x v ⟹ ⟨u, g⟩ = ⟨v, g⟩`.
  have huvg : relKroneckerH (pointComplement (m := m) x) u ((manifoldLocalIsoPC x).symm 1)
      = relKroneckerH (pointComplement (m := m) x) v ((manifoldLocalIsoPC x).symm 1) := by
    rw [← key, ← key, huv]
  -- `⟨u - v, g⟩ = 0`, and `g` spans `Hₙ(M|x)`, so `⟨u - v, ·⟩ = 0` everywhere ⟹ `u - v = 0` (PD-4d).
  refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (pointComplement (m := m) x) (u - v)
    (fun β => ?_))
  have hspan : (manifoldLocalIsoPC x β) • (manifoldLocalIsoPC x).symm 1 = β := by
    rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  have hg0 : relKroneckerH (pointComplement (m := m) x) (u - v) ((manifoldLocalIsoPC x).symm 1) = 0 := by
    rw [map_sub, LinearMap.sub_apply, huvg, sub_self]
  rw [← hspan, map_smul, hg0, smul_zero]

/-- **The local Poincaré-duality map is an isomorphism** (for connected `M`, i.e. `M` path-connected):
there is a local fundamental cycle `z` for which `D_x = relativeDuality0 (pointComplement x) (m+1) z` is
**bijective**. The injective half is `exists_localDuality_injective`'s argument; surjectivity adds the
augmentation iso `H₀(M) ≅ ℤ/2` (`SingularH0PathConnected.augH_injective`) plus surjectivity of the
pairing `⟨·, g⟩` (the local generator `g ≠ 0`, so `relHomology_eq_zero_of_relKroneckerH` forces some `w₀`
with `⟨w₀, g⟩ = 1`). The base case of the Poincaré-duality induction in its `5`-lemma-ready iso form. -/
theorem exists_localDuality_iso {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] [PathConnectedSpace ↑(TopCat.of M)] (x : M) :
    ∃ (z : SingularChain (TopCat.of M) (m + 2))
      (hz : chainBoundary (TopCat.of M) (m + 1) z ∈ subspaceChains (pointComplement (m := m) x) (m + 1)),
      Function.Bijective (relativeDuality0 (pointComplement (m := m) x) (m + 1) z hz) := by
  obtain ⟨z, hz, hgen⟩ := exists_relCycle_chain_rep (k := m + 1) (pointComplement (m := m) x)
    ((manifoldLocalIsoPC x).symm 1)
  have key : ∀ w, augH (TopCat.of M) (relativeDuality0 (pointComplement (m := m) x) (m + 1) z hz w)
      = relKroneckerH (pointComplement (m := m) x) w ((manifoldLocalIsoPC x).symm 1) := by
    intro w
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [show (Submodule.Quotient.mk a : RelativeCohomology (pointComplement (m := m) x) (m + 1 + 1))
        = RelativeCohomology.mk (pointComplement (m := m) x) (m + 1 + 1) a from rfl,
      augH_relativeDuality0_eq_relKroneckerH, hgen]
  refine ⟨z, hz, ?_, ?_⟩
  · -- injective (as in `exists_localDuality_injective`)
    intro u v huv
    have huvg : relKroneckerH (pointComplement (m := m) x) u ((manifoldLocalIsoPC x).symm 1)
        = relKroneckerH (pointComplement (m := m) x) v ((manifoldLocalIsoPC x).symm 1) := by
      rw [← key, ← key, huv]
    refine sub_eq_zero.mp (relCohomology_eq_zero_of_relKroneckerH (pointComplement (m := m) x) (u - v)
      (fun β => ?_))
    have hspan : (manifoldLocalIsoPC x β) • (manifoldLocalIsoPC x).symm 1 = β := by
      rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
    have hg0 : relKroneckerH (pointComplement (m := m) x) (u - v) ((manifoldLocalIsoPC x).symm 1) = 0 := by
      rw [map_sub, LinearMap.sub_apply, huvg, sub_self]
    rw [← hspan, map_smul, hg0, smul_zero]
  · -- surjective: `augH` injective (path-connected) + `⟨·, g⟩` surjective (`g ≠ 0`)
    intro h
    have hgne : (manifoldLocalIsoPC (m := m) x).symm 1 ≠ 0 :=
      fun hh => one_ne_zero ((LinearEquiv.map_eq_zero_iff _).1 hh)
    have hex : ∃ w₀, relKroneckerH (pointComplement (m := m) x) w₀ ((manifoldLocalIsoPC (m := m) x).symm 1) ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact hgne (relHomology_eq_zero_of_relKroneckerH (N := m + 1) (pointComplement (m := m) x)
        ((manifoldLocalIsoPC (m := m) x).symm 1) hall)
    obtain ⟨w₀, hw₀⟩ := hex
    have hz2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    have hw1 : relKroneckerH (pointComplement (m := m) x) w₀ ((manifoldLocalIsoPC (m := m) x).symm 1) = 1 :=
      hz2 _ hw₀
    refine ⟨(augH (TopCat.of M) h) • w₀, augH_injective ?_⟩
    rw [key, map_smul, LinearMap.smul_apply, hw1, smul_eq_mul, mul_one]

end SKEFTHawking.SingularLocalDualityInjective
