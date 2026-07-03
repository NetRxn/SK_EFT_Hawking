import Mathlib
import SKEFTHawking.SingularRelativeUC
import SKEFTHawking.SingularManifoldFundamentalClass
import SKEFTHawking.SingularCompactlySupportedOpen

/-!
# Phase 5q.F (w₂-foundation, G1 PD track A) — relative-cohomology top-degree vanishing

The cohomology half of the Hatcher-3.27 high-degree vanishing: relative COHOMOLOGY vanishes in every
degree where the corresponding relative HOMOLOGY vanishes. Over the field `ℤ/2` this is immediate from
relative universal coefficients (`SingularRelativeUC.relCohomology_eq_zero_of_relKroneckerH`): a
cohomology class pairing to `0` with every homology class is `0`, and when every homology class *is*
`0` the pairing is vacuously `0` (each `relKroneckerH ω` is linear, so it kills `0`).

Wired to the project's compactness-induction machinery in two forms:

* `relCohomology_eq_zero_of_vanishAbove` — `vanishAbove n K` (`Hᵢ(M|K) = 0` for `i > n`,
  `SingularManifoldFundamentalClass`) gives `Hⁱ(M|K) = 0` for `i > n` (the cohomology of the pair
  `RelativeCohomology Kᶜ i`), the top-degree-vanishing input of the Poincaré-duality induction.
* `cohomGW_eq_zero_of_vanishAbove` — the same vanishing re-expressed at a stage `K ∈ CompactsIn W` of
  the compactly-supported-cohomology directed system (`cohomGW W k K = Hᵏ(M|K)`), the per-stage form
  the `Hᵏ_c(W)` colimit-vanishing lemma consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularCohomologyColimit
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularRelCohomVanishAbove

variable {X : TopCat}

/-- **Relative-cohomology vanishing from relative-homology vanishing** (over the field `ℤ/2`): if
every relative homology class in degree `N+1` is `0`, then every relative cohomology class in degree
`N+1` is `0`. Universal coefficients (`relCohomology_eq_zero_of_relKroneckerH`): `ω` pairs to `0`
with every `β` — vacuously, since every `β = 0` and `relKroneckerH ω` is linear. -/
theorem relCohomology_eq_zero_of_relHomology_eq_zero (S : Set ↑X) {N : ℕ}
    (h : ∀ β : RelativeHomology S (N + 1), β = 0) (ω : RelativeCohomology S (N + 1)) : ω = 0 :=
  SingularRelativeUC.relCohomology_eq_zero_of_relKroneckerH S ω (fun β => by rw [h β, map_zero])

/-- **Top-degree cohomology vanishing from `vanishAbove`**: `vanishAbove n K` (the homology half,
`Hᵢ(M|K) = 0` for all `i > n`) gives the cohomology half `Hⁱ(M|K) = 0` for all `i > n` — every class
of `RelativeCohomology Kᶜ i` vanishes. The degree `i > n ≥ 0` is a successor, so relative universal
coefficients applies. -/
theorem relCohomology_eq_zero_of_vanishAbove {n : ℕ} {K : Set ↑X} (h : vanishAbove n K)
    {i : ℕ} (hi : n < i) (ω : RelativeCohomology Kᶜ i) : ω = 0 := by
  obtain ⟨N, rfl⟩ : ∃ N, i = N + 1 := ⟨i - 1, by omega⟩
  exact relCohomology_eq_zero_of_relHomology_eq_zero Kᶜ (fun β => h (N + 1) hi β) ω

/-- **Stage-wise vanishing of the `Hᵏ_c(W)` directed system from `vanishAbove`**: at a compact stage
`K ∈ CompactsIn W` with `vanishAbove n ↑K` and `k > n`, every element of the system object
`cohomGW W k K = Hᵏ(M|K)` is `0`. The per-stage input of the colimit top-degree vanishing
`Hᵏ_c(W) = 0` (`SingularCSCVanishAbove`). -/
theorem cohomGW_eq_zero_of_vanishAbove {n : ℕ} {W : Set ↑X} {k : ℕ} (hk : n < k)
    (K : CompactsIn W) (h : vanishAbove n (↑K.1 : Set ↑X)) (x : cohomGW W k K) : x = 0 :=
  relCohomology_eq_zero_of_vanishAbove h hk x

end SKEFTHawking.SingularRelCohomVanishAbove
