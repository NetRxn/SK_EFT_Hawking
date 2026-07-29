/-
# Phase 5q.H (E1 integral topology) — the Δ/Σ cap-naturality squares of the integral PD 5-lemma

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityMVSquare`. The two "easy" vertical squares of the
integral Poincaré-duality `5`-lemma ladder — `D_W` commutes with the compactly-supported-cohomology MV
diagonal/sum `cscMvDiagInt`/`cscMvSumInt` (extension maps) and the homology MV diagonal/sum
`subHomDiagInt`/`subHomSumInt` (the subspace-inclusion maps `homOfSubsetInt`). Both follow **directly** from
`SingularOpenDualityNatInt.openDuality_cscOpenMonotoneInt` (`D_{W'} ∘ cscOpenMonotoneInt = homOfSubsetInt ∘
D_W`), since `cscMvDiagInt`/`cscMvSumInt` and `subHomDiagInt`/`subHomSumInt` are built from
`cscOpenMonotoneInt` and `homOfSubsetInt` respectively.

The remaining (hard) vertical is the **connecting** square `D ∘ cscMvConnectingInt = mvDeltaInt ∘ D` (a
separate chain-level brick). Together with the integral cscMv LES and the homology MV LES these feed the
`5`-lemma giving `D_{U∪V}` iso — the local→global inductive step of the integral PD cover-induction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityNatInt
import SKEFTHawking.SingularCSCMayerVietorisInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCMayerVietorisInt
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityNatInt

namespace SKEFTHawking.SingularOpenDualityMVSquareInt

variable {X : TopCat} [T2Space ↑X]

/-- **The integral homology MV diagonal** `Hₙ(sub(U∩V);ℤ) → Hₙ(sub U;ℤ) ⊕ Hₙ(sub V;ℤ)`, the pair of
subspace-inclusion maps (`homOfSubsetInt`) — the bottom-row `Δ` of the integral PD `5`-lemma ladder. -/
noncomputable def subHomDiagInt (U V : Set ↑X) (n : ℕ) :
    Homology (sub (U ∩ V)) n →ₗ[ℤ] Homology (sub U) n × Homology (sub V) n :=
  (homOfSubsetInt Set.inter_subset_left n).prod (homOfSubsetInt Set.inter_subset_right n)

/-- **The integral homology MV sum** `Hₙ(sub U;ℤ) ⊕ Hₙ(sub V;ℤ) → Hₙ(sub(U∪V);ℤ)`, the difference of the
subspace-inclusion maps — the bottom-row `Σ` of the integral PD `5`-lemma ladder. -/
noncomputable def subHomSumInt (U V : Set ↑X) (n : ℕ) :
    Homology (sub U) n × Homology (sub V) n →ₗ[ℤ] Homology (sub (U ∪ V)) n :=
  (homOfSubsetInt Set.subset_union_left n).comp (LinearMap.fst _ _ _)
    - (homOfSubsetInt Set.subset_union_right n).comp (LinearMap.snd _ _ _)

/-- **The `Δ` cap-naturality square** (integral): `subHomDiagInt ∘ D_{U∩V} = (D_U ⊕ D_V) ∘ cscMvDiagInt`,
by `openDuality_cscOpenMonotoneInt` applied to the two `cscOpenMonotoneInt` components. -/
theorem subHomDiagInt_openDuality {k m : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (α : CompactlySupportedCohomologyOpenInt (U ∩ V) k) :
    subHomDiagInt U V (m + 1) (openDuality (hU.inter hV) z₀ hz₀ α)
      = (openDuality hU z₀ hz₀ (cscOpenMonotoneInt Set.inter_subset_left k α),
          openDuality hV z₀ hz₀ (cscOpenMonotoneInt Set.inter_subset_right k α)) := by
  rw [subHomDiagInt, LinearMap.prod_apply]
  simp only [Function.prod_def]
  rw [
    ← openDuality_cscOpenMonotoneInt (hU.inter hV) hU Set.inter_subset_left z₀ hz₀,
    ← openDuality_cscOpenMonotoneInt (hU.inter hV) hV Set.inter_subset_right z₀ hz₀]

/-- **The `Σ` cap-naturality square** (integral): `D_{U∪V} ∘ cscMvSumInt = subHomSumInt ∘ (D_U ⊕ D_V)`,
by `openDuality_cscOpenMonotoneInt` applied to the two `cscOpenMonotoneInt` components (difference). -/
theorem subHomSumInt_openDuality {k m : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (αU : CompactlySupportedCohomologyOpenInt U k) (αV : CompactlySupportedCohomologyOpenInt V k) :
    openDuality (hU.union hV) z₀ hz₀ (cscMvSumInt U V k (αU, αV))
      = subHomSumInt U V (m + 1) (openDuality hU z₀ hz₀ αU, openDuality hV z₀ hz₀ αV) := by
  rw [cscMvSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_sub,
    openDuality_cscOpenMonotoneInt hU (hU.union hV) Set.subset_union_left z₀ hz₀,
    openDuality_cscOpenMonotoneInt hV (hU.union hV) Set.subset_union_right z₀ hz₀, subHomSumInt,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]

end SKEFTHawking.SingularOpenDualityMVSquareInt
