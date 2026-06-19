import Mathlib
import SKEFTHawking.SingularOpenDualityNat
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularSubsetHomology

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c-Δ/Σ) — the Δ/Σ cap-naturality squares of the PD 5-lemma

The two "easy" vertical squares of the Poincaré-duality `5`-lemma ladder — `D_W` commutes with the
compactly-supported-cohomology MV diagonal/sum `cscMvDiag`/`cscMvSum` (extension maps) and the homology MV
diagonal/sum `subHomDiag`/`subHomSum` (the subspace-inclusion maps `homOfSubset`). Both follow **directly**
from `SingularOpenDualityNat.openDuality_cscOpenMonotone` (PD6f-(a), `D_{W'} ∘ cscOpenMonotone = homOfSubset
∘ D_W`), since `cscMvDiag`/`cscMvSum` and `subHomDiag`/`subHomSum` are built from `cscOpenMonotone` and
`homOfSubset` respectively.

The remaining (hard) vertical is the **connecting** square `D ∘ cscMvConnecting = mvDelta ∘ D` (a separate
chain-level brick). Together with the cscMv LES (`SingularCSCMayerVietoris*Exact`) and the homology MV LES
(`SingularMayerVietorisLES`) these feed the `5`-lemma giving `D_{U∪V}` iso.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularCSCMayerVietoris
  SKEFTHawking.SingularCSCOpenMonotone
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityNat

namespace SKEFTHawking.SingularOpenDualityMVSquare

variable {X : TopCat} [T2Space ↑X]

/-- **The homology MV diagonal** `Hₙ(sub(U∩V)) → Hₙ(sub U) ⊕ Hₙ(sub V)`, the pair of subspace-inclusion
maps (`homOfSubset`) — the bottom-row `Δ` of the PD `5`-lemma ladder. -/
noncomputable def subHomDiag (U V : Set ↑X) (n : ℕ) :
    Homology (sub (U ∩ V)) n →ₗ[ZMod 2] Homology (sub U) n × Homology (sub V) n :=
  (homOfSubset Set.inter_subset_left n).prod (homOfSubset Set.inter_subset_right n)

/-- **The homology MV sum** `Hₙ(sub U) ⊕ Hₙ(sub V) → Hₙ(sub(U∪V))`, the difference (over `ℤ/2`) of the
subspace-inclusion maps — the bottom-row `Σ` of the PD `5`-lemma ladder. -/
noncomputable def subHomSum (U V : Set ↑X) (n : ℕ) :
    Homology (sub U) n × Homology (sub V) n →ₗ[ZMod 2] Homology (sub (U ∪ V)) n :=
  (homOfSubset Set.subset_union_left n).comp (LinearMap.fst _ _ _)
    - (homOfSubset Set.subset_union_right n).comp (LinearMap.snd _ _ _)

/-- **The `Δ` cap-naturality square**: `(D_U ⊕ D_V) ∘ cscMvDiag = subHomDiag ∘ D_{U∩V}`, by PD6f-(a)
applied to the two `cscOpenMonotone` components. -/
theorem subHomDiag_openDuality {k m : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen (U ∩ V) k) :
    subHomDiag U V (m + 1) (openDuality (hU.inter hV) z₀ hz₀ α)
      = (openDuality hU z₀ hz₀ (cscOpenMonotone Set.inter_subset_left k α),
          openDuality hV z₀ hz₀ (cscOpenMonotone Set.inter_subset_right k α)) := by
  rw [subHomDiag, LinearMap.prod_apply, Pi.prod,
    ← openDuality_cscOpenMonotone (hU.inter hV) hU Set.inter_subset_left z₀ hz₀,
    ← openDuality_cscOpenMonotone (hU.inter hV) hV Set.inter_subset_right z₀ hz₀]

/-- **The `Σ` cap-naturality square**: `D_{U∪V} ∘ cscMvSum = subHomSum ∘ (D_U ⊕ D_V)`, by PD6f-(a)
applied to the two `cscOpenMonotone` components (difference over `ℤ/2`). -/
theorem subHomSum_openDuality {k m : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (αU : CompactlySupportedCohomologyOpen U k) (αV : CompactlySupportedCohomologyOpen V k) :
    openDuality (hU.union hV) z₀ hz₀ (cscMvSum U V k (αU, αV))
      = subHomSum U V (m + 1) (openDuality hU z₀ hz₀ αU, openDuality hV z₀ hz₀ αV) := by
  rw [cscMvSum, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_sub,
    openDuality_cscOpenMonotone hU (hU.union hV) Set.subset_union_left z₀ hz₀,
    openDuality_cscOpenMonotone hV (hU.union hV) Set.subset_union_right z₀ hz₀, subHomSum,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply]

end SKEFTHawking.SingularOpenDualityMVSquare
