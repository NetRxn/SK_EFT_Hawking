/-
# Phase 5q.H (W-A arm 4) — the MV overlap PAIR `dim H_{m'+2}(M×I, (M∖σ)×(I∖t))` (δ-closer flank #2)

Route-B δ-closer flank #2. The relative-MV LES around the punctured-product target
`T = H_{m'+3}(M×I, {x}ᶜ)` (`…PuncturedCover`/`…PuncturedMVBookkeeping`) has its connecting `δ` land in the
**overlap pair** `H_{m'+2}(M×I, (M∖σ)×(I∖t))` (`overlap x = puncU x ∩ puncV x`), where the prism class
must survive. This module computes that overlap pair's dimension by its OWN pair-LES — genuinely
`M`-local-homology data, NOT the plain ⊔-additive subspace bookkeeping of `…PuncturedOverlap` (the
inclusion `H_j(sub overlap) → H_j(M×I)` is the base-deletion `ι_* : H_j(M∖σ) → H_j(M)` doubled, which is
not top-surjective — `H_{m'+2}(M∖σ) = 0` open vs `ℤ/2` closed).

The honest output is the **exact-segment decomposition** the δ-closer plugs into, in terms of `M`-side
Betti data and the `ι_*`-kernel/image:

  `dim H_{k+2}(X, overlap) = (dim H_{k+2}(M) − dim range ι_{k+2}) + dim ker ι_{k+1}`,

where `ι_j = homIncl (overlap x) j : H_j(sub overlap) → H_j(M×I)` is the overlap-subspace inclusion,
`H_{k+2}(M×I) ≅ H_{k+2}(M)` (interval collapse), and `dim H_j(sub overlap) = 2·dim H_j(M∖σ)`
(`…PuncturedOverlap.finrank_overlapSubHom`). The δ-closer degree is `k = m'`.

The three pair-LES exact segments (`SingularPairLES.exact_homIncl_homProj`/`exact_homProj_connecting`/
`exact_connecting_homIncl`) feed the general rank engine `finrank_of_exact_segment`
(`…PuncturedMVBookkeeping`):

  `H_{k+2}(sub overlap) →[ι] H_{k+2}(X) →[homProj] H_{k+2}(X,overlap) →[δ] H_{k+1}(sub overlap) →[ι] H_{k+1}(X)`.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the pair exact-segment decomposition** `overlap_pair_finrank_decomp` (`= range homProj +
  range δ`), the `range homProj` sub-decomposition `overlap_pair_range_homProj` (`= dim H(X) − range ι`),
  and `overlap_pair_range_connecting` (`range δ = ker ι`).
* **§2 — the assembled finrank** `overlap_pair_finrank` and its `M`-side form `overlap_pair_finrank_base`
  (interval collapse `H_{k+2}(X) ≅ H_{k+2}(M)`), plus the `M∖σ`-Betti bound `overlap_pair_finrank_le`
  (`≤ dim H_{k+2}(M) + 2·dim H_{k+1}(M∖σ)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.SingularPairLES
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlap
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedMVBookkeeping

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlapPair

noncomputable section

variable {N : TopCat} (x : ↑(cyl N))

/-! ## §1. The pair-LES exact-segment decomposition of the overlap pair -/

/-- **The overlap-pair exact-segment decomposition** (`= range homProj + range δ`). Exactness of the
pair-LES at the pair `H_{k+2}(X, overlap)` (`exact_homProj_connecting`) plus the rank engine
`finrank_of_exact_segment`: `dim H_{k+2}(X, overlap) = dim range(homProj) + dim range(connecting)` —
the `homProj`-image (from `H_{k+2}(X)`) plus the `δ`-image (into `H_{k+1}(sub overlap)`). -/
theorem overlap_pair_finrank_decomp (k : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeHomology (overlap x) (k + 2))] :
    Module.finrank (ZMod 2) (RelativeHomology (overlap x) (k + 2))
      = Module.finrank (ZMod 2) (LinearMap.range (homProj (overlap x) (k + 2)))
        + Module.finrank (ZMod 2) (LinearMap.range (connecting (overlap x) (k + 1))) :=
  finrank_of_exact_segment (exact_homProj_connecting (overlap x) (k + 1))

/-- **The `range homProj` sub-decomposition** `= dim H_{k+2}(X) − dim range ι_{k+2}`. Exactness at
`H_{k+2}(X)` (`exact_homIncl_homProj`): `dim H_{k+2}(X) = dim range(homIncl) + dim range(homProj)`, so
the `homProj`-image is the cokernel of the overlap-subspace inclusion `ι_{k+2}`. -/
theorem overlap_pair_range_homProj (k : ℕ)
    [FiniteDimensional (ZMod 2) (Homology (cyl N) (k + 2))] :
    Module.finrank (ZMod 2) (LinearMap.range (homProj (overlap x) (k + 2)))
      = Module.finrank (ZMod 2) (Homology (cyl N) (k + 2))
        - Module.finrank (ZMod 2) (LinearMap.range (homIncl (overlap x) (k + 2))) := by
  have h := finrank_of_exact_segment (exact_homIncl_homProj (overlap x) (k + 2))
  omega

/-- **The `δ`-image is the `ι`-kernel** `dim range(connecting) = dim ker ι_{k+1}`. Exactness at
`H_{k+1}(sub overlap)` (`exact_connecting_homIncl`): `range(connecting) = ker(homIncl)`. -/
theorem overlap_pair_range_connecting (k : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.range (connecting (overlap x) (k + 1)))
      = Module.finrank (ZMod 2) (LinearMap.ker (homIncl (overlap x) (k + 1))) := by
  rw [(exact_connecting_homIncl (overlap x) (k + 1)).linearMap_ker_eq]

/-! ## §2. The assembled overlap-pair finrank and its `M`-side form -/

/-- **The overlap-pair finrank in terms of the `ι`-kernel/image**:
`dim H_{k+2}(X, overlap) = (dim H_{k+2}(X) − dim range ι_{k+2}) + dim ker ι_{k+1}`. The exact-segment
decomposition, `homProj`-image and `δ`-image resolved into the overlap-subspace inclusion data. -/
theorem overlap_pair_finrank (k : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeHomology (overlap x) (k + 2))]
    [FiniteDimensional (ZMod 2) (Homology (cyl N) (k + 2))] :
    Module.finrank (ZMod 2) (RelativeHomology (overlap x) (k + 2))
      = (Module.finrank (ZMod 2) (Homology (cyl N) (k + 2))
          - Module.finrank (ZMod 2) (LinearMap.range (homIncl (overlap x) (k + 2))))
        + Module.finrank (ZMod 2) (LinearMap.ker (homIncl (overlap x) (k + 1))) := by
  rw [overlap_pair_finrank_decomp x k, overlap_pair_range_homProj x k,
    overlap_pair_range_connecting x k]

/-- **The interval-factor collapse** `dim H_{k+2}(M×I) = dim H_{k+2}(M)` — the contractible interval
factor of `cyl N = M×I` (`prodContractibleHomologyEquiv`). Brings the `M`-side Betti number into the
overlap-pair count. -/
theorem finrank_homology_cyl_collapse (k : ℕ) :
    Module.finrank (ZMod 2) (Homology (cyl N) (k + 2))
      = Module.finrank (ZMod 2) (Homology N (k + 2)) :=
  (prodContractibleHomologyEquiv N (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one (k + 1)).finrank_eq

/-- **The overlap-pair finrank in terms of `M`-side Betti data**:
`dim H_{k+2}(M×I, (M∖σ)×(I∖t)) = (dim H_{k+2}(M) − dim range ι_{k+2}) + dim ker ι_{k+1}`, the
interval-collapsed form of `overlap_pair_finrank`. The δ-closer's exact structural input: the base
Betti number `dim H_{k+2}(M)` minus the top-degree `ι`-image, plus the below-degree `ι`-kernel. -/
theorem overlap_pair_finrank_base (k : ℕ)
    [FiniteDimensional (ZMod 2) (RelativeHomology (overlap x) (k + 2))]
    [FiniteDimensional (ZMod 2) (Homology (cyl N) (k + 2))] :
    Module.finrank (ZMod 2) (RelativeHomology (overlap x) (k + 2))
      = (Module.finrank (ZMod 2) (Homology N (k + 2))
          - Module.finrank (ZMod 2) (LinearMap.range (homIncl (overlap x) (k + 2))))
        + Module.finrank (ZMod 2) (LinearMap.ker (homIncl (overlap x) (k + 1))) := by
  rw [overlap_pair_finrank x k, finrank_homology_cyl_collapse (N := N) k]

/-- **The `M∖σ`-Betti bound on the overlap pair**:
`dim H_{k+2}(M×I, (M∖σ)×(I∖t)) ≤ dim H_{k+2}(M) + 2·dim H_{k+1}(M∖σ)`. Bounding the `ι`-kernel by the
whole below-degree overlap subspace `dim H_{k+1}(sub overlap) = 2·dim H_{k+1}(M∖σ)`
(`finrank_overlapSubHom`) and dropping the `− range ι` correction. The clean `M`-side ceiling for the
δ-closer's `range δ ⊆ H_{k+2}(X, overlap)`. -/
theorem overlap_pair_finrank_le (k : ℕ) (ht0 : (0 : ℝ) < (x.2 : ℝ)) (ht1 : (x.2 : ℝ) < 1)
    [FiniteDimensional (ZMod 2) (RelativeHomology (overlap x) (k + 2))]
    [FiniteDimensional (ZMod 2) (Homology (cyl N) (k + 2))]
    [FiniteDimensional (ZMod 2) (Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1))] :
    Module.finrank (ZMod 2) (RelativeHomology (overlap x) (k + 2))
      ≤ Module.finrank (ZMod 2) (Homology N (k + 2))
        + 2 * Module.finrank (ZMod 2) (Homology (TopCat.of ↑(sub ({x.1}ᶜ : Set ↑N))) (k + 1)) := by
  haveI := finiteDimensional_overlapSubHom x ht0 ht1 k
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (homIncl (overlap x) (k + 1)))
      ≤ Module.finrank (ZMod 2) (Homology (sub (overlap x)) (k + 1)) :=
    Submodule.finrank_le _
  rw [finrank_overlapSubHom x ht0 ht1 k] at hker
  rw [overlap_pair_finrank_base x k]
  omega

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedOverlapPair
