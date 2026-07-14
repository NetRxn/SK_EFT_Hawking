/-
# Phase 5q.H (W-A.1g suspension) — the cylinder's pair-suspension DIMENSION count, and `dimeq`

The last remaining `dimeq` residual of `PoincareLefschetzRelFundClassCylinderNumerics`: the Betti
equality `dim H^k(W) = dim H^{5-k}(W,∂W)` for the reflexive cylinder `W = M × [0,1]` over a **closed
4-manifold** `M`. This module discharges it via the **pair-suspension dimension count**
`dim H_{n+1}(W,∂W) = dim H_n(M)`.

## The route chosen — DUALIZE at the finrank level, count on the homology side

The consumers (`dimeq14`/`dimeq23`) need only `finrank` EQUALITIES, and over the field `ℤ/2` the
Kronecker pairings are perfect (`kroneckerHEquiv`/`relKroneckerHEquiv`, finite-dim-free), so
`finrank H^k = finrank H_k` for both the absolute and relative groups. That collapses the whole
question to the HOMOLOGY side, where the pair-LES is already fully exact in-tree
(`SingularPairLES`), the contractible-factor collapse `H_*(W) ≅ H_*(M)` is landed
(`…Numerics` §5), and the boundary split `H_*(∂W) ≅ H_*(M)²` is landed (`…Numerics` §7). This is
strictly cheaper than a fresh chain-level cohomology pair-LES: it reuses the exact homology LES and
the §5/§7 cylinder infrastructure verbatim, adding only the geometric surjectivity of the boundary
inclusion and a rank count.

## What this module banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the inclusion bridge.** `homIncl_eq_map`: the pair-LES chain-level `homIncl` IS
  `Homology.map` of the subspace inclusion (`mapChain_subInclCM`). Lets functoriality touch `homIncl`.
* **§2 — boundary-inclusion surjectivity.** `homIncl_boundary_surjective`: `i_* : H_k(∂W) → H_k(W)`
  is surjective in every positive degree — the geometric heart. One slice `M × {⊥} ↪ W` is a
  homology iso (`prodFst`/`ptPieceToM` bijective), and it factors through `∂W`, so `i_*` is onto.
* **§3 — the LES rank count** (general): `finrank_relHom_of_homIncl_surj`. When `i_*` is onto in
  degrees `n` and `n+1`, the connecting map is injective with image `ker i_*`, so
  `finrank H_{n+1}(X,S) = finrank H_n(S) − finrank H_n(X)`. Reusable project-wide.
* **§4 — the suspension count.** `cylinder_relHom_finrank`: `finrank H_{n+1}(W,∂W) = finrank H_n(M)`
  (`= 2·b_n − b_n`, boundary split minus collapse).
* **§5 — `dimeq`.** `finrank_cohomology_eq_homology`/`finrank_relCohomology_eq_relHomology` (Kronecker
  finrank transports); `cylinder_dimeq23_holds` (UNCONDITIONAL — both sides `b_2`); and
  `cylinder_dimeq14_of_basePD` (reduced to `M`'s own Poincaré duality `b_1(M) = b_3(M)`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
import SKEFTHawking.SingularCohomologyPairRestrict
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularRelativeKroneckerEquiv

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularRelativeKroneckerEquiv
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension

noncomputable section

/-! ## §1. The pair-LES inclusion `i_*` is `Homology.map` of the subspace inclusion -/

/-- **The pair-LES `homIncl` is `Homology.map (subInclCM)`**: the chain-level inclusion `chainIncl`
underlying `homIncl` is exactly the pushforward `mapChain (subInclCM)` (`mapChain_subInclCM`), so the
two induced homology maps agree. Lets homology functoriality (`Homology.map_comp`) reach `homIncl`. -/
theorem homIncl_eq_map {X : TopCat} (S : Set ↑X) (n : ℕ) :
    homIncl S n = Homology.map (subInclCM S) n := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show homIncl S n (Homology.mk (sub S) n z) = Homology.map (subInclCM S) n (Homology.mk (sub S) n z)
  rw [homIncl_mk, Homology.map_mk]
  refine congrArg (Homology.mk X n) (Subtype.ext ?_)
  rw [cyclesMap_coe, mapChain_subInclCM]

/-! ## §2. The boundary inclusion `i_* : H_k(∂W) → H_k(W)` is surjective in positive degree -/

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **The boundary inclusion is a homology surjection in every positive degree.** For the cylinder
`W = M × [0,1]`, the inclusion `∂W ↪ W` induces a SURJECTION `H_{k+1}(∂W) → H_{k+1}(W)`. Reason: the
bottom slice `M × {⊥} ↪ W` induces a homology ISO (its post-composition with `prodFst` is the slice
homeomorphism `ptPieceToM`, and both `prodFst` and `ptPieceToM` are homology bijections), and that
slice inclusion FACTORS through `∂W`; a surjective composite forces the second factor `i_*` onto. -/
theorem homIncl_boundary_surjective (k : ℕ) :
    Function.Surjective
      (homIncl (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) (k + 1)) := by
  set S : Set ↑(TopCat.of (cylW M)) := (cylModel 2).boundary (cylW M) with hS
  set ιU : C(↑(sub (ptPiece M ⊥)), ↑(sub S)) := subInclCM (ptPiece M ⊥) with hιU
  set ιS : C(↑(sub S), ↑(TopCat.of (cylW M))) := subInclCM S with hιS
  have hcomp : (prodFst (TopCat.of M) (TopCat.of unitInterval)).comp (ιS.comp ιU)
      = ptPieceToM (M := M) ⊥ := by
    apply ContinuousMap.ext; intro x; rfl
  have hbij_prodFst : Function.Bijective
      (Homology.map (prodFst (TopCat.of M) (TopCat.of unitInterval)) (k + 1)) :=
    prodFst_homology_bijective (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one k
  have hbij_ptM : Function.Bijective (Homology.map (ptPieceToM (M := M) ⊥) (k + 1)) :=
    ptPieceToM_homology_bijective ⊥ (by simp) (k + 1)
  have hbij_comp : Function.Bijective (Homology.map (ιS.comp ιU) (k + 1)) := by
    have hmapcomp :
        (Homology.map (prodFst (TopCat.of M) (TopCat.of unitInterval)) (k + 1)).comp
          (Homology.map (ιS.comp ιU) (k + 1))
        = Homology.map (ptPieceToM (M := M) ⊥) (k + 1) := by
      rw [← Homology.map_comp, hcomp]
    have hcompbij : Function.Bijective
        (⇑(Homology.map (prodFst (TopCat.of M) (TopCat.of unitInterval)) (k + 1))
          ∘ ⇑(Homology.map (ιS.comp ιU) (k + 1))) := by
      rw [← LinearMap.coe_comp, hmapcomp]; exact hbij_ptM
    exact (hbij_prodFst.of_comp_iff' _).mp hcompbij
  have hdecomp : Homology.map (ιS.comp ιU) (k + 1)
      = (homIncl S (k + 1)).comp (Homology.map ιU (k + 1)) := by
    rw [Homology.map_comp, homIncl_eq_map]
  have hsurj_comp : Function.Surjective (Homology.map (ιS.comp ιU) (k + 1)) := hbij_comp.surjective
  rw [hdecomp, LinearMap.coe_comp] at hsurj_comp
  exact hsurj_comp.of_comp

/-! ## §3. The pair-LES rank count (general): `dim H_{n+1}(X,S) = dim H_n(S) − dim H_n(X)` when `i_*`
is onto in degrees `n` and `n+1` -/

/-- **The pair-LES rank count.** When the inclusion `i_* : H_k(S) → H_k(X)` is SURJECTIVE in both
degrees `n` and `n+1`, the connecting map `δ : H_{n+1}(X,S) → H_n(S)` is injective with image exactly
`ker i_*` (from the two exactness statements + `j_* = 0`), so `dim H_{n+1}(X,S) = dim(ker i_*) =
dim H_n(S) − dim H_n(X)` by rank–nullity. Reusable project-wide (the numerical core of a suspension
isomorphism). -/
theorem finrank_relHom_of_homIncl_surj {X : TopCat} (S : Set ↑X) (n : ℕ)
    (hfin : FiniteDimensional (ZMod 2) (Homology (sub S) n))
    (hn : Function.Surjective (homIncl S n))
    (hn1 : Function.Surjective (homIncl S (n + 1))) :
    Module.finrank (ZMod 2) (RelativeHomology S (n + 1))
      = Module.finrank (ZMod 2) (Homology (sub S) n) - Module.finrank (ZMod 2) (Homology X n) := by
  haveI := hfin
  have hproj0 : homProj S (n + 1) = 0 := by
    rw [← LinearMap.ker_eq_top, (exact_homIncl_homProj S (n + 1)).linearMap_ker_eq]
    exact LinearMap.range_eq_top.mpr hn1
  have hinj : Function.Injective (connecting S n) := by
    rw [← LinearMap.ker_eq_bot, (exact_homProj_connecting S n).linearMap_ker_eq, hproj0,
      LinearMap.range_zero]
  have hrange : LinearMap.range (connecting S n) = LinearMap.ker (homIncl S n) :=
    ((exact_connecting_homIncl S n).linearMap_ker_eq).symm
  have hD : Module.finrank (ZMod 2) (RelativeHomology S (n + 1))
      = Module.finrank (ZMod 2) (LinearMap.ker (homIncl S n)) := by
    rw [(LinearEquiv.ofInjective (connecting S n) hinj).finrank_eq, hrange]
  have hF := LinearMap.finrank_range_add_finrank_ker (homIncl S n)
  have hG : Module.finrank (ZMod 2) (LinearMap.range (homIncl S n))
      = Module.finrank (ZMod 2) (Homology X n) := by
    rw [LinearMap.range_eq_top.mpr hn, finrank_top]
  rw [hD]; omega

/-! ## §4. The cylinder pair-suspension DIMENSION count `dim H_{n+1}(W,∂W) = dim H_n(M)` -/

omit [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] in
/-- **The cylinder's absolute homology finrank collapses to `M`** (positive degree):
`dim H_{m+1}(W) = dim H_{m+1}(M)` via the contractible-factor collapse (`…Numerics` §5). -/
theorem cylinder_homW_finrank (m : ℕ) :
    Module.finrank (ZMod 2) (Homology (TopCat.of (cylW M)) (m + 1))
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) (m + 1)) :=
  (prodContractibleHomologyEquiv (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
    slice_iccContraction_zero slice_iccContraction_one m).finrank_eq

/-- **The pair-suspension dimension count for the cylinder.** For `W = M × [0,1]` over a closed
4-manifold `M`, `dim H_{m+2}(W,∂W) = dim H_{m+1}(M)` (positive degree). The pair-LES rank count (§3,
via the boundary-inclusion surjectivity §2) gives `dim H_{m+2}(W,∂W) = dim H_{m+1}(∂W) − dim
H_{m+1}(W)`; the boundary split (`…Numerics` §7) makes `dim H_{m+1}(∂W) = 2·dim H_{m+1}(M)` and the
contractible-factor collapse (`…Numerics` §5) makes `dim H_{m+1}(W) = dim H_{m+1}(M)`, so the count
is `2·b − b = b`. -/
theorem cylinder_relHom_finrank (m : ℕ)
    [FiniteDimensional (ZMod 2) (Homology (TopCat.of M) (m + 1))] :
    Module.finrank (ZMod 2)
        (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) (m + 1 + 1))
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) (m + 1)) := by
  haveI hbd : FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) (m + 1)) :=
    boundary_homology_findim (m + 1) inferInstance
  rw [finrank_relHom_of_homIncl_surj (X := TopCat.of (cylW M))
    ((cylModel 2).boundary (cylW M)) (m + 1) hbd
    (homIncl_boundary_surjective m) (homIncl_boundary_surjective (m + 1))]
  have hsplit : Module.finrank (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) (m + 1))
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) (m + 1))
        + Module.finrank (ZMod 2) (Homology (TopCat.of M) (m + 1)) := by
    rw [(boundaryHomologyEquiv (m + 1)).finrank_eq, Module.finrank_prod]
  rw [hsplit, cylinder_homW_finrank m]; omega

/-! ## §5. Kronecker finrank transports and the `dimeq` reductions -/

/-- **Absolute Kronecker finrank transport** (mod-2 field UC): `dim Hᵏ(X) = dim Hₖ(X)` (`k = N+1`) —
the perfect pairing `kroneckerHEquiv` identifies `Hᵏ(X)` with the dual of `Hₖ(X)`, and the dual has
equal finrank (`Subspace.dual_finrank_eq`, unconditional over a field: both sides `0` in the
infinite-dimensional case). -/
theorem finrank_cohomology_eq_homology {X : TopCat} (N : ℕ) :
    Module.finrank (ZMod 2) (Cohomology X (N + 1))
      = Module.finrank (ZMod 2) (Homology X (N + 1)) := by
  rw [(kroneckerHEquiv (X := X) N).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **Relative Kronecker finrank transport**: `dim Hᵏ(X,S) = dim Hₖ(X,S)` (`k = N+1`)
(`relKroneckerHEquiv`). -/
theorem finrank_relCohomology_eq_relHomology {X : TopCat} (S : Set ↑X) (N : ℕ) :
    Module.finrank (ZMod 2) (RelativeCohomology S (N + 1))
      = Module.finrank (ZMod 2) (RelativeHomology S (N + 1)) := by
  rw [(relKroneckerHEquiv S N).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **The `(2,3)` Lefschetz Betti equality `dim H²(W) = dim H³(W,∂W)` holds UNCONDITIONALLY** (given
`b_2(M) < ∞`): both sides equal `b_2(M)`. Kronecker-transport each cohomology group to its homology
group, collapse `H_2(W) ≅ H_2(M)`, and use the pair-suspension count `dim H_3(W,∂W) = dim H_2(M)` —
the middle Betti number is its own suspension partner, so no Poincaré-duality input is needed. This
DISCHARGES the `dimeq23` residual of `PinPlusCylinderWAdmPinned`. -/
theorem cylinder_dimeq23_holds
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2)) :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
  haveI := hM2
  calc Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2)
      = Module.finrank (ZMod 2) (Homology (TopCat.of (cylW M)) 2) :=
        finrank_cohomology_eq_homology 1
    _ = Module.finrank (ZMod 2) (Homology (TopCat.of M) 2) := cylinder_homW_finrank 1
    _ = Module.finrank (ZMod 2)
          (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
        (cylinder_relHom_finrank 1).symm
    _ = Module.finrank (ZMod 2)
          (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
        (finrank_relCohomology_eq_relHomology (X := TopCat.of (cylW M))
          ((cylModel 2).boundary (cylW M)) 2).symm

/-- **The `(1,4)` Lefschetz Betti equality `dim H¹(W) = dim H⁴(W,∂W)` REDUCES to `M`'s own Poincaré
duality `b_1(M) = b_3(M)`** (given `b_3(M) < ∞`): the LHS is `b_1(M)` (Kronecker + collapse), the RHS
is `b_3(M)` (Kronecker + the pair-suspension count `dim H_4(W,∂W) = dim H_3(M)`). On a closed
4-manifold `M` the residual `basePD` is exactly `M`'s degree-1↔3 Poincaré duality — the honest close.
This DISCHARGES the `dimeq14` residual of `PinPlusCylinderWAdmPinned` given that named `M`-side input. -/
theorem cylinder_dimeq14_of_basePD
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (basePD : Module.finrank (ZMod 2) (Homology (TopCat.of M) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3)) :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
  haveI := hM3
  calc Module.finrank (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1)
      = Module.finrank (ZMod 2) (Homology (TopCat.of (cylW M)) 1) :=
        finrank_cohomology_eq_homology 0
    _ = Module.finrank (ZMod 2) (Homology (TopCat.of M) 1) := cylinder_homW_finrank 0
    _ = Module.finrank (ZMod 2) (Homology (TopCat.of M) 3) := basePD
    _ = Module.finrank (ZMod 2)
          (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
        (cylinder_relHom_finrank 2).symm
    _ = Module.finrank (ZMod 2)
          (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
        (finrank_relCohomology_eq_relHomology (X := TopCat.of (cylW M))
          ((cylModel 2).boundary (cylW M)) 3).symm

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
