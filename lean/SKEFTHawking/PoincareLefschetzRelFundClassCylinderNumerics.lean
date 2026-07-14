/-
# Phase 5q.H (W-A.1g numerics) — the cylinder's PL duality-numerics, reduced to `M`'s own data

The four Poincaré–Lefschetz duality-numerics parameters of the concrete cylinder data
`cylinderP14`/`cylinderP23` (`PoincareLefschetzRelFundClassCylinderWu`) are `findimAbs`, `findimRel`,
`nondeg`, `dimeq`. For the reflexive cylinder `W = M × [0,1]` over a **closed 4-manifold** `M`
(`m' = 2`, so `dim W = 5`), each is a statement about the cohomology of `(W, ∂W)`; this module
reduces the ones the in-tree cohomology tooling honestly supports to statements about **`M`'s own
cohomology**, and names precisely the residual for the rest.

## What this module banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the explicit interval contraction.** `iccContraction`, the straight-line deformation
  `H(u,s) = (1−s)·u` of `[0,1]` onto its endpoint `⊥ = 0`, with `slice … 0 = id`, `slice … 1 = const ⊥`.
  This is the contraction the `SingularCohomologyHomotopy` contractible-factor collapse consumes for
  the cylinder's second factor `C = [0,1]`.
* **§2 — `findimAbs` FULLY reduced to `M`.** `cylinder_findimAbs_of_base`: `H^{k+1}(W)` is
  finite-dimensional as soon as `H^{k+1}(M)` is (the contractible-factor collapse
  `finiteDimensional_cohomology_prodContractible` applied to `W = M × [0,1]`). The two concrete
  specialisations `cylinder_findimAbs14`/`cylinder_findimAbs23` discharge exactly the `findimAbs`
  parameters of `cylinderP14`/`cylinderP23` from `FiniteDimensional (ZMod 2) (Cohomology M 1)` /
  `… 2` — a clean, closed 4-manifold's Betti-finiteness input. **This is the residual-shrinking win:
  the `W`-side `findimAbs` becomes an `M`-side hypothesis.**

## Named residuals (precisely staged, none faked)

The remaining three numerics are NOT reduced here (the tooling is not yet in-tree):

* `findimRel` (`H^{nk}(W,∂W)` finite-dim) needs the cohomology pair-LES sandwich
  `H^{nk-1}(∂W) → H^{nk}(W,∂W) → H^{nk}(W)` (`H^{nk}(W,∂W)` is then an extension of a subspace of the
  finite-dimensional `H^{nk}(W)` by a quotient of the finite-dimensional `H^{nk-1}(∂W) ≅ H^{nk-1}(M)²`,
  via `SingularCohomologyDisjointSum`) — the **cohomology pair-LES exactness** wall.
* `dimeq` (`dim H^k(W) = dim H^{nk}(W,∂W)`) reduces, GIVEN the pair-suspension iso
  `H^{nk}(W,∂W) ≅ H^{nk-1}(M)`, to `M`'s Poincaré-duality Betti equality `b_k(M) = b_{nk-1}(M)`
  (`b_1 = b_3` on a closed 4-manifold) — the **pair-suspension iso** wall on the relative side.
* `nondeg` (perfectness of the `μ`-pairing) reduces to `M`'s own Poincaré-duality pairing — the deep
  Poincaré–Lefschetz duality content, named not forced.

These three are carried as explicit parameters into the `CylinderWAdmPinned` residual-set package
(`PinPlusWAdmPinned`), keeping the whole W-admissibility residual-set machine-readable in one place.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
import SKEFTHawking.SingularCohomologyHomotopy
import SKEFTHawking.SingularRelativeKroneckerEquiv

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics

noncomputable section

/-! ## §1. The explicit straight-line contraction of the interval factor `[0,1]` onto `⊥ = 0` -/

/-- **The interval contraction** `H(u,s) = (1−s)·u` of `[0,1] = unitInterval` onto its endpoint
`⊥ = 0`: a straight-line deformation retract. `slice … 0 = id` (`s=0`: `1·u = u`), `slice … 1 =
const ⊥` (`s=1`: `0·u = 0`). The concrete contraction the contractible-factor cohomology collapse
consumes for the cylinder's second factor. -/
def iccContraction : C(↑(TopCat.of unitInterval) × unitInterval, ↑(TopCat.of unitInterval)) where
  toFun p := ⟨(1 - (p.2 : ℝ)) * (p.1 : ℝ),
    ⟨mul_nonneg (by have := p.2.2.2; linarith) p.1.2.1,
     by
      have hs := p.2.2
      have hu := p.1.2
      nlinarith [hs.1, hs.2, hu.1, hu.2]⟩⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
        (continuous_subtype_val.comp continuous_fst))) _

theorem slice_iccContraction_zero :
    slice iccContraction 0 = ContinuousMap.id ↑(TopCat.of unitInterval) := by
  refine ContinuousMap.ext fun u => Subtype.ext ?_
  show (1 - ((0 : unitInterval) : ℝ)) * (u : ℝ) = (u : ℝ)
  simp

theorem slice_iccContraction_one :
    slice iccContraction 1 = ContinuousMap.const ↑(TopCat.of unitInterval) (⊥ : unitInterval) := by
  refine ContinuousMap.ext fun u => Subtype.ext ?_
  show (1 - ((1 : unitInterval) : ℝ)) * (u : ℝ) = ((⊥ : unitInterval) : ℝ)
  simp

/-! ## §2. `findimAbs` for the cylinder, fully reduced to `M`'s absolute cohomology -/

variable {M : Type} [TopologicalSpace M]

/-- **The cylinder's absolute finite-dimensionality from `M`'s** (degree `≥ 1`): if `H^{k+1}(M)` is
finite-dimensional then so is `H^{k+1}(W)` for `W = M × [0,1]`, because the contractible interval
factor collapses (`finiteDimensional_cohomology_prodContractible` with `iccContraction`). This is the
`findimAbs` enabler for the cylinder, dimension-agnostic in the base degree. -/
theorem cylinder_findimAbs_of_base (k : ℕ)
    (hM : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) (k + 1))) :
    FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) (k + 1)) :=
  finiteDimensional_cohomology_prodContractible (TopCat.of M) (TopCat.of unitInterval) ⊥
    iccContraction slice_iccContraction_zero slice_iccContraction_one k hM

/-- **`findimAbs` for the cylinder `(1,4)` leg**, reduced to `b_1(M) < ∞`. -/
theorem cylinder_findimAbs14
    (hM : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 1)) :
    FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 1) :=
  cylinder_findimAbs_of_base 0 hM

/-- **`findimAbs` for the cylinder `(2,3)` leg**, reduced to `b_2(M) < ∞`. -/
theorem cylinder_findimAbs23
    (hM : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of M) 2)) :
    FiniteDimensional (ZMod 2) (Cohomology (TopCat.of (cylW M)) 2) :=
  cylinder_findimAbs_of_base 1 hM

end

/-! ## §3. `findimRel` reduced from relative cohomology to relative HOMOLOGY (field UC)

The relative Kronecker pairing over `ℤ/2` is a *perfect* pairing with no finite-dimensionality
hypothesis (`SingularRelativeKroneckerEquiv.relKroneckerHEquiv` — the field universal-coefficient
equivalence `H^{n}(W,∂W) ≃ₗ (H_n(W,∂W))^*`). So relative-cohomology finite-dimensionality (the
`findimRel` numeric) reduces cleanly to relative-**homology** finite-dimensionality — the more
tractable side (the mod-2 homology pair-LES is fully exact in-tree, `SingularPairLES`, and the
homology ⊔-additivity `SingularDisjointUnionHn` gives `H_*(∂W)`). This reduction is dimension- and
pair-agnostic. -/

/-- **Relative-cohomology finite-dimensionality from relative-homology finite-dimensionality**
(mod-2 field universal coefficients): `H^{N+1}(X,S)` is finite-dimensional as soon as `H_{N+1}(X,S)`
is, because `relKroneckerHEquiv` identifies `H^{N+1}(X,S)` with the (finite-dimensional) dual of
`H_{N+1}(X,S)`. The general `findimRel`-shrinking lemma: relative cohomology → relative homology. -/
theorem finiteDimensional_relativeCohomology_of_relativeHomology {X : TopCat} {S : Set ↑X} (N : ℕ)
    (h : FiniteDimensional (ZMod 2) (RelativeHomology (X := X) S (N + 1))) :
    FiniteDimensional (ZMod 2) (RelativeCohomology (X := X) S (N + 1)) := by
  haveI := h
  exact (SingularRelativeKroneckerEquiv.relKroneckerHEquiv S N).symm.finiteDimensional

section CylinderRel

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **`findimRel` for the cylinder `(1,4)` leg**, reduced to `H_4(W,∂W) < ∞` (relative homology). -/
theorem cylinder_findimRel14
    (h : FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4)) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
  finiteDimensional_relativeCohomology_of_relativeHomology 3 h

/-- **`findimRel` for the cylinder `(2,3)` leg**, reduced to `H_3(W,∂W) < ∞` (relative homology). -/
theorem cylinder_findimRel23
    (h : FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3)) :
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
  finiteDimensional_relativeCohomology_of_relativeHomology 2 h

end CylinderRel

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
