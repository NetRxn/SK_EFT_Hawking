/-
# Phase 5q.H (W-A.1g numerics) — the cylinder's PL duality-numerics, reduced to `M`'s own data

The four Poincaré–Lefschetz duality-numerics parameters of the concrete cylinder data
`cylinderP14`/`cylinderP23` (`PoincareLefschetzRelFundClassCylinderWu`) are `findimAbs`, `findimRel`,
`nondeg`, `dimeq`. For the reflexive cylinder `W = M × [0,1]` over a **closed 4-manifold** `M`
(`m' = 2`, so `dim W = 5`), each is a statement about the (co)homology of `(W, ∂W)`; this module
reduces the finite-dimensionality numerics (`findimAbs`, `findimRel`) ALL THE WAY to `M`'s own Betti
data, and names precisely the residual for the two genuinely-deep ones.

## What this module banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the explicit interval contraction.** `iccContraction`, the straight-line deformation
  `H(u,s) = (1−s)·u` of `[0,1]` onto its endpoint `⊥ = 0`. The contraction the contractible-factor
  collapses (cohomology and homology) consume for the cylinder's second factor `C = [0,1]`.
* **§2 — `findimAbs` FULLY reduced to `M`.** `cylinder_findimAbs14`/`23`: `H^{k}(W)` finite-dim from
  `H^{k}(M)` finite-dim (`finiteDimensional_cohomology_prodContractible`).
* **§3 — `findimRel` reduced to relative HOMOLOGY.** `finiteDimensional_relativeCohomology_of_
  relativeHomology` (field UC via `relKroneckerHEquiv`): `H^{N+1}(X,S) < ∞ ⟸ H_{N+1}(X,S) < ∞`, the
  more tractable side. `cylinder_findimRel14`/`23` specialise it.
* **§4 — `finiteDimensional_of_exact`** (general): the middle of a 3-term exact sequence is
  finite-dim when both ends are (`Module.Finite.of_submodule_quotient`). Reusable project-wide.
* **§5 — the mod-2 HOMOLOGY contractible-factor collapse.** `cylinder_findimHomW_of_base`:
  `H_{k}(W) < ∞ ⟸ H_{k}(M) < ∞` (the homology mirror of §2's collapse).
* **§6 — `findimRelHom` via the homology pair-LES sandwich.** `cylinder_findimRelHom14/23_of_base`:
  `H_{n+1}(W,∂W) < ∞` from `b_{n+1}(M) < ∞` (via §5) and the boundary homology `H_n(∂W) < ∞`
  (exactness at the middle of `H_{n+1}(W) → H_{n+1}(W,∂W) → H_n(∂W)`,
  `SingularPairLES.exact_homProj_connecting` + §4). **Net: `findimRel` ⟹ `M`'s homology Betti data +
  the boundary homology `H_*(∂W)`.**

## Named residuals (precisely staged, none faked)

* `H_*(∂W) < ∞` (the last input to §6): `∂W ≅ M ⊔ M`, so `H_*(∂W) ≅ H_*(M)²` via
  `SingularDisjointUnionHn` (all-degree ⊔-additivity, homology side) + a slice homeomorphism
  `M × {pt} ≅ M` — the remaining ⊔-additivity brick, named not forced.
* `dimeq` (`dim H^k(W) = dim H^{nk}(W,∂W)`) reduces, GIVEN the pair-suspension iso
  `H^{nk}(W,∂W) ≅ H^{nk-1}(M)`, to `M`'s Poincaré-duality Betti equality `b_k(M) = b_{nk-1}(M)`
  (`b_1 = b_3` on a closed 4-manifold) — the **pair-suspension iso** wall on the relative side.
* `nondeg` (perfectness of the `μ`-pairing) reduces to `M`'s own Poincaré-duality pairing — the deep
  Poincaré–Lefschetz duality content, named not forced.

The remaining residuals are carried as explicit parameters into the `CylinderWAdmPinned` residual-set
package (`PinPlusCylinderWAdmPinned`), keeping the whole W-admissibility residual-set machine-readable
in one place.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
import SKEFTHawking.SingularCohomologyHomotopy
import SKEFTHawking.SingularRelativeKroneckerEquiv

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularPairLES

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

/-! ## §4. Finite-dimensionality of the middle of a 3-term exact sequence (general)

The general linear-algebra brick powering the homology pair-LES sandwich: the middle `B` of an
exact `A →f B →g C` is finite-dimensional as soon as `A` and `C` are (`ker g = range f` is a
quotient-image of `A`, and `B ⧸ ker g ≅ range g ⊆ C`, so `B` extends a finite-dim submodule by a
finite-dim quotient — `Module.Finite.of_submodule_quotient`). Reusable project-wide. -/

/-- **The middle of a 3-term exact sequence is finite-dimensional** when both ends are: for
`f : A →ₗ B`, `g : B →ₗ C` with `Function.Exact f g`, `A` and `C` finite-dimensional force `B`
finite-dimensional. -/
theorem finiteDimensional_of_exact {A B C : Type*}
    [AddCommGroup A] [Module (ZMod 2) A] [AddCommGroup B] [Module (ZMod 2) B]
    [AddCommGroup C] [Module (ZMod 2) C]
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) C]
    {f : A →ₗ[ZMod 2] B} {g : B →ₗ[ZMod 2] C} (hexact : Function.Exact f g) :
    FiniteDimensional (ZMod 2) B := by
  haveI hker : FiniteDimensional (ZMod 2) (LinearMap.ker g) := by
    rw [hexact.linearMap_ker_eq]
    exact (f.quotKerEquivRange).finiteDimensional
  haveI hquot : FiniteDimensional (ZMod 2) (B ⧸ LinearMap.ker g) :=
    (g.quotKerEquivRange).symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

/-! ## §5. The contractible-factor collapse on singular `ℤ/2` HOMOLOGY (the cylinder's `H_*(W)`)

The mod-2 homology mirror of `SingularProdContractibleInt.prodFst_bijectiveInt` (integral) and
`SingularCohomologyHomotopy.prodFst_cohomology_bijective` (cohomology), reusing their projection/
section/homotopy topology and `Homology.map_bijective_of_homotopyEquiv`. For `W = M × [0,1]` these
give `H_{k}(W) ≅ H_{k}(M)` and its `findim` transfer — the `H_*(W)` input to the homology pair-LES. -/

/-- **The first-factor projection is a homology isomorphism (bijective)** in every positive degree
when the factor `C` carries a contraction (`Homology.map (prodFst)`). -/
theorem prodFst_homology_bijective (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Function.Bijective (Homology.map (prodFst Y C) (n + 1)) :=
  Homology.map_bijective_of_homotopyEquiv (prodFst Y C) (prodSect Y C c₀)
    (prodHomotopy Y C H) (slice_prodHomotopy_zero Y C c₀ H h1) (slice_prodHomotopy_one Y C H h0)
    (constHomotopy Y) ((slice_constHomotopy Y 0).trans (prodFst_comp_prodSect Y C c₀).symm)
    (slice_constHomotopy Y 1) n

/-- **The contractible-factor homology collapse** `H_{n+1}(Y × C) ≃ₗ[ZMod 2] H_{n+1}(Y)`. -/
noncomputable def prodContractibleHomologyEquiv (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Homology (ProdSp Y C) (n + 1) ≃ₗ[ZMod 2] Homology Y (n + 1) :=
  LinearEquiv.ofBijective (Homology.map (prodFst Y C) (n + 1))
    (prodFst_homology_bijective Y C c₀ H h0 h1 n)

/-- **Finite-dimensionality of the cylinder's absolute homology from the base**: `findim H_{n+1}(M)`
gives `findim H_{n+1}(M × C)` for a contractible factor `C` — the `H_*(W)` enabler. -/
theorem finiteDimensional_homology_prodContractible (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ)
    (h : FiniteDimensional (ZMod 2) (Homology Y (n + 1))) :
    FiniteDimensional (ZMod 2) (Homology (ProdSp Y C) (n + 1)) :=
  haveI := h
  (prodContractibleHomologyEquiv Y C c₀ H h0 h1 n).symm.finiteDimensional

section CylinderHomW

variable {M : Type} [TopologicalSpace M]

/-- **The cylinder's absolute homology finite-dimensionality from `M`'s** (degree `≥ 1`):
`findim H_{k+1}(M)` gives `findim H_{k+1}(W)` for `W = M × [0,1]` (the interval factor collapses). -/
theorem cylinder_findimHomW_of_base (k : ℕ)
    (hM : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) (k + 1))) :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of (cylW M)) (k + 1)) :=
  finiteDimensional_homology_prodContractible (TopCat.of M) (TopCat.of unitInterval) ⊥
    iccContraction slice_iccContraction_zero slice_iccContraction_one k hM

end CylinderHomW

/-! ## §6. `findimRelHom` reduced via the homology pair-LES sandwich

The mod-2 homology pair-LES `H_{n+1}(W) →(j_*) H_{n+1}(W,∂W) →(∂) H_n(∂W)` is exact at the middle
(`SingularPairLES.exact_homProj_connecting`), so `finiteDimensional_of_exact` gives `H_{n+1}(W,∂W)`
finite-dimensional from `H_{n+1}(W)` (→ `M` via the homology collapse) and `H_n(∂W)`. This reduces
the cylinder's `findimRelHom` residual to `M`'s absolute homology `b_*(M) < ∞` plus the boundary
homology `H_*(∂W) < ∞` (itself `≅ H_*(M)²` via `∂W ≅ M ⊔ M`, `SingularDisjointUnionHn` — the
remaining ⊔-additivity brick, named). -/

section CylinderRelHom

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **`findimRelHom` for the `(1,4)` leg via the pair-LES sandwich**: `H_4(W,∂W) < ∞` from `H_4(W)`
and `H_3(∂W)` finite-dimensional (exactness at the middle of `H_4(W) → H_4(W,∂W) → H_3(∂W)`). -/
theorem cylinder_findimRelHom14
    (hW : FiniteDimensional (ZMod 2) (Homology (TopCat.of (cylW M)) 4))
    (hBd : FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) 3)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) := by
  haveI := hW; haveI := hBd
  exact finiteDimensional_of_exact
    (exact_homProj_connecting (X := TopCat.of (cylW M))
      (S := (cylModel 2).boundary (cylW M)) 3)

/-- **`findimRelHom` for the `(2,3)` leg via the pair-LES sandwich**: `H_3(W,∂W) < ∞` from `H_3(W)`
and `H_2(∂W)` finite-dimensional. -/
theorem cylinder_findimRelHom23
    (hW : FiniteDimensional (ZMod 2) (Homology (TopCat.of (cylW M)) 3))
    (hBd : FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) 2)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) := by
  haveI := hW; haveI := hBd
  exact finiteDimensional_of_exact
    (exact_homProj_connecting (X := TopCat.of (cylW M))
      (S := (cylModel 2).boundary (cylW M)) 2)

/-- **`findimRelHom` `(1,4)` leg fully reduced to `M`'s absolute homology + the boundary homology**:
`H_4(W,∂W) < ∞` from `b_4(M) < ∞` (via the homology collapse `H_4(W) ≅ H_4(M)`) and `H_3(∂W) < ∞`. -/
theorem cylinder_findimRelHom14_of_base
    (hM : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (hBd : FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) 3)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
  cylinder_findimRelHom14 (cylinder_findimHomW_of_base 3 hM) hBd

/-- **`findimRelHom` `(2,3)` leg fully reduced to `M`'s absolute homology + the boundary homology**:
`H_3(W,∂W) < ∞` from `b_3(M) < ∞` and `H_2(∂W) < ∞`. -/
theorem cylinder_findimRelHom23_of_base
    (hM : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hBd : FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) 2)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
  cylinder_findimRelHom23 (cylinder_findimHomW_of_base 2 hM) hBd

end CylinderRelHom

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
