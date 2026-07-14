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
* **§6 — `findimRelHom` via the homology pair-LES sandwich.** `cylinder_findimRelHom14/23`:
  `H_{n+1}(W,∂W) < ∞` from `H_{n+1}(W) < ∞` (→ `M` via §5) and the boundary homology `H_n(∂W) < ∞`
  (exactness at the middle of `H_{n+1}(W) → H_{n+1}(W,∂W) → H_n(∂W)`,
  `SingularPairLES.exact_homProj_connecting` + §4).
* **§7 — the boundary homology split `H_n(∂W) ≅ H_n(M)²`.** `∂W = M × {⊥,⊤}` splits into two clopen
  slices (`isClopen_ptPiece_bot`), each homeomorphic to `M` (`ptPieceToM`/`mToPtPiece`);
  `SingularDisjointUnionHn.splitHnEquiv` + functoriality give `boundaryHomologyEquiv` and
  `boundary_homology_findim` — the former ⊔-additivity residual, DISCHARGED.
* **§8 — `findimRelHom` FULLY reduced to `M`.** `cylinder_findimRelHom14/23_of_base`:
  `H_4(W,∂W) < ∞` from `b_4(M), b_3(M) < ∞`; `H_3(W,∂W) < ∞` from `b_3(M), b_2(M) < ∞` (§6
  composed with §5 + §7). **Net: `findimRel` ⟹ `M`'s homology Betti data alone.**

## Named residuals (precisely staged, none faked)

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
import SKEFTHawking.SingularDisjointUnionHn

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularDisjointUnionHn

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
homology `H_*(∂W) < ∞` (itself `≅ H_*(M)²` — discharged in §7; the fully-reduced `_of_base` forms
land in §8). -/

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

end CylinderRelHom

/-! ## §7. The boundary homology `H_*(∂W)` reduced to `M`'s own homology (the ⊔-additivity brick)

The last named residual of this file's docstring: `H_*(∂W) < ∞` from `M`'s own homology finiteness.
`∂W = M × {⊥,⊤}` (`cyl_boundary_eq`) splits as the union of its two slices `M × {⊥}`, `M × {⊤}`; as
subsets of the SUBSPACE `sub ∂W` (the nested-subtype presentation, `ptPiece`) they form a clopen
partition (`isClopen_ptPiece_bot`), so the all-degree ⊔-additivity `SingularDisjointUnionHn.
splitHnEquiv` gives `H_n(∂W) ≅ H_n(ptPiece ⊥) × H_n(ptPiece ⊤)`. Each slice is homeomorphic to `M`
itself (`(m,pt) ↦ m`), so functoriality (`Homology.map_bijective_of_comp_id_all`, the pipeline's
homeomorphism-transport idiom) identifies each summand with `H_n(M)`. Net: `H_n(∂W) ≅ H_n(M) ×
H_n(M)`, discharging the boundary input to `cylinder_findimRelHom14/23_of_base` purely from `M`'s
own Betti data. -/

section BoundaryHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **The `pt`-slice** `M × {pt} ⊆ W` for `pt : unitInterval`. -/
def ptSlice (M : Type) [TopologicalSpace M] (pt : unitInterval) : Set (cylW M) :=
  Set.univ ×ˢ ({pt} : Set unitInterval)

/-- **The cylinder boundary splits as the union of its two slices.** -/
theorem boundary_eq_union_ptSlice :
    (cylModel 2).boundary (cylW M) = ptSlice M ⊥ ∪ ptSlice M ⊤ := by
  rw [cyl_boundary_eq, ptSlice, ptSlice, ← Set.prod_union, Set.insert_eq]

/-- **The `pt`-piece of `∂W`**, as a subset of the nested subtype `↥∂W` (`sub ∂W`'s own points). -/
def ptPiece (M : Type) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (pt : unitInterval) :
    Set ↑(sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) :=
  {x | x.1 ∈ ptSlice M pt}

/-- **The forward slice map** `↥(ptPiece pt) → M`, `(m,pt) ↦ m`. -/
def ptPieceToM (pt : unitInterval) : C(↑(sub (ptPiece M pt)), ↑(TopCat.of M)) where
  toFun x := x.1.1.1
  continuous_toFun := continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)

/-- The point `(m,pt) ∈ ∂W`, as an element of `↥∂W` (given `pt ∈ {⊥,⊤}`). -/
def mToBdryPt (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) (m : M) :
    ↑(sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) :=
  ⟨(m, pt), by rw [cyl_boundary_eq]; exact ⟨Set.mem_univ _, hpt⟩⟩

theorem mToBdryPt_mem_ptPiece (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) (m : M) :
    mToBdryPt pt hpt m ∈ ptPiece M pt :=
  ⟨Set.mem_univ _, rfl⟩

theorem continuous_mToBdryPt (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) :
    Continuous (mToBdryPt (M := M) pt hpt) :=
  Continuous.subtype_mk (continuous_id.prodMk continuous_const) _

/-- **The backward slice map** `M → ↥(ptPiece pt)`, `m ↦ (m,pt)`, given `pt ∈ {⊥,⊤}` (so `(m,pt) ∈
∂W`). -/
def mToPtPiece (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) :
    C(↑(TopCat.of M), ↑(sub (ptPiece M pt))) where
  toFun m := ⟨mToBdryPt pt hpt m, mToBdryPt_mem_ptPiece pt hpt m⟩
  continuous_toFun := Continuous.subtype_mk (continuous_mToBdryPt pt hpt) _

theorem mToPtPiece_comp_ptPieceToM (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) :
    (mToPtPiece (M := M) pt hpt).comp (ptPieceToM pt) = ContinuousMap.id ↑(sub (ptPiece M pt)) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  have hx : x.1.1.2 = pt := x.2.2
  show (x.1.1.1, pt) = x.1.1
  exact Prod.ext rfl hx.symm

theorem ptPieceToM_comp_mToPtPiece (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval)) :
    (ptPieceToM (M := M) pt).comp (mToPtPiece pt hpt) = ContinuousMap.id ↑(TopCat.of M) := rfl

/-- **The slice homology bijection** `H_n(ptPiece pt) → H_n(M)` (a homeomorphism transported through
functoriality, the pipeline's `map_bijective_of_comp_id_all` idiom). -/
theorem ptPieceToM_homology_bijective (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval))
    (n : ℕ) : Function.Bijective (Homology.map (ptPieceToM (M := M) pt) n) :=
  Homology.map_bijective_of_comp_id_all (ptPieceToM pt) (mToPtPiece pt hpt)
    (mToPtPiece_comp_ptPieceToM pt hpt) (ptPieceToM_comp_mToPtPiece pt hpt) n

/-- **The slice homology equiv** `H_n(ptPiece pt) ≃ₗ H_n(M)`. -/
noncomputable def ptPieceHomologyEquiv (pt : unitInterval) (hpt : pt ∈ ({⊥, ⊤} : Set unitInterval))
    (n : ℕ) : Homology (sub (ptPiece M pt)) n ≃ₗ[ZMod 2] Homology (TopCat.of M) n :=
  LinearEquiv.ofBijective (Homology.map (ptPieceToM pt) n) (ptPieceToM_homology_bijective pt hpt n)

/-- Both slices are closed subsets of `↥∂W` (preimages of the closed `M × {pt}` under the continuous
subspace inclusion `↥∂W ↪ W`). -/
theorem isClosed_ptPiece (pt : unitInterval) : IsClosed (ptPiece M pt) := by
  have hSlice : IsClosed (ptSlice M pt) := by
    have heq : ptSlice M pt = (Prod.snd : cylW M → unitInterval) ⁻¹' {pt} := by
      ext p; simp [ptSlice, Set.mem_prod]
    rw [heq]
    exact isClosed_singleton.preimage continuous_snd
  exact hSlice.preimage continuous_subtype_val

/-- **Membership in `∂W`, split across the two slices.** A fresh-variable restatement of
`boundary_eq_union_ptSlice` (avoids rewriting inside a subtype-dependent hypothesis). -/
theorem mem_boundary_iff (p : cylW M) :
    p ∈ (cylModel 2).boundary (cylW M) ↔ p ∈ ptSlice M ⊥ ∨ p ∈ ptSlice M ⊤ := by
  rw [boundary_eq_union_ptSlice, Set.mem_union]

/-- **The two pieces are complementary**: `(ptPiece ⊥)ᶜ = ptPiece ⊤`. -/
theorem ptPiece_bot_compl : (ptPiece M ⊥)ᶜ = ptPiece M ⊤ := by
  ext x
  simp only [ptPiece, Set.mem_compl_iff, Set.mem_setOf_eq, ptSlice, Set.mem_prod,
    Set.mem_singleton_iff, Set.mem_univ, true_and]
  have hx := (mem_boundary_iff (x.1 : cylW M)).mp x.2
  simp only [ptSlice, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, true_and] at hx
  rcases hx with h | h
  · simp [h, bot_ne_top]
  · simp [h]

/-- **`ptPiece ⊥` is clopen** in `sub ∂W`: its complement is `ptPiece ⊤` (`ptPiece_bot_compl`), and
both pieces are closed (`isClosed_ptPiece`) — so `ptPiece ⊥` is also open. -/
theorem isClopen_ptPiece_bot : IsClopen (ptPiece (M := M) ⊥) := by
  refine ⟨isClosed_ptPiece ⊥, ?_⟩
  rw [← compl_compl (ptPiece M ⊥)]
  refine isOpen_compl_iff.mpr ?_
  rw [ptPiece_bot_compl]
  exact isClosed_ptPiece ⊤

/-- **The boundary's homology, split**: `H_n(∂W) ≅ H_n(M) × H_n(M)` (the ⊔-additivity brick). -/
noncomputable def boundaryHomologyEquiv (n : ℕ) :
    Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) n ≃ₗ[ZMod 2]
      Homology (TopCat.of M) n × Homology (TopCat.of M) n :=
  (splitHnEquiv (isClopen_ptPiece_bot (M := M)) n).symm.trans
    (LinearEquiv.prodCongr (ptPieceHomologyEquiv ⊥ (by simp) n)
      (ptPiece_bot_compl (M := M) ▸ ptPieceHomologyEquiv ⊤ (by simp) n))

/-- **`H_*(∂W) < ∞` from `M`'s own homology finiteness** — discharges the last named residual of
this file's docstring purely from `M`'s side. -/
theorem boundary_homology_findim (n : ℕ)
    (hM : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) n)) :
    FiniteDimensional (ZMod 2)
      (Homology (sub (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M))) n) :=
  haveI := hM
  (boundaryHomologyEquiv n).symm.finiteDimensional

end BoundaryHomology

/-! ## §8. `findimRelHom` FULLY reduced to `M`'s own Betti data

§6's pair-LES sandwich composed with §5's homology collapse (the `H_{n+1}(W)` end) and §7's
boundary split (the `H_n(∂W)` end): the cylinder's relative-homology finite-dimensionality
numerics from `M`'s own homology Betti data alone — no `W`-side or boundary-side input remains. -/

section CylinderRelHomOfBase

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-- **`findimRelHom` `(1,4)` leg FULLY reduced to `M`**: `H_4(W,∂W) < ∞` from `b_4(M), b_3(M) < ∞`
(homology collapse `H_4(W) ≅ H_4(M)` for the left end, boundary split `H_3(∂W) ≅ H_3(M)²` for the
right end of the pair-LES sandwich). -/
theorem cylinder_findimRelHom14_of_base
    (hM4 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 4))
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4) :=
  cylinder_findimRelHom14 (cylinder_findimHomW_of_base 3 hM4) (boundary_homology_findim 3 hM3)

/-- **`findimRelHom` `(2,3)` leg FULLY reduced to `M`**: `H_3(W,∂W) < ∞` from
`b_3(M), b_2(M) < ∞`. -/
theorem cylinder_findimRelHom23_of_base
    (hM3 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 3))
    (hM2 : FiniteDimensional (ZMod 2) (Homology (TopCat.of M) 2)) :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3) :=
  cylinder_findimRelHom23 (cylinder_findimHomW_of_base 2 hM3) (boundary_homology_findim 2 hM2)

end CylinderRelHomOfBase

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
