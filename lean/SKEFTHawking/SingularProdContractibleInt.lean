/-
# Phase 5q.H (N5 witness tower) — the S²×S² product-homology arc OPENER:
# the contractible-factor collapse `Hₙ₊₁(Y × C; ℤ) ≅ Hₙ₊₁(Y; ℤ)`

The first slice of the product-homology machinery the `SphereProdHData` freeze
(`SphereWitnessTowerInt` §4) waits on: for ANY space `Y` and a factor `C` carrying a contraction
(`H(·,0) = id`, `H(·,1) = const c₀`), the first-factor projection induces an isomorphism on
integral homology in every positive degree — a product with a contractible factor collapses onto
the other factor. No Künneth machinery is needed for this slice: the projection/section pair is a
homotopy equivalence, and the in-tree integral homotopy invariance
(`Homology.mapInt_bijective_of_homotopyEquiv`, built on the integral prism operator) does the rest.

* §0 — homeomorphism transports: `homeoHomologyEquivInt` (a homeomorphism induces a homology iso
  in every degree — the `seamHomologyEquivInt` pattern packaged once, reusable) and
  `homeoContraction` (a contraction transports backwards across a homeomorphism, with its two
  slice lemmas). These feed the punctured-sphere contraction (stereographic transport of the
  straight-line contraction of ℝⁿ) in `SphereProdHOneInt`.
* §1 — the product data: projection `prodFst`, section `prodSect c₀` (a strict retraction:
  `prodFst ∘ prodSect = id`), the constant homotopy `constHomotopy` witnessing the strict half,
  and the product homotopy `prodHomotopy H = ((y,c),t) ↦ (y, H(c, 1−t))` interpolating
  `prodSect ∘ prodFst ≃ id` from a contraction `H` of the factor (time-REVERSED so `slice 0 =
  prodSect ∘ prodFst` and `slice 1 = id` — the exact binder shape
  `Homology.mapInt_bijective_of_homotopyEquiv` consumes).
* §2 — the collapse: `prodFst_bijectiveInt` and the packaged iso
  `prodContractibleEquivInt : Hₙ₊₁(Y × C; ℤ) ≃ₗ[ℤ] Hₙ₊₁(Y; ℤ)`.
* §3 — the subtype seam: `prodSetHomeo : sub (univ ×ˢ U) ≃ₜ Y × sub U` (a product-shaped subset
  of a product space IS the product of the ambient factor with the factor subtype) + the composite
  `prodSetContractibleEquivInt : Hₙ₊₁(sub (univ ×ˢ U); ℤ) ≃ₗ[ℤ] Hₙ₊₁(Y; ℤ)` — the exact shape the
  Mayer–Vietoris legs of a product-space polar cover consume (`A = univ ×ˢ (S²∖{N})` etc.).

Every continuous-map-level construction (§0's homeo/contraction transports, §1's product data and
homotopies, §3's seam homeo) is coefficient-agnostic — the future mod-2 mirror of this module only
re-instantiates the homology layer (`Homology.map` for `Homology.mapInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularSphereHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)

namespace SKEFTHawking.SingularProdContractibleInt

/-! ## §0. Homeomorphism transports -/

/-- **A homeomorphism induces an integral homology isomorphism in every degree** — the
`seamHomologyEquivInt` construction pattern (functoriality + `mapInt_bijective_of_comp_id_all`)
packaged once for reuse. -/
noncomputable def homeoHomologyEquivInt {X Y : TopCat} (φ : ↑X ≃ₜ ↑Y) (n : ℕ) :
    Homology X n ≃ₗ[ℤ] Homology Y n :=
  LinearEquiv.ofBijective (Homology.mapInt ⟨φ, φ.continuous⟩ n)
    (Homology.mapInt_bijective_of_comp_id_all ⟨φ, φ.continuous⟩ ⟨φ.symm, φ.symm.continuous⟩
      (ContinuousMap.ext fun x => φ.symm_apply_apply x)
      (ContinuousMap.ext fun y => φ.apply_symm_apply y) n)

@[simp] theorem homeoHomologyEquivInt_apply {X Y : TopCat} (φ : ↑X ≃ₜ ↑Y) (n : ℕ)
    (x : Homology X n) :
    homeoHomologyEquivInt φ n x = Homology.mapInt ⟨φ, φ.continuous⟩ n x := rfl

/-- **A contraction transports backwards across a homeomorphism**: if `Z` contracts via `H`, then
`X ≃ₜ Z` contracts via `(x, t) ↦ φ⁻¹ (H (φ x, t))`. Coefficient-agnostic (pure topology). -/
noncomputable def homeoContraction {X Z : TopCat} (φ : ↑X ≃ₜ ↑Z)
    (H : C(↑Z × unitInterval, ↑Z)) : C(↑X × unitInterval, ↑X) :=
  ⟨fun p => φ.symm (H (φ p.1, p.2)),
    φ.symm.continuous.comp (H.continuous.comp
      ((φ.continuous.comp continuous_fst).prodMk continuous_snd))⟩

/-- If `H`'s `t = 0` slice is the identity, so is the transported contraction's. -/
theorem slice_homeoContraction_zero {X Z : TopCat} (φ : ↑X ≃ₜ ↑Z)
    (H : C(↑Z × unitInterval, ↑Z)) (h0 : slice H 0 = ContinuousMap.id ↑Z) :
    slice (homeoContraction φ H) 0 = ContinuousMap.id ↑X := by
  refine ContinuousMap.ext fun x => ?_
  show φ.symm (slice H 0 (φ x)) = x
  rw [h0]
  exact φ.symm_apply_apply x

/-- If `H`'s `t = 1` slice is the constant map at `b`, the transported contraction's `t = 1` slice
is the constant map at `φ⁻¹ b`. -/
theorem slice_homeoContraction_one {X Z : TopCat} (φ : ↑X ≃ₜ ↑Z)
    (H : C(↑Z × unitInterval, ↑Z)) (b : ↑Z) (h1 : slice H 1 = ContinuousMap.const ↑Z b) :
    slice (homeoContraction φ H) 1 = ContinuousMap.const ↑X (φ.symm b) := by
  refine ContinuousMap.ext fun x => ?_
  show φ.symm (slice H 1 (φ x)) = φ.symm b
  rw [h1]
  rfl

/-! ## §1. The product data: projection, section, and the interpolating homotopies -/

/-- `Y × C` as a topological space object (the product topology). -/
abbrev ProdSp (Y C : TopCat) : TopCat := TopCat.of (↑Y × ↑C)

/-- The first-factor projection `Y × C → Y`. -/
def prodFst (Y C : TopCat) : C(↑(ProdSp Y C), ↑Y) := ⟨Prod.fst, continuous_fst⟩

/-- The section `y ↦ (y, c₀)` of the projection at a chosen basepoint of the factor. -/
def prodSect (Y C : TopCat) (c₀ : ↑C) : C(↑Y, ↑(ProdSp Y C)) :=
  ⟨fun y => (y, c₀), (continuous_id.prodMk continuous_const)⟩

/-- The section is a strict right inverse of the projection: `prodFst ∘ prodSect = id`. -/
theorem prodFst_comp_prodSect (Y C : TopCat) (c₀ : ↑C) :
    (prodFst Y C).comp (prodSect Y C c₀) = ContinuousMap.id ↑Y :=
  ContinuousMap.ext fun _ => rfl

/-- The constant (stationary) homotopy on `Y`: every slice is the identity. Witnesses the strict
half `prodFst ∘ prodSect = id` in the homotopy-equivalence binder shape. -/
def constHomotopy (Y : TopCat) : C(↑Y × unitInterval, ↑Y) := ⟨Prod.fst, continuous_fst⟩

theorem slice_constHomotopy (Y : TopCat) (r : unitInterval) :
    slice (constHomotopy Y) r = ContinuousMap.id ↑Y :=
  ContinuousMap.ext fun _ => rfl

/-- **The product homotopy** `((y, c), t) ↦ (y, H(c, 1 − t))` interpolating `prodSect ∘ prodFst ≃
id` from a contraction `H` of the factor — time-REVERSED (`1 − t` via `unitInterval.symm`) so that
`slice 0 = prodSect ∘ prodFst` and `slice 1 = id`, the exact binder shape
`Homology.mapInt_bijective_of_homotopyEquiv` consumes. -/
noncomputable def prodHomotopy (Y C : TopCat) (H : C(↑C × unitInterval, ↑C)) :
    C(↑(ProdSp Y C) × unitInterval, ↑(ProdSp Y C)) :=
  ⟨fun p => (p.1.1, H (p.1.2, unitInterval.symm p.2)),
    ((continuous_fst.comp continuous_fst).prodMk (H.continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk
        (unitInterval.continuous_symm.comp continuous_snd))))⟩

/-- The product homotopy's `t = 0` slice is `prodSect ∘ prodFst` (the factor sits at the
contraction's endpoint `H(·, 1) = c₀`). -/
theorem slice_prodHomotopy_zero (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) :
    slice (prodHomotopy Y C H) 0 = (prodSect Y C c₀).comp (prodFst Y C) := by
  refine ContinuousMap.ext fun p => ?_
  show (p.1, H (p.2, unitInterval.symm 0)) = (p.1, c₀)
  rw [unitInterval.symm_zero]
  exact congrArg (Prod.mk p.1) (ContinuousMap.congr_fun h1 p.2)

/-- The product homotopy's `t = 1` slice is the identity (the factor sits at the contraction's
start `H(·, 0) = id`). -/
theorem slice_prodHomotopy_one (Y C : TopCat) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) :
    slice (prodHomotopy Y C H) 1 = ContinuousMap.id ↑(ProdSp Y C) := by
  refine ContinuousMap.ext fun p => ?_
  show (p.1, H (p.2, unitInterval.symm 1)) = p
  rw [unitInterval.symm_one]
  exact (congrArg (Prod.mk p.1) (ContinuousMap.congr_fun h0 p.2)).trans rfl

/-! ## §2. The collapse: `Hₙ₊₁(Y × C; ℤ) ≅ Hₙ₊₁(Y; ℤ)` for a contractible factor -/

/-- **The projection is a homology isomorphism (bijective) in every positive degree** when the
factor carries a contraction: `prodFst`/`prodSect` are homotopy inverse (`prodHomotopy` one way,
strictly the other), so integral homotopy invariance applies. -/
theorem prodFst_bijectiveInt (Y C : TopCat) (c₀ : ↑C) (H : C(↑C × unitInterval, ↑C))
    (h0 : slice H 0 = ContinuousMap.id ↑C) (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Function.Bijective (Homology.mapInt (prodFst Y C) (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (prodFst Y C) (prodSect Y C c₀)
    (prodHomotopy Y C H) (slice_prodHomotopy_zero Y C c₀ H h1) (slice_prodHomotopy_one Y C H h0)
    (constHomotopy Y) ((slice_constHomotopy Y 0).trans (prodFst_comp_prodSect Y C c₀).symm)
    (slice_constHomotopy Y 1) n

/-- **The contractible-factor collapse** `Hₙ₊₁(Y × C; ℤ) ≃ₗ[ℤ] Hₙ₊₁(Y; ℤ)`, induced by the
first-factor projection. The product-homology arc's first reusable primitive. -/
noncomputable def prodContractibleEquivInt (Y C : TopCat) (c₀ : ↑C)
    (H : C(↑C × unitInterval, ↑C)) (h0 : slice H 0 = ContinuousMap.id ↑C)
    (h1 : slice H 1 = ContinuousMap.const ↑C c₀) (n : ℕ) :
    Homology (ProdSp Y C) (n + 1) ≃ₗ[ℤ] Homology Y (n + 1) :=
  LinearEquiv.ofBijective (Homology.mapInt (prodFst Y C) (n + 1))
    (prodFst_bijectiveInt Y C c₀ H h0 h1 n)

/-! ## §3. The subtype seam: `sub (univ ×ˢ U) ≃ₜ Y × sub U` and the composite collapse -/

/-- **The product-set seam homeomorphism** `sub (univ ×ˢ U) ≃ₜ Y × sub U`: a product-shaped
subset of a product space, with full first factor, IS the product of the ambient first factor with
the second-factor subtype. Underlying map: reassociation (identity on points). Coefficient-agnostic
(pure topology); mirror of the `seamHomeo` pattern. -/
def prodSetHomeo (Y C : TopCat) (U : Set ↑C) :
    ↥(sub (X := ProdSp Y C) ((Set.univ : Set ↑Y) ×ˢ U)) ≃ₜ ↑(ProdSp Y (sub U)) where
  toFun p := (p.1.1, ⟨p.1.2, p.2.2⟩)
  invFun q := ⟨(q.1, q.2.1), ⟨Set.mem_univ _, q.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The subtype-seamed contractible-factor collapse**
`Hₙ₊₁(sub (univ ×ˢ U); ℤ) ≃ₗ[ℤ] Hₙ₊₁(Y; ℤ)`, for a factor subset `U` whose subtype carries a
contraction — the exact shape the Mayer–Vietoris legs of a product-space polar cover consume. -/
noncomputable def prodSetContractibleEquivInt (Y C : TopCat) (U : Set ↑C) (c₀ : ↑(sub U))
    (H : C(↑(sub U) × unitInterval, ↑(sub U)))
    (h0 : slice H 0 = ContinuousMap.id ↑(sub U))
    (h1 : slice H 1 = ContinuousMap.const ↑(sub U) c₀) (n : ℕ) :
    Homology (sub (X := ProdSp Y C) ((Set.univ : Set ↑Y) ×ˢ U)) (n + 1) ≃ₗ[ℤ] Homology Y (n + 1) :=
  (homeoHomologyEquivInt (prodSetHomeo Y C U) (n + 1)).trans
    (prodContractibleEquivInt Y (sub U) c₀ H h0 h1 n)

end SKEFTHawking.SingularProdContractibleInt
