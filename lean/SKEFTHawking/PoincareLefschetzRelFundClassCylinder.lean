/-
# Phase 5q.H (W-A.1g) — the CONCRETE cylinder `[W,∂W]` datum via the explicit product collar

The lead's collar-fork ruling: **no general collar theorem** — the op-bordisms' `W`'s are *products*
`W = M × [0,1]` with **explicit** collars, so build the relative-fundamental-class datum for the
cylinder using the product structure directly. Here `M` is a **closed** (compact `T2` `Nonempty`)
manifold charted on `Eᵐ'⁺² = EuclideanSpace ℝ (Fin (m'+2))` (e.g. a closed 4-manifold at `m' = 2`);
`W = M × [0,1]` is charted on `(𝓡 (m'+2)).prod (𝓡∂ 1)` — a manifold-with-boundary of dimension
`m'+3`, whose relative fundamental class lives at top degree `m'+3 = (m'+1)+2`, i.e. the
`RelFundClassDatum` is at `m := m'+1`.

## What this module banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the concrete cylinder pair.** `cylW = M × [0,1]`, its boundary
  `∂W = M × {⊥,⊤}` (Mathlib `boundary_product`, since `𝓡 (m'+2)` is boundaryless), the **interior
  slab** `K = M × [¼,¾]` (an *interior compact* avoiding `∂W`), with the genuine geometric facts
  `interiorSlab_subset_compl_boundary` (`K ⊆ (∂W)ᶜ`) and `isCompact_interiorSlab`.
* **§2 — the datum reduced to a SINGLE existence obligation.** The interior-chart linear equiv
  `εcyl : Eᵐ'⁺² × E¹ ≃L Eᵐ'⁺³` (`EuclideanSpace.finAddEquivProd`) is supplied *concretely*, so the
  concrete cylinder datum `cylinderRelFundClassDatum` needs ONLY a `HasRelFundClass` existence
  witness — the `ε`-obligation of `relFundClassDatumOf` is discharged for the cylinder.
* **§3 — Wall 2 (`DeterminedByInteriorPoints`) for the cylinder.** Specialises the predecessor's
  `determinedByInteriorPoints_of_interiorInjective` to `K = interiorSlab`: the cylinder is
  determined by its interior points given (a) the closed-case `determinedByPoints` on the slab and
  (b) the **collar-injectivity** residual `Injective (relIncl (∂W ⊆ Kᶜ))` — exactly the piece the
  explicit product collar `M × ([0,¼) ∪ (¾,1])` discharges (`∂W` is a deformation retract of `Kᶜ`
  through the collar). The dimension-agnostic reduction; the residual is stated precisely.

The remaining *existence* obligation is the honest product route `[W,∂W] = [M] × [I,∂I]` at degree
`m'+3` from `M`'s in-tree mod-2 fundamental class (`SingularFundamentalClassExist.fundamentalClass`
at `m'`); the exact missing tool is a relative cross-product `Hₚ(M) ⊗ H₁(I,∂I) → Hₚ₊₁(M×I, M×∂I)`
(mod-2), and the collar-injectivity `hinj` needs a mod-2 pair homotopy-invariance + pair-LES
five-lemma (only the *integral* pair homotopy invariance is currently in-tree). Both are named below.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.PoincareLefschetzRelFundClassGeom
import SKEFTHawking.PoincareLefschetzRelFundClassBoundary

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzRelFundClassBoundary
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinder

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- The unit-interval fact needed for the `[0,1]` manifold-with-boundary structure. -/
instance : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- **The cylinder `W = M × [0,1]`** as a plain type (the underlying space of the product
manifold-with-boundary). -/
abbrev cylW (M : Type) [TopologicalSpace M] : Type := M × Set.Icc (0 : ℝ) 1

/-- **The cylinder model** `(𝓡 (m'+2)).prod (𝓡∂ 1)` — the base's boundaryless self-model crossed
with the half-space model of `[0,1]`. -/
abbrev cylModel (m' : ℕ) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin (m' + 2)) × EuclideanSpace ℝ (Fin 1))
      (ModelProd (EuclideanSpace ℝ (Fin (m' + 2))) (EuclideanHalfSpace 1)) :=
  (𝓡 (m' + 2)).prod (𝓡∂ 1)

/-! ## §1. The concrete cylinder pair: boundary, interior slab, and their geometry -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The cylinder boundary** `∂W = M × {⊥,⊤}` (Mathlib `boundary_product`; `𝓡 (m'+2)` is
boundaryless). This is the `S` of the relative pair `(W, ∂W)`. -/
theorem cyl_boundary_eq :
    (cylModel m').boundary (cylW M) = Set.univ ×ˢ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) :=
  boundary_product (I := 𝓡 (m' + 2))

/-- **The interior slab** `K = M × [¼,¾]` — an interior compact of the cylinder that avoids the
boundary; the closed-case determination region of Wall 2 (`determinedByInteriorPoints`). -/
def interiorSlab (M : Type) [TopologicalSpace M] : Set (cylW M) :=
  {p | (1 : ℝ) / 4 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 3 / 4}

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The interior slab avoids the boundary**: `K ⊆ (∂W)ᶜ`. Its interval coordinate lies in `[¼,¾]`,
so it is never an endpoint `⊥ = 0` or `⊤ = 1`; hence it is not on `∂W = M × {⊥,⊤}`. The genuine
interior-ness of the slab that lets Wall 2's closed-case machinery apply. -/
theorem interiorSlab_subset_compl_boundary :
    interiorSlab M ⊆ ((cylModel m').boundary (cylW M))ᶜ := by
  intro p hp
  simp only [interiorSlab, Set.mem_setOf_eq] at hp
  rw [Set.mem_compl_iff, cyl_boundary_eq]
  intro hmem
  rcases hmem.2 with h | h
  · have h0 : (p.2 : ℝ) = 0 := by rw [h]; rfl
    linarith [hp.1, h0]
  · have h1 : (p.2 : ℝ) = 1 := by rw [Set.mem_singleton_iff.mp h]; rfl
    linarith [hp.2, h1]

omit [T2Space M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] in
/-- **The interior slab is compact** — `M` compact crossed with the closed subinterval `[¼,¾]`. -/
theorem isCompact_interiorSlab : IsCompact (interiorSlab M) := by
  apply IsClosed.isCompact
  have hc : Continuous (fun p : cylW M => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

/-! ## §2. The interior-chart linear equiv and the datum reduced to a single existence obligation

The interior generator family `interiorGenFamily` (slice 1 of `PoincareLefschetzRelFundClassGeom`)
needs a linear homeomorphism `ε` of the cylinder model's vector space
`Eᵐ'⁺² × E¹ = EuclideanSpace ℝ (Fin (m'+2)) × EuclideanSpace ℝ (Fin 1)` onto
`EuclideanSpace ℝ (Fin (m'+3))` (`= Fin ((m'+1)+2)`, the top degree). Mathlib's
`EuclideanSpace.finAddEquivProd` supplies it *canonically*. Feeding this explicit `ε` into
`relFundClassDatumOf` discharges the `ε`-obligation for the cylinder, leaving the concrete datum
depending on ONLY the product-existence witness `HasRelFundClass`. -/

/-- **The cylinder interior-chart linear equiv** `Eᵐ'⁺² × E¹ ≃L Eᵐ'⁺³`, the concrete `ε` the
interior generator family consumes (`EuclideanSpace.finAddEquivProd`, canonical). -/
def εcyl (m' : ℕ) :
    (EuclideanSpace ℝ (Fin (m' + 2)) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (m' + 1 + 2)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m' + 2) (m := 1)).symm

/-- **The cylinder interior generator family** `∀ x ∉ ∂W, Hₙ(W, W∖x) ≅ ℤ/2` at every interior point
(`interiorGenFamily` of slice 1, with the concrete `εcyl`). Sealed as its own `def` — its unfolding
threads the heavy `EuclideanSpace.finAddEquivProd` chain, so keeping it un-unfolded prevents whnf
blowups in the datum/uniqueness statements that consume it. -/
def cylGen [T1Space (cylW M)] :
    ∀ x : ↑(TopCat.of (cylW M)), x ∉ (cylModel m').boundary (cylW M) →
      (RelativeHomology ({x}ᶜ) (m' + 1 + 2) ≃ₗ[ZMod 2] ZMod 2) :=
  interiorGenFamily (cylModel m') (εcyl m')

/-- **The concrete cylinder relative-fundamental-class datum, reduced to a single existence witness.**
Given a `HasRelFundClass` existence witness for the cylinder's interior generator family
(`interiorGenFamily (cylModel m') (εcyl m')`), `relFundClassDatumOf` — with the explicit `εcyl` —
packages the full `RelFundClassDatum` for `(W, ∂W)` at `m := m'+1` (top degree `m'+3`). The
`ε`-obligation of `relFundClassDatumOf` is discharged concretely for the cylinder; the product
existence obligation `hcls` is the sole remaining input. Its `μ` functional then feeds the
Poincaré–Lefschetz Wu tower via `RelFundClassDatum.toLefschetzWuDatum`. -/
def cylinderRelFundClassDatum [T1Space (cylW M)]
    (hcls : HasRelFundClass (X := TopCat.of (cylW M))
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) :=
  relFundClassDatumOf (cylModel m') (εcyl m') hcls

/-! ## §3. Wall 2 (`DeterminedByInteriorPoints`) for the cylinder via the interior slab -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The boundary sits in the slab complement**: `∂W ⊆ Kᶜ` — the domain of the collar restriction
`relIncl (∂W ⊆ Kᶜ)`. The flipped form of `interiorSlab_subset_compl_boundary`. -/
theorem boundary_subset_compl_interiorSlab :
    ((cylModel m').boundary (cylW M)) ⊆ (interiorSlab M)ᶜ :=
  Set.subset_compl_comm.mp interiorSlab_subset_compl_boundary

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **Wall 2 for the cylinder** (`DeterminedByInteriorPoints` at the top degree `m'+3`). Specialises
the predecessor's `determinedByInteriorPoints_of_interiorInjective` to `K = interiorSlab`: the pair
`(W, ∂W)` is determined by its interior points once (a) the slab carries the closed-case
`determinedByPoints` and (b) `relIncl (∂W ⊆ Kᶜ)` is injective — the **collar-injectivity residual**.
The explicit product collar `M × ([0,¼) ∪ (¾,1])` deformation-retracts `Kᶜ` onto `∂W` (via the clamp
`(σ,t) ↦ (σ, clamp t)`), which is precisely what discharges (b) once a mod-2 pair homotopy-invariance
+ pair-LES five-lemma is available. The reduction itself is dimension-agnostic and unconditional. -/
theorem cylinder_determinedByInteriorPoints
    (hdet : determinedByPoints (X := TopCat.of (cylW M)) (m' + 1 + 2) (interiorSlab M))
    (hinj : Function.Injective
      (relIncl (M := TopCat.of (cylW M))
        (boundary_subset_compl_interiorSlab (m' := m') (M := M)) (m' + 1 + 2))) :
    DeterminedByInteriorPoints (X := TopCat.of (cylW M))
      ((cylModel m').boundary (cylW M)) (m' + 1 + 2) :=
  determinedByInteriorPoints_of_interiorInjective interiorSlab_subset_compl_boundary hdet hinj

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **Uniqueness of the cylinder relative fundamental class** given Wall 2, in extraction form: two
classes restricting to the interior generator family everywhere are equal once
`DeterminedByInteriorPoints` holds (Wall 2, from `cylinder_determinedByInteriorPoints`). Applying the
predecessor's `relFundClass_unique` at the cylinder's `gen`; combined with `cylinderRelFundClassDatum`
(existence) it pins `[W,∂W]` uniquely. Stated via `gen` explicit to avoid re-deriving the heavy
`εcyl` chain: the caller supplies the generator family it already holds. -/
theorem cylinderRelFundClass_unique [T1Space (cylW M)]
    (gen : ∀ x : ↑(TopCat.of (cylW M)), x ∉ (cylModel m').boundary (cylW M) →
      (RelativeHomology ({x}ᶜ) (m' + 1 + 2) ≃ₗ[ZMod 2] ZMod 2))
    (hdi : DeterminedByInteriorPoints (X := TopCat.of (cylW M))
      ((cylModel m').boundary (cylW M)) (m' + 1 + 2))
    {α β : RelativeHomology (X := TopCat.of (cylW M))
      ((cylModel m').boundary (cylW M)) (m' + 1 + 2)}
    (hα : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) gen α)
    (hβ : RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) gen β) : α = β :=
  relFundClass_unique (X := TopCat.of (cylW M)) (m := m' + 1)
    ((cylModel m').boundary (cylW M)) gen hdi hα hβ

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinder
