/-
# Phase 5q.H close-out (#148, part 1) — the cohomology δ-image calculus on the annihilator pair
# model, and the δ-naturality of the pinned relative Steenrod squares `relSq²` / `relSq¹`

The Wu-leaf Sq-suspension atoms (`hsusp23`/`hsusp14`, `PinPlusCylDataDischargeWuLeafSusp`) need the
classical STABILITY mechanism: every relative class in the suspension degrees is the image of the
pair's cohomology connecting map, and the Steenrod squares commute with that connecting map. On this
substrate's annihilator model (`relCochains S` = cochains killing the subspace chains) the connecting
image has a particularly light description — the **δ-image class** `[δz] ∈ Hⁿ⁺¹(X,S)` of an absolute
cochain `z ∈ Cⁿ(X)` whose coboundary annihilates the subcomplex. This module banks, for a generic
pair `(X, S)`:

* **§1 `deltaRelH`** — the δ-image class `[δz]`, and the exactness converse
  `exists_deltaRelH_of_relToAbs_eq_zero`: every relative class killed by the pair restriction
  `j* : Hⁿ⁺¹(X,S) → Hⁿ⁺¹(X)` is a δ-image (the `ker j* ⊆ im δ` half the atoms consume — on the
  cylinder `j*` vanishes in the suspension degrees, so EVERY class is a δ-image).
* **§2 second-factor annihilation** — `cup`/`cupOne23` with a RELATIVE second factor annihilate the
  subcomplex (mirrors of the in-tree first-factor lemmas; every face-restriction of a subspace
  simplex is a subspace simplex, `simplexIncl_map`).
* **§3 `relSq2_deltaRelH`** — **δ-naturality of the pinned `relSq²`**: `relSq² [δz] = [δ(z ⌣ z)]`
  for `z ∈ C²(X)`. The engine is the banked absolute Hirsch shift `sq2_cochain_shift` at basepoint
  `0`: `δz ⌣₁ δz = δ(z ⌣₁ δz) + δ(z ⌣ z)` (`cupOne33_coboundary_diag`), whose correction cochain
  `z ⌣₁ δz` is relative by §2 — so the two relative classes agree. This is the Sq-stability content:
  the suspension of the sub-top square is the top (cup-)square.
* **§4 `relSq1_deltaRelH`** — **δ-naturality of the pinned `relSq¹`**: `relSq¹ [δz] = [δ(sq1Defect z)]`
  where `sq1Defect z = castHom₂(half(lift(δz) − δ₄(lift z)))` is the EXPLICIT ℤ/4 Bockstein defect
  cochain (the constructive witness inside `SingularBockstein.Sq1cochain_coboundary`, extracted here
  as a named `def` because its endpoint restrictions are what the cylinder atoms evaluate). The class
  identity holds on the nose: `δ(sq1Defect z) = Sq1cochain (δz)` (`coboundary_sq1Defect`).
* **§5 pullback evaluations** — along any map `φ : Y → X` landing in `S`: a relative cochain pulls
  back to the zero cochain (`cochainPullback_eq_zero_of_mapsTo`), and `sq1Defect` pulls back to the
  Bockstein cochain of the pullback (`cochainPullback_sq1Defect`) — the two computations the
  cylinder-end evaluation of δ-image classes runs on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeAbsCompat
import SKEFTHawking.SingularRelativeSteenrodSq2
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.SingularExcision

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeAbsCompat
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularExcision (single_mem_subspaceChains_of_subordinate)

namespace SKEFTHawking.SingularRelativeCohomDelta

noncomputable section

variable {X : TopCat} {S : Set ↑X}

/-! ## §0. Relative cochains kill simplices with image in `S` -/

/-- A relative cochain vanishes on ANY simplex whose realization lands in `S` (not only on
`simplexIncl`-simplices): such a simplex generates a subspace chain
(`single_mem_subspaceChains_of_subordinate`). -/
theorem relCochain_vanish_of_range_subset {n : ℕ} (f : relCochains S n)
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    (hτ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S) :
    (f : SingularCochain X n) τ = 0 := by
  have h := f.2 (Finsupp.single τ 1) (single_mem_subspaceChains_of_subordinate hτ)
  rwa [kronecker_single, one_mul] at h

/-- The pushforward of a simplex along a map landing in `S` realizes into `S`. -/
theorem range_toSSet_mapSimplex_subset {Y : TopCat} (φ : C(↑Y, ↑X)) (hφ : ∀ y, φ y ∈ S) {n : ℕ}
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (mapSimplex φ σ)) ⊆ S := by
  rintro x ⟨t, rfl⟩
  simp only [mapSimplex, Equiv.apply_symm_apply]
  exact hφ _

/-- **Pullback along a map into `S` kills relative cochains** (pointwise-zero cochain). -/
theorem cochainPullback_eq_zero_of_mapsTo {Y : TopCat} (φ : C(↑Y, ↑X)) (hφ : ∀ y, φ y ∈ S)
    {n : ℕ} (f : relCochains S n) :
    cochainPullback φ n (f : SingularCochain X n) = 0 := by
  funext σ
  rw [cochainPullback_apply]
  exact relCochain_vanish_of_range_subset f (mapSimplex φ σ)
    (range_toSSet_mapSimplex_subset φ hφ σ)

/-! ## §1. The δ-image class and exactness at the pair restriction -/

/-- The coboundary `δz` of an absolute cochain, packaged as a **relative cocycle** when it
annihilates the subcomplex (the cocycle condition is `δ² = 0`). -/
def deltaRelCocycle {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    LinearMap.ker (relCoboundaryₗ S (n + 1)) :=
  ⟨⟨coboundaryₗ X n z, h⟩, LinearMap.mem_ker.mpr ((relCoboundary_eq_zero_iff _).mpr
    (coboundary_comp_coboundary X n z))⟩

@[simp] theorem deltaRelCocycle_coe {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    ((deltaRelCocycle z h : LinearMap.ker (relCoboundaryₗ S (n + 1))) :
      SingularCochain X (n + 1)) = coboundaryₗ X n z := rfl

/-- **The δ-image class** `[δz] ∈ Hⁿ⁺¹(X,S)` — the cohomology connecting-map image on the
annihilator model. -/
def deltaRelH {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) : RelativeCohomology S (n + 1) :=
  RelativeCohomology.mk S (n + 1) (deltaRelCocycle z h)

/-- **Exactness at the pair restriction** (`ker j* ⊆ im δ`): a relative class killed by
`relToAbs = j*` is a δ-image. This is the δ-decomposability the suspension atoms consume. -/
theorem exists_deltaRelH_of_relToAbs_eq_zero {n : ℕ} (b : RelativeCohomology S (n + 1))
    (hb : relToAbs b = 0) :
    ∃ (z : SingularCochain X n) (h : coboundaryₗ X n z ∈ relCochains S (n + 1)),
      b = deltaRelH z h := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show (Submodule.Quotient.mk a : RelativeCohomology S (n + 1))
      = RelativeCohomology.mk S (n + 1) a from rfl, relToAbs_mk] at hb
  have h2 := (Submodule.Quotient.mk_eq_zero _).mp hb
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
    show coboundaryRange X (n + 1) = LinearMap.range (coboundaryₗ X n) from rfl] at h2
  obtain ⟨z, hz⟩ := h2
  have hz' : coboundaryₗ X n z = a.1.1 := hz.trans (relToAbsCocycleₗ_coe a)
  refine ⟨z, by rw [hz']; exact a.1.2, ?_⟩
  exact congrArg (RelativeCohomology.mk S (n + 1)) (Subtype.ext (Subtype.ext hz'.symm))

/-! ## §2. Second-factor annihilation -/

/-- The absolute cup of a relative SECOND factor annihilates the subcomplex (mirror of
`cup_mem_relCochains`; the back face of a subspace simplex is a subspace simplex). -/
theorem cup_mem_relCochains_right {p q : ℕ} (f : SingularCochain X p) (g : relCochains S q) :
    cup f (g : SingularCochain X q) ∈ relCochains S (p + q) := by
  apply mem_relCochains_of_vanish
  intro τ
  rw [cup_apply]
  unfold backFace
  rw [simplexIncl_map (backIncl p q), relCochain_vanish g, mul_zero]

/-- `cupOne23` of a relative SECOND factor annihilates the subcomplex (mirror of
`cupOne23_mem_relCochains`). -/
theorem cupOne23_mem_relCochains_right (c : SingularCochain X 2) (d : relCochains S 3) :
    cupOne23 c (d : SingularCochain X 3) ∈ relCochains S 4 := by
  apply mem_relCochains_of_vanish
  intro τ
  simp only [cupOne23]
  rw [simplexIncl_map cwx0123, simplexIncl_map cwy1234, relCochain_vanish d, relCochain_vanish d,
    mul_zero, mul_zero, add_zero]

/-! ## §3. δ-naturality of the pinned `relSq²` -/

/-- Zero-left collapse of `cupOne33` (every term has a first factor). -/
theorem cupOne33_zero_left (y : SingularCochain X 3) :
    cupOne33 (0 : SingularCochain X 3) y = 0 := by
  funext σ
  simp [cupOne33]

/-- Zero-left collapse of `cupTwo33` (every term has a first factor). -/
theorem cupTwo33_zero_left (y : SingularCochain X 3) :
    cupTwo33 (0 : SingularCochain X 3) y = 0 := by
  funext σ
  simp [cupTwo33]

/-- **The Hirsch coboundary-square identity** `δz ⌣₁ δz = δ(z ⌣₁ δz) + δ(z ⌣ z)` for any
`z ∈ C²(X)` — the banked `sq2_cochain_shift` at basepoint `0`. The suspension engine: the cup-1
self-product of a coboundary is, modulo the coboundary of the cup-1 correction, the coboundary of
the cup SQUARE. -/
theorem cupOne33_coboundary_diag (z : SingularCochain X 2) :
    cupOne33 (coboundaryₗ X 2 z) (coboundaryₗ X 2 z)
      = coboundaryₗ X 4 (cupOne23 z (coboundaryₗ X 2 z)) + coboundaryₗ X 4 (cup z z) := by
  have h := sq2_cochain_shift (X := X) 0 z (map_zero _)
  simp only [zero_add, cupOne33_zero_left, cupTwo33_zero_left, map_add] at h
  exact h

/-- `δ(z ⌣ z)` annihilates the subcomplex when `δz` does: it is `δz ⌣₁ δz` (first-factor relative)
plus the coboundary of the relative correction `z ⌣₁ δz` (second-factor relative). -/
theorem coboundary_cup_self_mem_relCochains (z : SingularCochain X 2)
    (h : coboundaryₗ X 2 z ∈ relCochains S 3) :
    coboundaryₗ X 4 (cup z z) ∈ relCochains S 5 := by
  have h2 : coboundaryₗ X 4 (cup z z)
      = cupOne33 (coboundaryₗ X 2 z) (coboundaryₗ X 2 z)
        - coboundaryₗ X 4 (cupOne23 z (coboundaryₗ X 2 z)) := by
    rw [cupOne33_coboundary_diag]; abel
  rw [h2]
  refine Submodule.sub_mem _ (cupOne33_mem_relCochains ⟨_, h⟩ _) ?_
  exact coboundary_mem_relCochains S 4 _ (cupOne23_mem_relCochains_right z ⟨_, h⟩)

/-- **δ-naturality of the pinned `relSq²`**: `relSq² [δz] = [δ(z ⌣ z)]` for `z ∈ C²(X)` with `δz`
relative. The two relative 5-cocycles differ by the relative coboundary of `z ⌣₁ δz`
(`cupOne33_coboundary_diag` + §2). The suspension of the sub-top square is the top square. -/
theorem relSq2_deltaRelH (z : SingularCochain X 2)
    (h : coboundaryₗ X 2 z ∈ relCochains S 3) :
    relSq2 (deltaRelH z h)
      = deltaRelH (n := 4) (cup z z) (coboundary_cup_self_mem_relCochains z h) := by
  rw [deltaRelH, relSq2_apply, deltaRelH]
  change (Submodule.Quotient.mk _ : _ ⧸ _) = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  rw [show relCoboundaryRange S 5 = LinearMap.range (relCoboundaryₗ S 4) from rfl]
  refine ⟨⟨cupOne23 z (coboundaryₗ X 2 z), cupOne23_mem_relCochains_right z ⟨_, h⟩⟩, ?_⟩
  apply Subtype.ext
  rw [relCoboundaryₗ_coe, AddSubgroupClass.coe_sub, relSq2cocycle_coe, deltaRelCocycle_coe]
  show coboundary X 4 (cupOne23 z (coboundaryₗ X 2 z))
      = cupOne33 (coboundaryₗ X 2 z) (coboundaryₗ X 2 z) - coboundaryₗ X 4 (cup z z)
  rw [cupOne33_coboundary_diag]
  abel

/-! ## §4. δ-naturality of the pinned `relSq¹` via the explicit Bockstein defect -/

/-- The ℤ/4 **Bockstein defect** of `z`: `half(lift(δz) − δ₄(lift z))` re-lifted to ℤ/4 — the
constructive coboundary-witness cochain inside `SingularBockstein.Sq1cochain_coboundary`, extracted
as a named `def` so its endpoint restrictions can be evaluated. -/
def sq1Defect4 {n : ℕ} (z : SingularCochain X n) : Cochain4 X (n + 1) :=
  fun σ => ((half (lift (coboundaryₗ X n z) σ - coboundary4 X n (lift z) σ)).val : ZMod 4)

/-- The mod-2 **Bockstein defect cochain** `sq1Defect z ∈ Cⁿ⁺¹(X)`, satisfying
`δ(sq1Defect z) = Sq1cochain (δz)` (`coboundary_sq1Defect`). -/
def sq1Defect {n : ℕ} (z : SingularCochain X n) : SingularCochain X (n + 1) :=
  fun σ => (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (sq1Defect4 z σ)

/-- The defining divisibility: `lift(δz) − δ₄(lift z) = 2 · sq1Defect4 z` pointwise (the difference
is even since both lift `δz` mod 2). -/
theorem sq1Defect4_spec {n : ℕ} (z : SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    lift (coboundaryₗ X n z) σ - coboundary4 X n (lift z) σ = 2 * sq1Defect4 z σ := by
  have heven : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (lift (coboundaryₗ X n z) σ - coboundary4 X n (lift z) σ) = 0 := by
    rw [map_sub, castHom_coboundary4_lift, castHom_lift]
    show coboundary X n z σ - coboundary X n z σ = 0
    ring
  simp only [sq1Defect4]
  rw [two_mul_half_val_of_even _ heven]

/-- **The explicit Bockstein coboundary identity** `δ(sq1Defect z) = Sq1cochain (δz)` — the body of
`SingularBockstein.Sq1cochain_coboundary` with its witness named (`sq1Defect`). -/
theorem coboundary_sq1Defect {n : ℕ} (z : SingularCochain X n) :
    coboundaryₗ X (n + 1) (sq1Defect z) = Sq1cochain (coboundaryₗ X n z) := by
  have hcob : ∀ σ, coboundary4 X (n + 1) (lift (coboundaryₗ X n z)) σ
      = 2 * coboundary4 X (n + 1) (sq1Defect4 z) σ := by
    intro σ
    have hsub : lift (coboundaryₗ X n z)
        = coboundary4 X n (lift z) + fun τ => 2 * sq1Defect4 z τ := by
      funext τ
      rw [Pi.add_apply, ← sq1Defect4_spec z τ]
      ring
    rw [hsub, coboundary4_apply]
    simp only [Pi.add_apply]
    have hsplit : coboundary4 X (n + 1) (coboundary4 X n (lift z)) σ
        + ∑ i : Fin (n + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) * (2 * sq1Defect4 z (face i σ))
        = ∑ i : Fin (n + 1 + 2), (-1 : ZMod 4) ^ (i : ℕ) *
            (coboundary4 X n (lift z) (face i σ) + 2 * sq1Defect4 z (face i σ)) := by
      rw [coboundary4_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [← hsplit, coboundary4_comp_coboundary4 X n (lift z)]
    show (0 : ZMod 4) + _ = _
    rw [zero_add, coboundary4_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  funext σ
  show coboundary X (n + 1) (sq1Defect z) σ = Sq1cochain (coboundaryₗ X n z) σ
  rw [show sq1Defect z = fun τ =>
      (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (sq1Defect4 z τ) from rfl,
    ← castHom_coboundary4, Sq1cochain_apply, hcob, half_two_smul]

/-- `δ(sq1Defect z)` annihilates the subcomplex when `δz` does (it is `Sq1cochain(δz)`, and the
Bockstein cochain of a relative cochain is relative — `relSq1cochain_mem`). -/
theorem coboundary_sq1Defect_mem_relCochains {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    coboundaryₗ X (n + 1) (sq1Defect z) ∈ relCochains S (n + 1 + 1) := by
  rw [coboundary_sq1Defect]
  exact relSq1cochain_mem ⟨_, h⟩

/-- **δ-naturality of the pinned `relSq¹`**: `relSq¹ [δz] = [δ(sq1Defect z)]` — on the nose (the
two representative cocycles are literally equal, `coboundary_sq1Defect`). -/
theorem relSq1_deltaRelH {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    relSq1 (n := n) (deltaRelH z h)
      = deltaRelH (sq1Defect z) (coboundary_sq1Defect_mem_relCochains z h) := by
  rw [deltaRelH, relSq1_apply, deltaRelH]
  refine congrArg (RelativeCohomology.mk S (n + 1 + 1)) (Subtype.ext (Subtype.ext ?_))
  rw [relSq1cocycle_coe, deltaRelCocycle_coe]
  exact (coboundary_sq1Defect z).symm

/-- `relSq1_deltaRelH` at the `(1,4)` suspension degree, with the literal-degree spelling the
cylinder atoms rewrite against (`z ∈ C³`, δ-image in `H⁴`, Bockstein image in `H⁵`). -/
theorem relSq1_deltaRelH_three (z : SingularCochain X 3)
    (h : coboundaryₗ X 3 z ∈ relCochains S (3 + 1)) :
    relSq1 (n := 3) (deltaRelH (n := 3) z h)
      = deltaRelH (n := 4) (sq1Defect z) (coboundary_sq1Defect_mem_relCochains z h) :=
  relSq1_deltaRelH z h

/-! ## §5. Pullback evaluations along maps into `S` -/

/-- `castHom₂ ∘ (val-relift) = id` on `ℤ/2`. -/
theorem castHom_val_cast (t : ZMod 2) :
    (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) ((t.val : ZMod 4)) = t := by
  fin_cases t <;> decide

/-- An even element of `ℤ/4` is its own negative. -/
theorem neg_eq_self_of_castHom_eq_zero (v : ZMod 4)
    (h : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) v = 0) : -v = v := by
  revert h
  fin_cases v <;> decide

/-- `lift` commutes with the cochain pullback (pointwise, definitional). -/
theorem lift_cochainPullback {Y : TopCat} (φ : C(↑Y, ↑X)) {n : ℕ} (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n))) :
    lift (cochainPullback φ n a) σ = lift a (mapSimplex φ σ) := rfl

/-- `δ₄ ∘ lift` commutes with the cochain pullback (faces commute with the pushforward). -/
theorem coboundary4_lift_cochainPullback {Y : TopCat} (φ : C(↑Y, ↑X)) {n : ℕ}
    (a : SingularCochain X n)
    (σ : (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk (n + 1)))) :
    coboundary4 Y n (lift (cochainPullback φ n a)) σ
      = coboundary4 X n (lift a) (mapSimplex φ σ) := by
  rw [coboundary4_apply, coboundary4_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lift_cochainPullback, face_mapSimplex]

/-- **Pullback of the Bockstein defect along a map into `S`** is the Bockstein cochain of the
pullback: `φ*(sq1Defect z) = Sq1cochain (φ*z)` when `δz` annihilates the subcomplex and `φ` lands in
`S`. The `lift(δz)` term dies (relative cochain, image in `S`) and the parity of `δ₄(lift z)` kills
the sign. -/
theorem cochainPullback_sq1Defect {Y : TopCat} (φ : C(↑Y, ↑X)) (hφ : ∀ y, φ y ∈ S) {n : ℕ}
    (z : SingularCochain X n) (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    cochainPullback φ (n + 1) (sq1Defect z) = Sq1cochain (cochainPullback φ n z) := by
  funext σ
  rw [cochainPullback_apply, Sq1cochain_apply]
  have hvanish : coboundaryₗ X n z (mapSimplex φ σ) = 0 :=
    relCochain_vanish_of_range_subset ⟨_, h⟩ (mapSimplex φ σ)
      (range_toSSet_mapSimplex_subset φ hφ σ)
  have hδ : lift (coboundaryₗ X n z) (mapSimplex φ σ) = 0 := by
    rw [lift_apply, hvanish]
    simp
  have heven : (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2))
      (coboundary4 X n (lift z) (mapSimplex φ σ)) = 0 := by
    rw [castHom_coboundary4_lift]
    exact hvanish
  show (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2)) (sq1Defect4 z (mapSimplex φ σ)) = _
  simp only [sq1Defect4]
  rw [castHom_val_cast, hδ, zero_sub, neg_eq_self_of_castHom_eq_zero _ heven,
    ← coboundary4_lift_cochainPullback]

end

end SKEFTHawking.SingularRelativeCohomDelta
