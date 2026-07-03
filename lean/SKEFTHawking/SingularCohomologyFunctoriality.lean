import Mathlib
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularCupH13

/-!
# Phase 5q.G (G3 F1) — contravariant functoriality of singular `ℤ/2` cohomology

The cochain **pullback** `φ* : Cⁿ(Y) → Cⁿ(X)` along `φ : X → Y` (precompose the simplex
pushforward), its coboundary commutation (via `face_mapSimplex`), the Kronecker adjunction
`⟨φ*a, c⟩ = ⟨a, φ₊c⟩`, the descended **`Cohomology.pullback`** `Hⁿ(Y) → Hⁿ(X)`, functoriality,
and the homeomorphism equivalence `cohomologyHomeoEquiv` — the contravariant foundation the
w₂-certificate transport (the faithful Pin⁺ datum's ops) consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open Opposite

namespace SKEFTHawking.SingularCohomologyFunctoriality

/-- **The cochain pullback** `φ* : Cⁿ(Y) → Cⁿ(X)`, `(φ*a)(σ) = a(φ ∘ σ)`. -/
noncomputable def cochainPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    SingularCochain Y n →ₗ[ZMod 2] SingularCochain X n where
  toFun a := fun σ => a (mapSimplex φ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cochainPullback_apply {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochain Y n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    cochainPullback φ n a σ = a (mapSimplex φ σ) := rfl

/-- **The pullback is a cochain map**: `δ(φ*a) = φ*(δa)` (face-naturality of the pushforward). -/
theorem coboundary_cochainPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochain Y n) :
    coboundary X n (cochainPullback φ n a) = cochainPullback φ (n + 1) (coboundary Y n a) := by
  funext σ
  show ∑ i : Fin (n + 2), a (mapSimplex φ (face i σ))
    = ∑ i : Fin (n + 2), a (face i (mapSimplex φ σ))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [face_mapSimplex]

/-- **The Kronecker adjunction** `⟨φ*a, c⟩ = ⟨a, φ₊c⟩`. -/
theorem kronecker_cochainPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (a : SingularCochain Y n) (c : SingularChain X n) :
    kronecker (cochainPullback φ n a) c = kronecker a (mapChain φ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s => rw [kronecker_single, mapChain_single, kronecker_single, cochainPullback_apply]

/-- The pullback of a cocycle is a cocycle. -/
theorem cochainPullback_mem_ker {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (a : LinearMap.ker (coboundaryₗ Y n)) :
    cochainPullback φ n a.1 ∈ LinearMap.ker (coboundaryₗ X n) := by
  rw [LinearMap.mem_ker]
  show coboundary X n (cochainPullback φ n a.1) = 0
  rw [coboundary_cochainPullback,
    show coboundary Y n a.1 = coboundaryₗ Y n a.1 from rfl, LinearMap.mem_ker.mp a.2, map_zero]

/-- **The cohomology pullback** `φ* : Hⁿ(Y) → Hⁿ(X)` — the descended cochain pullback. -/
noncomputable def cohomologyPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    Cohomology Y n →ₗ[ZMod 2] Cohomology X n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cochainPullback φ n).domRestrict (LinearMap.ker (coboundaryₗ Y n))).codRestrict
        (LinearMap.ker (coboundaryₗ X n)) fun a => cochainPullback_mem_ker φ a))
    (by
      intro a ha
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk _ = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
      cases n with
      | zero =>
          have ha0 : (a.1 : SingularCochain Y 0) = 0 := by
            have := ha
            rwa [show coboundaryRange Y 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
              Submodule.mem_bot] at this
          rw [show coboundaryRange X 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
            Submodule.mem_bot, ha0, map_zero]
      | succ m =>
          obtain ⟨b, hb⟩ := ha
          refine ⟨cochainPullback φ m b, ?_⟩
          show coboundaryₗ X m (cochainPullback φ m b) = cochainPullback φ (m + 1) a.1
          rw [show coboundaryₗ X m (cochainPullback φ m b)
              = coboundary X m (cochainPullback φ m b) from rfl,
            coboundary_cochainPullback]
          rw [show coboundary Y m b = coboundaryₗ Y m b from rfl, hb])

/-- The computation rule for `cohomologyPullback` on a representative cocycle. -/
@[simp] theorem cohomologyPullback_mk {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ Y n)) :
    cohomologyPullback φ n (Cohomology.mk Y n a)
      = Cohomology.mk X n ⟨cochainPullback φ n a.1, cochainPullback_mem_ker φ a⟩ :=
  rfl

/-- **Pullback functoriality**: `(ψ ∘ φ)* = φ* ∘ ψ*`. -/
theorem cohomologyPullback_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ) :
    cohomologyPullback (ψ.comp φ) n
      = (cohomologyPullback φ n).comp (cohomologyPullback ψ n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show cohomologyPullback (ψ.comp φ) n (Cohomology.mk Z n a)
    = cohomologyPullback φ n (cohomologyPullback ψ n (Cohomology.mk Z n a))
  rw [cohomologyPullback_mk, cohomologyPullback_mk, cohomologyPullback_mk]
  congr 1

/-- **Pullback of the identity is the identity.** -/
theorem cohomologyPullback_id {X : TopCat} (n : ℕ) :
    cohomologyPullback (ContinuousMap.id ↑X) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show cohomologyPullback (ContinuousMap.id ↑X) n (Cohomology.mk X n a) = Cohomology.mk X n a
  rw [cohomologyPullback_mk]
  congr 1

/-- **The cohomology equivalence of a homeomorphism** `Hⁿ(Y) ≃ₗ Hⁿ(X)` (contravariant). -/
noncomputable def cohomologyHomeoEquiv {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) (n : ℕ) :
    Cohomology Y n ≃ₗ[ZMod 2] Cohomology X n :=
  LinearEquiv.ofLinear (cohomologyPullback (⟨e, e.continuous⟩ : C(↑X, ↑Y)) n)
    (cohomologyPullback (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)) n)
    (by
      rw [← cohomologyPullback_comp,
        show (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)).comp
            (⟨e, e.continuous⟩ : C(↑X, ↑Y)) = ContinuousMap.id ↑X
          from ContinuousMap.ext (fun x => e.symm_apply_apply x),
        cohomologyPullback_id])
    (by
      rw [← cohomologyPullback_comp,
        show (⟨e, e.continuous⟩ : C(↑X, ↑Y)).comp
            (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)) = ContinuousMap.id ↑Y
          from ContinuousMap.ext (fun y => e.apply_symm_apply y),
        cohomologyPullback_id])

/-! ## F2 — cup-pullback multiplicativity (Alexander–Whitney naturality) -/

/-- The front face commutes with the simplex pushforward. -/
theorem frontFace_mapSimplex {X Y : TopCat} {p q : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (mapSimplex φ σ) = mapSimplex φ (frontFace (p := p) (q := q) σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk p))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- The back face commutes with the simplex pushforward. -/
theorem backFace_mapSimplex {X Y : TopCat} {p q : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (p + q)))) :
    backFace (mapSimplex φ σ) = mapSimplex φ (backFace (p := p) (q := q) σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk q))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- **Cup-pullback multiplicativity** (cochain level): `φ*(f ⌣ g) = φ*f ⌣ φ*g`. -/
theorem cochainPullback_cup {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (f : SingularCochain Y p) (g : SingularCochain Y q) :
    cochainPullback φ (p + q) (cup f g)
      = cup (cochainPullback φ p f) (cochainPullback φ q g) := by
  funext σ
  show cup f g (mapSimplex φ σ)
    = f (mapSimplex φ (frontFace σ)) * g (mapSimplex φ (backFace σ))
  rw [cup_apply, frontFace_mapSimplex, backFace_mapSimplex]

/-- **`cupH24`-pullback compatibility**: `φ*(a ∪ b) = φ*a ∪ φ*b` on `H² × H² → H⁴`. -/
theorem cohomologyPullback_cupH24 {X Y : TopCat} (φ : C(↑X, ↑Y))
    (a : Cohomology Y 2) (b : Cohomology Y 2) :
    cohomologyPullback φ 4 (cupH24 a b)
      = cupH24 (cohomologyPullback φ 2 a) (cohomologyPullback φ 2 b) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk (Subtype.ext (cochainPullback_cup φ fa.1 fb.1))

/-- **`cupH13`-pullback compatibility**: `φ*(a ∪ b) = φ*a ∪ φ*b` on `H¹ × H³ → H⁴`. -/
theorem cohomologyPullback_cupH13 {X Y : TopCat} (φ : C(↑X, ↑Y))
    (a : Cohomology Y 1) (b : Cohomology Y 3) :
    cohomologyPullback φ 4 (cupH13 a b)
      = cupH13 (cohomologyPullback φ 1 a) (cohomologyPullback φ 3 b) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk (Subtype.ext (cochainPullback_cup φ fa.1 fb.1))

/-- **`cupH`-pullback compatibility**: `φ*(a ∪ b) = φ*a ∪ φ*b` on `H¹ × H¹ → H²`. -/
theorem cohomologyPullback_cupH {X Y : TopCat} (φ : C(↑X, ↑Y))
    (a : Cohomology Y 1) (b : Cohomology Y 1) :
    cohomologyPullback φ 2 (cupH a b)
      = cupH (cohomologyPullback φ 1 a) (cohomologyPullback φ 1 b) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk (Subtype.ext (cochainPullback_cup φ fa.1 fb.1))

/-! ## F3 — the homology-level Kronecker adjunction -/

/-- **The descended Kronecker adjunction** `⟨φ*ω, β⟩ = ⟨ω, φ₊β⟩` on (co)homology classes. -/
theorem kroneckerH_cohomologyPullback {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (ω : Cohomology Y n) (β : Homology X n) :
    kroneckerH (X := X) n (cohomologyPullback φ n ω) β
      = kroneckerH (X := Y) n ω (Homology.map φ n β) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  show kronecker (cochainPullback φ n a.1) c.1 = kronecker a.1 (mapChain φ n c.1)
  exact kronecker_cochainPullback φ a.1 c.1


end SKEFTHawking.SingularCohomologyFunctoriality
