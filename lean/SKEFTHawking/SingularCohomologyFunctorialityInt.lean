import Mathlib
import SKEFTHawking.SingularCupInt
import SKEFTHawking.SingularFunctorialityInt

/-!
# Phase 5q.H · E1 — contravariant functoriality of singular **integral** cohomology

The integral mirror of `SingularCohomologyFunctoriality` (the ℤ/2 version). The cochain **pullback**
`φ* : Cⁿ(Y;ℤ) → Cⁿ(X;ℤ)` along `φ : X → Y` (precompose the simplex pushforward), its coboundary
commutation (via `face_mapSimplex`), the Kronecker adjunction `⟨φ*a, c⟩ = ⟨a, φ₊c⟩`, the descended
**`cohomologyPullbackInt`** `Hⁿ(Y;ℤ) → Hⁿ(X;ℤ)`, functoriality, the homeomorphism equivalence, and —
the headline for the S²×S² Gram computation — the **cup-pullback multiplicativity**
`cohomologyPullbackInt φ 4 (a ∪ b) = φ*a ∪ φ*b` on `H² × H² → H⁴` and the descended Kronecker
adjunction `⟨φ*ω, β⟩ = ⟨ω, φ₊β⟩` over ℤ.

The load-bearing difference from the mod-2 file is the *signed* coboundary `δf = ∑ (-1)ⁱ f(∂ᵢ)`; the
cup product itself is sign-free at the cochain level (`cup f g σ = f(front σ) · g(back σ)`), so
`cochainPullbackInt_cup` mirrors verbatim.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open SKEFTHawking.SingularHomologyInt SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularFunctorialityInt
open Opposite

namespace SKEFTHawking.SingularCohomologyFunctorialityInt

/-- **The integral cochain pullback** `φ* : Cⁿ(Y;ℤ) → Cⁿ(X;ℤ)`, `(φ*a)(σ) = a(φ ∘ σ)`. -/
noncomputable def cochainPullbackInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    SingularCochainInt Y n →ₗ[ℤ] SingularCochainInt X n where
  toFun a := fun σ => a (mapSimplex φ σ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cochainPullbackInt_apply {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochainInt Y n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    cochainPullbackInt φ n a σ = a (mapSimplex φ σ) := rfl

/-- **Face-naturality for the integral `face`** — the integral `SingularCohomologyInt.face` is the
same purely-simplicial operation `(toSSet.obj X).map (δ i).op σ` as the mod-2 `face`, so the shared
`SingularFunctoriality.face_mapSimplex` transports verbatim (definitional at the coefficient-agnostic
simplex level). -/
theorem face_mapSimplexInt {X Y : TopCat} {n : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    face i (mapSimplex φ σ) = mapSimplex φ (face i σ) :=
  SKEFTHawking.SingularFunctoriality.face_mapSimplex φ σ i

/-- **The pullback is a cochain map**: `δ(φ*a) = φ*(δa)` (face-naturality of the pushforward). The
signs `(-1)ⁱ` factor out of the term-by-term face-naturality rewrite. -/
theorem coboundary_cochainPullbackInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : SingularCochainInt Y n) :
    coboundary X n (cochainPullbackInt φ n a)
      = cochainPullbackInt φ (n + 1) (coboundary Y n a) := by
  funext σ
  show ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * a (mapSimplex φ (face i σ))
    = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) * a (face i (mapSimplex φ σ))
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [face_mapSimplexInt]

/-- **The Kronecker adjunction** `⟨φ*a, c⟩ = ⟨a, φ₊c⟩` (integral, cochain level). -/
theorem kronecker_cochainPullbackInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (a : SingularCochainInt Y n) (c : SingularChainInt X n) :
    kronecker (cochainPullbackInt φ n a) c = kronecker a (mapChainInt φ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [kronecker_single, mapChainInt_single, kronecker_single, cochainPullbackInt_apply]

/-- The pullback of a cocycle is a cocycle. -/
theorem cochainPullbackInt_mem_ker {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (a : LinearMap.ker (coboundaryₗ Y n)) :
    cochainPullbackInt φ n a.1 ∈ LinearMap.ker (coboundaryₗ X n) := by
  rw [LinearMap.mem_ker]
  show coboundary X n (cochainPullbackInt φ n a.1) = 0
  rw [coboundary_cochainPullbackInt,
    show coboundary Y n a.1 = coboundaryₗ Y n a.1 from rfl, LinearMap.mem_ker.mp a.2, map_zero]

/-- **The integral cohomology pullback** `φ* : Hⁿ(Y;ℤ) → Hⁿ(X;ℤ)` — the descended cochain pullback. -/
noncomputable def cohomologyPullbackInt {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    Cohomology Y n →ₗ[ℤ] Cohomology X n :=
  Submodule.liftQ _
    ((Submodule.mkQ _).comp
      (((cochainPullbackInt φ n).domRestrict (LinearMap.ker (coboundaryₗ Y n))).codRestrict
        (LinearMap.ker (coboundaryₗ X n)) fun a => cochainPullbackInt_mem_ker φ a))
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
          have ha0 : (a.1 : SingularCochainInt Y 0) = 0 := by
            have := ha
            rwa [show coboundaryRange Y 0 = (⊥ : Submodule ℤ _) from rfl,
              Submodule.mem_bot] at this
          rw [show coboundaryRange X 0 = (⊥ : Submodule ℤ _) from rfl,
            Submodule.mem_bot, ha0, map_zero]
      | succ m =>
          obtain ⟨b, hb⟩ := ha
          refine ⟨cochainPullbackInt φ m b, ?_⟩
          show coboundaryₗ X m (cochainPullbackInt φ m b) = cochainPullbackInt φ (m + 1) a.1
          rw [show coboundaryₗ X m (cochainPullbackInt φ m b)
              = coboundary X m (cochainPullbackInt φ m b) from rfl,
            coboundary_cochainPullbackInt]
          rw [show coboundary Y m b = coboundaryₗ Y m b from rfl, hb])

/-- The computation rule for `cohomologyPullbackInt` on a representative cocycle. -/
@[simp] theorem cohomologyPullbackInt_mk {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ Y n)) :
    cohomologyPullbackInt φ n (Cohomology.mk Y n a)
      = Cohomology.mk X n ⟨cochainPullbackInt φ n a.1, cochainPullbackInt_mem_ker φ a⟩ :=
  rfl

/-- **Pullback functoriality**: `(ψ ∘ φ)* = φ* ∘ ψ*`. -/
theorem cohomologyPullbackInt_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ) :
    cohomologyPullbackInt (ψ.comp φ) n
      = (cohomologyPullbackInt φ n).comp (cohomologyPullbackInt ψ n) := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show cohomologyPullbackInt (ψ.comp φ) n (Cohomology.mk Z n a)
    = cohomologyPullbackInt φ n (cohomologyPullbackInt ψ n (Cohomology.mk Z n a))
  rw [cohomologyPullbackInt_mk, cohomologyPullbackInt_mk, cohomologyPullbackInt_mk]
  congr 1

/-- **Pullback of the identity is the identity.** -/
theorem cohomologyPullbackInt_id {X : TopCat} (n : ℕ) :
    cohomologyPullbackInt (ContinuousMap.id ↑X) n = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show cohomologyPullbackInt (ContinuousMap.id ↑X) n (Cohomology.mk X n a) = Cohomology.mk X n a
  rw [cohomologyPullbackInt_mk]
  congr 1

/-- **The integral cohomology equivalence of a homeomorphism** `Hⁿ(Y;ℤ) ≃ₗ Hⁿ(X;ℤ)` (contravariant). -/
noncomputable def cohomologyHomeoEquivInt {X Y : TopCat} (e : ↑X ≃ₜ ↑Y) (n : ℕ) :
    Cohomology Y n ≃ₗ[ℤ] Cohomology X n :=
  LinearEquiv.ofLinear (cohomologyPullbackInt (⟨e, e.continuous⟩ : C(↑X, ↑Y)) n)
    (cohomologyPullbackInt (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)) n)
    (by
      rw [← cohomologyPullbackInt_comp,
        show (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)).comp
            (⟨e, e.continuous⟩ : C(↑X, ↑Y)) = ContinuousMap.id ↑X
          from ContinuousMap.ext (fun x => e.symm_apply_apply x),
        cohomologyPullbackInt_id])
    (by
      rw [← cohomologyPullbackInt_comp,
        show (⟨e, e.continuous⟩ : C(↑X, ↑Y)).comp
            (⟨e.symm, e.symm.continuous⟩ : C(↑Y, ↑X)) = ContinuousMap.id ↑Y
          from ContinuousMap.ext (fun y => e.apply_symm_apply y),
        cohomologyPullbackInt_id])

/-! ## Cup-pullback multiplicativity (Alexander–Whitney naturality) -/

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
theorem cochainPullbackInt_cup {X Y : TopCat} (φ : C(↑X, ↑Y)) {p q : ℕ}
    (f : SingularCochainInt Y p) (g : SingularCochainInt Y q) :
    cochainPullbackInt φ (p + q) (cup f g)
      = cup (cochainPullbackInt φ p f) (cochainPullbackInt φ q g) := by
  funext σ
  show cup f g (mapSimplex φ σ)
    = f (mapSimplex φ (frontFace σ)) * g (mapSimplex φ (backFace σ))
  rw [cup_apply, frontFace_mapSimplex, backFace_mapSimplex]

/-- **`cupH24`-pullback compatibility**: `φ*(a ∪ b) = φ*a ∪ φ*b` on `H² × H² → H⁴`. The tool the
S²×S² intersection form's diagonal-vanishing consumes: a factor-pullback square is the pullback of a
cup product living in `H⁴` of a single 2-sphere factor. -/
theorem cohomologyPullbackInt_cupH24 {X Y : TopCat} (φ : C(↑X, ↑Y))
    (a : Cohomology Y 2) (b : Cohomology Y 2) :
    cohomologyPullbackInt φ 4 (cupH24 a b)
      = cupH24 (cohomologyPullbackInt φ 2 a) (cohomologyPullbackInt φ 2 b) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  exact congrArg Submodule.Quotient.mk (Subtype.ext (cochainPullbackInt_cup φ fa.1 fb.1))

/-- **The descended integral Kronecker adjunction** `⟨φ*ω, β⟩ = ⟨ω, φ₊β⟩` on (co)homology classes. -/
theorem kroneckerHInt_cohomologyPullbackInt {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ}
    (ω : Cohomology Y n) (β : Homology X n) :
    kroneckerHInt (X := X) n (cohomologyPullbackInt φ n ω) β
      = kroneckerHInt (X := Y) n ω (Homology.mapInt φ n β) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  show kronecker (cochainPullbackInt φ n a.1) c.1 = kronecker a.1 (mapChainInt φ n c.1)
  exact kronecker_cochainPullbackInt φ a.1 c.1

end SKEFTHawking.SingularCohomologyFunctorialityInt
