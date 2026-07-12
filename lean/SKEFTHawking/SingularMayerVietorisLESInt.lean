/-
# Phase 5q.H (E1 integral topology) — the absolute homology Mayer–Vietoris maps
# `Hₙ(A∩B;ℤ) → Hₙ(A;ℤ)⊕Hₙ(B;ℤ) → Hₙ(X;ℤ)` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularMayerVietorisLES` — the "easy half" of the absolute homology
Mayer–Vietoris sequence of a space `X` under a two-set open cover `{A, B}`: the diagonal/sum maps and the
complex condition `Σ ∘ Δ = 0`. Built on the integral functoriality `Homology.mapInt` applied to the subspace
inclusions `subIncl`/`ambIncl` (coefficient-agnostic continuous maps, reused from the mod-2 module).

The mod-2 `mvHomSum` was a `coprod` (a difference over `ℤ/2`, where `+ = −`); over ℤ the sum is the honest
**difference** `(ι_A)_* u − (ι_B)_* v`, so the complex condition `Σ ∘ Δ = 0` closes by `sub_self` (both
inclusion routes `A∩B ↪ A ↪ X` and `A∩B ↪ B ↪ X` equal the single `A∩B ↪ X`) rather than `c + c = 0`.

The connecting map `δ : Hₙ₊₁(X;ℤ) → Hₙ(A∩B;ℤ)` (`mvConnectingInt`/`mvDeltaInt`) AND all three exactness
statements (`mv_exact_ambientInt`/`mv_exact_interInt`/`mv_exact_middleInt`) are IN THIS FILE — the integral
MV LES is COMPLETE (stale-header fix 2026-07-12 arm-2: the round-5 product-homology worker consumed the full
LES and flagged this paragraph, which still described them as future bricks).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularMayerVietorisLES
import SKEFTHawking.SingularSubsetHomologyInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.SingularLocalHomologyInt
import SKEFTHawking.SingularConvexRadialBaseInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)
open SKEFTHawking.SingularMayerVietorisLES
  (ambIncl subIncl ambIncl_comp_subIncl_left ambIncl_comp_subIncl_right seamHomeo)

namespace SKEFTHawking.SingularMayerVietorisLESInt

variable {X : TopCat}

/-- **The integral MV diagonal** `Hₙ(A∩B;ℤ) → Hₙ(A;ℤ) ⊕ Hₙ(B;ℤ)`, `w ↦ ((ι_A)_* w, (ι_B)_* w)`. -/
noncomputable def mvHomDiagInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub (A ∩ B)) n →ₗ[ℤ] Homology (sub A) n × Homology (sub B) n :=
  (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n).prod
    (Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n)

/-- **The integral MV sum** `Hₙ(A;ℤ) ⊕ Hₙ(B;ℤ) → Hₙ(X;ℤ)`, `(u, v) ↦ (ι_A)_* u − (ι_B)_* v` (the honest
ℤ-difference; the mod-2 `coprod` becomes a `sub`). -/
noncomputable def mvHomSumInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub A) n × Homology (sub B) n →ₗ[ℤ] Homology X n :=
  (Homology.mapInt (ambIncl A) n).comp (LinearMap.fst _ _ _)
    - (Homology.mapInt (ambIncl B) n).comp (LinearMap.snd _ _ _)

@[simp] theorem mvHomDiagInt_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomDiagInt A B n w
      = (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n w,
         Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n w) := rfl

@[simp] theorem mvHomSumInt_apply (A B : Set ↑X) (n : ℕ)
    (p : Homology (sub A) n × Homology (sub B) n) :
    mvHomSumInt A B n p
      = Homology.mapInt (ambIncl A) n p.1 - Homology.mapInt (ambIncl B) n p.2 := rfl

/-- **The integral MV chain-complex condition** `mvHomSumInt ∘ mvHomDiagInt = 0`: both inclusion routes
from `A∩B` land in `Hₙ(X;ℤ)` as the same map, so the difference is `c − c = 0`. -/
theorem mvHomSumInt_mvHomDiagInt (A B : Set ↑X) (n : ℕ) (w : Homology (sub (A ∩ B)) n) :
    mvHomSumInt A B n (mvHomDiagInt A B n w) = 0 := by
  rw [mvHomDiagInt_apply, mvHomSumInt_apply]
  rw [show Homology.mapInt (ambIncl A) n
          (Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n w)
        = Homology.mapInt (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ambIncl_comp_subIncl_left],
    show Homology.mapInt (ambIncl B) n
          (Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n w)
        = Homology.mapInt (ambIncl (A ∩ B)) n w by
        rw [← LinearMap.comp_apply, ← Homology.mapInt_comp, ambIncl_comp_subIncl_right]]
  exact sub_self _

/-! ## The integral Mayer–Vietoris connecting homomorphism `δ : Hₙ₊₁(X;ℤ) → Hₙ(A ∩ B;ℤ)` -/

/-- **The integral MV connecting homomorphism (pre-seam)** `Hₙ₊₁(X;ℤ) → Hₙ(sub (restr A B);ℤ)`, assembled
Barratt–Whitehead-style from the integral pair LES (`homProjInt`/`connectingInt`) and integral excision
(`excisionEquivInt`): project to the relative group, cross the excision iso backwards, then apply the pair
connecting map. Integral mirror of `SingularMayerVietorisLES.mvConnecting`. -/
noncomputable def mvConnectingInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ℤ] Homology (sub (restr A B)) n :=
  (connectingInt (restr A B) n).comp
    (((excisionEquivInt A B n hcov).symm.toLinearMap).comp (homProjInt A (n + 1)))

/-- The seam **homology isomorphism** `Hₙ(sub (restr A B);ℤ) ≅ Hₙ(sub (A ∩ B);ℤ)`, induced by the
(coefficient-agnostic) reassociation homeomorphism `seamHomeo A B` (a homeomorphism, so integral
functoriality + `mapInt_bijective_of_comp_id_all` give the iso in every degree). Bridges `mvConnectingInt`'s
codomain (`sub (restr A B)`) to `mvHomDiagInt`'s domain (`sub (A ∩ B)`). -/
noncomputable def seamHomologyEquivInt (A B : Set ↑X) (n : ℕ) :
    Homology (sub (restr A B)) n ≃ₗ[ℤ] Homology (sub (A ∩ B)) n :=
  LinearEquiv.ofBijective
    (Homology.mapInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n)
    (Homology.mapInt_bijective_of_comp_id_all ⟨seamHomeo A B, (seamHomeo A B).continuous⟩
      ⟨(seamHomeo A B).symm, (seamHomeo A B).symm.continuous⟩
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl) n)

@[simp] theorem seamHomologyEquivInt_apply (A B : Set ↑X) (n : ℕ) (w : Homology (sub (restr A B)) n) :
    seamHomologyEquivInt A B n w
      = Homology.mapInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n w := rfl

/-- **The integral Mayer–Vietoris connecting map** `δ : Hₙ₊₁(X;ℤ) → Hₙ(A ∩ B;ℤ)` in the `sub (A ∩ B)`
representation — `mvConnectingInt` post-composed with the seam iso, so its codomain matches `mvHomDiagInt`'s
domain. Closes the bottom-row integral MV LES
`⋯ → Hₙ₊₁(X;ℤ) →[δ] Hₙ(A∩B;ℤ) →[mvHomDiagInt] Hₙ(A;ℤ)⊕Hₙ(B;ℤ) →[mvHomSumInt] Hₙ(X;ℤ) → ⋯`. -/
noncomputable def mvDeltaInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Homology X (n + 1) →ₗ[ℤ] Homology (sub (A ∩ B)) n :=
  (seamHomologyEquivInt A B n).toLinearMap.comp (mvConnectingInt A B n hcov)

/-! ## Naturality bridges for the connecting map (excision Barratt–Whitehead square) -/

/-- The inclusion `A ∩ B ↪ A`, from the `restr A B` (inside `sub B`) representation, as a `ContinuousMap`
`sub (restr A B) → sub A` (`p.1 ∈ restr A B = Subtype.val ⁻¹' A` gives `p.1.1 ∈ A`). Coefficient-agnostic
mirror of `SingularMayerVietorisLES.inclRA`. -/
def inclRAInt (A B : Set ↑X) : C(↥(sub (restr A B)), ↥(sub A)) :=
  ⟨fun p => ⟨p.1.1, p.2⟩, by fun_prop⟩

/-- **The `Homology.mapInt ↔ homIncl` bridge**: `Homology.mapInt (ambIncl S) = homIncl S` — the LES-side
functorial pushforward and the pair-LES inclusion-induced map coincide (both descend from `chainIncl` via
`mapChainInt_ambIncl`). Lets the integral MV exactness reuse the pair-LES `homIncl_connectingInt` etc.
Integral mirror of `SingularMayerVietorisLES.Homology.map_ambIncl`. -/
theorem Homology.mapInt_ambIncl (S : Set ↑X) (n : ℕ) :
    Homology.mapInt (ambIncl S) n = homIncl S n := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Homology.mapInt (ambIncl S) n (Homology.mk (sub S) n z) = homIncl S n (Homology.mk (sub S) n z)
  rw [Homology.mapInt_mk, homIncl_mk]
  exact congrArg (Homology.mk X n)
    (Subtype.ext (by rw [cyclesMapInt_coe, mapChainInt_ambIncl]))

/-- **Naturality of the connecting map under excision** (the integral Barratt–Whitehead square): the
inclusion `A ∩ B ↪ A` after the `(B, A∩B)` connecting map equals the `(X, A)` connecting map after excision.
The crux of integral MV exactness at `Hₙ(A∩B)` and `Hₙ(X)`. Integral mirror of
`SingularMayerVietorisLES.inclRA_connecting`. -/
theorem inclRA_connectingInt (A B : Set ↑X) (n : ℕ) (y : RelHomologyInt (restr A B) (n + 1)) :
    Homology.mapInt (inclRAInt A B) n (connectingInt (restr A B) n y)
      = connectingInt A n (excisionMapInt A B (n + 1) y) := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective (restr A B) n y
  rw [connectingInt_relCycleToHom]
  have hc' : chainBoundary X n (chainIncl B (n + 1) (c : SingularChainInt (sub B) (n + 1)))
      ∈ subspaceChainsInt A n := by
    rw [← chainIncl_chainBoundary]
    exact (chainIncl_mem_subspaceChainsInt_iff A B _).2 (Submodule.mem_comap.mp c.2)
  have hexc : excisionMapInt A B (n + 1) (relCycleToHom (restr A B) n c)
      = relCycleToHom A n ⟨chainIncl B (n + 1) c, hc'⟩ := by
    rw [relCycleToHom_apply, excisionMapInt_mk, relCycleToHom_apply]
    exact congrArg (RelHomologyInt.mk A (n + 1)) (Subtype.ext (relChainInclInt_mk A B (n + 1) c))
  rw [hexc, connectingInt_relCycleToHom, connectingLift_apply, connectingLift_apply, Homology.mapInt_mk]
  refine congrArg (Homology.mk (sub A) n) (Subtype.ext ?_)
  rw [cyclesMapInt_coe]
  apply chainIncl_injective A n
  rw [chainIncl_boundaryExtract, ← chainIncl_chainBoundary,
    ← chainIncl_boundaryExtract (restr A B) n c, ← mapChainInt_ambIncl A, ← mapChainInt_ambIncl B,
    ← mapChainInt_ambIncl (restr A B), ← mapChainInt_comp, ← mapChainInt_comp]
  congr 1

/-- The `A`-inclusion after the seam iso is `Homology.mapInt (inclRAInt)` (functoriality;
`subIncl_{A∩B↪A} ∘ seamHomeo = inclRAInt`). -/
theorem map_subInclL_seamInt (A B : Set ↑X) (n : ℕ) (y : Homology (sub (restr A B)) n) :
    Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n (seamHomologyEquivInt A B n y)
      = Homology.mapInt (inclRAInt A B) n y := by
  rw [seamHomologyEquivInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The `B`-inclusion after the seam iso is `homIncl (restr A B)` (functoriality + the `mapInt ↔ homIncl`
bridge; `subIncl_{A∩B↪B} ∘ seamHomeo = ambIncl (restr A B)`). -/
theorem map_subInclR_seamInt (A B : Set ↑X) (n : ℕ) (y : Homology (sub (restr A B)) n) :
    Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n (seamHomologyEquivInt A B n y)
      = homIncl (restr A B) n y := by
  rw [seamHomologyEquivInt_apply, ← LinearMap.comp_apply, ← Homology.mapInt_comp,
    show (subIncl (Set.inter_subset_right (s := A) (t := B))).comp
          ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ = ambIncl (restr A B) from rfl,
    Homology.mapInt_ambIncl]

/-- **Excision–projection naturality** (integral): `excisionMapInt ∘ j_*^{(B,A∩B)} = j_*^{(X,A)} ∘ i_*^{B}`.
Both send a `(sub B)`-cycle to the class of its `chainIncl B` image in `(X,A)`. -/
theorem excisionMap_homProjInt (A B : Set ↑X) (n : ℕ) (v : Homology (sub B) (n + 1)) :
    excisionMapInt A B (n + 1) (homProjInt (restr A B) (n + 1) v)
      = homProjInt A (n + 1) (homIncl B (n + 1) v) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  show excisionMapInt A B (n + 1) (homProjInt (restr A B) (n + 1) (Homology.mk (sub B) (n + 1) z))
      = homProjInt A (n + 1) (homIncl B (n + 1) (Homology.mk (sub B) (n + 1) z))
  rw [homProjInt_mk, excisionMapInt_mk, homIncl_mk, homProjInt_mk]
  exact congrArg (RelHomologyInt.mk A (n + 1)) (Subtype.ext (relChainInclInt_mk A B (n + 1) z))

/-- The two routes `A∩B ↪ A ↪ X` and `A∩B ↪ B ↪ X` of a class agree (both are the single inclusion
`A∩B ↪ X`). Used in the middle MV exactness. -/
theorem homIncl_inclRAInt (A B : Set ↑X) (n : ℕ) (w : Homology (sub (restr A B)) n) :
    homIncl A n (Homology.mapInt (inclRAInt A B) n w) = homIncl B n (homIncl (restr A B) n w) := by
  rw [← Homology.mapInt_ambIncl A, ← Homology.mapInt_ambIncl B, ← Homology.mapInt_ambIncl (restr A B),
    ← LinearMap.comp_apply, ← Homology.mapInt_comp, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-! ## The integral Mayer–Vietoris complex conditions and exactness -/

/-- **Integral MV complex condition at `Hₙ(A∩B)`**: `mvHomDiagInt ∘ δ = 0`. -/
theorem mvHomDiagInt_mvDeltaInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) (x : Homology X (n + 1)) :
    mvHomDiagInt A B n (mvDeltaInt A B n hcov x) = 0 := by
  refine Prod.ext ?_ ?_
  · show Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n
        (seamHomologyEquivInt A B n (connectingInt (restr A B) n
          ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) x)))) = 0
    rw [map_subInclL_seamInt, inclRA_connectingInt,
      show excisionMapInt A B (n + 1) ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) x))
        = homProjInt A (n + 1) x from (excisionEquivInt A B n hcov).apply_symm_apply _,
      connectingInt_homProjInt]
  · show Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n
        (seamHomologyEquivInt A B n (connectingInt (restr A B) n
          ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) x)))) = 0
    rw [map_subInclR_seamInt, SingularLocalHomologyInt.homIncl_connectingInt]

/-- **Integral MV complex condition at `Hₙ(X)`**: `δ ∘ mvHomSumInt = 0`. The `A`-summand dies under
`homProjInt A` (`homProjInt_homIncl`); the `B`-summand is excision of the `(B,A∩B)`-projection
(`excisionMap_homProjInt`), so after `excisionEquivInt.symm` it is `∓ j_*^{(B,A∩B)} v`, killed by
`connectingInt_homProjInt`. The mod-2 `zero_add` becomes `zero_sub`/`map_neg` (the ℤ-difference). -/
theorem mvDeltaInt_mvHomSumInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (uv : Homology (sub A) (n + 1) × Homology (sub B) (n + 1)) :
    mvDeltaInt A B n hcov (mvHomSumInt A B (n + 1) uv) = 0 := by
  obtain ⟨u, v⟩ := uv
  have hp : homProjInt A (n + 1) (mvHomSumInt A B (n + 1) (u, v))
      = -excisionMapInt A B (n + 1) (homProjInt (restr A B) (n + 1) v) := by
    rw [mvHomSumInt_apply, map_sub, Homology.mapInt_ambIncl, Homology.mapInt_ambIncl,
      SingularSphereHomologyInt.homProjInt_homIncl, zero_sub, excisionMap_homProjInt]
  show seamHomologyEquivInt A B n (connectingInt (restr A B) n
      ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) (mvHomSumInt A B (n + 1) (u, v))))) = 0
  rw [hp, map_neg,
    show (excisionEquivInt A B n hcov).symm (excisionMapInt A B (n + 1) (homProjInt (restr A B) (n + 1) v))
        = homProjInt (restr A B) (n + 1) v from (excisionEquivInt A B n hcov).symm_apply_apply _,
    map_neg, connectingInt_homProjInt, neg_zero, map_zero]

/-- **Integral MV exactness at `Hₙ(X)`**: `Function.Exact mvHomSumInt mvDeltaInt`. The Barratt–Whitehead
chase; the witness is `(u', -v')` (the ℤ-difference `mvHomSumInt` needs the negated `B`-component to
reproduce the sum `homIncl A u' + homIncl B v' = w`). -/
theorem mv_exact_ambientInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Function.Exact (mvHomSumInt A B (n + 1)) (mvDeltaInt A B n hcov) := by
  intro w
  refine ⟨fun hw => ?_, fun hr => ?_⟩
  · have h1 : connectingInt (restr A B) n
        ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) w)) = 0 :=
      (seamHomologyEquivInt A B n).injective (by rw [map_zero]; exact hw)
    obtain ⟨v', hv'⟩ := (SingularLocalHomologyInt.exact_homProjInt_connectingInt (restr A B) n _).mp h1
    have h2 : homProjInt A (n + 1) (w - homIncl B (n + 1) v') = 0 := by
      rw [map_sub, ← excisionMap_homProjInt, hv',
        show excisionMapInt A B (n + 1) ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) w))
          = homProjInt A (n + 1) w from (excisionEquivInt A B n hcov).apply_symm_apply _, sub_self]
    obtain ⟨u', hu'⟩ := (SingularSphereHomologyInt.exact_homIncl_homProjInt A (n + 1) _).mp h2
    refine ⟨(u', -v'), ?_⟩
    show Homology.mapInt (ambIncl A) (n + 1) u' - Homology.mapInt (ambIncl B) (n + 1) (-v') = w
    rw [Homology.mapInt_ambIncl, Homology.mapInt_ambIncl, map_neg, sub_neg_eq_add, hu', sub_add_cancel]
  · obtain ⟨uv, rfl⟩ := hr
    exact mvDeltaInt_mvHomSumInt A B n hcov uv

/-- **Integral MV exactness at `Hₙ(A∩B)`**: `Function.Exact mvDeltaInt mvHomDiagInt`. The `B`-component of
`mvHomDiagInt w = 0` gives `homIncl_{(B,A∩B)}(seam⁻¹ w) = 0`, so `seam⁻¹ w = connectingInt y'`; the
`A`-component + `inclRA_connectingInt` + `exact_homProjInt_connectingInt` produce `x` with
`homProjInt_A x = excisionMapInt y'`, whence `δ x = w`. -/
theorem mv_exact_interInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Function.Exact (mvDeltaInt A B n hcov) (mvHomDiagInt A B n) := by
  intro w
  refine ⟨fun hw => ?_, fun hr => ?_⟩
  · have hwA : Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) n w = 0 :=
      congrArg Prod.fst hw
    have hwB : Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) n w = 0 :=
      congrArg Prod.snd hw
    have hB : homIncl (restr A B) n ((seamHomologyEquivInt A B n).symm w) = 0 := by
      rw [← map_subInclR_seamInt, (seamHomologyEquivInt A B n).apply_symm_apply]; exact hwB
    obtain ⟨y', hy'⟩ := (SingularLocalHomologyInt.exact_connectingInt_homIncl (restr A B) n _).mp hB
    have hA : connectingInt A n (excisionMapInt A B (n + 1) y') = 0 := by
      rw [← inclRA_connectingInt, hy', ← map_subInclL_seamInt, (seamHomologyEquivInt A B n).apply_symm_apply]
      exact hwA
    obtain ⟨x, hx⟩ := (SingularLocalHomologyInt.exact_homProjInt_connectingInt A n _).mp hA
    refine ⟨x, ?_⟩
    show seamHomologyEquivInt A B n (connectingInt (restr A B) n
        ((excisionEquivInt A B n hcov).symm (homProjInt A (n + 1) x))) = w
    rw [hx, show (excisionEquivInt A B n hcov).symm (excisionMapInt A B (n + 1) y') = y' from
        (excisionEquivInt A B n hcov).symm_apply_apply _, hy', (seamHomologyEquivInt A B n).apply_symm_apply]
  · obtain ⟨x, rfl⟩ := hr
    exact mvHomDiagInt_mvDeltaInt A B n hcov x

/-- **Integral MV middle exactness** at `Hₙ₊₁(A) ⊕ Hₙ₊₁(B)`: `Function.Exact mvHomDiagInt mvHomSumInt`.
The Barratt–Whitehead chase; the ℤ-difference `mvHomSumInt` turns the mod-2 sums into differences
(`homIncl A u − homIncl B v = 0`, the combining witness `u − mapInt(inclRAInt) w''`, and `hu` closing by
`abel`). Integral mirror of `SingularMayerVietorisLES.mv_exact_middle`. -/
theorem mv_exact_middleInt (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ) :
    Function.Exact (mvHomDiagInt A B (n + 1)) (mvHomSumInt A B (n + 1)) := by
  intro uv
  refine ⟨fun huv => ?_, fun hr => ?_⟩
  · obtain ⟨u, v⟩ := uv
    have hsum : homIncl A (n + 1) u - homIncl B (n + 1) v = 0 := by
      simpa only [mvHomSumInt_apply, Homology.mapInt_ambIncl] using huv
    have h1 : homProjInt A (n + 1) (homIncl B (n + 1) v) = 0 := by
      have h := congrArg (homProjInt A (n + 1)) hsum
      rw [map_sub, SingularSphereHomologyInt.homProjInt_homIncl, zero_sub, map_zero, neg_eq_zero] at h
      exact h
    have h2 : homProjInt (restr A B) (n + 1) v = 0 := by
      apply excisionMapInt_injective A B n hcov
      rw [excisionMap_homProjInt, map_zero]; exact h1
    obtain ⟨w'', hw''⟩ := (SingularSphereHomologyInt.exact_homIncl_homProjInt (restr A B) (n + 1) _).mp h2
    have h4 : homIncl A (n + 1) (u - Homology.mapInt (inclRAInt A B) (n + 1) w'') = 0 := by
      rw [map_sub, homIncl_inclRAInt, hw'']; exact hsum
    obtain ⟨c', hc'⟩ := (SingularLocalHomologyInt.exact_connectingInt_homIncl A (n + 1) _).mp h4
    obtain ⟨c'', hc''⟩ := (excisionEquivInt A B (n + 1) hcov).surjective c'
    have hu : Homology.mapInt (inclRAInt A B) (n + 1) (w'' + connectingInt (restr A B) (n + 1) c'') = u := by
      rw [map_add, inclRA_connectingInt, show excisionMapInt A B (n + 2) c'' = c' from hc'', hc']
      abel
    refine ⟨seamHomologyEquivInt A B (n + 1) (w'' + connectingInt (restr A B) (n + 1) c''), ?_⟩
    refine Prod.ext ?_ ?_
    · show Homology.mapInt (subIncl (Set.inter_subset_left (s := A) (t := B))) (n + 1)
          (seamHomologyEquivInt A B (n + 1) (w'' + connectingInt (restr A B) (n + 1) c'')) = u
      rw [map_subInclL_seamInt]; exact hu
    · show Homology.mapInt (subIncl (Set.inter_subset_right (s := A) (t := B))) (n + 1)
          (seamHomologyEquivInt A B (n + 1) (w'' + connectingInt (restr A B) (n + 1) c'')) = v
      rw [map_subInclR_seamInt, map_add, hw'', SingularLocalHomologyInt.homIncl_connectingInt, add_zero]
  · obtain ⟨w, rfl⟩ := hr
    exact mvHomSumInt_mvHomDiagInt A B (n + 1) w

end SKEFTHawking.SingularMayerVietorisLESInt
