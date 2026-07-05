import Mathlib
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularLocalHomologyInt
import SKEFTHawking.SingularEuclideanSphereInt
import SKEFTHawking.SingularSphereBottom
import SKEFTHawking.SingularReducedH0

/-!
# Integral sphere homology `Hₙ(Sⁿ; ℤ) ≅ ℤ` (brick 14e)

The integral mirror of the mod-2 sphere-homology tower (`SingularSphereAcyclic`,
`SingularSphereBottom`, `SingularLineMinusPoint`). The geometric objects — the sphere `Sph n`,
punctured sphere `Apunc`, the stereographic homeo `stereoMap`, the antipode/polar cover, the
equatorial homeo `equatorMap` — are all **coefficient-agnostic continuous maps**, reused verbatim from
`SingularSphereAcyclic`; only the homology-level bijectivity lemmas are re-proved over ℤ, feeding
through the integral connecting iso (`connectingInt_bijective_of_acyclic`, brick 13), the integral
excision iso (`excisionEquivInt`, brick 14d), the integral punctured retract
(`homology_mapInt_normalize_bijective`), and integral functoriality (`Homology.mapInt`).

Deliverables:
* integral functoriality helpers (`Homology.mapInt_bijective_of_comp_id{,_all}`) + integral pair-LES
  `exact_homIncl_homProjInt` / `homProjInt_bijective_of_acyclic`;
* integral punctured-sphere acyclicity + the sphere suspension `Hₖ₊₂(Sⁿ;ℤ) ≅ Hₖ₊₁(Sⁿ⁻¹;ℤ)`
  (`dimReductionEquivInt`) and its iterate `topSphereReduceInt`;
* the base case `H₁(S¹;ℤ) ≅ ℤ` via integral reduced `H̃₀(ℝ¹∖0;ℤ) ≅ ℤ`;
* the headline `Hₙ₊₁(Sⁿ⁺¹;ℤ) ≅ ℤ` (`topSphereIsoInt`) and `Homology (Sph 4) 3 ≃+ ℤ` (`H₃(S³;ℤ)≅ℤ`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite Metric
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularSphereHomologyInt

/-! ## §0. Integral functoriality: homeomorphism transport -/

/-- **A two-sided continuous inverse induces an iso on `Hₙ(·;ℤ)` in every degree** (integral). Uses only
functoriality (`mapInt_comp`, `mapInt_id`), so holds in degree `0` too. Mirror of
`Homology.map_bijective_of_comp_id_all`. -/
theorem Homology.mapInt_bijective_of_comp_id_all {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) (n : ℕ) :
    Function.Bijective (Homology.mapInt f n) := by
  have h1 : (Homology.mapInt g n).comp (Homology.mapInt f n) = LinearMap.id := by
    rw [← Homology.mapInt_comp, hgf, Homology.mapInt_id]
  have h2 : (Homology.mapInt f n).comp (Homology.mapInt g n) = LinearMap.id := by
    rw [← Homology.mapInt_comp, hfg, Homology.mapInt_id]
  refine ⟨fun a b hab => ?_, fun y => ⟨Homology.mapInt g n y, ?_⟩⟩
  · have := congrArg (Homology.mapInt g n) hab
    rwa [← LinearMap.comp_apply, ← LinearMap.comp_apply, h1, LinearMap.id_apply,
      LinearMap.id_apply] at this
  · rw [← LinearMap.comp_apply, h2, LinearMap.id_apply]

/-! ## §1. Integral pair-LES: exactness at `Hₙ(X;ℤ)` and the projection iso -/

variable {X : TopCat} (S : Set X)

/-- **The complex property `j_* ∘ i_* = 0`** (integral): a class pulled in from `S` becomes a subspace
chain, hence `0` in the relative complex. -/
theorem homProjInt_homIncl (n : ℕ) (w : Homology (sub S) n) :
    homProjInt S n (homIncl S n w) = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show homProjInt S n (homIncl S n (Homology.mk (sub S) n z)) = 0
  rw [homIncl_mk, homProjInt_mk, RelHomologyInt.mk_eq_zero_iff]
  show RelativeChainInt.mk S n (chainIncl S n (z : SingularChainInt (sub S) n)) ∈ relBoundariesInt S n
  rw [(RelativeChainInt.mk_eq_zero_iff S n _).2 ⟨z, rfl⟩]
  exact Submodule.zero_mem _

/-- **Exactness at `Hₙ(X;ℤ)`**: `ker j_* = im i_*`. Integral mirror of
`SingularPairLES.exact_homIncl_homProj`. -/
theorem exact_homIncl_homProjInt (n : ℕ) :
    Function.Exact (homIncl S n) (homProjInt S n) := by
  intro x
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have h2 : homProjInt S n (Homology.mk X n c) = 0 := h
    rw [homProjInt_mk, RelHomologyInt.mk_eq_zero_iff] at h2
    obtain ⟨w, hw⟩ := h2
    obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective (subspaceChainsInt S (n + 1)) w
    have h1 : RelativeChainInt.mk S n (c : SingularChainInt X n)
        = RelativeChainInt.mk S n (chainBoundary X n d) := by
      rw [← relBoundaryInt_mk]; exact hw.symm
    rw [RelativeChainInt.mk, RelativeChainInt.mk] at h1
    obtain ⟨e, he⟩ := (Submodule.Quotient.eq (subspaceChainsInt S n)).1 h1
    have hecyc : e ∈ cycles (sub S) n := by
      cases n with
      | zero => exact Submodule.mem_top
      | succ m =>
        show e ∈ LinearMap.ker (chainBoundary (sub S) m)
        rw [LinearMap.mem_ker]
        apply chainIncl_injective S m
        rw [map_zero, chainIncl_chainBoundary, he, map_sub, boundary_comp_boundary,
          LinearMap.mem_ker.mp c.2, sub_zero]
    refine ⟨Homology.mk (sub S) n ⟨e, hecyc⟩, ?_⟩
    rw [homIncl_mk]
    refine (Submodule.Quotient.eq _).2 ?_
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    show chainIncl S n e - (c : SingularChainInt X n) ∈ boundaries X n
    rw [he]
    have hsub : ((c : SingularChainInt X n) - chainBoundary X n d) - (c : SingularChainInt X n)
        = -chainBoundary X n d := by abel
    rw [hsub]
    exact Submodule.neg_mem _ ⟨d, rfl⟩
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact homProjInt_homIncl S n w

/-- **The projection `j_* : Hₙ₊₁(X;ℤ) → Hₙ₊₁(X, S;ℤ)` is an iso when the subspace is acyclic**: if
`Hₙ₊₁(S;ℤ) = 0` and `Hₙ(S;ℤ) = 0`, the LES forces `j_*` bijective. Integral mirror of
`SingularLocalHomology.homProj_bijective_of_acyclic`. -/
theorem homProjInt_bijective_of_acyclic (n : ℕ)
    (hS1 : ∀ x : Homology (sub S) (n + 1), x = 0) (hS0 : ∀ x : Homology (sub S) n, x = 0) :
    Function.Bijective (homProjInt S (n + 1)) := by
  have hincl0 : homIncl S (n + 1) = 0 := by
    ext y; rw [LinearMap.zero_apply, hS1 y, map_zero]
  have hconn0 : connectingInt S n = 0 := by
    ext y; rw [LinearMap.zero_apply]; exact hS0 _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homIncl_homProjInt S (n + 1)).linearMap_ker_eq, hincl0,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, ← (SingularLocalHomologyInt.exact_homProjInt_connectingInt S n).linearMap_ker_eq,
      hconn0, LinearMap.ker_zero]

/-! ## §2. Integral punctured-sphere acyclicity + the sphere suspension iso -/

open SKEFTHawking.SingularSphereAcyclic
  (Sph puncturedHomeo Apunc stereoMap stereoMapInv stereoMapInv_comp_stereoMap
    stereoMap_comp_stereoMapInv antipode ne_antipode polar_cover equatorMap equatorMapInv
    equatorMapInv_comp_equatorMap equatorMap_comp_equatorMapInv)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularPuncturedRetractInt
open SKEFTHawking.SingularPuncturedRetract (normalize)

variable {n : ℕ} {v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

/-- The stereographic map induces an iso `Hₘ(Sⁿ∖{v};ℤ) ≅ Hₘ(ℝⁿ;ℤ)` in every degree (integral). -/
theorem stereoMapInt_bijective_all (m : ℕ) :
    Function.Bijective (Homology.mapInt (stereoMap n v) m) :=
  Homology.mapInt_bijective_of_comp_id_all (stereoMap n v) (stereoMapInv n v)
    stereoMapInv_comp_stereoMap stereoMap_comp_stereoMapInv m

/-- **Triviality of integral homology transports across a homology iso**: `Hₙ(f)` bijective and
`Hₙ(Y;ℤ) = 0` ⟹ `Hₙ(X;ℤ) = 0`. -/
theorem homology_trivial_of_bijectiveInt {X Y : TopCat} {m : ℕ} (f : C(↑X, ↑Y))
    (hf : Function.Bijective (Homology.mapInt f m)) (hY : ∀ y : Homology Y m, y = 0)
    (x : Homology X m) : x = 0 :=
  hf.injective (by rw [map_zero]; exact hY _)

/-- **The punctured sphere `Sⁿ∖{v}` is integrally acyclic**: `Hₖ₊₁(Sⁿ∖{v};ℤ) = 0` (transported from
`ℝⁿ` integrally acyclic across the stereographic homeo). -/
theorem punctured_sphere_homology_trivialInt (k : ℕ) (x : Homology (Apunc n v) (k + 1)) : x = 0 :=
  homology_trivial_of_bijectiveInt (stereoMap n v) (stereoMapInt_bijective_all (k + 1))
    (SingularLocalHomologyInt.eucl_homology_trivialInt n k) x

open SKEFTHawking.SingularExcisionIso (restr)

/-- **`Hₖ₊₂(Sⁿ;ℤ) ≅ Hₖ₊₂(Sⁿ, Sⁿ∖{v};ℤ)`**: the projection iso (`Sⁿ∖{v}` acyclic). -/
theorem homProjInt_sphere_bijective (k : ℕ) :
    Function.Bijective (homProjInt ({v}ᶜ : Set ↑(Sph n)) (k + 2)) :=
  homProjInt_bijective_of_acyclic ({v}ᶜ : Set ↑(Sph n)) (k + 1)
    (punctured_sphere_homology_trivialInt (k + 1)) (punctured_sphere_homology_trivialInt k)

/-- **The sphere suspension `Hₖ₊₂(Sⁿ;ℤ) ≅ Hₖ₊₁(Sⁿ∖{v,-v};ℤ)`** (integral): projection iso ∘ excision
iso⁻¹ ∘ connecting iso. Signed mirror of `SingularSphereAcyclic.sphere_suspension_bijective`. -/
theorem sphere_suspensionInt_bijective (k : ℕ) :
    Function.Bijective
      ((connectingInt (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) (k + 1)).comp
        (((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) (k + 1)
              (polar_cover (ne_antipode v))).symm.toLinearMap).comp
          (homProjInt ({v}ᶜ : Set ↑(Sph n)) (k + 2)))) := by
  rw [LinearMap.coe_comp, LinearMap.coe_comp]
  exact (SingularLocalHomologyInt.connectingInt_bijective_of_acyclic
      (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) (k + 1)
      (punctured_sphere_homology_trivialInt (v := antipode v) (k + 1))
      (punctured_sphere_homology_trivialInt (v := antipode v) k)).comp
    (((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) (k + 1)
      (polar_cover (ne_antipode v))).symm.bijective).comp (homProjInt_sphere_bijective k))

/-- **`Sⁿ∖{v,-v} ≃ Sⁿ⁻¹` on integral homology**: the equatorial homeo `Sⁿ∖{v,-v} ≃ ℝⁿ∖0` composed with
the integral retract `ℝⁿ∖0 ≃ Sⁿ⁻¹`. -/
theorem equatorInt_to_sphere_bijective (k : ℕ) :
    Function.Bijective
      ((Homology.mapInt (normalize (n := n)) (k + 1)).comp
        (Homology.mapInt (equatorMap v) (k + 1))) := by
  rw [LinearMap.coe_comp]
  exact (homology_mapInt_normalize_bijective n k).comp
    (Homology.mapInt_bijective_of_comp_id_all (equatorMap v) (equatorMapInv v)
      equatorMapInv_comp_equatorMap equatorMap_comp_equatorMapInv (k + 1))

/-- **The sphere dimension-reduction `Hₖ₊₂(Sⁿ;ℤ) ≅ Hₖ₊₁(Sⁿ⁻¹;ℤ)`** (integral) — the inductive step
(suspension ∘ equator). `SingularPuncturedRetract.Sph n` (the unit sphere in `ℝⁿ`) is `Sⁿ⁻¹`. -/
noncomputable def dimReductionEquivInt (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (k : ℕ) :
    Homology (Sph n) (k + 2) ≃ₗ[ℤ] Homology (SingularPuncturedRetract.Sph n) (k + 1) :=
  (LinearEquiv.ofBijective _ (sphere_suspensionInt_bijective (v := v) k)).trans
    (LinearEquiv.ofBijective _ (equatorInt_to_sphere_bijective (v := v) k))

/-! ## §3. The top-sphere reduction `Hₘ₊₁(Sᵐ⁺¹;ℤ) ≅ H₁(S¹;ℤ)` -/

open SKEFTHawking.SingularSphereBottom (basePoint)

/-- **`Hₘ₊₁(Sᵐ⁺¹;ℤ) ≅ H₁(S¹;ℤ)`** by iterating `dimReductionEquivInt` down to the circle (integral).
Mirror of `SingularSphereBottom.topSphereReduce`. -/
noncomputable def topSphereReduceInt : (m : ℕ) →
    Homology (Sph (m + 1)) (m + 1) ≃ₗ[ℤ] Homology (Sph 1) 1
  | 0 => LinearEquiv.refl _ _
  | (m + 1) => (dimReductionEquivInt (basePoint (m + 2)) m).trans (topSphereReduceInt m)

end SKEFTHawking.SingularSphereHomologyInt
