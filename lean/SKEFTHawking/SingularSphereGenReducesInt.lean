import Mathlib
import SKEFTHawking.SingularLocalHomologyRedCompatInt

/-!
# `SphereGenReducesNonzero`: the ℤ→ℤ/2 reduction of the `H₃(S³;ℤ)` generator is nonzero (brick 17)

Discharges the single non-functorial residual of the integral local-homology `redCompat` tower
(`SingularLocalHomologyRedCompatInt.SphereGenReducesNonzero`): the ℤ→ℤ/2 reduction of the integral
generator of `H₃(S³;ℤ)` (`H3S3IsoInt.symm 1`) is nonzero in the mod-2 group `H₃(S³;ℤ/2)`.

Strategy. Both `H3S3IsoInt` and the mod-2 `topSphereIso 2` compose the SAME tower of primitive maps
(`connectingInt`/`connecting`, `excisionEquivInt`/`excisionEquiv`, `homProjInt`/`homProj`,
`Homology.mapInt`/`Homology.map`, plus the base `ker ε̄` iso). Each primitive commutes with the ℤ→ℤ/2
reduction bridge (`SingularLocalHomologyRedCompatInt` §1–§10 + this file's base square). Composing the
per-stage squares gives the sphere-level `redCompat`
`topSphereIso 2 (redHomology z) = ((H3S3IsoInt z : ℤ) : ZMod 2)`; at `z = H3S3IsoInt.symm 1` the RHS
is `1 ≠ 0`, so `redHomology (H3S3IsoInt.symm 1) ≠ 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularSphereGenReducesInt

open SKEFTHawking.SingularLineMinusPointInt
open SKEFTHawking.SingularLineMinusPoint

/-! ## §1. Base square: the reduction intertwines `augHInt` and `augH` -/

/-- **The reduction commutes with the integral/mod-2 augmentation (chain level).**
`augmentation X (redChain X 0 c) = ((augmentationInt X c : ℤ) : ZMod 2)`. Both augmentations are the
coefficient-sum; `redChain` is the pointwise cast, and casting commutes with the sum. -/
theorem augmentation_redChain (X : TopCat) (c : SingularChainInt X 0) :
    SKEFTHawking.SingularH0.augmentation X (redChain X 0 c)
      = ((SKEFTHawking.SingularLineMinusPointInt.augmentationInt X c : ℤ) : ZMod 2) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, ← Int.cast_add, map_add]
  | single σ a =>
      rw [redChain_single,
        SKEFTHawking.SingularH0.augmentation_single,
        SKEFTHawking.SingularLineMinusPointInt.augmentationInt_single]

/-- **The reduction commutes with the augmentation on homology.**
`augH X (redHomology X 0 h) = ((augHInt X h : ℤ) : ZMod 2)`. -/
theorem augH_redHomology (X : TopCat) (h : Homology X 0) :
    SKEFTHawking.SingularH0.augH X (redHomology X 0 h)
      = ((SKEFTHawking.SingularLineMinusPointInt.augHInt X h : ℤ) : ZMod 2) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  show SKEFTHawking.SingularH0.augH X (redHomology X 0 (Homology.mk X 0 z))
    = ((SKEFTHawking.SingularLineMinusPointInt.augHInt X (Homology.mk X 0 z) : ℤ) : ZMod 2)
  rw [redHomology_mk, SKEFTHawking.SingularH0.augH_mk,
    SKEFTHawking.SingularLineMinusPointInt.augHInt_mk]
  exact augmentation_redChain X (z : SingularChainInt X 0)

/-! ## §2. `π : ker(ε̄_ℤ) ≃ ℤ` — the anti-diagonal projection, and generators are odd -/

open SKEFTHawking.SingularH0 (augH)
open SKEFTHawking.SingularDisjointUnion (splitH0 splitH0Equiv)

variable {X : TopCat} {U : Set ↑X}

/-- **The anti-diagonal projection** `π : ker(ε̄_ℤ) →ₗ[ℤ] ℤ`, `x ↦ ε̄_U (fst (splitH0IntEquiv⁻¹ x))`.
The `U`-component of the integral additivity decomposition, then the `U`-augmentation. On `ker(ε̄_X)`
this is a linear isomorphism onto `ℤ` (the anti-diagonal `{(a,-a)} ≅ ℤ` picking off `a`). -/
noncomputable def antiDiagProjInt (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U))) :
    ↥(LinearMap.ker (augHInt X)) →ₗ[ℤ] ℤ :=
  (augHInt (sub U)).comp
    ((LinearMap.fst ℤ (Homology (sub U) 0) (Homology (sub Uᶜ) 0)).comp
      ((splitH0IntEquiv hU).symm.toLinearMap.comp (LinearMap.ker (augHInt X)).subtype))

/-- **`antiDiagProjInt` is bijective** — `ker(ε̄_X) ≃ ℤ`. Injective: `π x = 0 ⟹ ε̄_U a = 0 ⟹ a = 0`
(iso), and on `ker`, `ε̄_Uᶜ b = -ε̄_U a = 0 ⟹ b = 0`, so `x.1 = split(0,0) = 0`. Surjective: given
`n`, take `a = eU⁻¹ n`, `b = eUc⁻¹(-n)`; then `ε̄_U a + ε̄_Uᶜ b = 0` so `split(a,b) ∈ ker` and `π = n`. -/
theorem antiDiagProjInt_bijective (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U)))
    (hUcbij : Function.Bijective (augHInt (sub Uᶜ))) :
    Function.Bijective (antiDiagProjInt (X := X) hU hUbij) := by
  let eU := LinearEquiv.ofBijective (augHInt (sub U)) hUbij
  let eUc := LinearEquiv.ofBijective (augHInt (sub Uᶜ)) hUcbij
  constructor
  · -- injective
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨x, hx⟩ hxk
    rw [Submodule.mem_bot]
    rw [LinearMap.mem_ker] at hxk
    -- decompose x = split (a, b)
    obtain ⟨⟨a, b⟩, hab⟩ := (splitH0IntEquiv hU).surjective x
    have haU0 : augHInt (sub U) a = 0 := by
      have heq : antiDiagProjInt (X := X) hU hUbij ⟨x, hx⟩ = augHInt (sub U) a := by
        show augHInt (sub U) ((splitH0IntEquiv hU).symm x).1 = augHInt (sub U) a
        rw [← hab, (splitH0IntEquiv hU).symm_apply_apply]
      rw [heq] at hxk; exact hxk
    have ha0 : a = 0 := eU.injective (by rw [show eU a = augHInt (sub U) a from rfl, haU0]; simp)
    -- on ker: ε̄_U a + ε̄_Uᶜ b = 0, with ε̄_U a = 0, so ε̄_Uᶜ b = 0, so b = 0
    have hsum : augHInt (sub U) a + augHInt (sub Uᶜ) b = 0 := by
      have hxker : augHInt X x = 0 := hx
      rw [← hab] at hxker
      rw [show (splitH0IntEquiv hU) (a, b) = splitH0Int U (a, b) from rfl,
        augHInt_splitH0Int] at hxker
      exact hxker
    have hbUc0 : augHInt (sub Uᶜ) b = 0 := by rw [haU0, zero_add] at hsum; exact hsum
    have hb0 : b = 0 := eUc.injective (by rw [show eUc b = augHInt (sub Uᶜ) b from rfl, hbUc0]; simp)
    apply Subtype.ext
    show x = (0 : Homology X 0)
    rw [← hab, ha0, hb0]
    show (splitH0IntEquiv hU) (0, 0) = (0 : Homology X 0)
    rw [show ((0 : Homology (sub U) 0), (0 : Homology (sub Uᶜ) 0)) = (0 : Homology (sub U) 0 × Homology (sub Uᶜ) 0) from rfl,
      map_zero]
  · -- surjective
    intro n
    refine ⟨⟨(splitH0IntEquiv hU) (eU.symm n, eUc.symm (-n)), ?_⟩, ?_⟩
    · show augHInt X ((splitH0IntEquiv hU) (eU.symm n, eUc.symm (-n))) = 0
      rw [show (splitH0IntEquiv hU) (eU.symm n, eUc.symm (-n)) = splitH0Int U (eU.symm n, eUc.symm (-n))
            from rfl, augHInt_splitH0Int]
      show eU (eU.symm n) + eUc (eUc.symm (-n)) = 0
      rw [eU.apply_symm_apply, eUc.apply_symm_apply, add_neg_cancel]
    · show augHInt (sub U) ((splitH0IntEquiv hU).symm
          ((splitH0IntEquiv hU) (eU.symm n, eUc.symm (-n)))).1 = n
      rw [(splitH0IntEquiv hU).symm_apply_apply]
      show eU (eU.symm n) = n
      rw [eU.apply_symm_apply]

/-! ## §3. Reduction commutes with the degree-0 split, and the base generator reduces nonzero -/

open SKEFTHawking.SingularLocalHomologyRedCompatInt (redHomology_homIncl)

/-- **The reduction commutes with the integral additivity map** `splitH0Int`:
`redHomology X 0 (splitH0Int U p) = splitH0 U (redHomology p.1, redHomology p.2)`. Both are the
coprod of the two `homIncl`s; `redHomology_homIncl` (brick 16 §10) commutes reduction with each. -/
theorem redHomology_splitH0Int (U : Set ↑X)
    (p : Homology (sub U) 0 × Homology (sub Uᶜ) 0) :
    redHomology X 0 (splitH0Int U p)
      = splitH0 U (redHomology (sub U) 0 p.1, redHomology (sub Uᶜ) 0 p.2) := by
  show redHomology X 0 (homIncl U 0 p.1 + homIncl Uᶜ 0 p.2)
    = SKEFTHawking.SingularPairLES.homIncl U 0 (redHomology (sub U) 0 p.1)
      + SKEFTHawking.SingularPairLES.homIncl Uᶜ 0 (redHomology (sub Uᶜ) 0 p.2)
  rw [map_add, redHomology_homIncl, redHomology_homIncl]

/-- **The base-generator detector functional** `Λ : H₀(Punc 1;ℤ/2) →ₗ[ZMod 2] ZMod 2`, the mod-2
`U`-augmentation of the mod-2 additivity `U`-component. Detects the reduction of the integral `ker ε̄`
generator: `Λ (redHomology g) = ↑(antiDiagProjInt g)`. -/
noncomputable def baseDetector (hU : IsClopen U) :
    SKEFTHawking.SingularHomologyMod2.Homology X 0 →ₗ[ZMod 2] ZMod 2 :=
  (augH (sub U)).comp
    ((LinearMap.fst (ZMod 2) (SKEFTHawking.SingularHomologyMod2.Homology (sub U) 0)
        (SKEFTHawking.SingularHomologyMod2.Homology (sub Uᶜ) 0)).comp
      (splitH0Equiv hU).symm.toLinearMap)

/-- **The detector reads off the anti-diagonal projection after reduction.** For a class `x` in
`ker(augHInt X)`, `baseDetector (redHomology X 0 x) = ((antiDiagProjInt hU hUbij ⟨x,·⟩ : ℤ) : ZMod 2)`.
Chases: `split.symm (redHomology x) = (red aU, red bUc)` (`redHomology_splitH0Int` applied to
`x = splitH0Int (aU,bUc)`), then `augH_U (red aU) = ↑(augHInt_U aU) = ↑(antiDiagProjInt)`. -/
theorem baseDetector_redHomology (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U)))
    (x : Homology X 0) (hx : x ∈ LinearMap.ker (augHInt X)) :
    baseDetector (X := X) hU (redHomology X 0 x)
      = ((antiDiagProjInt (X := X) hU hUbij ⟨x, hx⟩ : ℤ) : ZMod 2) := by
  -- write `x = splitH0Int U (aU, bUc)`
  obtain ⟨⟨aU, bUc⟩, hab⟩ := (splitH0IntEquiv hU).surjective x
  have hsplitInt : splitH0Int U (aU, bUc) = x := by
    rw [← hab]; rfl
  -- LHS: baseDetector (redHomology x) = augH_U (fst (split.symm (redHomology x)))
  have hxred : (splitH0Equiv hU).symm (redHomology X 0 x)
      = (redHomology (sub U) 0 aU, redHomology (sub Uᶜ) 0 bUc) := by
    apply (splitH0Equiv hU).injective
    rw [LinearEquiv.apply_symm_apply]
    rw [← hsplitInt, redHomology_splitH0Int]
    rfl
  have hLHS : baseDetector (X := X) hU (redHomology X 0 x)
      = augH (sub U) (redHomology (sub U) 0 aU) := by
    show augH (sub U) ((splitH0Equiv hU).symm (redHomology X 0 x)).1 = _
    rw [hxred]
  rw [hLHS, augH_redHomology]
  -- RHS: antiDiagProjInt ⟨x,hx⟩ = augHInt_U aU
  congr 1
  show augHInt (sub U) aU = augHInt (sub U) ((splitH0IntEquiv hU).symm x).1
  rw [← hsplitInt, show splitH0Int U (aU, bUc) = (splitH0IntEquiv hU) (aU, bUc) from rfl,
    (splitH0IntEquiv hU).symm_apply_apply]

/-! ## §4. The base generator reduces nonzero -/

/-- **A ℤ-linear map bijective on `ker(ε̄_ℤ) ≅ ℤ` sends any `≅ℤ`-generator to `±1` (a unit).**
`antiDiagProjInt` is a linear iso `ker ≅ ℤ`; composed with the inverse of `e : ker ≃ ℤ` it is a
`ℤ`-linear automorphism of `ℤ`, so `antiDiagProjInt (e.symm 1)` is a unit. -/
theorem antiDiagProjInt_generator_isUnit (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U)))
    (hUcbij : Function.Bijective (augHInt (sub Uᶜ)))
    (e : ↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ℤ) :
    IsUnit (antiDiagProjInt (X := X) hU hUbij (e.symm 1)) := by
  set π := LinearEquiv.ofBijective (antiDiagProjInt (X := X) hU hUbij)
    (antiDiagProjInt_bijective hU hUbij hUcbij) with hπ
  -- φ := e.symm.trans π : ℤ ≃ₗ ℤ, and antiDiagProjInt (e.symm 1) = φ 1
  set φ : ℤ ≃ₗ[ℤ] ℤ := e.symm.trans π with hφ
  have hval : antiDiagProjInt (X := X) hU hUbij (e.symm 1) = φ 1 := rfl
  rw [hval]
  -- φ 1 * φ.symm 1 = φ (1 * φ.symm 1) ... use φ (φ.symm 1) = 1 and ℤ-linearity
  refine IsUnit.of_mul_eq_one (φ.symm 1) ?_
  have h2 : (φ.symm 1) * φ 1 = 1 := by
    rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, φ.apply_symm_apply]
  rw [mul_comm]; exact h2

/-- **The reduction of the integral `ker ε̄` generator is nonzero** (base of the sphere-suspension
tower). For a clopen `U ⊔ Uᶜ` with both pieces `ε̄`-bijective, and any iso `e : ker(ε̄_ℤ) ≅ ℤ`, the
class `e.symm 1 : Homology X 0` reduces to a nonzero mod-2 class: `baseDetector (redHomology _) = ±1 =
1 ≠ 0`. The concrete input to `SphereGenReducesNonzero` (with `X = Punc 1`, `U = posSet`, `e` the base
iso `augHInt_ker_punc1_iso_int.some`). -/
theorem base_generator_reduces_ne_zero (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U)))
    (hUcbij : Function.Bijective (augHInt (sub Uᶜ)))
    (e : ↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ℤ) :
    redHomology X 0 (e.symm 1 : ↥(LinearMap.ker (augHInt X))) ≠ 0 := by
  intro hzero
  -- detector reads ↑(antiDiagProjInt (e.symm 1)) = ±1 = 1
  have hdet := baseDetector_redHomology (X := X) hU hUbij
    (e.symm 1 : ↥(LinearMap.ker (augHInt X))) (e.symm 1).2
  rw [hzero, map_zero] at hdet
  -- hdet : 0 = ↑(antiDiagProjInt ⟨(e.symm 1).1, _⟩)
  have hval : antiDiagProjInt (X := X) hU hUbij ⟨(e.symm 1 : ↥(LinearMap.ker (augHInt X))).1,
      (e.symm 1).2⟩ = antiDiagProjInt (X := X) hU hUbij (e.symm 1) := by
    congr 1
  rw [hval] at hdet
  have hunit := antiDiagProjInt_generator_isUnit hU hUbij hUcbij e
  rw [Int.isUnit_iff] at hunit
  rcases hunit with h1 | hm1
  · rw [h1] at hdet; simp at hdet
  · rw [hm1] at hdet; norm_num at hdet

/-! ## §5. Non-vanishing transports through a reduction-natural injective map -/

/-- **Non-vanishing lifts through a reduction-natural map with injective, zero-preserving mod-2 side.**
If the mod-2 map `gmod` is injective with `gmod 0 = 0` and reduction is natural
(`rB (gint a) = gmod (rA a)`), then `rA a ≠ 0` forces `rB (gint a) ≠ 0`. The single inductive step of
the sphere-suspension tower chase (`gmod` is always a mod-2 additive equiv, so both hypotheses hold). -/
theorem ne_zero_transport {A B A' B' : Type*}
    {gint : A → B} {rA : A → A'} {rB : B → B'} {gmod : A' → B'} [Zero A'] [Zero B']
    (hgmod : Function.Injective gmod) (hgmod0 : gmod 0 = 0)
    (hnat : ∀ a, rB (gint a) = gmod (rA a))
    {a : A} (ha : rA a ≠ 0) : rB (gint a) ≠ 0 := by
  rw [hnat a]
  intro h
  exact ha (hgmod (h.trans hgmod0.symm))

/-- **`.symm`-transport: non-vanishing lifts through the inverse of a reduction-natural equiv.**
Given integral/mod-2 additive equivs `Fint : A ≃+ B`, `Fmod : A' ≃+ B'`, reductions `rA : A →+ A'`,
`rB : B →+ B'`, and the FORWARD naturality `rB (Fint a) = Fmod (rA a)`, if `rB b ≠ 0` then
`rA (Fint.symm b) ≠ 0`. (Apply `Fmod.symm` to the forward square: `rA (Fint.symm b) = Fmod.symm (rB b)`,
and `Fmod.symm` injective + zero-preserving.) Lets the tower chase run on `.symm` legs from the base. -/
theorem ne_zero_transport_symm {A B A' B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    (Fint : A ≃+ B) (Fmod : A' ≃+ B') (rA : A →+ A') (rB : B →+ B')
    (hnat : ∀ a, rB (Fint a) = Fmod (rA a))
    {b : B} (hb : rB b ≠ 0) : rA (Fint.symm b) ≠ 0 := by
  have hkey : rA (Fint.symm b) = Fmod.symm (rB b) := by
    apply Fmod.injective
    rw [Fmod.apply_symm_apply, ← hnat, Fint.apply_symm_apply]
  rw [hkey]
  intro h
  apply hb
  have := congrArg Fmod h
  rwa [Fmod.apply_symm_apply, map_zero] at this

/-! ## §6. Tower-stage naturality squares (forward), toward the sphere generator -/

open SKEFTHawking.SingularSphereHomologyInt
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt excisionMapInt)
open SKEFTHawking.SingularExcisionIso (restr excisionEquiv)
open SKEFTHawking.SingularSphereAcyclic (Sph antipode ne_antipode polar_cover)
open SKEFTHawking.SingularLocalHomologyRedCompatInt
  (redRelHomology_excisionMap redRelHomology_homProjInt redHomology_connectingInt
   redHomology_homologyMapInt)

/-- **The reduction commutes with the inverse excision equiv.** From the forward square
`redRelHomology ∘ excisionMapInt = excisionMap ∘ redRelHomology` (`redRelHomology_excisionMap`), apply
`(excisionEquiv).symm` on both sides: `redRelHomology (restr A B) ∘ (excisionEquivInt).symm =
(excisionEquiv).symm ∘ redRelHomology A`. -/
theorem redRelHomology_excisionEquivInt_symm {X : TopCat} (A B : Set ↑X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑X)), interior U) = Set.univ)
    (z : RelHomologyInt A (n + 1)) :
    redRelHomology (restr A B) (n + 1) ((excisionEquivInt A B n hcov).symm z)
      = (excisionEquiv A B n hcov).symm (redRelHomology A (n + 1) z) := by
  apply (excisionEquiv A B n hcov).injective
  rw [(excisionEquiv A B n hcov).apply_symm_apply]
  have hfwd := redRelHomology_excisionMap A B (n + 1)
    ((excisionEquivInt A B n hcov).symm z)
  -- excisionEquiv (redRelHomology (restr) ((excisionEquivInt).symm z))
  --   = redRelHomology A (excisionMapInt ((excisionEquivInt).symm z))
  --   = redRelHomology A z    (since excisionMapInt = excisionEquivInt forward)
  rw [show (excisionEquiv A B n hcov) (redRelHomology (restr A B) (n + 1)
        ((excisionEquivInt A B n hcov).symm z))
      = SKEFTHawking.SingularExcisionIso.excisionMap A B (n + 1)
          (redRelHomology (restr A B) (n + 1) ((excisionEquivInt A B n hcov).symm z)) from rfl,
    ← hfwd]
  congr 1
  show excisionMapInt A B (n + 1) ((excisionEquivInt A B n hcov).symm z) = z
  exact (excisionEquivInt A B n hcov).apply_symm_apply z

open SKEFTHawking.SingularLineMinusPointInt (bottomSuspMapInt)
open SKEFTHawking.SingularSphereBottom (bottomSuspMap)

/-- **The reduction commutes with the bottom-degree sphere suspension map.**
`redHomology (equator) 0 ∘ bottomSuspMapInt = bottomSuspMap ∘ redHomology (Sph n) 1`. Composes the
three primitive squares: pair-projection (`redRelHomology_homProjInt`), inverse-excision
(`redRelHomology_excisionEquivInt_symm`), and connecting (`redHomology_connectingInt`). -/
theorem redHomology_bottomSuspMapInt {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (h : Homology (Sph n) 1) :
    redHomology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0
        (bottomSuspMapInt n v h)
      = bottomSuspMap n v (redHomology (Sph n) 1 h) := by
  -- unfold both composites and chase the three squares
  show redHomology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0
      ((SingularRelHomologyInt.connectingInt (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) 0)
        ((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
              (polar_cover (ne_antipode v))).symm
          ((SingularRelHomologyInt.homProjInt ({v}ᶜ : Set ↑(Sph n)) 1) h)))
    = (SKEFTHawking.SingularPairLES.connecting (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) 0)
        ((excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
              (polar_cover (ne_antipode v))).symm
          ((SKEFTHawking.SingularPairLES.homProj ({v}ᶜ : Set ↑(Sph n)) 1)
            (redHomology (Sph n) 1 h)))
  rw [redHomology_connectingInt, redRelHomology_excisionEquivInt_symm, redRelHomology_homProjInt]

open SKEFTHawking.SingularSphereAcyclic (equatorMap dimReductionEquiv)
open SKEFTHawking.SingularPuncturedRetract (normalize)

/-- **The reduction commutes with the sphere dimension-reduction equiv** `Hₖ₊₂(Sⁿ) ≅ Hₖ₊₁(Sⁿ⁻¹)`.
`redHomology ∘ dimReductionEquivInt = dimReductionEquiv ∘ redHomology`. Composes the suspension square
(homProj + excision.symm + connecting, at degree `k+1`) with the equator-retract square
(two `Homology.mapInt` naturalities, `redHomology_homologyMapInt`). -/
theorem redHomology_dimReductionEquivInt {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (k : ℕ)
    (h : Homology (Sph n) (k + 2)) :
    redHomology (SingularPuncturedRetract.Sph n) (k + 1) (dimReductionEquivInt v k h)
      = dimReductionEquiv v k (redHomology (Sph n) (k + 2) h) := by
  show redHomology (SingularPuncturedRetract.Sph n) (k + 1)
      ((Homology.mapInt (normalize (n := n)) (k + 1))
        ((Homology.mapInt (equatorMap v) (k + 1))
          ((SingularRelHomologyInt.connectingInt
                (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) (k + 1))
            ((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) (k + 1)
                  (polar_cover (ne_antipode v))).symm
              ((SingularRelHomologyInt.homProjInt ({v}ᶜ : Set ↑(Sph n)) (k + 2)) h)))))
    = (SKEFTHawking.SingularFunctoriality.Homology.map (normalize (n := n)) (k + 1))
        ((SKEFTHawking.SingularFunctoriality.Homology.map (equatorMap v) (k + 1))
          ((SKEFTHawking.SingularPairLES.connecting
                (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) (k + 1))
            ((excisionEquiv ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) (k + 1)
                  (polar_cover (ne_antipode v))).symm
              ((SKEFTHawking.SingularPairLES.homProj ({v}ᶜ : Set ↑(Sph n)) (k + 2))
                (redHomology (Sph n) (k + 2) h)))))
  rw [redHomology_homologyMapInt, redHomology_homologyMapInt, redHomology_connectingInt,
    redRelHomology_excisionEquivInt_symm, redRelHomology_homProjInt]

open SKEFTHawking.SingularSphereBottom (basePoint topSphereReduce)

/-- **The reduction commutes with the iterated top-sphere reduction** `Hₘ₊₁(Sᵐ⁺¹) ≅ H₁(S¹)`.
`redHomology (Sph 1) 1 ∘ topSphereReduceInt m = topSphereReduce m ∘ redHomology (Sph (m+1)) (m+1)`.
Induction on `m` mirroring the recursion; the step is `redHomology_dimReductionEquivInt`. -/
theorem redHomology_topSphereReduceInt : (m : ℕ) → (h : Homology (Sph (m + 1)) (m + 1)) →
    redHomology (Sph 1) 1 (topSphereReduceInt m h)
      = topSphereReduce m (redHomology (Sph (m + 1)) (m + 1) h)
  | 0, h => by
      show redHomology (Sph 1) 1 ((LinearEquiv.refl ℤ (Homology (Sph 1) 1)) h)
        = (LinearEquiv.refl (ZMod 2)
            (SKEFTHawking.SingularHomologyMod2.Homology (Sph 1) 1)) (redHomology (Sph 1) 1 h)
      rfl
  | (m + 1), h => by
      show redHomology (Sph 1) 1
          (topSphereReduceInt m (dimReductionEquivInt (basePoint (m + 2)) m h))
        = topSphereReduce m (dimReductionEquiv (basePoint (m + 2)) m
            (redHomology (Sph (m + 2)) (m + 2) h))
      rw [redHomology_topSphereReduceInt m, redHomology_dimReductionEquivInt]

/-! ## §7. The `ker ε̄` reduction homomorphism and the equator/circle stages -/

/-- **The reduction preserves reduced `H̃₀ = ker ε̄`**: `augH X (redHomology X 0 x) = ↑(augHInt X x)`
(`augH_redHomology`), so `x ∈ ker(augHInt) ⟹ redHomology x ∈ ker(augH)`. As an additive hom. -/
noncomputable def redHomologyKer (X : TopCat) :
    ↥(LinearMap.ker (augHInt X)) →+ ↥(LinearMap.ker (augH X)) where
  toFun x := ⟨redHomology X 0 (x : Homology X 0), by
    rw [LinearMap.mem_ker, augH_redHomology, show augHInt X (x : Homology X 0) = 0 from x.2,
      Int.cast_zero]⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

@[simp] theorem redHomologyKer_coe (X : TopCat) (x : ↥(LinearMap.ker (augHInt X))) :
    ((redHomologyKer X x : ↥(LinearMap.ker (augH X))) :
        SKEFTHawking.SingularHomologyMod2.Homology X 0)
      = redHomology X 0 (x : Homology X 0) := rfl

/-- **The reduced-`H̃₀` generator reduces to a nonzero `ker ε̄` class** (base of the tower, ker level).
The mod-2 class `redHomologyKer (e.symm 1)` is nonzero in `ker(augH X)` — its underlying `Homology`
class is nonzero (`base_generator_reduces_ne_zero`), and the ker inclusion is injective. -/
theorem redHomologyKer_base_ne_zero (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U)))
    (hUcbij : Function.Bijective (augHInt (sub Uᶜ)))
    (e : ↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ℤ) :
    redHomologyKer X (e.symm 1) ≠ 0 := by
  intro h
  apply base_generator_reduces_ne_zero hU hUbij hUcbij e
  have hc := congrArg (fun w : ↥(LinearMap.ker (augH X)) =>
    (w : SKEFTHawking.SingularHomologyMod2.Homology X 0)) h
  simp only [redHomologyKer_coe, ZeroMemClass.coe_zero] at hc
  exact hc

open SKEFTHawking.SingularLineMinusPointInt (augHIntKerEquivOfHomeo)
open SKEFTHawking.SingularDisjointUnion (augHKerEquivOfHomeo)

/-- **The reduction commutes with the homeo `ker ε̄` transport** (ker level):
`redHomologyKer Y ∘ augHIntKerEquivOfHomeo f g = augHKerEquivOfHomeo f g ∘ redHomologyKer X`. The
underlying element is `Homology.mapInt f 0`, whose reduction naturality is `redHomology_homologyMapInt`. -/
theorem redHomologyKer_augHIntKerEquivOfHomeo {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y)
    (x : ↥(LinearMap.ker (augHInt X))) :
    redHomologyKer Y (augHIntKerEquivOfHomeo f g hgf hfg x)
      = augHKerEquivOfHomeo f g hgf hfg (redHomologyKer X x) := by
  apply Subtype.ext
  show redHomology Y 0 ((augHIntKerEquivOfHomeo f g hgf hfg x : ↥(LinearMap.ker (augHInt Y))) : Homology Y 0)
    = ((augHKerEquivOfHomeo f g hgf hfg (redHomologyKer X x) : ↥(LinearMap.ker (augH Y))) :
        SKEFTHawking.SingularHomologyMod2.Homology Y 0)
  rw [show ((augHIntKerEquivOfHomeo f g hgf hfg x : ↥(LinearMap.ker (augHInt Y))) : Homology Y 0)
        = Homology.mapInt f 0 (x : Homology X 0) from rfl,
    show ((augHKerEquivOfHomeo f g hgf hfg (redHomologyKer X x) : ↥(LinearMap.ker (augH Y))) :
          SKEFTHawking.SingularHomologyMod2.Homology Y 0)
        = SKEFTHawking.SingularFunctoriality.Homology.map f 0
            ((redHomologyKer X x : ↥(LinearMap.ker (augH X))) :
              SKEFTHawking.SingularHomologyMod2.Homology X 0) from rfl,
    redHomologyKer_coe, redHomology_homologyMapInt]

open SKEFTHawking.SingularLineMinusPointInt (bottomSuspEquivInt)
open SKEFTHawking.SingularSphereBottom (bottomSuspEquiv)

/-- **The reduction commutes with the bottom sphere suspension equiv** (ker codomain):
`redHomologyKer (equator) ∘ bottomSuspEquivInt = bottomSuspEquiv ∘ redHomology (Sph n) 1`. Underlying
element is `bottomSuspMapInt`, whose reduction naturality is `redHomology_bottomSuspMapInt`. -/
theorem redHomologyKer_bottomSuspEquivInt {n : ℕ}
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (h : Homology (Sph n) 1) :
    redHomologyKer (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))
        (bottomSuspEquivInt (n := n) (v := v) h)
      = bottomSuspEquiv (n := n) (v := v) (redHomology (Sph n) 1 h) := by
  apply Subtype.ext
  show redHomology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0
      ((bottomSuspEquivInt (n := n) (v := v) h :
        ↥(LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))))) :
          Homology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0)
    = ((bottomSuspEquiv (n := n) (v := v) (redHomology (Sph n) 1 h) :
        ↥(LinearMap.ker (augH (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))))) :
          SKEFTHawking.SingularHomologyMod2.Homology
            (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0)
  rw [show ((bottomSuspEquivInt (n := n) (v := v) h :
          ↥(LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))))) :
            Homology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0)
        = bottomSuspMapInt n v h from rfl,
    show ((bottomSuspEquiv (n := n) (v := v) (redHomology (Sph n) 1 h) :
          ↥(LinearMap.ker (augH (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))))) :
            SKEFTHawking.SingularHomologyMod2.Homology
              (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0)
        = bottomSuspMap n v (redHomology (Sph n) 1 h) from rfl,
    redHomology_bottomSuspMapInt]

/-! ## §8. Assembly: `SphereGenReducesNonzero` -/

open SKEFTHawking.SingularLineMinusPointInt
  (H3S3IsoInt circleH1EquivInt topSphereIsoInt augHInt_ker_punc1_iso_int
   augHInt_posSet_bijective augHInt_posSetCompl_bijective)
open SKEFTHawking.SingularLineMinusPoint (isClopen_posSet)
open SKEFTHawking.SingularSphereAcyclic
  (equatorMap equatorMapInv equatorMapInv_comp_equatorMap equatorMap_comp_equatorMapInv)
open SKEFTHawking.SingularSphereHomologyInt (topSphereReduceInt)

/-- **`SphereGenReducesNonzero`** — the ℤ→ℤ/2 reduction of the integral `H₃(S³;ℤ)` generator
`H3S3IsoInt.symm 1` is nonzero in `H₃(S³;ℤ/2)`. This discharges the single non-functorial residual of
the integral local-homology `redCompat` tower. Chases the base non-vanishing
(`redHomologyKer_base_ne_zero` at `ℝ¹∖0`) up through the equator homeo, the bottom sphere suspension,
and the iterated dimension reduction, using the `.symm`-transport of each stage's reduction-naturality
square. -/
theorem sphereGenReducesNonzero :
    SKEFTHawking.SingularLocalHomologyRedCompatInt.SphereGenReducesNonzero := by
  -- base: the ℝ¹∖0 reduced generator reduces nonzero (ker level)
  have hbase : redHomologyKer (SingularPuncturedRetract.Punc 1)
      (augHInt_ker_punc1_iso_int.some.symm 1) ≠ 0 :=
    redHomologyKer_base_ne_zero isClopen_posSet augHInt_posSet_bijective
      augHInt_posSetCompl_bijective augHInt_ker_punc1_iso_int.some
  -- equator homeo (.symm): lift to ker(augHInt (equator))
  set eqf := equatorMap (SingularSphereBottom.basePoint 1) with heqf
  set eqg := equatorMapInv (SingularSphereBottom.basePoint 1) with heqg
  have hgf : eqg.comp eqf = ContinuousMap.id _ := equatorMapInv_comp_equatorMap
  have hfg : eqf.comp eqg = ContinuousMap.id _ := equatorMap_comp_equatorMapInv
  have hequator : redHomologyKer _
      ((augHIntKerEquivOfHomeo eqf eqg hgf hfg).symm
        (augHInt_ker_punc1_iso_int.some.symm 1)) ≠ 0 :=
    ne_zero_transport_symm
      (augHIntKerEquivOfHomeo eqf eqg hgf hfg).toAddEquiv
      (augHKerEquivOfHomeo eqf eqg hgf hfg).toAddEquiv
      (redHomologyKer _) (redHomologyKer _)
      (redHomologyKer_augHIntKerEquivOfHomeo eqf eqg hgf hfg) hbase
  -- bottom suspension (.symm): lift to Homology (Sph 1) 1
  have hcircle : redHomology (Sph 1) 1
      ((bottomSuspEquivInt (n := 1) (v := SingularSphereBottom.basePoint 1)).symm
        ((augHIntKerEquivOfHomeo eqf eqg hgf hfg).symm
          (augHInt_ker_punc1_iso_int.some.symm 1))) ≠ 0 :=
    ne_zero_transport_symm
      (bottomSuspEquivInt (n := 1) (v := SingularSphereBottom.basePoint 1)).toAddEquiv
      (bottomSuspEquiv (n := 1) (v := SingularSphereBottom.basePoint 1)).toAddEquiv
      (redHomology (Sph 1) 1) (redHomologyKer _)
      (redHomologyKer_bottomSuspEquivInt _) hequator
  -- top-sphere reduction (.symm): lift to Homology (Sph 3) 3
  have htop : redHomology (Sph 3) 3
      ((topSphereReduceInt 2).symm
        ((bottomSuspEquivInt (n := 1) (v := SingularSphereBottom.basePoint 1)).symm
          ((augHIntKerEquivOfHomeo eqf eqg hgf hfg).symm
            (augHInt_ker_punc1_iso_int.some.symm 1)))) ≠ 0 :=
    ne_zero_transport_symm
      (topSphereReduceInt 2).toAddEquiv (SingularSphereBottom.topSphereReduce 2).toAddEquiv
      (redHomology (Sph 3) 3) (redHomology (Sph 1) 1)
      (redHomology_topSphereReduceInt 2) hcircle
  -- H3S3IsoInt.symm 1 unfolds to exactly the nested .symm chain above
  show redHomology (Sph 3) 3 (H3S3IsoInt.symm 1) ≠ 0
  -- v4.32:  now leaves the (definitional) equality as an open goal;
  -- the chain is defeq, so close it directly.
  exact htop

end SKEFTHawking.SingularSphereGenReducesInt
