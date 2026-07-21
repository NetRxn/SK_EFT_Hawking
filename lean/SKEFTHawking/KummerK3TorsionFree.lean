/-
# Phase 5q.H — K7 finale: `Torsion(H₂(K3;ℤ)) = ⊥` reduced to ONE geometric parity fact

`KummerK7Delta1Window` pinned the free part of `H₂(K3;ℤ)` unconditionally (`kummerK3_H2_rank`
`= 22`, `freePartEquiv : H₂/T ≃ₗ ℤ²²`) and isolated the sharp residual: the whole gap between the
landed window and `kummerK3_b2_target` (`H₂(K3;ℤ) ≅ ℤ²²` on the nose) is **torsion-freeness**
(`kummerK3_b2_target_of_torsion_free`).

This module reduces that residual to a **single, geometrically-meaningful, convention-robust
statement about two explicit maps** `H₂(K3;ℤ) → (ℤ/2)¹⁶`.

## The two maps

* **The tube coordinate** (`tubeCoord`). Every class doubles into the piece block
  (`k7H2_two_smul_mem_range`) and `Σ₂` is injective (`k7Sum2_injective`), so
  `x ↦ Σ₂⁻¹(2x) ∈ ℤ⁶ × ℤ¹⁶` is a well-defined linear map (`blockCoord`, characterized by
  `sigma2_blockCoord`). Its `E`-block, reduced mod 2, is `tubeCoord`.
* **The MV connecting map** `δ₁` read in the collar identification
  `H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` (`interH1EquivInt ∘ k7Delta 1`).

Both kill the piece block — `tubeCoord` unconditionally (`tubeCoord_eq_zero_of_mem_pieceBlock`),
`δ₁` by MV exactness (`ker_k7Delta_one`) — so both factor through the exponent-2 cokernel
`coker Σ₂ ≅ im δ₁ ↪ (ℤ/2)¹⁶`; they are the same *kind* of object, and the assertion that they
agree is a statement of chain-level geometry, not of algebra.

## The reduction chain

`TubeParity` (`tubeCoord = δ₁`) `→` `TubeSeparates` (`tubeCoord` detects the piece block) `→`
`Torsion(H₂(K3;ℤ)) = ⊥` `→` `kummerK3_b2_target`.

`TubeSeparates` is the weakest hypothesis the torsion argument consumes; `TubeParity` is the
geometric statement that supplies it. Neither is an axiom: both are `Prop`s carried explicitly by
every downstream theorem.

## The residual is a statement about a finite group

`tubeCoord` descends to `tubeQuot : coker Σ₂ → (ℤ/2)¹⁶` (§5), and `coker Σ₂ ≅ im δ₁ ↪ (ℤ/2)¹⁶` is
finite elementary abelian. So

* `TubeSeparates ↔ Function.Injective tubeQuot` (`tubeSeparates_iff_tubeQuot_injective`), and
* `TubeParity ↔ tubeQuot = cokerSigma2Embed` (`tubeParity_iff_tubeQuot_eq`) — an equality of two
  ℤ-linear maps out of a finite elementary abelian 2-group,

so the residual is a finite, per-copy checkable assertion, not a statement quantified over all of
`H₂(K3;ℤ)`. Unconditionally (no hypothesis at all) the torsion is already trapped by that one map:
`Torsion(H₂(K3;ℤ))` embeds ℤ-linearly into `ker tubeQuot` (`torsionIntoKerTubeQuot`,
`torsionIntoKerTubeQuot_injective`), so `tubeQuot` is an exact measure of what remains.

## `TubeParity` has real content (§6)

`tubeCoord` reads off exactly which exceptional classes are being halved: if `2y` is the
exceptional combination `v` then `tubeCoord y = v mod 2`
(`tubeCoord_of_two_smul_eq_exceptional`, unconditional). Combined with the landed δ₁-image parity
cut (`KummerK7Delta1Image.delta1_image_parity`), `TubeParity` therefore forces the classical
**Kummer even-weight condition** — an exceptional combination can only become divisible by 2 with
even weight (`exceptional_half_even_weight`) — and in particular no single exceptional sphere is
2-divisible (`exceptional_not_two_divisible`). Both are true facts about the Kummer K3, so this is
a nontrivial consistency check on the hypothesis rather than a vacuous carrier.

## What `TubeParity` costs geometrically (the honest residual)

Through excision `H₂(K3, qThick) ≅ H₂(eImage, collar)` the connecting map `δ₁` is the pair
connecting map of `(E, ∂E)`, and for the resolution piece `E ≃ 𝒪(−2)`-disk-bundle over `S²`
(`KummerResolutionPiece`) the pair sequence reads
`0 → H₂(E) ≅ ℤ¹⁶ --(×(−2))--> H₂(E,∂E) ≅ ℤ¹⁶ --(mod 2)--> H₁(∂E) ≅ (ℤ/2)¹⁶ → 0`
(`H₂(∂E) = H₂(ℝP³) = 0 = H₁(E)`). Chasing `2x` through it gives exactly
`δ₁ x = (E-block of Σ₂⁻¹(2x)) mod 2`. The load-bearing input is the Euler number `−2` of the
resolution piece — irreducibly the `ℝP³ = S³/±1` clutching geometry, and the reason the parity is
2 rather than 1 or 3. That per-copy computation is the remaining work; it is NOT algebra, and no
chain-level rearrangement can produce it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7Delta1Window
import SKEFTHawking.KummerK7Delta1Image

namespace SKEFTHawking.KummerK3TorsionFree

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerK7MVAssembly
  (k7Delta k7Sum2_injective interH1EquivInt exceptionalEmbed eImageH2EquivInt)
open SKEFTHawking.KummerK7Delta1Image (delta1_image_parity)
open scoped SKEFTHawking.KummerK7Delta1Image
open SKEFTHawking.KummerK7Delta1Window
  (Sigma2 pieceBlock sigma2SourceEquiv doubleIntoBlock ker_k7Delta_one
    torsion_inf_pieceBlock_eq_bot torsion_two_smul_eq_zero cokerSigma2Embed)

noncomputable section

/-! ## §1. The block coordinates of a doubled class -/

/-- **The doubled-class block coordinates** `x ↦ Σ₂⁻¹(2x) ∈ ℤ⁶ × ℤ¹⁶`. Well defined because
`2·H₂(K3;ℤ) ⊆ im Σ₂` (`doubleIntoBlock`) and `Σ₂` is injective (`k7Sum2_injective`). -/
def blockCoord : Homology KummerK3top 2 →ₗ[ℤ] ((Fin 6 → ℤ) × (EIndex → ℤ)) :=
  sigma2SourceEquiv.toLinearMap.comp
    (((LinearEquiv.ofInjective Sigma2 k7Sum2_injective).symm.toLinearMap).comp doubleIntoBlock)

/-- **The defining property of `blockCoord`**: it really is the `Σ₂`-preimage of the double. -/
theorem sigma2_blockCoord (x : Homology KummerK3top 2) :
    Sigma2 (sigma2SourceEquiv.symm (blockCoord x)) = (2 : ℤ) • x := by
  have h1 : sigma2SourceEquiv.symm (blockCoord x)
      = (LinearEquiv.ofInjective Sigma2 k7Sum2_injective).symm (doubleIntoBlock x) := by
    simp [blockCoord]
  rw [h1]
  have h2 : (LinearEquiv.ofInjective Sigma2 k7Sum2_injective)
      ((LinearEquiv.ofInjective Sigma2 k7Sum2_injective).symm (doubleIntoBlock x))
      = doubleIntoBlock x := LinearEquiv.apply_symm_apply _ _
  exact congrArg Subtype.val h2

/-- `blockCoord` on a piece-block class is just its `Σ₂`-coordinate vector, doubled. -/
theorem blockCoord_sigma2 (p : (Fin 6 → ℤ) × (EIndex → ℤ)) :
    blockCoord (Sigma2 (sigma2SourceEquiv.symm p)) = (2 : ℤ) • p := by
  apply sigma2SourceEquiv.symm.injective
  apply k7Sum2_injective
  rw [sigma2_blockCoord, map_smul, map_smul]

/-! ## §2. The tube coordinate -/

/-- Coefficientwise mod-2 reduction `ℤ¹⁶ →ₗ[ℤ] (ℤ/2)¹⁶`. -/
def redMod2 : (EIndex → ℤ) →ₗ[ℤ] (EIndex → ZMod 2) where
  toFun v i := ((v i : ℤ) : ZMod 2)
  map_add' u v := by funext i; simp
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    push_cast
    ring

@[simp] theorem redMod2_apply (v : EIndex → ℤ) (i : EIndex) :
    redMod2 v i = ((v i : ℤ) : ZMod 2) := rfl

/-- **The tube coordinate** `H₂(K3;ℤ) → (ℤ/2)¹⁶`: the `E`-block of `Σ₂⁻¹(2x)`, mod 2. This is the
algebraic shadow of the exceptional-tube parity of `x` — the number of times `x` crosses the `i`-th
collar `ℝP³`, mod 2. -/
def tubeCoord : Homology KummerK3top 2 →ₗ[ℤ] (EIndex → ZMod 2) :=
  redMod2.comp ((LinearMap.snd ℤ (Fin 6 → ℤ) (EIndex → ℤ)).comp blockCoord)

/-- **The tube coordinate kills the piece block** — unconditional. A piece class `p` has
`Σ₂⁻¹(2p) = 2·(coords of p)`, all of whose entries are even. Together with
`ker δ₁ = im Σ₂` this puts `tubeCoord` and `δ₁` on the same footing: both factor through the
exponent-2 cokernel `coker Σ₂`. -/
theorem tubeCoord_eq_zero_of_mem_pieceBlock {x : Homology KummerK3top 2} (hx : x ∈ pieceBlock) :
    tubeCoord x = 0 := by
  obtain ⟨p, rfl⟩ := hx
  have hp : p = sigma2SourceEquiv.symm (sigma2SourceEquiv p) :=
    (sigma2SourceEquiv.symm_apply_apply p).symm
  rw [hp, tubeCoord, LinearMap.comp_apply, LinearMap.comp_apply, blockCoord_sigma2]
  funext i
  show ((((2 : ℤ) • sigma2SourceEquiv p).2 i : ℤ) : ZMod 2) = 0
  show (((2 : ℤ) * (sigma2SourceEquiv p).2 i : ℤ) : ZMod 2) = 0
  push_cast
  rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul]

/-- **The tube coordinate kills every double** — the exponent-2 shadow of
`tubeCoord_eq_zero_of_mem_pieceBlock` (`2x ∈ im Σ₂` for every `x`). -/
theorem tubeCoord_two_smul (x : Homology KummerK3top 2) : tubeCoord ((2 : ℤ) • x) = 0 :=
  tubeCoord_eq_zero_of_mem_pieceBlock (doubleIntoBlock x).2

/-- **`tubeCoord` kills torsion — unconditional.** A torsion class is 2-torsion
(`torsion_two_smul_eq_zero`), so it doubles to `0` and its block coordinates vanish outright.
This is the step that makes the tube coordinate a torsion detector. -/
theorem tubeCoord_eq_zero_of_torsion {t : Homology KummerK3top 2}
    (ht : t ∈ Submodule.torsion ℤ (Homology KummerK3top 2)) : tubeCoord t = 0 := by
  have hdb : doubleIntoBlock t = 0 := Subtype.ext (torsion_two_smul_eq_zero ht)
  rw [tubeCoord, LinearMap.comp_apply, LinearMap.comp_apply, blockCoord,
    LinearMap.comp_apply, LinearMap.comp_apply, hdb, map_zero, map_zero, map_zero, map_zero]

/-! ## §3. The two named hypotheses -/

/-- **`TubeSeparates`** — the tube coordinate detects the piece block: a class whose doubled
`E`-coordinates are all even already lies in `im Σ₂`. This is the weakest statement the
torsion argument consumes. -/
def TubeSeparates : Prop :=
  ∀ x : Homology KummerK3top 2, tubeCoord x = 0 → x ∈ pieceBlock

/-- **`TubeParity`** — the geometric statement: the MV connecting map `δ₁`, read in
`H₁(collar;ℤ) ≅ (ℤ/2)¹⁶`, IS the mod-2 `E`-block of `Σ₂⁻¹(2x)`.

This is what the `(E, ∂E)` pair sequence for the `𝒪(−2)`-disk-bundle resolution piece delivers:
`H₂(E) --(×(−2))--> H₂(E,∂E) --(mod 2)--> H₁(∂E)`. It is convention-robust — the target is
2-torsion, so the orientation sign of `δ₁` and of the per-copy generators of `H₂(ResE) ≅ ℤ` are
both invisible. -/
def TubeParity : Prop :=
  ∀ x : Homology KummerK3top 2, tubeCoord x = interH1EquivInt (k7Delta 1 x)

/-- **`TubeParity → TubeSeparates`** — through MV exactness `ker δ₁ = im Σ₂` and the injectivity
of the collar identification. -/
theorem tubeSeparates_of_tubeParity (h : TubeParity) : TubeSeparates := by
  intro x hx
  have h1 : interH1EquivInt (k7Delta 1 x) = 0 := (h x).symm.trans hx
  have h2 : k7Delta 1 x = 0 := (LinearEquiv.map_eq_zero_iff interH1EquivInt).mp h1
  have h3 : x ∈ LinearMap.ker (k7Delta 1) := h2
  rwa [ker_k7Delta_one] at h3

/-! ## §4. The finale -/

/-- **Torsion-freeness of `H₂(K3;ℤ)` from tube separation.** A torsion class is 2-torsion
(`torsion_two_smul_eq_zero`), so its doubled block coordinates vanish outright, so `TubeSeparates`
lands it in the piece block — where `torsion_inf_pieceBlock_eq_bot` kills it. -/
theorem torsion_eq_bot_of_tubeSeparates (h : TubeSeparates) :
    Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  have hpb : t ∈ pieceBlock := h t (tubeCoord_eq_zero_of_torsion ht)
  have hinf : t ∈ Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock :=
    Submodule.mem_inf.mpr ⟨ht, hpb⟩
  rwa [torsion_inf_pieceBlock_eq_bot] at hinf

/-- **`Torsion(H₂(K3;ℤ)) = ⊥` from the tube-parity geometry** — the K7 finale, modulo the single
named geometric fact `TubeParity`. -/
theorem kummerK3_torsion_free_of_tube_parity (h : TubeParity) :
    Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥ :=
  torsion_eq_bot_of_tubeSeparates (tubeSeparates_of_tubeParity h)

/-- **`H₂(K3;ℤ) ≅ ℤ²²` on the nose from tube parity** — the rank pin of `KummerK7Delta1Window`
(unconditional) plus the torsion kill. -/
theorem kummerK3_H2_equiv_of_tube_parity (h : TubeParity) :
    Nonempty (Homology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ)) :=
  SKEFTHawking.KummerK7Delta1Window.kummerK3_H2_equiv_of_torsion_free
    (kummerK3_torsion_free_of_tube_parity h)

/-- **`kummerK3_b2_target` from tube parity** — the ℤ²² headline with its residual named and
carried explicitly, not axiomatized. -/
theorem kummerK3_b2_target_of_tube_parity (h : TubeParity) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  SKEFTHawking.KummerK7Delta1Window.kummerK3_b2_target_of_torsion_free
    (kummerK3_torsion_free_of_tube_parity h)

/-! ## §5. Both hypotheses live on the finite group `coker Σ₂` — and the unconditional bound -/

/-- **The tube coordinate descends to `coker Σ₂`** (`tubeCoord_eq_zero_of_mem_pieceBlock`). Since
`coker Σ₂ ≅ im δ₁ ↪ (ℤ/2)¹⁶` is finite of exponent 2, `tubeQuot` is a ℤ-linear map between
explicit finite elementary abelian 2-groups — so both `TubeSeparates` and `TubeParity` are
finite, per-copy checkable assertions rather than statements about all of `H₂(K3;ℤ)`. -/
def tubeQuot : (Homology KummerK3top 2 ⧸ pieceBlock) →ₗ[ℤ] (EIndex → ZMod 2) :=
  pieceBlock.liftQ tubeCoord (fun _ hx => tubeCoord_eq_zero_of_mem_pieceBlock hx)

@[simp] theorem tubeQuot_mk (x : Homology KummerK3top 2) :
    tubeQuot (Submodule.Quotient.mk x : Homology KummerK3top 2 ⧸ pieceBlock) = tubeCoord x := rfl

/-- **`TubeSeparates` is exactly the injectivity of `tubeQuot`** — the residual as a statement
about one map out of a finite elementary abelian 2-group. -/
theorem tubeSeparates_iff_tubeQuot_injective : TubeSeparates ↔ Function.Injective tubeQuot := by
  constructor
  · intro h
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [LinearMap.mem_ker, tubeQuot_mk] at hy
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h x hy)
  · intro h x hx
    have h1 : tubeQuot (Submodule.Quotient.mk x : Homology KummerK3top 2 ⧸ pieceBlock)
        = tubeQuot 0 := by
      rw [tubeQuot_mk, hx, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp (h h1)

/-- **`TubeParity` is exactly the equality of two maps on `coker Σ₂`** — `tubeQuot` versus the
landed injective cokernel embedding `cokerSigma2Embed`. This is the sharpest packaging of the
residual: both sides are ℤ-linear maps `coker Σ₂ → (ℤ/2)¹⁶` out of a finite group. -/
theorem tubeParity_iff_tubeQuot_eq : TubeParity ↔ tubeQuot = cokerSigma2Embed := by
  constructor
  · intro h
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [tubeQuot_mk, h x]
    rfl
  · intro h x
    have h1 : tubeQuot (Submodule.Quotient.mk x : Homology KummerK3top 2 ⧸ pieceBlock)
        = cokerSigma2Embed (Submodule.Quotient.mk x) := by rw [h]
    rw [tubeQuot_mk] at h1
    exact h1

/-- **The unconditional torsion bound**: `Torsion(H₂(K3;ℤ))` embeds ℤ-linearly into
`ker tubeQuot`. No hypothesis — this is the exact sense in which `tubeQuot` measures the
remaining torsion: the torsion is trapped inside an explicitly computable kernel, and
`TubeSeparates` says only that this kernel is trivial. -/
def torsionIntoKerTubeQuot :
    ↥(Submodule.torsion ℤ (Homology KummerK3top 2)) →ₗ[ℤ] ↥(LinearMap.ker tubeQuot) :=
  LinearMap.codRestrict _
    (pieceBlock.mkQ.comp (Submodule.torsion ℤ (Homology KummerK3top 2)).subtype)
    (fun t => by
      rw [LinearMap.mem_ker]
      show tubeQuot (Submodule.Quotient.mk (t : Homology KummerK3top 2)) = 0
      rw [tubeQuot_mk]
      exact tubeCoord_eq_zero_of_torsion t.2)

theorem torsionIntoKerTubeQuot_injective : Function.Injective torsionIntoKerTubeQuot := by
  intro s t hst
  have h1 : pieceBlock.mkQ ((s : Homology KummerK3top 2) - (t : Homology KummerK3top 2)) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val hst
  have h2 : (s : Homology KummerK3top 2) - (t : Homology KummerK3top 2) ∈ pieceBlock :=
    (Submodule.Quotient.mk_eq_zero _).mp h1
  have h3 : (s : Homology KummerK3top 2) - (t : Homology KummerK3top 2)
      ∈ Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock :=
    Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ s.2 t.2, h2⟩
  rw [torsion_inf_pieceBlock_eq_bot] at h3
  exact Subtype.ext (sub_eq_zero.mp h3)

/-! ## §6. What `TubeParity` buys — the Kummer even-weight condition -/

/-- **Unconditional**: if `2y` is the exceptional combination `v`, then `tubeCoord y` is `v` mod 2.
The tube coordinate literally reads off *which* exceptional classes are being halved. -/
theorem tubeCoord_of_two_smul_eq_exceptional {y : Homology KummerK3top 2} {v : EIndex → ℤ}
    (h : (2 : ℤ) • y = exceptionalEmbed v) : tubeCoord y = redMod2 v := by
  have hE : exceptionalEmbed v = Sigma2 (0, eImageH2EquivInt.symm v) := by
    simp only [exceptionalEmbed, LinearMap.comp_apply, LinearMap.inr_apply,
      LinearEquiv.coe_toLinearMap]
  have h1 : Sigma2 (sigma2SourceEquiv.symm (blockCoord y))
      = Sigma2 (0, eImageH2EquivInt.symm v) := by
    rw [sigma2_blockCoord, h, hE]
  have h2 : sigma2SourceEquiv.symm (blockCoord y) = (0, eImageH2EquivInt.symm v) :=
    k7Sum2_injective h1
  have h3 : blockCoord y = sigma2SourceEquiv (0, eImageH2EquivInt.symm v) := by
    rw [← h2, LinearEquiv.apply_symm_apply]
  have h4 : (sigma2SourceEquiv (0, eImageH2EquivInt.symm v)).2 = v := by
    simp [sigma2SourceEquiv]
  show redMod2 ((blockCoord y).2) = redMod2 v
  rw [h3, h4]

/-- **Under `TubeParity`, an exceptional combination can only be halved with even weight.** This is
the classical Kummer-lattice condition: the sums of exceptional classes that become divisible by 2
in `H₂(K3;ℤ)` form an even-weight binary code. It combines the tube reading
(`tubeCoord_of_two_smul_eq_exceptional`) with the landed δ₁-image parity cut
(`delta1_image_parity`). -/
theorem exceptional_half_even_weight (hTP : TubeParity) {y : Homology KummerK3top 2}
    {v : EIndex → ℤ} (h : (2 : ℤ) • y = exceptionalEmbed v) :
    (∑ c, ((v c : ℤ) : ZMod 2)) = 0 := by
  have h2 := delta1_image_parity (w := k7Delta 1 y) ⟨y, rfl⟩
  rw [← hTP y, tubeCoord_of_two_smul_eq_exceptional h] at h2
  exact h2

/-- **Under `TubeParity` no single exceptional class is 2-divisible in `H₂(K3;ℤ)`** — the 16
exceptional spheres are primitive classes. A concrete falsifiable consequence, and the standard
Kummer-surface fact: weight-1 vectors are not in the even-weight Kummer code. -/
theorem exceptional_not_two_divisible (hTP : TubeParity) (c : EIndex)
    (y : Homology KummerK3top 2) :
    (2 : ℤ) • y ≠ exceptionalEmbed (Pi.single c (1 : ℤ) : EIndex → ℤ) := by
  intro h
  have h1 := exceptional_half_even_weight hTP h
  have h2 : ∀ d : EIndex, (((Pi.single c (1 : ℤ) : EIndex → ℤ) d : ℤ) : ZMod 2)
      = (Pi.single c (1 : ZMod 2) : EIndex → ZMod 2) d := by
    intro d
    by_cases hd : d = c
    · subst hd; simp
    · rw [Pi.single_eq_of_ne hd, Pi.single_eq_of_ne hd]; simp
  rw [Finset.sum_congr rfl (fun d _ => h2 d)] at h1
  rw [show (∑ d, (Pi.single c (1 : ZMod 2) : EIndex → ZMod 2) d) = 1 from
    SKEFTHawking.KummerK7Delta1Image.sumF_single_one c] at h1
  exact one_ne_zero h1

end

end SKEFTHawking.KummerK3TorsionFree
