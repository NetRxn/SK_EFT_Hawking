/-
# Phase 5q.H — K7 residual (b): the δ₁-image window — coker Σ₂, torsion, and the `b₂ = 22` free part

The unconditional structural consequences of the landed collar-thickened Mayer–Vietoris
(`KummerK7MVAssembly`) + the unconditional `H₂(Q;ℤ) ≅ ℤ⁶` (`KummerPuncturedMV`), sharpening the
`b₂ = 22` window toward the exact `H₂(K3;ℤ)` computation:

* **The δ₁-image window** (`ker_k7Delta_one`, `range_k7Delta_one`, `mem_range_k7Delta_one_iff`):
  `ker δ₁ = im Σ₂` and `im δ₁ = ker(H₁(collar) → H₁(qThick))` — the δ₁-image IS the kernel of the
  seam-to-`Q` map on `H₁` (the `E`-side is dead: `H₁(eImage) = 0`).
* **coker Σ₂ pinned to the δ₁ image** (`cokerSigma2Equiv`): `H₂(K3;ℤ)/im Σ₂ ≅ im δ₁`, an
  elementary abelian 2-group (`two_smul_cokerSigma2`) embedding in `H₁(collar) ≅ (ℤ/2)¹⁶`
  (`cokerSigma2Embed`, injective).
* **Torsion status, honest**: `Torsion(H₂) ∩ im Σ₂ = ⊥` (`torsion_inf_pieceBlock_eq_bot`), every
  torsion class is 2-torsion (`torsion_two_smul_eq_zero`), and the torsion subgroup embeds
  ℤ-linearly in `(ℤ/2)¹⁶` (`torsionEmbed_injective`) — so it is finite elementary abelian of
  2-rank ≤ 16 (`finite_torsion`).
* **`H₂(K3;ℤ)` is finitely generated** (`kummerK3_H2_finite`) with **free part exactly `ℤ²²`**:
  `finrank ℤ (H₂/T) = 22` (`finrank_freePart`), `H₂(K3;ℤ)/T ≅ ℤ²²` (`freePartEquiv`), and
  `Module.rank ℤ H₂(K3;ℤ) = 22` (`kummerK3_H2_rank`) — the `b₂ = 22` rank pin, unconditional.
* **The sharp residual** (`kummerK3_H2_equiv_of_torsion_free`): `H₂(K3;ℤ) ≅ ℤ²²` on the nose
  ⟸ `Torsion(H₂(K3;ℤ)) = ⊥`. The remaining gap to `kummerK3_b2_target` is EXACTLY the
  torsion-freeness question, which the δ₁-image computation (`im δ₁` sized `2¹¹` forces
  `coker Σ₂` odd-free… ) attacks through `mem_range_k7Delta_one_iff`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerPuncturedMV

namespace SKEFTHawking.KummerK7Delta1Window

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt mvHomDiagInt_apply)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (EIndex eImage)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.KummerPuncturedMV (qH2EquivInt)

noncomputable section

/-! ## §1. The canonical pieces -/

/-- The MV piece-sum `Σ₂ : H₂(qThick) × H₂(eImage) → H₂(K3;ℤ)`. -/
abbrev Sigma2 :
    Homology (sub (X := KummerK3top) qThick) 2 × Homology (sub (X := KummerK3top) eImage) 2
      →ₗ[ℤ] Homology KummerK3top 2 :=
  mvHomSumInt (X := KummerK3top) qThick eImage 2

/-- **The piece block** `im Σ₂ ⊆ H₂(K3;ℤ)` — the canonical rank-22 free sublattice. -/
abbrev pieceBlock : Submodule ℤ (Homology KummerK3top 2) := LinearMap.range Sigma2

/-- The Σ₂-source is (unconditionally) `ℤ⁶ × ℤ¹⁶`. -/
def sigma2SourceEquiv :
    (Homology (sub (X := KummerK3top) qThick) 2 × Homology (sub (X := KummerK3top) eImage) 2)
      ≃ₗ[ℤ] ((Fin 6 → ℤ) × (EIndex → ℤ)) :=
  LinearEquiv.prodCongr ((qThickHnEquivInt 1).trans qH2EquivInt) eImageH2EquivInt

/-! ## §2. The δ₁-image window -/

/-- `ker δ₁ = im Σ₂` — MV exactness at `H₂(K3;ℤ)`. -/
theorem ker_k7Delta_one : LinearMap.ker (k7Delta 1) = pieceBlock :=
  (k7_exact_ambient 1).linearMap_ker_eq

/-- `im δ₁ = ker j₁` — MV exactness at `H₁(collar)`. -/
theorem range_k7Delta_one :
    LinearMap.range (k7Delta 1)
      = LinearMap.ker (mvHomDiagInt (X := KummerK3top) qThick eImage 1) :=
  ((k7_exact_inter 1).linearMap_ker_eq).symm

/-- **The δ₁-image IS the kernel of the seam-to-`Q` map**: `w ∈ im δ₁` iff `w` dies in
`H₁(qThick;ℤ)` — the `E`-side leg is automatic (`H₁(eImage;ℤ) = 0`). This reduces the δ₁-image
(= coker Σ₂) computation to the single map `H₁(collar) → H₁(qThick) ≅ H₁(Q)`. -/
theorem mem_range_k7Delta_one_iff (w : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 1) :
    w ∈ LinearMap.range (k7Delta 1)
      ↔ Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1 w = 0 := by
  rw [range_k7Delta_one, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    rwa [mvHomDiagInt_apply] at h1
  · intro h
    rw [mvHomDiagInt_apply]
    exact Prod.ext h (eImageH1_eq_zero _)

/-! ## §3. coker Σ₂ ≅ im δ₁ — an elementary abelian 2-group in `(ℤ/2)¹⁶` -/

/-- **coker Σ₂ ≅ im δ₁** — the first-isomorphism pin of the MV cokernel. -/
def cokerSigma2Equiv :
    (Homology KummerK3top 2 ⧸ pieceBlock) ≃ₗ[ℤ] LinearMap.range (k7Delta 1) :=
  (Submodule.quotEquivOfEq pieceBlock (LinearMap.ker (k7Delta 1)) ker_k7Delta_one.symm).trans
    (k7Delta 1).quotKerEquivRange

/-- **coker Σ₂ has exponent 2** — `2·H₂(K3;ℤ) ⊆ im Σ₂`. -/
theorem two_smul_cokerSigma2 (x : Homology KummerK3top 2 ⧸ pieceBlock) : (2 : ℤ) • x = 0 := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk ((2 : ℤ) • y) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  obtain ⟨p, hp⟩ := k7H2_two_smul_mem_range y
  exact ⟨p, hp⟩

/-- **The cokernel embedding** `H₂(K3;ℤ)/im Σ₂ ↪ H₁(collar;ℤ) ≅ (ℤ/2)¹⁶`. -/
def cokerSigma2Embed : (Homology KummerK3top 2 ⧸ pieceBlock) →ₗ[ℤ] (EIndex → ZMod 2) :=
  (interH1EquivInt.toLinearMap.comp (LinearMap.range (k7Delta 1)).subtype).comp
    cokerSigma2Equiv.toLinearMap

theorem cokerSigma2Embed_injective : Function.Injective cokerSigma2Embed :=
  (interH1EquivInt.injective.comp (Submodule.injective_subtype _)).comp
    cokerSigma2Equiv.injective

/-! ## §4. The torsion status of `H₂(K3;ℤ)`, honest -/

/-- **The piece block is torsion-free in `H₂(K3;ℤ)`**: `Torsion(H₂) ∩ im Σ₂ = ⊥` (the block is
the injective image of the free `ℤ²²`). -/
theorem torsion_inf_pieceBlock_eq_bot :
    Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  rw [Submodule.mem_inf] at ht
  obtain ⟨htor, p, rfl⟩ := ht
  obtain ⟨⟨n, hn⟩, hsmul⟩ := (Submodule.mem_torsion_iff _).mp htor
  have h1 : Sigma2 (n • p) = 0 := by rw [map_smul]; exact hsmul
  have h2 : n • p = 0 := k7Sum2_injective (by rw [h1, map_zero])
  have h3 : n • sigma2SourceEquiv p = 0 := by
    rw [← map_smul, h2, map_zero]
  have hn0 : (n : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
  have h4 : sigma2SourceEquiv p = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h hn0
    · exact h
  rw [show p = 0 from sigma2SourceEquiv.map_eq_zero_iff.mp h4, map_zero]

/-- **Every torsion class of `H₂(K3;ℤ)` is 2-torsion**: `2t ∈ im Σ₂` is torsion in a torsion-free
block. -/
theorem torsion_two_smul_eq_zero {t : Homology KummerK3top 2}
    (ht : t ∈ Submodule.torsion ℤ (Homology KummerK3top 2)) : (2 : ℤ) • t = 0 := by
  obtain ⟨p, hp⟩ := k7H2_two_smul_mem_range t
  have h1 : (2 : ℤ) • t ∈ Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock :=
    ⟨Submodule.smul_mem _ _ ht, ⟨p, hp⟩⟩
  rw [torsion_inf_pieceBlock_eq_bot] at h1
  exact h1

/-- **The torsion embedding** `Torsion(H₂(K3;ℤ)) ↪ (ℤ/2)¹⁶` — through the cokernel of the piece
block. -/
def torsionEmbed : ↥(Submodule.torsion ℤ (Homology KummerK3top 2)) →ₗ[ℤ] (EIndex → ZMod 2) :=
  (cokerSigma2Embed.comp pieceBlock.mkQ).comp
    (Submodule.torsion ℤ (Homology KummerK3top 2)).subtype

/-- **The torsion embedding is injective** — a torsion class in the piece block is zero. So the
torsion subgroup of `H₂(K3;ℤ)` is elementary abelian of 2-rank ≤ 16. -/
theorem torsionEmbed_injective : Function.Injective torsionEmbed := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨t, ht⟩ hker
  rw [LinearMap.mem_ker] at hker
  have h0 : cokerSigma2Embed (pieceBlock.mkQ t) = cokerSigma2Embed 0 :=
    hker.trans (map_zero cokerSigma2Embed).symm
  have h1 : pieceBlock.mkQ t = 0 := cokerSigma2Embed_injective h0
  have h2 : t ∈ Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock :=
    Submodule.mem_inf.mpr ⟨ht, (Submodule.Quotient.mk_eq_zero _).mp h1⟩
  rw [torsion_inf_pieceBlock_eq_bot] at h2
  exact Subtype.ext h2

/-- **The torsion subgroup is finite** (it embeds in the 2¹⁶-element `(ℤ/2)¹⁶`). -/
theorem finite_torsion : Finite ↥(Submodule.torsion ℤ (Homology KummerK3top 2)) :=
  Finite.of_injective torsionEmbed torsionEmbed_injective

/-! ## §5. `H₂(K3;ℤ)` is finitely generated; the free part is exactly `ℤ²²` -/

instance : Module.Finite ℤ
    (Homology (sub (X := KummerK3top) qThick) 2 × Homology (sub (X := KummerK3top) eImage) 2) :=
  Module.Finite.equiv sigma2SourceEquiv.symm

instance : Module.Finite ℤ ↥pieceBlock := Module.Finite.range Sigma2

instance : Finite (Homology KummerK3top 2 ⧸ pieceBlock) :=
  Finite.of_injective cokerSigma2Embed cokerSigma2Embed_injective

instance : Module.Finite ℤ (Homology KummerK3top 2 ⧸ pieceBlock) :=
  Module.Finite.of_finite

/-- **`H₂(K3;ℤ)` is finitely generated** — extension of the finite cokernel by the free `ℤ²²`
piece block. -/
theorem kummerK3_H2_finite : Module.Finite ℤ (Homology KummerK3top 2) :=
  Module.Finite.of_submodule_quotient pieceBlock

/-- The torsion quotient `H₂(K3;ℤ)/T` — the free part carrier. -/
abbrev freePart : Type :=
  Homology KummerK3top 2 ⧸ Submodule.torsion ℤ (Homology KummerK3top 2)

/-- `ℤ²² → H₂/T`: the piece block composed into the torsion quotient. -/
def freePartInto : ((Fin 6 → ℤ) × (EIndex → ℤ)) →ₗ[ℤ] freePart :=
  ((Submodule.torsion ℤ (Homology KummerK3top 2)).mkQ.comp Sigma2).comp
    sigma2SourceEquiv.symm.toLinearMap

/-- `ℤ²² ↪ H₂/T` is injective: a piece-block class that is torsion is zero. -/
theorem freePartInto_injective : Function.Injective freePartInto := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  have h1 : Sigma2 (sigma2SourceEquiv.symm v)
      ∈ Submodule.torsion ℤ (Homology KummerK3top 2) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hv
  have h2 : Sigma2 (sigma2SourceEquiv.symm v)
      ∈ Submodule.torsion ℤ (Homology KummerK3top 2) ⊓ pieceBlock :=
    ⟨h1, ⟨_, rfl⟩⟩
  rw [torsion_inf_pieceBlock_eq_bot] at h2
  have h3 : sigma2SourceEquiv.symm v = 0 := k7Sum2_injective (by rw [h2, map_zero])
  rwa [LinearEquiv.map_eq_zero_iff] at h3

/-- The doubling map `H₂(K3;ℤ) → im Σ₂` (well-defined by `2·H₂ ⊆ im Σ₂`). -/
def doubleIntoBlock : Homology KummerK3top 2 →ₗ[ℤ] ↥pieceBlock :=
  LinearMap.codRestrict pieceBlock ((2 : ℤ) • LinearMap.id) (fun x => by
    obtain ⟨p, hp⟩ := k7H2_two_smul_mem_range x
    exact ⟨p, hp⟩)

/-- `H₂/T → ℤ²²`: halve through the piece block (`x̄ ↦ Σ₂⁻¹(2x)`), well-defined and injective
because the 2-torsion is exactly the torsion. -/
def freePartOut : freePart →ₗ[ℤ] ((Fin 6 → ℤ) × (EIndex → ℤ)) :=
  Submodule.liftQ _
    (sigma2SourceEquiv.toLinearMap.comp
      (((LinearEquiv.ofInjective Sigma2 k7Sum2_injective).symm.toLinearMap).comp
        doubleIntoBlock))
    (by
      intro t ht
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
      have h1 : doubleIntoBlock t = 0 := by
        apply Subtype.ext
        show (2 : ℤ) • t = 0
        exact torsion_two_smul_eq_zero ht
      rw [h1, map_zero, map_zero])

theorem freePartOut_injective : Function.Injective freePartOut := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, freePartOut] at hx
  erw [Submodule.liftQ_apply] at hx
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.map_eq_zero_iff, LinearEquiv.coe_toLinearMap,
    LinearEquiv.map_eq_zero_iff] at hx
  have h2 : (2 : ℤ) • y = 0 := by
    have h3 : (2 : ℤ) • y = ((0 : ↥pieceBlock) : Homology KummerK3top 2) :=
      congrArg Subtype.val hx
    simpa using h3
  rw [Submodule.Quotient.mk_eq_zero]
  exact (Submodule.mem_torsion_iff _).mpr ⟨⟨2, by norm_num [mem_nonZeroDivisors_iff_ne_zero]⟩, h2⟩

/-! ### The rank pin -/

instance : Module.Finite ℤ (Homology KummerK3top 2) := kummerK3_H2_finite

instance : Module.Finite ℤ freePart := Module.Finite.quotient ℤ _

instance : Module.IsTorsionFree ℤ freePart :=
  Submodule.QuotientTorsion.instIsTorsionFree

instance : Module.Free ℤ freePart := Module.free_of_finite_type_torsion_free'

theorem finrank_source : Module.finrank ℤ ((Fin 6 → ℤ) × (EIndex → ℤ)) = 22 := by
  rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi, Fintype.card_fin,
    SKEFTHawking.KummerWeld.eIndex_card]

/-- **The free part of `H₂(K3;ℤ)` has rank exactly 22** — the `b₂ = 22` pin, unconditional. -/
theorem finrank_freePart : Module.finrank ℤ freePart = 22 := by
  refine le_antisymm ?_ ?_
  · have h := LinearMap.finrank_le_finrank_of_injective freePartOut_injective
    rwa [finrank_source] at h
  · have h := LinearMap.finrank_le_finrank_of_injective freePartInto_injective
    rwa [finrank_source] at h

/-- **`H₂(K3;ℤ)/Torsion ≅ ℤ²²`** — the free part on the nose. -/
def freePartEquiv : freePart ≃ₗ[ℤ] (Fin 22 → ℤ) :=
  (Module.Free.chooseBasis ℤ freePart).equivFun.trans
    (LinearEquiv.funCongrLeft ℤ ℤ
      (Fintype.equivFinOfCardEq
        (by rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_freePart])).symm)

/-- **`rank H₂(K3;ℤ) = 22`** — the `b₂ = 22` rank headline, unconditional (torsion does not
contribute to rank). -/
theorem kummerK3_H2_rank : Module.rank ℤ (Homology KummerK3top 2) = 22 := by
  have h1 : Module.rank ℤ freePart = Module.rank ℤ (Homology KummerK3top 2) :=
    rank_quotient_eq_of_le_torsion
      (le_refl (Submodule.torsion ℤ (Homology KummerK3top 2)))
  have h2 : Module.rank ℤ freePart = 22 := by
    rw [freePartEquiv.rank_eq]
    simp
  rw [← h1, h2]

/-- **The sharp residual, named**: `H₂(K3;ℤ) ≅ ℤ²²` on the nose ⟸ torsion-freeness. The
remaining gap between the landed window and `kummerK3_b2_target` is EXACTLY
`Torsion(H₂(K3;ℤ)) = ⊥`. -/
theorem kummerK3_H2_equiv_of_torsion_free
    (h : Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥) :
    Nonempty (Homology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ)) :=
  ⟨((Submodule.quotEquivOfEqBot _ h).symm.trans freePartEquiv)⟩

/-- **`b₂ = 22` reaches the target under torsion-freeness** — the named-residual form of
`kummerK3_b2_target`. -/
theorem kummerK3_b2_target_of_torsion_free
    (h : Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  kummerK3_H2_equiv_of_torsion_free h

end

end SKEFTHawking.KummerK7Delta1Window
