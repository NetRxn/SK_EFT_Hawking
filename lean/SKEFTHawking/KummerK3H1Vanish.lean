/-
# Phase 5q.H — K10 span 2 residual: the degree-1 weld cokernel, `H₁(K3;ℤ) = 0`

The `h1Free` field of `KummerK3E1Package.KummerK3E1Residuals` asks for `Module.Free ℤ (H₁(K3;ℤ))`.
Freeness is the weak shadow of the real fact, `H₁(K3;ℤ) = 0`; this module proves the vanishing
(and derives the freeness from it) modulo ONE named geometric residual, and closes every other
link of the chain.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerK7H1Window
import SKEFTHawking.KummerK7Delta1Image

namespace SKEFTHawking.KummerK3H1Vanish

open SKEFTHawking.SingularHomologyInt (Homology SingularChainInt chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt mapChainInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt mvHomDiagInt_apply
  mvHomSumInt_apply)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (EIndex eImage)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop qmkC tauC)
open SKEFTHawking.KummerRP3Covering (normChain diffChain chainBoundary_diffChain)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3SmithSES (hmlEquivHomology)
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.KummerQuotientDeckFunctional (qDeck qDeckHml qDeck_qBdryMap qBdryMapC
  genRP3Class phiB phiB_mk psiB psiB_spec kerD_eq_Amod)
open SKEFTHawking.KummerK7MVAssembly
open SKEFTHawking.KummerK7Delta1Image (qThickEquiv_incl_single zmod2_cases)
open SKEFTHawking.KummerK7H1Window (k7H1_surjective_from_qThick)

open scoped SKEFTHawking.KummerK7Delta1Image

noncomputable section

/-! ## §1. The 16 seam classes of `H₁(Q;ℤ)` and the subgroup they span -/

/-- **The `c`-th seam class of `H₁(Q;ℤ)`** — the image of the pinned `H₁(ℝP³;ℤ)` generator under
the `c`-th seam boundary map `qBdryMap c : ℝP³ → Q`. -/
def seamClass (c : EIndex) : Homology Qtop 1 :=
  Homology.mapInt (qBdryMapC c) 1 genRP3Class

/-- **The seam subgroup of `H₁(Q;ℤ)`** — the ℤ-span of the 16 seam classes. This is exactly the
subgroup the weld kills: `H₁(K3;ℤ)` is `H₁(Q;ℤ)` modulo it (§2–§3). -/
def seamSpan : Submodule ℤ (Homology Qtop 1) :=
  Submodule.span ℤ (Set.range seamClass)

theorem seamClass_mem_seamSpan (c : EIndex) : seamClass c ∈ seamSpan :=
  Submodule.subset_span ⟨c, rfl⟩

/-! ## §2. The Mayer–Vietoris cut: the collar's `H₁` dies in `H₁(K3;ℤ)` -/

/-- **The collar leg is killed by the weld**: a class pushed from the collar into `qThick` and
then into `K3` vanishes. `Σ₁ ∘ Δ₁ = 0` (K7 MV exactness at the middle) plus `H₁(eImage;ℤ) = 0`
removes the `E`-side term. -/
theorem ambIncl_collar_eq_zero (w : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) 1) :
    Homology.mapInt (ambIncl (X := KummerK3top) qThick) 1
        (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1 w) = 0 := by
  have h := (k7_exact_middle 0).apply_apply_eq_zero w
  rw [mvHomDiagInt_apply, mvHomSumInt_apply,
    eImageH1_eq_zero (Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_right (s := qThick) (t := eImage))) 1 w), map_zero, sub_zero] at h
  exact h

/-- **The degree-1 weld cokernel, exactly**: if the collar leg `H₁(collar;ℤ) → H₁(qThick;ℤ)` is
onto then `H₁(K3;ℤ) = 0`. `Σ₁` is onto (`k7Sum1_surjective`, from `δ₀ = 0`) and
`H₁(eImage;ℤ) = 0`, so every `K3` class comes from `qThick`; §2's cut then kills it. -/
theorem h1K3_eq_zero_of_collar_range
    (hs : LinearMap.range (Homology.mapInt (subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))) 1) = ⊤)
    (x : Homology KummerK3top 1) : x = 0 := by
  obtain ⟨u, hu⟩ := k7H1_surjective_from_qThick x
  obtain ⟨w, hw⟩ : u ∈ LinearMap.range (Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_left (s := qThick) (t := eImage))) 1) := by
    rw [hs]; trivial
  rw [← hu, ← hw, ambIncl_collar_eq_zero]

/-! ## §3. The collar leg's image IS the seam span -/

/-- **The seam classes are hit by the collar leg** — the `c`-th collar generator maps to the `c`-th
seam class under the thickening identification `H₁(qThick;ℤ) ≅ H₁(Q;ℤ)`. -/
theorem seamClass_mem_map_collar_range (c : EIndex) :
    seamClass c ∈ Submodule.map (qThickHnEquivInt 0).toLinearMap
      (LinearMap.range (Homology.mapInt (subIncl (X := KummerK3top)
        (Set.inter_subset_left (s := qThick) (t := eImage))) 1)) :=
  ⟨_, ⟨(interHnEquivInt 0).symm (Pi.single c genRP3Class), rfl⟩, qThickEquiv_incl_single c⟩

/-- **The seam span controls the collar leg**: if the 16 seam classes generate `H₁(Q;ℤ)` then the
collar leg `H₁(collar;ℤ) → H₁(qThick;ℤ)` is onto. -/
theorem collar_range_eq_top_of_seamSpan (h : seamSpan = ⊤) :
    LinearMap.range (Homology.mapInt (subIncl (X := KummerK3top)
      (Set.inter_subset_left (s := qThick) (t := eImage))) 1) = ⊤ := by
  have hspan : (⊤ : Submodule ℤ (Homology Qtop 1)) ≤
      Submodule.map (qThickHnEquivInt 0).toLinearMap
        (LinearMap.range (Homology.mapInt (subIncl (X := KummerK3top)
          (Set.inter_subset_left (s := qThick) (t := eImage))) 1)) := by
    rw [← h, seamSpan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact seamClass_mem_map_collar_range c
  rw [Submodule.eq_top_iff']
  intro u
  obtain ⟨r, hr, hre⟩ := hspan (Submodule.mem_top (x := (qThickHnEquivInt 0) u))
  exact (qThickHnEquivInt 0).injective hre ▸ hr

/-- **`H₁(K3;ℤ) = 0` from the seam-generation of `H₁(Q;ℤ)`** — §2 ∘ §3. -/
theorem h1K3_eq_zero_of_seamSpan (h : seamSpan = ⊤) (x : Homology KummerK3top 1) : x = 0 :=
  h1K3_eq_zero_of_collar_range (collar_range_eq_top_of_seamSpan h) x

/-! ## §4. The Smith side: `ker qDeck = im p_*` -/

/-- **`φ_B : H₀(B;ℤ) → ℤ/2` is injective** — i.e. `H₀(B;ℤ) ≅ ℤ/2`, so the norm-parity functional
sees ALL of the SES-III connecting target.

The `KummerQuotientSmithSES.inclAH_injective` argument, mirrored on `B`: a `B`-class of even
norm-parity is `D c` with `ε(c)` even; subtracting `⌊ε(c)/2⌋·N(basepoint)` (which `D` kills, since
`ker D = A = N·C`) makes the augmentation vanish, path-connectedness of `T⁴°` fills it as `∂v`,
and `D ∂ v = ∂ (D v)` is a `B`-boundary. -/
theorem phiB_injective : Function.Injective phiB := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dB 0 x
  rw [LinearMap.mem_ker, phiB_mk] at hx
  obtain ⟨c, hc⟩ := (z : Bc 0).2
  have hpsi : psiB (z : Bc 0) = ((augmentationInt PTtop c : ℤ) : ZMod 2) := psiB_spec _ c hc
  have hdvd : (2 : ℤ) ∣ augmentationInt PTtop c := by
    rw [hpsi, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
    exact_mod_cast hx
  obtain ⟨k, hk⟩ := hdvd
  have hDN : ∀ y : SingularChainInt PTtop 0, diffChain tauC 0 (normChain tauC 0 y) = 0 := by
    intro y
    have hy : normChain tauC 0 y ∈ Amod 0 := ⟨y, rfl⟩
    rw [← kerD_eq_Amod] at hy
    exact hy
  set c' : SingularChainInt PTtop 0 :=
    c - normChain tauC 0 (k • Finsupp.single baseSimplex (1 : ℤ)) with hc'def
  have haug' : augmentationInt PTtop c' = 0 := by
    rw [hc'def, map_sub, aug_normChain, map_smul, aug_single_baseSimplex, hk]
    ring
  have hD' : diffChain tauC 0 c' = (z : SingularChainInt PTtop 0) := by
    rw [hc'def, map_sub, hDN, sub_zero, hc]
  obtain ⟨v, hv⟩ :=
    SKEFTHawking.SingularH0PathConnectedInt.mem_boundaries_of_augmentationInt_eq_zero
      (X := PTtop) basePt c' haug'
  rw [Hml.mk_eq_zero_iff]
  refine ⟨⟨diffChain tauC 1 v, ⟨v, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show chainBoundary PTtop 0 (diffChain tauC 1 v) = (z : SingularChainInt PTtop 0)
  rw [chainBoundary_diffChain, hv, hD']

/-- **The deck functional's kernel is exactly the lifted part**: `ker qDeck = im (p_* : H₁(T⁴°;ℤ)
→ H₁(Q;ℤ))`. The `⊇` half is `qDeckHml_projH`; this is the substantive `⊆` half — `qDeck` is
`φ_B ∘ δ₀` with `φ_B` injective (§4), so a deck-even class has vanishing SES-III connecting image
and is lifted by exactness. -/
theorem mem_range_projH_of_qDeckHml_eq_zero {x : Hml (chainBoundary Qtop) 1}
    (hx : qDeckHml x = 0) : x ∈ LinearMap.range (projH 1) := by
  have h : deltaIII 0 x = 0 := phiB_injective (by rw [map_zero]; exact hx)
  exact (exact_projH_deltaIII 0 x).mp h

/-- The engine's SES-III epi leg IS the covering projection on homology (both quotient-lift
`p₊ = mapChainInt qmkC`; the carriers agree definitionally at positive degree). -/
theorem projH_eq_mapInt (n : ℕ) (x : Hml (chainBoundary PTtop) (n + 1)) :
    projH (n + 1) x = Homology.mapInt qmkC (n + 1) x := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary PTtop) (n + 1) x
  rfl

/-- `qDeck` in engine form (the `Hml`/`Homology` carriers agree at positive degree). -/
theorem qDeck_eq_qDeckHml (x : Homology Qtop 1) : qDeck x = qDeckHml x := rfl

/-! ## §5. The residual, and the reduction of `H₁(K3;ℤ) = 0` to it -/

/-- **THE ONE RESIDUAL of the `h1Free` span** — *the images of the four `T⁴`-lattice circles lie in
the seam span.*

Geometrically: `π₁(Q) = ℤ⁴ ⋊ ⟨σ⟩` with `σ` acting by `−1`, and the seam at the fixed point of
half-period `v` is the element `t_{2v} σ`; so `seamClass v − seamClass v' = t_{2v−2v'}`, and as
`v, v'` range over the 16 half-periods the differences realise every class of `ℤ⁴/2ℤ⁴` — i.e. the
whole of `im p_*` (which is `ℤ⁴` modulo `im(1 − τ_*) = 2ℤ⁴`).

**Discharge plan.** The seam-difference identity is a loop computation in `T⁴°`: for a path `δ`
from `sphereEmbedPT c' sBase` to `sphereEmbedPT c sBase`, the loop
`δ ⬝ γ_c ⬝ (τ∘δ)⁻¹ ⬝ γ_{c'}⁻¹` (with `γ_c` the sphere half-loop of
`KummerQuotientDeckFunctional.liftChain`) projects to `seamClass c − seamClass c'`, and its class in
`H₁(T⁴°;ℤ)` is the lattice vector `2v_c − 2v_{c'}`, evaluated by the four winding functionals
(`KummerCircleInvolutionWind` / `CircleWindingCocycle`) against
`KummerPuncturedMV.puncture_hX1`'s `H₁(T⁴°;ℤ) ↪ H₁(T⁴;ℤ)`. This is the SUFFICIENCY counterpart of
the four translation rows named as the sharp residual in `KummerK7Delta1Image`'s header. -/
def QLatticeInSeamSpan : Prop :=
  ∀ y : Homology PTtop 1, Homology.mapInt qmkC 1 y ∈ seamSpan

/-- **The residual generates**: `im p_* ⊆ ⟨seams⟩` upgrades to `⟨seams⟩ = H₁(Q;ℤ)`, because a
deck-ODD class differs from a seam class (each of which is deck-odd, `qDeck_qBdryMap`) by a
deck-even one, and deck-even classes are lifted (§4). -/
theorem seamSpan_eq_top_of_residual (h : QLatticeInSeamSpan) : seamSpan = ⊤ := by
  haveI : Nonempty EIndex :=
    Fintype.card_pos_iff.mp (by rw [SKEFTHawking.KummerWeld.eIndex_card]; omega)
  have hlift : ∀ x : Homology Qtop 1, qDeck x = 0 → x ∈ seamSpan := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_range_projH_of_qDeckHml_eq_zero
      (x := (x : Hml (chainBoundary Qtop) 1)) (by rw [← qDeck_eq_qDeckHml]; exact hx)
    rw [projH_eq_mapInt 0] at hy
    exact hy ▸ h y
  rw [Submodule.eq_top_iff']
  intro x
  set c₀ : EIndex := Classical.arbitrary EIndex with hc₀
  rcases zmod2_cases (qDeck x) with h0 | h1
  · exact hlift x h0
  · have hd : qDeck (x - seamClass c₀) = 0 := by
      rw [map_sub, h1, seamClass, qDeck_qBdryMap, sub_self]
    have := hlift _ hd
    have hx : x = (x - seamClass c₀) + seamClass c₀ := by abel
    rw [hx]
    exact Submodule.add_mem _ this (seamClass_mem_seamSpan c₀)

/-! ## §6. `H₁(K3;ℤ) = 0`, and the `h1Free` atom -/

/-- **`H₁(K3;ℤ) = 0`** on the welded carrier, modulo the §5 residual. -/
theorem h1K3_eq_zero (h : QLatticeInSeamSpan) (x : Homology KummerK3top 1) : x = 0 :=
  h1K3_eq_zero_of_seamSpan (seamSpan_eq_top_of_residual h) x

/-- **`H₁(K3;ℤ)` is trivial** — the `Subsingleton` form. -/
theorem subsingleton_h1K3 (h : QLatticeInSeamSpan) : Subsingleton (Homology KummerK3top 1) :=
  ⟨fun a b => by rw [h1K3_eq_zero h a, h1K3_eq_zero h b]⟩

/-- **The `h1Free` residual field of `KummerK3E1Package.KummerK3E1Residuals`**, derived from the
vanishing — NOT assumed, and not obtained from a finiteness+freeness shortcut. -/
theorem free_h1K3 (h : QLatticeInSeamSpan) : Module.Free ℤ (Homology KummerK3top 1) :=
  haveI := subsingleton_h1K3 h
  Module.Free.of_subsingleton ℤ _

end

end SKEFTHawking.KummerK3H1Vanish
