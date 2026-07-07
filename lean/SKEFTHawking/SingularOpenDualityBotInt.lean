/-
# Phase 5q.H (E1 CSC-PD tower) — integral `legW₀`/`openDuality₀` (bottom `H₀`-valued duality), §1–§2

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityBot`. The bottom (`H₀`-valued) analogue of
`legW`/`openDuality`, built on the on-main integral d=0 local duality `SingularLocalDualityKBotInt`
(`relativeDualityK₀Int`). Needed for the binary-cover five-lemma of the integral PD cover-induction
(the connecting square's `U∩V` side lands in `openDuality₀`).

This module: §1 the `castChainInt`-headed transport helpers (`subst`-liners) + §2 the bottom-presented
fundamental cycle `fundCycleW₀Int` (the `(k,0)`-instance of `fundCycleW`, recast to the `(k+1)`-spelling).
§3 (the bottom `relativeDualityK₀Int` restrict/cycle-compat — TORSION-SAFE, ℤ-difference form, NOT the
mod-2 `add_self`/`neg_eq_self` route) + §4 (`legW₀Int`/`openDuality₀Int`) follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularOpenDualityMVConnSquareInt
import SKEFTHawking.SingularLocalDualityKBotInt
import SKEFTHawking.SingularLocalDualityKCycleInt
import SKEFTHawking.SingularCompactlySupportedOpenInt
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCapSupportInt
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularFundCycleOpen (interiors_cover_of_compact_subset_open)
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityCycleInt
open SKEFTHawking.SingularOpenDualityMVConnSquareInt
open SKEFTHawking.SingularLocalDualityKBotInt
open SKEFTHawking.SingularLocalDualityKCycleInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)

namespace SKEFTHawking.SingularOpenDualityBotInt

variable {X : TopCat}

/-! ## §1. `castChainInt`-headed transport helpers (generic `subst`-liners) -/

private theorem castChainInt_mem_subspaceChainsInt {a b : ℕ} (e : a = b) {S : Set ↑X}
    {c : SingularChainInt X a} (hc : c ∈ subspaceChainsInt S a) :
    castChainInt e c ∈ subspaceChainsInt S b := by
  subst e; rw [castChainInt_eq]; exact hc

private theorem chainBoundary_castChainInt {a b : ℕ} (e : a + 1 = b + 1) (e' : a = b)
    (c : SingularChainInt X (a + 1)) :
    chainBoundary X b (castChainInt e c) = castChainInt e' (chainBoundary X a c) := by
  subst e'; rw [castChainInt_eq, castChainInt_eq]

/-- The ℤ-difference form of the `relB` transport (the general integral family uses the honest
`RelativeChainInt.mk`-difference, not the mod-2 `coprod`-sum). -/
private theorem relB_pair_castChainInt {a b : ℕ} (e : a = b) {S : Set ↑X}
    (x y : SingularChainInt X a)
    (h : RelativeChainInt.mk S a x - RelativeChainInt.mk S a y ∈ relBoundariesInt S a) :
    RelativeChainInt.mk S b (castChainInt e x) - RelativeChainInt.mk S b (castChainInt e y)
      ∈ relBoundariesInt S b := by
  subst e; rw [castChainInt_eq, castChainInt_eq]; exact h

/-! ## §2. The bottom-presented fundamental cycle (single-choice: the `(k, 0)`-instance recast) -/

/-- The `(k, 0)`-instance of the integral `fundCycleW` (the SAME `.choose`), presented at the clean
`(k+1)`-spelling through `castChainInt`. -/
noncomputable def fundCycleW₀Int [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    SingularChainInt X (k + 1) :=
  castChainInt rfl (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀Int_mem_W [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    fundCycleW₀Int hW z₀ hz₀ K ∈ subspaceChainsInt W (k + 1) :=
  castChainInt_mem_subspaceChainsInt (a := k + 0 + 1) (b := k + 1) rfl
    (fundCycleW_mem_W (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀Int_boundary [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X k (fundCycleW₀Int hW z₀ hz₀ K) ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) k := by
  rw [fundCycleW₀Int, chainBoundary_castChainInt (a := k + 0) (b := k) rfl rfl]
  exact castChainInt_mem_subspaceChainsInt (a := k + 0) (b := k) rfl
    (fundCycleW_boundary (k := k) (m := 0) hW z₀ hz₀ K)

/-! ## §3. Bottom restriction / cycle compatibility for `relativeDualityK₀Int` (torsion-safe) -/

/-- **Bottom restriction compatibility** (`relativeDualityK₀Int` under `relCohomRestrictInt`). Both sides
cap the same `z` against the same underlying cochain (`relCocycleRestrictInt` is retype-identity). -/
theorem relativeDualityK₀Int_restrict_compat {k : ℕ} {K : Set ↑X}
    (z : SingularChainInt X (k + 1)) {S T : Set ↑X} (h : S ⊆ T)
    (hzK : z ∈ subspaceChainsInt K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k)
    (hzT : chainBoundary X k z ∈ subspaceChainsInt T k)
    (x : RelativeCohomologyInt T (k + 1)) :
    relativeDualityK₀Int S K k z hzK hzS (relCohomRestrictInt h (k + 1) x)
      = relativeDualityK₀Int T K k z hzK hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomologyInt T (k + 1))
      = RelativeCohomologyInt.mk T (k + 1) a := rfl
  rw [hx, relCohomRestrictInt_mk, relativeDualityK₀Int_mk, relativeDualityK₀Int_mk]
  apply congrArg (Homology.mk (sub K) 0)
  apply Subtype.ext
  apply chainIncl_injective K 0
  rw [chainIncl_pullbackDualityIntₗ₀, chainIncl_pullbackDualityIntₗ₀]
  rfl

/-- **Bottom chain-level boundary core** (torsion-safe, ℤ-difference form). If `ac` vanishes on
`S`-simplices and is an absolute cocycle, and `u + ∂wW ∈ C(S)` with `u`, `wW` both `W`-supported, then
the pulled-back `cap ac u` is a boundary of `sub W` at degree `0`. The witness bounding chain is
`(-1)^{(k+1)+1} • (ac ⌢ wW)`: the sign makes `∂((-1)^{(k+1)+1}•(ac⌢wW)) = (-1)^{2(k+1)+1}•(ac⌢∂wW)
= -(ac⌢∂wW) = ac⌢u` (using `ac⌢(u+∂wW)=0`). The mod-2 mirror's `ZModModule.add_self` HIDES this real
sign (over `ℤ/2`, `+ = -`). -/
theorem cap_pullback_mem_boundaries_of_relBoundaryW₀Int {k : ℕ} {S W : Set ↑X}
    (ac : SingularCochainInt X (k + 1))
    (hav : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (k + 1)))),
      ac (simplexIncl S (k + 1) τ) = 0)
    (hδ : coboundaryₗ X (k + 1) ac = 0)
    (u : SingularChainInt X (k + 1)) (wW : SingularChainInt X (k + 1 + 1))
    (huW : u ∈ subspaceChainsInt W (k + 1)) (hwW : wW ∈ subspaceChainsInt W (k + 1 + 1))
    (hrel : u + chainBoundary X (k + 1) wW ∈ subspaceChainsInt S (k + 1)) :
    (inclRangeEquiv W 0).symm ⟨capInt (m := 0) ac u, capInt_mem_subspaceChainsInt W ac huW⟩
      ∈ boundaries (sub W) 0 := by
  refine inclRangeEquiv_symm_mem_boundaries₀Int W (capInt (m := 0) ac u) _
    ((-1 : ℤ) ^ (k + 1 + 1) • capInt (m := 1) ac wW)
    (Submodule.smul_mem _ _ (capInt_mem_subspaceChainsInt W ac hwW)) ?_
  rw [map_smul, capInt_cocycle_chainMap (m := 0) ac hδ wW, smul_smul, ← pow_add]
  have hodd : Odd ((k + 1 + 1) + (k + 1)) := ⟨k + 1, by ring⟩
  rw [hodd.neg_one_pow, neg_one_smul]
  have hz := capInt_subspaceChainInt_eq_zero (m := 0) S ac hav hrel
  rw [map_add] at hz
  exact neg_eq_of_add_eq_zero_left hz

/-- **Bottom cycle-difference compatibility** (torsion-safe, ℤ-difference form). `D_W⁰` is independent of
the `W`-supported relative-cycle representative within a relative homology class. -/
theorem relativeDualityK₀Int_cycle_compat {k : ℕ} {S W : Set ↑X}
    (z z' : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt W (k + 1)) (hz'K : z' ∈ subspaceChainsInt W (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k)
    (hz'S : chainBoundary X k z' ∈ subspaceChainsInt S k)
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChainInt X (k + 1 + 1))
    (hw : (z - z') + chainBoundary X (k + 1) w ∈ subspaceChainsInt S (k + 1))
    (x : RelativeCohomologyInt S (k + 1)) :
    relativeDualityK₀Int S W k z hzK hzS x = relativeDualityK₀Int S W k z' hz'K hz'S x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hsmall : z - z' ∈ smallChainsInt ({W, S} : Set (Set ↑X)) (k + 1) :=
    subspaceChainsInt_le_smallChainsInt (Set.mem_insert _ _) (k + 1)
      (Submodule.sub_mem _ hzK hz'K)
  have hrcyc : chainBoundary X k (z - z') ∈ subspaceChainsInt S k := by
    rw [map_sub]; exact Submodule.sub_mem _ hzS hz'S
  obtain ⟨w', hw'small, hw'rel⟩ := relative_small_boundaryInt hcov hsmall hrcyc hw
  obtain ⟨wW, hwW, wS, hwS, hsplit⟩ :=
    Submodule.mem_sup.mp (smallChainsInt_two_le W S (k + 1 + 1) hw'small)
  have hwWrel : (z - z') + chainBoundary X (k + 1) wW ∈ subspaceChainsInt S (k + 1) := by
    have hbdeq : chainBoundary X (k + 1) wW
        = chainBoundary X (k + 1) w' - chainBoundary X (k + 1) wS :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [hbdeq, ← add_sub_assoc]
    exact Submodule.sub_mem _ hw'rel (chainBoundary_mem_subspaceChainsInt S (k + 1) wS hwS)
  have hmem := cap_pullback_mem_boundaries_of_relBoundaryW₀Int (S := S) (W := W) a.1.1
    (relCochainInt_vanish S a.1) (relCocycleInt_coboundary_zero S a) (z - z') wW
    (Submodule.sub_mem _ hzK hz'K) hwW hwWrel
  have hpull : pullbackDualityIntₗ₀ S W z hzK a - pullbackDualityIntₗ₀ S W z' hz'K a
      = (inclRangeEquiv W 0).symm ⟨capInt (m := 0) a.1.1 (z - z'),
          capInt_mem_subspaceChainsInt W a.1.1 (Submodule.sub_mem _ hzK hz'K)⟩ := by
    apply chainIncl_injective W 0
    rw [map_sub, chainIncl_pullbackDualityIntₗ₀, chainIncl_pullbackDualityIntₗ₀,
      chainIncl_inclRangeEquiv_symm]
    show capInt (m := 0) a.1.1 z - capInt (m := 0) a.1.1 z' = capInt (m := 0) a.1.1 (z - z')
    rw [map_sub]
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S (k + 1))
      = RelativeCohomologyInt.mk S (k + 1) a from rfl,
    relativeDualityK₀Int_mk, relativeDualityK₀Int_mk, Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, map_sub]
  show pullbackDualityIntₗ₀ S W z hzK a - pullbackDualityIntₗ₀ S W z' hz'K a
    ∈ boundaries (sub W) 0
  rw [hpull]
  exact hmem

/-- **`relBoundaries`-form of the bottom cycle-difference compatibility** (torsion-safe). -/
theorem relativeDualityK₀Int_cycle_compat_relB {k : ℕ} {S W : Set ↑X}
    (z z' : SingularChainInt X (k + 1))
    (hzK : z ∈ subspaceChainsInt W (k + 1)) (hz'K : z' ∈ subspaceChainsInt W (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChainsInt S k)
    (hz'S : chainBoundary X k z' ∈ subspaceChainsInt S k)
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (hrel : RelativeChainInt.mk S (k + 1) z - RelativeChainInt.mk S (k + 1) z'
        ∈ relBoundariesInt S (k + 1))
    (x : RelativeCohomologyInt S (k + 1)) :
    relativeDualityK₀Int S W k z hzK hzS x = relativeDualityK₀Int S W k z' hz'K hz'S x := by
  obtain ⟨wRel, hwRel⟩ := hrel
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  refine relativeDualityK₀Int_cycle_compat z z' hzK hz'K hzS hz'S hcov (-w) ?_ x
  have h1 : (Submodule.Quotient.mk (chainBoundary X (k + 1) w) : RelativeChainInt S (k + 1))
      = Submodule.Quotient.mk z - Submodule.Quotient.mk z' := hwRel
  rw [← RelativeChainInt.mk_eq_zero_iff]
  show Submodule.Quotient.mk ((z - z') + chainBoundary X (k + 1) (-w))
    = (0 : RelativeChainInt S (k + 1))
  rw [map_neg, Submodule.Quotient.mk_add, Submodule.Quotient.mk_neg, Submodule.Quotient.mk_sub, h1]
  abel

/-! ## §4. `legW₀Int` and its colimit — the bottom duality legs -/

variable [T2Space ↑X]

/-- **The bottom per-compact duality leg** `legW₀Int : Hᵏ⁺¹(M|K;ℤ) → H₀(sub W;ℤ)`. -/
noncomputable def legW₀Int {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    cohomGWInt W (k + 1) K →ₗ[ℤ] Homology (sub W) 0 :=
  relativeDualityK₀Int ((↑K.1 : Set ↑X)ᶜ) W k (fundCycleW₀Int hW z₀ hz₀ K)
    (fundCycleW₀Int_mem_W hW z₀ hz₀ K) (fundCycleW₀Int_boundary hW z₀ hz₀ K)

/-- **The bottom duality-leg colimit compatibility** (integral): the restriction move, then the `relB`
cycle swap (ℤ-difference `fundCycleW_relHomologous`), with the rel-homology glue at the native
`(k+0+1)`-spelling transported through `castChainInt` once (`relB_pair_castChainInt`). -/
theorem legW₀Int_compat {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K K' : CompactsIn W) (h : K ≤ K') (x : cohomGWInt W (k + 1) K) :
    legW₀Int hW z₀ hz₀ K' (cohomFWInt W (k + 1) K K' h x) = legW₀Int hW z₀ hz₀ K x := by
  have hKK' : (↑K'.1 : Set ↑X)ᶜ ⊆ (↑K.1 : Set ↑X)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr h)
  have hzK'_S : chainBoundary X k (fundCycleW₀Int hW z₀ hz₀ K')
      ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) k :=
    subspaceChainsInt_mono hKK' k (fundCycleW₀Int_boundary hW z₀ hz₀ K')
  have step1 : legW₀Int hW z₀ hz₀ K' (cohomFWInt W (k + 1) K K' h x)
      = relativeDualityK₀Int ((↑K.1 : Set ↑X)ᶜ) W k (fundCycleW₀Int hW z₀ hz₀ K')
          (fundCycleW₀Int_mem_W hW z₀ hz₀ K') hzK'_S x :=
    relativeDualityK₀Int_restrict_compat (fundCycleW₀Int hW z₀ hz₀ K') hKK'
      (fundCycleW₀Int_mem_W hW z₀ hz₀ K') (fundCycleW₀Int_boundary hW z₀ hz₀ K') hzK'_S x
  rw [step1, legW₀Int]
  refine relativeDualityK₀Int_cycle_compat_relB (fundCycleW₀Int hW z₀ hz₀ K')
    (fundCycleW₀Int hW z₀ hz₀ K)
    (fundCycleW₀Int_mem_W hW z₀ hz₀ K') (fundCycleW₀Int_mem_W hW z₀ hz₀ K) hzK'_S
    (fundCycleW₀Int_boundary hW z₀ hz₀ K)
    (interiors_cover_of_compact_subset_open K.1.isCompact' hW K.2) ?_ x
  -- the rel-homology glue (ℤ-difference), at the native (k+0+1)-spelling, then ONE castChainInt transport
  have hglue : RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
        (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
      - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
        (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
      ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) := by
    set S : Set ↑X := (↑K.1 : Set ↑X)ᶜ with hS
    have hA : RelativeChainInt.mk S (k + 0 + 1) z₀
          - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
        ∈ relBoundariesInt S (k + 0 + 1) :=
      fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
    have hB' : RelativeChainInt.mk S (k + 0 + 1) z₀
          - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
        ∈ relBoundariesInt S (k + 0 + 1) := by
      have hmono := relBoundaries_monoInt hKK'
        (z₀ - fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
        (by
          show Submodule.Quotient.mk (z₀ - fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
            ∈ relBoundariesInt ((↑K'.1 : Set ↑X)ᶜ) (k + 0 + 1)
          rw [Submodule.Quotient.mk_sub]
          exact fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K')
      have hconv : RelativeChainInt.mk S (k + 0 + 1)
            (z₀ - fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
          = RelativeChainInt.mk S (k + 0 + 1) z₀
            - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K') :=
        Submodule.Quotient.mk_sub _
      rwa [hconv] at hmono
    have heq : RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
          - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
        = (RelativeChainInt.mk S (k + 0 + 1) z₀
            - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K))
          - (RelativeChainInt.mk S (k + 0 + 1) z₀
            - RelativeChainInt.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')) := by
      abel
    rw [heq]
    exact Submodule.sub_mem _ hA hB'
  exact relB_pair_castChainInt (a := k + 0 + 1) (b := k + 1) rfl _ _ hglue

/-- **The bottom open Poincaré-duality map** `D_W⁰ : Hᵏ⁺¹_c(W;ℤ) → H₀(sub W;ℤ)`. -/
noncomputable def openDuality₀Int {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) :
    CompactlySupportedCohomologyOpenInt W (k + 1) →ₗ[ℤ] Homology (sub W) 0 :=
  Module.DirectLimit.lift ℤ (CompactsIn W) (cohomGWInt W (k + 1)) (cohomFWInt W (k + 1))
    (legW₀Int hW z₀ hz₀) (fun K K' h x => legW₀Int_compat hW z₀ hz₀ K K' h x)

/-- **Computation rule for `D_W⁰`** on a `K`-stage class. -/
@[simp] theorem openDuality₀Int_of {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) (a : cohomGWInt W (k + 1) K) :
    openDuality₀Int hW z₀ hz₀
        (Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W (k + 1)) (cohomFWInt W (k + 1)) K a)
      = legW₀Int hW z₀ hz₀ K a :=
  Module.DirectLimit.lift_of _ _ a

end SKEFTHawking.SingularOpenDualityBotInt
