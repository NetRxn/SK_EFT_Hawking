import Mathlib
import SKEFTHawking.SingularLocalDualityKBot
import SKEFTHawking.SingularOpenDuality
import SKEFTHawking.SingularOpenDualityMVConnSquare

/-!
# Phase 5q.G (G1 PD-induction, the ₀-family, part 2) — `legW₀` and the bottom open-duality map

The bottom (H₀-valued) analogues of `legW` / `openDuality`: the per-compact duality legs
`legW₀ : Hᵏ⁺¹(M, M∖K) → H₀(sub W)` built on `relativeDualityK₀`, their colimit compatibility
(mirroring `legW_compat`'s two steps — the subspace-restriction move and the `relB` cycle swap),
and the colimit `openDuality₀ : Hᵏ⁺¹_c(W) → H₀(sub W)`.

Single-choice discipline: the fundamental cycles are the `(k, 0)`-instances of the SAME
`fundCycleW` choices the main family uses, presented at the `(k+1)`-spelling through the
project's canonical `castChain` (36th-push friction: a cross-spelling `k+0+1` vs `k+1` defeq
through `subspaceChains`/`SingularChain` walls the unifier, and raw `▸`-wrappers fight Eq.rec
motive mismatches — `castChain`'s stable head is the established fix). The csc-side colimit is
the SAME `CompactlySupportedCohomologyOpen W (k+1)` system the main family uses at `k+1`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap SKEFTHawking.SingularCapSupport
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularLocalDualityKBot
  SKEFTHawking.SingularLocalDualityKCycle SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularExcision SKEFTHawking.SingularRelativeDuality
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularOpenDualityMVConnSquare
  SKEFTHawking.SingularFundCycleOpen

namespace SKEFTHawking.SingularOpenDualityBot

variable {X : TopCat}

/-! ## §1. `castChain`-headed transport helpers (generic `subst`-liners — after `subst` every cast
is a same-index `castChain rfl`, a cheap delta with no cross-index unification) -/

private theorem castChain_mem_subspaceChains {a b : ℕ} (e : a = b) {S : Set ↑X}
    {c : SingularChain X a} (hc : c ∈ subspaceChains S a) :
    castChain e c ∈ subspaceChains S b := by
  subst e; rw [castChain_eq]; exact hc

private theorem chainBoundary_castChain {a b : ℕ} (e : a + 1 = b + 1) (e' : a = b)
    (c : SingularChain X (a + 1)) :
    chainBoundary X b (castChain e c) = castChain e' (chainBoundary X a c) := by
  subst e'; rw [castChain_eq, castChain_eq]

private theorem relB_pair_castChain {a b : ℕ} (e : a = b) {S : Set ↑X}
    (x y : SingularChain X a)
    (h : RelativeChain.mk S a x + RelativeChain.mk S a y ∈ relBoundaries S a) :
    RelativeChain.mk S b (castChain e x) + RelativeChain.mk S b (castChain e y)
      ∈ relBoundaries S b := by
  subst e; rw [castChain_eq, castChain_eq]; exact h

/-! ## §2. The bottom-presented fundamental cycle (single-choice: the `(k,0)`-instance recast) -/

/-- The `(k, 0)`-instance of `fundCycleW` (the SAME `.choose` — single-choice), presented at the
clean `(k+1)`-spelling through `castChain`. -/
noncomputable def fundCycleW₀ [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    SingularChain X (k + 1) :=
  castChain rfl (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀_mem_W [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    fundCycleW₀ hW z₀ hz₀ K ∈ subspaceChains W (k + 1) :=
  castChain_mem_subspaceChains (a := k + 0 + 1) (b := k + 1) rfl
    (fundCycleW_mem_W (k := k) (m := 0) hW z₀ hz₀ K)

theorem fundCycleW₀_boundary [T2Space ↑X] {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    chainBoundary X k (fundCycleW₀ hW z₀ hz₀ K) ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) k := by
  rw [fundCycleW₀, chainBoundary_castChain (a := k + 0) (b := k) rfl rfl]
  exact castChain_mem_subspaceChains (a := k + 0) (b := k) rfl
    (fundCycleW_boundary (k := k) (m := 0) hW z₀ hz₀ K)

/-! ## §3. Bottom restriction / cycle compatibility for `relativeDualityK₀` -/

/-- **Bottom restriction compatibility** (`relativeDualityK₀` under `relCohomRestrict`). -/
theorem relativeDualityK₀_restrict_compat {k : ℕ} {K : Set ↑X}
    (z : SingularChain X (k + 1)) {S T : Set ↑X} (h : S ⊆ T)
    (hzK : z ∈ subspaceChains K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (hzT : chainBoundary X k z ∈ subspaceChains T k)
    (x : RelativeCohomology T (k + 1)) :
    relativeDualityK₀ S K k z hzK hzS (relCohomRestrict h (k + 1) x)
      = relativeDualityK₀ T K k z hzK hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomology T (k + 1))
      = RelativeCohomology.mk T (k + 1) a := rfl
  rw [hx, relCohomRestrict_mk, relativeDualityK₀_mk, relativeDualityK₀_mk]
  apply congrArg (Homology.mk (sub K) 0)
  apply Subtype.ext
  apply chainIncl_injective K 0
  rw [chainIncl_pullbackDualityₗ₀, chainIncl_pullbackDualityₗ₀]
  rfl

/-- **Bottom chain-level boundary core**. -/
theorem cap_pullback_mem_boundaries_of_relBoundaryW₀ {k : ℕ} {S W : Set ↑X}
    (ac : SingularCochain X (k + 1))
    (hav : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (k + 1)))),
      ac (simplexIncl S (k + 1) τ) = 0)
    (hδ : coboundaryₗ X (k + 1) ac = 0)
    (u : SingularChain X (k + 1)) (wW : SingularChain X (k + 1 + 1))
    (huW : u ∈ subspaceChains W (k + 1)) (hwW : wW ∈ subspaceChains W (k + 1 + 1))
    (hrel : u + chainBoundary X (k + 1) wW ∈ subspaceChains S (k + 1)) :
    (subspaceChainsEquiv W 0).symm ⟨cap (m := 0) ac u, cap_mem_subspaceChains W ac huW⟩
      ∈ boundaries (sub W) 0 := by
  refine subspaceChainsEquiv_symm_mem_boundaries₀ W (cap (m := 0) ac u) _
    (cap (m := 1) ac wW) (cap_mem_subspaceChains W ac hwW) ?_
  rw [cap_cocycle_chainMap (m := 0) ac hδ wW]
  have hz := cap_subspaceChain_eq_zero (m := 0) S ac hav hrel
  rw [map_add] at hz
  rw [← add_right_inj (cap (m := 0) ac u), hz, ZModModule.add_self]

/-- **Bottom cycle-difference compatibility**. -/
theorem relativeDualityK₀_cycle_compat {k : ℕ} {S W : Set ↑X}
    (z z' : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains W (k + 1)) (hz'K : z' ∈ subspaceChains W (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (hz'S : chainBoundary X k z' ∈ subspaceChains S k)
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChain X (k + 1 + 1))
    (hw : (z + z') + chainBoundary X (k + 1) w ∈ subspaceChains S (k + 1))
    (x : RelativeCohomology S (k + 1)) :
    relativeDualityK₀ S W k z hzK hzS x = relativeDualityK₀ S W k z' hz'K hz'S x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hsmall : z + z' ∈ smallChains ({W, S} : Set (Set ↑X)) (k + 1) :=
    subspaceChains_le_smallChains (Set.mem_insert _ _) (k + 1) (Submodule.add_mem _ hzK hz'K)
  have hrcyc : chainBoundary X k (z + z') ∈ subspaceChains S k := by
    rw [map_add]; exact Submodule.add_mem _ hzS hz'S
  obtain ⟨w', hw'small, hw'rel⟩ := relative_small_boundary hcov hsmall hrcyc hw
  obtain ⟨wW, hwW, wS, hwS, hsplit⟩ :=
    Submodule.mem_sup.mp (smallChains_two_le W S (k + 1 + 1) hw'small)
  have hwWrel : (z + z') + chainBoundary X (k + 1) wW ∈ subspaceChains S (k + 1) := by
    have hbdeq : chainBoundary X (k + 1) wW
        = chainBoundary X (k + 1) w' - chainBoundary X (k + 1) wS :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [hbdeq, ← add_sub_assoc]
    exact Submodule.sub_mem _ hw'rel (chainBoundary_mem_subspaceChains S (k + 1) wS hwS)
  have hmem := cap_pullback_mem_boundaries_of_relBoundaryW₀ (S := S) (W := W) a.1.1
    (relCochain_vanish S a.1) (relCocycle_coboundary_zero S a) (z + z') wW
    (Submodule.add_mem _ hzK hz'K) hwW hwWrel
  have hpull : pullbackDualityₗ₀ S W z hzK a - pullbackDualityₗ₀ S W z' hz'K a
      = (subspaceChainsEquiv W 0).symm
          ⟨cap (m := 0) a.1.1 (z + z'),
            cap_mem_subspaceChains W a.1.1 (Submodule.add_mem _ hzK hz'K)⟩ := by
    apply chainIncl_injective W 0
    rw [map_sub, chainIncl_pullbackDualityₗ₀, chainIncl_pullbackDualityₗ₀,
      chainIncl_subspaceChainsEquiv_symm]
    show cap (m := 0) a.1.1 z - cap (m := 0) a.1.1 z' = cap (m := 0) a.1.1 (z + z')
    rw [map_add, sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
  rw [show (Submodule.Quotient.mk a : RelativeCohomology S (k + 1))
      = RelativeCohomology.mk S (k + 1) a from rfl,
    relativeDualityK₀_mk, relativeDualityK₀_mk, Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, map_sub]
  show pullbackDualityₗ₀ S W z hzK a - pullbackDualityₗ₀ S W z' hz'K a
    ∈ boundaries (sub W) 0
  rw [hpull]
  exact hmem

/-- **`relBoundaries`-form of the bottom cycle-difference compatibility**. -/
theorem relativeDualityK₀_cycle_compat_relB {k : ℕ} {S W : Set ↑X}
    (z z' : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains W (k + 1)) (hz'K : z' ∈ subspaceChains W (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (hz'S : chainBoundary X k z' ∈ subspaceChains S k)
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (hrel : RelativeChain.mk S (k + 1) z + RelativeChain.mk S (k + 1) z'
        ∈ relBoundaries S (k + 1))
    (x : RelativeCohomology S (k + 1)) :
    relativeDualityK₀ S W k z hzK hzS x = relativeDualityK₀ S W k z' hz'K hz'S x := by
  obtain ⟨wRel, hwRel⟩ := hrel
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  refine relativeDualityK₀_cycle_compat z z' hzK hz'K hzS hz'S hcov w ?_ x
  have h1 : (Submodule.Quotient.mk (chainBoundary X (k + 1) w) : RelativeChain S (k + 1))
      = Submodule.Quotient.mk z + Submodule.Quotient.mk z' := hwRel
  rw [← RelativeChain.mk_eq_zero_iff]
  show Submodule.Quotient.mk ((z + z') + chainBoundary X (k + 1) w)
    = (0 : RelativeChain S (k + 1))
  rw [Submodule.Quotient.mk_add, h1, Submodule.Quotient.mk_add]
  exact ZModModule.add_self _

/-! ## §4. `legW₀` and its colimit — the bottom duality legs -/

variable [T2Space ↑X]

/-- **The bottom per-compact duality leg** `legW₀ : Hᵏ⁺¹(M|K) → H₀(sub W)`. -/
noncomputable def legW₀ {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    cohomGW W (k + 1) K →ₗ[ZMod 2] Homology (sub W) 0 :=
  relativeDualityK₀ ((↑K.1 : Set ↑X)ᶜ) W k (fundCycleW₀ hW z₀ hz₀ K)
    (fundCycleW₀_mem_W hW z₀ hz₀ K) (fundCycleW₀_boundary hW z₀ hz₀ K)

/-- **The bottom duality-leg colimit compatibility** — mirrors `legW_compat`: the restriction move,
then the `relB` cycle swap, with the rel-homology glue done at the native `(k+0+1)`-spelling and
transported through `castChain` once (`relB_pair_castChain`). -/
theorem legW₀_compat {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K K' : CompactsIn W) (h : K ≤ K') (x : cohomGW W (k + 1) K) :
    legW₀ hW z₀ hz₀ K' (cohomFW W (k + 1) K K' h x) = legW₀ hW z₀ hz₀ K x := by
  have hKK' : (↑K'.1 : Set ↑X)ᶜ ⊆ (↑K.1 : Set ↑X)ᶜ :=
    Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr h)
  have hzK'_S : chainBoundary X k (fundCycleW₀ hW z₀ hz₀ K')
      ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) k :=
    SKEFTHawking.SingularMayerVietoris.subspaceChains_mono hKK' k
      (fundCycleW₀_boundary hW z₀ hz₀ K')
  have step1 : legW₀ hW z₀ hz₀ K' (cohomFW W (k + 1) K K' h x)
      = relativeDualityK₀ ((↑K.1 : Set ↑X)ᶜ) W k (fundCycleW₀ hW z₀ hz₀ K')
          (fundCycleW₀_mem_W hW z₀ hz₀ K') hzK'_S x :=
    relativeDualityK₀_restrict_compat (fundCycleW₀ hW z₀ hz₀ K') hKK'
      (fundCycleW₀_mem_W hW z₀ hz₀ K') (fundCycleW₀_boundary hW z₀ hz₀ K') hzK'_S x
  rw [step1, legW₀]
  refine relativeDualityK₀_cycle_compat_relB (fundCycleW₀ hW z₀ hz₀ K')
    (fundCycleW₀ hW z₀ hz₀ K)
    (fundCycleW₀_mem_W hW z₀ hz₀ K') (fundCycleW₀_mem_W hW z₀ hz₀ K) hzK'_S
    (fundCycleW₀_boundary hW z₀ hz₀ K)
    (interiors_cover_of_compact_subset_open K.1.isCompact' hW K.2) ?_ x
  -- the rel-homology glue, at the native (k+0+1)-spelling, then ONE castChain transport
  have hglue : RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
        (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
      + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1)
        (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
      ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + 0 + 1) := by
    set S : Set ↑X := (↑K.1 : Set ↑X)ᶜ with hS
    have hA := fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
    have hB : RelativeChain.mk S (k + 0 + 1) (z₀ + fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
        ∈ relBoundaries S (k + 0 + 1) := by
      refine relBoundaries_mono hKK' _ ?_
      show Submodule.Quotient.mk (z₀ + fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
        ∈ relBoundaries ((↑K'.1 : Set ↑X)ᶜ) (k + 0 + 1)
      rw [Submodule.Quotient.mk_add]
      exact fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K'
    have heq : RelativeChain.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K')
          + RelativeChain.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K)
        = (RelativeChain.mk S (k + 0 + 1) z₀
            + RelativeChain.mk S (k + 0 + 1) (fundCycleW (k := k) (m := 0) hW z₀ hz₀ K))
          + RelativeChain.mk S (k + 0 + 1)
            (z₀ + fundCycleW (k := k) (m := 0) hW z₀ hz₀ K') := by
      simp only [RelativeChain.mk, Submodule.Quotient.mk_add]
      abel_nf
      simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
    rw [heq]
    exact Submodule.add_mem _ hA hB
  exact relB_pair_castChain (a := k + 0 + 1) (b := k + 1) rfl _ _ hglue

/-- **The bottom open Poincaré-duality map** `D_W⁰ : Hᵏ⁺¹_c(W) → H₀(sub W)`. -/
noncomputable def openDuality₀ {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) :
    CompactlySupportedCohomologyOpen W (k + 1) →ₗ[ZMod 2] Homology (sub W) 0 :=
  Module.DirectLimit.lift (ZMod 2) (CompactsIn W) (cohomGW W (k + 1)) (cohomFW W (k + 1))
    (legW₀ hW z₀ hz₀) (fun K K' h x => legW₀_compat hW z₀ hz₀ K K' h x)

/-- **Computation rule for `D_W⁰`** on a `K`-stage class. -/
@[simp] theorem openDuality₀_of {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) (a : cohomGW W (k + 1) K) :
    openDuality₀ hW z₀ hz₀
        (Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W (k + 1)) (cohomFW W (k + 1)) K a)
      = legW₀ hW z₀ hz₀ K a :=
  Module.DirectLimit.lift_of _ _ a

end SKEFTHawking.SingularOpenDualityBot
