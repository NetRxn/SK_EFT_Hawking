/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, the fact-(i) ambient core (integral)

* `capInt_coboundary_cochainSplit_eq_explicitInt` — the `∃`-free ("explicit-witness") variant of the
  committed χ-engine `SingularCochainSplitInt.capInt_coboundary_cochainSplit_eqInt`, exposing the
  bounding chain `e = (-1)^N • (cochainSplit U ω ⌢ c)` (the committed lemma hides it under `∃ e`, which
  blocks the `C(U∩V)`-support proof Brick M needs).
* `fact_i_ambient_coreInt` (Brick M) — the fact-(i) seam-ambient core, on Brick L + the explicit χ-engine.

Sign: over ℤ the cocycle cap-map carries `(-1)^{N+1}` (`capInt_cocycle_chainMap`), so the `bF`-cap term
acquires an honest `(-1)^N` factor (char-2 hid it). This propagates to `fact_i_discharge`'s β-kill and is
pinned globally at `subHomConnecting_openDualityInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareFactIInt
import SKEFTHawking.SingularChainCastHelpersInt
import SKEFTHawking.SingularCochainSplitInt
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularCapSupportInt

open scoped Classical
open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_boundary)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt singularSdInt_iterate_chainBoundary)
open SKEFTHawking.SingularCochainSplitInt (cochainSplitInt cochainSplitInt_compl_mem_relCochainsInt)
open SKEFTHawking.SingularEuclideanCapIsoInt (relCoboundaryIntₗ relCoboundaryIntₗ_coe relCochainInt_vanish
  capInt_subspaceChainInt_eq_zero)
open SKEFTHawking.SingularExcisionIsoInt (singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularCapSupportInt (capInt_mem_subspaceChainsInt)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **Explicit-witness χ-engine** (integral). Same as the committed
`SingularCochainSplitInt.capInt_coboundary_cochainSplit_eqInt` but EXPOSES the bounding chain
`e = (-1)^N • (cochainSplit U ω ⌢ c)` (the committed lemma hides it under `∃ e`, which blocks the
`C(U∩V)`-support proof Brick M needs). Verbatim replica of the committed proof, `∃`-free. -/
theorem capInt_coboundary_cochainSplit_eq_explicitInt (U V : Set ↑X) {N m : ℕ}
    (ω : LinearMap.ker (relCoboundaryIntₗ (U ∩ V) (N + 1)))
    (c : SingularChainInt X (N + 1 + m + 1)) (u w : SingularChainInt X (N + 1 + m))
    (hu : u ∈ subspaceChainsInt U (N + 1 + m)) (hw : w ∈ subspaceChainsInt V (N + 1 + m))
    (hbd : chainBoundary X (N + 1 + m) c = u + w) (h : N + 1 + m + 1 = N + 1 + 1 + m) :
    capInt (m := m) (coboundary X (N + 1) (cochainSplitInt U (N + 1) ω.1.1)) (h ▸ c)
      = capInt (m := m) ω.1.1 w
        + chainBoundary X m ((-1 : ℤ) ^ N • capInt (m := m + 1) (cochainSplitInt U (N + 1) ω.1.1) c) := by
  have hu0 : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) u = 0 :=
    capInt_subspaceChainInt_eq_zero U _ (fun τ => if_pos ⟨τ, rfl⟩) hu
  have hωw : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) w = capInt (m := m) ω.1.1 w := by
    have hψw : capInt (m := m) (ω.1.1 - cochainSplitInt U (N + 1) ω.1.1) w = 0 :=
      capInt_subspaceChainInt_eq_zero V _
        (fun τ => relCochainInt_vanish V
          ⟨_, cochainSplitInt_compl_mem_relCochainsInt U V (N + 1) ω.1.1 ω.1.2⟩ τ) hw
    have hsplit : capInt (m := m) (ω.1.1 - cochainSplitInt U (N + 1) ω.1.1) w
        = capInt (m := m) ω.1.1 w - capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) w := by
      rw [← capIntₗ_apply, ← capIntₗ_apply, ← capIntₗ_apply, map_sub, LinearMap.sub_apply]
    rw [hsplit, sub_eq_zero] at hψw
    exact hψw.symm
  have hφbd : capInt (m := m) (cochainSplitInt U (N + 1) ω.1.1) (chainBoundary X (N + 1 + m) c)
      = capInt (m := m) ω.1.1 w := by
    rw [hbd, ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply, hu0, zero_add, hωw]
  have hleib := capInt_leibniz (cochainSplitInt U (N + 1) ω.1.1) c h
  rw [hφbd] at hleib
  have h1 : ((-1 : ℤ) ^ N) * ((-1) ^ (N + 1 + 1)) = 1 := by
    rw [← pow_add, show N + (N + 1 + 1) = 2 * (N + 1) by ring, pow_mul]; norm_num
  have h2 : ((-1 : ℤ) ^ N) * ((-1) ^ (N + 1)) = -1 := by
    rw [← pow_add, show N + (N + 1) = 2 * N + 1 by ring, pow_add, pow_mul]; norm_num
  rw [map_smul, hleib, smul_add, smul_smul, smul_smul, h1, h2, one_smul, neg_one_smul]
  abel

/-- **The fact-(i) ambient core** (Brick M, integral). ℤ port of
`SingularConnSquareCloseNC.fact_i_ambient_core`. **Sign:** over ℤ the cocycle cap-map carries
`(-1)^{N+1}` (`capInt_cocycle_chainMap`), so the `bF`-cap term acquires a `(-1)^N` factor
(honest ℤ; char-2 hid it). The bounding chain is `E := (-1)^{N+1}•E₂ + (cochainSplit LUᶜ g) ⌢ (f₃ − Sd^jF F₂)`,
both summands `C(U∩V)`-supported. -/
theorem fact_i_ambient_coreInt {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N p : ℕ}
    (g : LinearMap.ker (relCoboundaryIntₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChainInt X (N + 1 + (p + 1) + 1))
    (hz₀ : chainBoundary X (N + 1 + (p + 1)) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChainInt X (N + 1 + (p + 1) + 1))
    (hf₁ : f₁ ∈ subspaceChainsInt (U ∩ LVᶜ) (N + 1 + (p + 1) + 1))
    (hf₂ : f₂ ∈ subspaceChainsInt (V ∩ LUᶜ) (N + 1 + (p + 1) + 1))
    (hf₃ : f₃ ∈ subspaceChainsInt (U ∩ V) (N + 1 + (p + 1) + 1))
    (hIsplit : (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[μ]
        (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChainInt X (N + 1 + (p + 1) + 1))
    (hF₂mem : F₂ ∈ subspaceChainsInt (U ∩ V) (N + 1 + (p + 1) + 1))
    (η₂ : SingularChainInt X (N + 1 + (p + 1) + 1 + 1)) (a₂ : SingularChainInt X (N + 1 + (p + 1) + 1))
    (heq₂ : F₂ - z₀ = chainBoundary X (N + 1 + (p + 1) + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1) + 1))
    (hF₂bd : chainBoundary X (N + 1 + (p + 1)) F₂
      ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (N + 1 + (p + 1)))
    (aF : SingularChainInt (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (bF : SingularChainInt (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + (p + 1)))
    (hFsplit : chainBoundary X (N + 1 + (p + 1))
        ((⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂)
      = chainIncl _ (N + 1 + (p + 1)) aF + chainIncl _ (N + 1 + (p + 1)) bF) :
    ∃ E : SingularChainInt X (p + 1 + 1), E ∈ subspaceChainsInt (U ∩ V) (p + 1 + 1)
      ∧ chainBoundary X (p + 1) (capInt (m := p + 1 + 1) g.1.1 (f₂ + f₃))
          + (-1 : ℤ) ^ N • capInt (m := p + 1) g.1.1
              (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF)
        = chainBoundary X (p + 1) E := by
  have hgvan : ∀ τ, g.1.1 (simplexIncl (LUᶜ ∩ LVᶜ) (N + 1) τ) = 0 :=
    fun τ => relCochainInt_vanish (LUᶜ ∩ LVᶜ) g.1 τ
  have hgc : coboundary X (N + 1) g.1.1 = 0 := by
    have hh := congrArg Subtype.val g.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + (p + 1))) hIsplit
  rw [singularSdInt_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + (p + 1)) f₃
      = (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
          (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        - chainBoundary X (N + 1 + (p + 1)) f₁ - chainBoundary X (N + 1 + (p + 1)) f₂ := by
    rw [hbdIsplit]; abel
  have hSdKmem : (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChainsInt (LUᶜ ∩ LVᶜ) (N + 1 + (p + 1)) :=
    singularSdInt_iterate_mem_subspaceChainsInt
      (hK₁ ▸ fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ
  set u : SingularChainInt X (N + 1 + (p + 1)) :=
    (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
    - chainBoundary X (N + 1 + (p + 1)) f₂
    - chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF with hudef
  set w : SingularChainInt X (N + 1 + (p + 1)) :=
    -chainBoundary X (N + 1 + (p + 1)) f₁
    - chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF with hwdef
  have humem : u ∈ subspaceChainsInt LUᶜ (N + 1 + (p + 1)) :=
    Submodule.sub_mem _ (Submodule.sub_mem _
      (subspaceChainsInt_mono Set.inter_subset_left _ hSdKmem)
      (subspaceChainsInt_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChainsInt (V ∩ LUᶜ) (N + 1 + (p + 1)) f₂ hf₂)))
      (subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self (chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1))) aF))
  have hwmem : w ∈ subspaceChainsInt LVᶜ (N + 1 + (p + 1)) :=
    Submodule.sub_mem _ (Submodule.neg_mem _
      (subspaceChainsInt_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChainsInt (U ∩ LVᶜ) (N + 1 + (p + 1)) f₁ hf₁)))
      (subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1))) bF))
  have hbd_uncast : chainBoundary X (N + 1 + (p + 1))
      (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂) = u + w := by
    rw [map_sub, hFsplit, hf₃bd, hudef, hwdef]; abel
  have h : N + 1 + (p + 1) + 1 = N + 1 + 1 + (p + 1) := by omega
  set capφc : SingularChainInt X (p + 1 + 1) :=
    capInt (m := p + 1 + 1) (cochainSplitInt LUᶜ (N + 1) g.1.1)
      (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂) with hcapφc
  have hexplicit := capInt_coboundary_cochainSplit_eq_explicitInt LUᶜ LVᶜ g
    (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂) u w humem hwmem hbd_uncast h
  obtain ⟨E₂, hE₂mem, hE₂⟩ := fact_i_n2_killInt hU hV hLUc hLVc hLUU hLVV g z₀ hz₀ K₁ K₂ hK₁ hK₂
    μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit h
  -- ∂E₂ = capg w + (-1)^N • ∂capφc
  have hED : chainBoundary X (p + 1) E₂
      = capInt (m := p + 1) g.1.1 w + (-1 : ℤ) ^ N • chainBoundary X (p + 1) capφc := by
    have hcomb := hE₂.symm.trans hexplicit
    rwa [map_smul] at hcomb
  -- cycle-flip pieces (signed)
  have hcapf1 : chainBoundary X (p + 1) (capInt (m := p + 1 + 1) g.1.1 f₁)
      = (-1 : ℤ) ^ (N + 1) • capInt (m := p + 1) g.1.1 (chainBoundary X (N + 1 + (p + 1)) f₁) :=
    capInt_cocycle_chainMap (m := p + 1) g.1.1 hgc f₁
  have hsplit' : (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[μ]
      (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + (f₂ + f₃) :=
    hIsplit.trans (add_assoc f₁ f₂ f₃)
  have hcyc0 : chainBoundary X (p + 1) (capInt (m := p + 1 + 1) g.1.1
      ((⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[μ] (fundCycleW (hU.union hV) z₀ hz₀ K₁))) = 0 := by
    rw [capInt_cocycle_chainMap (m := p + 1) g.1.1 hgc _, singularSdInt_iterate_chainBoundary,
      capInt_subspaceChainInt_eq_zero (m := p + 1) (LUᶜ ∩ LVᶜ) g.1.1 hgvan hSdKmem, smul_zero]
  have hflip : chainBoundary X (p + 1) (capInt (m := p + 1 + 1) g.1.1 (f₂ + f₃))
      = -chainBoundary X (p + 1) (capInt (m := p + 1 + 1) g.1.1 f₁) := by
    have h1 : capInt (m := p + 1 + 1) g.1.1
        ((⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[μ] (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        = capInt (m := p + 1 + 1) g.1.1 f₁ + capInt (m := p + 1 + 1) g.1.1 (f₂ + f₃) := by
      rw [hsplit', ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply]
    have h2 := congrArg (chainBoundary X (p + 1)) h1
    rw [hcyc0, map_add] at h2
    exact eq_neg_of_add_eq_zero_right h2.symm
  have hwcap : capInt (m := p + 1) g.1.1 w
      = -capInt (m := p + 1) g.1.1 (chainBoundary X (N + 1 + (p + 1)) f₁)
        - capInt (m := p + 1) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF) := by
    rw [hwdef, ← capIntₗ_apply, map_sub, map_neg, capIntₗ_apply, capIntₗ_apply]
  have hsgn2 : (-1 : ℤ) ^ (N + 1) = -(-1) ^ N := by rw [pow_succ]; ring
  have hsq : ((-1 : ℤ) ^ N) * ((-1) ^ N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  refine ⟨(-1 : ℤ) ^ (N + 1) • E₂ + capφc,
    Submodule.add_mem _ (Submodule.smul_mem _ _ hE₂mem)
      (hcapφc ▸ capInt_mem_subspaceChainsInt (m := p + 1 + 1) (U ∩ V) _
        (Submodule.sub_mem _ hf₃ (singularSdInt_iterate_mem_subspaceChainsInt hF₂mem jF))), ?_⟩
  rw [hflip, hcapf1, map_add, map_smul, hED, hwcap, hsgn2]
  simp only [smul_add, smul_sub, smul_neg, smul_smul, neg_smul, neg_neg, neg_mul, hsq, one_smul]
  abel

end SKEFTHawking.SingularConnSquareCloseNCInt
