/-
# Phase 5q.H (E1 CSC-PD tower) — the fact-(i) chain at the BOTTOM window (degree-0 caps, integral)

The `m = 0` mirrors of the (N,p)-shaped Route-B bricks, for the BOT conjunct of `HcoreG`
(`k = 2+1, m = 0`; the upper closed 2026-07-12 via the shared F₂-split). The successor shapes
`capInt (m := n+1)` / `E : Chain (p+1+1)` of Brick J / L / M cannot reach the bot's degree-0 caps,
so each gets a ₀-variant (the `brick 4-bot mirrors brick 4` pattern); all their INGREDIENTS
(χ-engine, K′, cocycle-chainmap, Leibniz, kills, cap-support) are already `{m}`-generic and are
consumed at `m := 0` directly. Bonus simplification: at the bot frame `N+1+0+1 ≡ N+1+1` is
DEFINITIONAL (`Nat.add_zero`), so Brick L's entire cast-frame section vanishes.

* `cap_relCochains_pair_double_support_eq_boundary₀Int` — Brick J₀
* `fact_i_n2_kill₀Int` — Brick L₀ (K′ at `(k := N+1, m := 0)` + J₀; NO casts)
* `fact_i_ambient_core₀Int` — Brick M₀ (χ-explicit at `m := 0` + L₀)
* `homology_eq_of_ambient_boundary₀Int` — the H₀ descent bridge
* `legW₀Int_mk` — the bottom duality-leg `mk`-rule (rfl, via `relativeDualityK₀Int_mk`)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareCloseNCInt
import SKEFTHawking.SingularConnSquareFactIInt
import SKEFTHawking.SingularConnSquareFactICoreInt
import SKEFTHawking.SingularLocalDualityKBotInt
import SKEFTHawking.SingularOpenDualityBotInt
import SKEFTHawking.SingularHomologyDescentBridgeInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt iterHomotopyInt_chainHomotopy
  singularSdInt_iterate_chainBoundary)
open SKEFTHawking.SingularDualCochainInt (iterHomotopyIntₗ iterHomotopyIntₗ_apply)
open SKEFTHawking.SingularEuclideanCapIsoInt (relCoboundaryIntₗ relCoboundaryIntₗ_coe
  relCochainInt_vanish capInt_subspaceChainInt_eq_zero RelativeCohomologyInt)
open SKEFTHawking.SingularCapSupportInt (capInt_mem_subspaceChainsInt)
open SKEFTHawking.SingularExcisionIsoInt (iterHomotopyInt_mem_subspaceChainsInt
  mem_subspaceChainsInt_of_support subspaceChainsInt_inf singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularCoverFineSplitInt (exists_cover_fine_split_of_boundaryInt)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_boundary)
open SKEFTHawking.SingularCochainSplitInt (cochainSplitInt cochainSplitInt_coboundary_mem_UInt
  cochainSplitInt_coboundary_mem_VInt cochainSplitInt_compl_mem_relCochainsInt)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

omit [T2Space ↑X] in
/-- **The double-support δφ-kill at the bottom** (Brick J₀). `m = 0` mirror of
`cap_relCochains_pair_double_support_eq_boundaryInt`: the cochain sits at `k+1` (so the cap lands
in degree 0), the chain at `k+1`, and the bounding witness `E` at `0+1`; the cocycle-flip sign is
`(-1)^(k+1)`. Proof is the 1:1 mirror (D-cover-split telescope → b → double kills → cocycle flip). -/
theorem cap_relCochains_pair_double_support_eq_boundary₀Int {A B P : Set ↑X}
    (hA : IsOpen A) (hB : IsOpen B) (hP : IsOpen P)
    (hcover : P ∪ (A ∪ B) = Set.univ) {k : ℕ}
    (a : SingularCochainInt X (k + 1)) (hac : coboundary X (k + 1) a = 0)
    (haA : ∀ τ, a (simplexIncl A (k + 1) τ) = 0)
    (haB : ∀ τ, a (simplexIncl B (k + 1) τ) = 0)
    (c : SingularChainInt X (k + 1)) (hcP : c ∈ subspaceChainsInt P (k + 1))
    (D : SingularChainInt X (k + 1 + 1)) (ρ : SingularChainInt X (k + 1))
    (hρ : ρ ∈ subspaceChainsInt (A ∪ B) (k + 1))
    (heq : c = chainBoundary X (k + 1) D + ρ)
    (u' : SingularChainInt (sub A) k) (w' : SingularChainInt (sub B) k)
    (hbd : chainBoundary X k c = chainIncl A k u' + chainIncl B k w') :
    ∃ E : SingularChainInt X (0 + 1), E ∈ subspaceChainsInt P (0 + 1)
      ∧ capInt (m := 0) a c = chainBoundary X 0 E := by
  -- small D over the total cover (P, A∪B)
  have hDmem : D ∈ subspaceChainsInt (P ∪ (A ∪ B)) (k + 1 + 1) :=
    mem_subspaceChainsInt_of_support (fun τ _ => by rw [hcover]; exact Set.subset_univ _)
  obtain ⟨ν, D₁, D₂, hD₁, hD₂, hDsplit⟩ :=
    exists_iterate_cover_split_ambInt hP (hA.union hB) D hDmem
  have hhD := iterHomotopyInt_chainHomotopy X ν (k + 1) D
  have hDbnd : chainBoundary X (k + 1) D
      = chainBoundary X (k + 1) D₁ + chainBoundary X (k + 1) D₂
        + chainBoundary X (k + 1)
            (iterHomotopyInt X (k + 1) ν (chainBoundary X (k + 1) D)) := by
    have h1 := congrArg (chainBoundary X (k + 1)) hhD
    rw [map_add, boundary_comp_boundary, zero_add, map_sub, hDsplit, map_add] at h1
    rw [h1]; abel
  have hTsplitInt : iterHomotopyInt X (k + 1) ν (chainBoundary X (k + 1) D)
      = iterHomotopyInt X (k + 1) ν c - iterHomotopyInt X (k + 1) ν ρ := by
    have hdD : chainBoundary X (k + 1) D = c - ρ := by rw [heq]; abel
    rw [hdD, ← iterHomotopyIntₗ_apply, map_sub, iterHomotopyIntₗ_apply, iterHomotopyIntₗ_apply]
  set b : SingularChainInt X (k + 1) := ρ + chainBoundary X (k + 1) D₂
    - chainBoundary X (k + 1) (iterHomotopyInt X (k + 1) ν ρ) with hbdef
  have hbeqInt : c = chainBoundary X (k + 1)
      (D₁ + iterHomotopyInt X (k + 1) ν c) + b := by
    conv_lhs => rw [heq]
    rw [hDbnd, hTsplitInt, hbdef]
    simp only [map_add, map_sub]
    abel
  have hb2Int : b = c - chainBoundary X (k + 1)
      (D₁ + iterHomotopyInt X (k + 1) ν c) := by
    rw [eq_sub_iff_add_eq, add_comm b]; exact hbeqInt.symm
  have hbPInt : b ∈ subspaceChainsInt P (k + 1) := by
    rw [hb2Int]
    exact Submodule.sub_mem _ hcP (chainBoundary_mem_subspaceChainsInt P (k + 1) _
      (Submodule.add_mem _ hD₁ (iterHomotopyInt_mem_subspaceChainsInt hcP ν)))
  have hbABInt : b ∈ subspaceChainsInt (A ∪ B) (k + 1) := by
    rw [hbdef]
    exact Submodule.sub_mem _ (Submodule.add_mem _ hρ
      (chainBoundary_mem_subspaceChainsInt (A ∪ B) (k + 1) _ hD₂))
      (chainBoundary_mem_subspaceChainsInt (A ∪ B) (k + 1) _
        (iterHomotopyInt_mem_subspaceChainsInt hρ ν))
  have hbInterInt : b ∈ subspaceChainsInt ((P ∩ A) ∪ (P ∩ B)) (k + 1) := by
    have h := Submodule.mem_inf.mpr ⟨hbPInt, hbABInt⟩
    rw [subspaceChainsInt_inf, Set.inter_union_distrib_left] at h
    exact h
  obtain ⟨κ, bA, bB, hbA, hbB, hbSplit⟩ :=
    exists_iterate_cover_split_ambInt (hP.inter hA) (hP.inter hB) b hbInterInt
  have hhbInt := iterHomotopyInt_chainHomotopy X κ k b
  have hkill1Int : capInt (m := 0) a ((⇑(singularSdInt X (k + 1)))^[κ] b) = 0 := by
    have hbAA : bA ∈ subspaceChainsInt A (k + 1) :=
      subspaceChainsInt_mono Set.inter_subset_right (k + 1) hbA
    have hbBB : bB ∈ subspaceChainsInt B (k + 1) :=
      subspaceChainsInt_mono Set.inter_subset_right (k + 1) hbB
    rw [hbSplit, ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply,
      capInt_subspaceChainInt_eq_zero (m := 0) A a haA hbAA,
      capInt_subspaceChainInt_eq_zero (m := 0) B a haB hbBB, add_zero]
  have hkill2Int : capInt (m := 0) a
      (iterHomotopyInt X k κ (chainBoundary X k b)) = 0 := by
    have hcbdInt : chainBoundary X k b = chainBoundary X k c := by
      rw [hb2Int, map_sub, boundary_comp_boundary, sub_zero]
    rw [hcbdInt, hbd,
      show iterHomotopyInt X k κ (chainIncl A k u' + chainIncl B k w')
          = iterHomotopyInt X k κ (chainIncl A k u')
            + iterHomotopyInt X k κ (chainIncl B k w')
        from by rw [← iterHomotopyIntₗ_apply, map_add, iterHomotopyIntₗ_apply,
          iterHomotopyIntₗ_apply],
      ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply,
      capInt_subspaceChainInt_eq_zero (m := 0) A a haA
        (iterHomotopyInt_mem_subspaceChainsInt (LinearMap.mem_range_self (chainIncl A k) u') κ),
      capInt_subspaceChainInt_eq_zero (m := 0) B a haB
        (iterHomotopyInt_mem_subspaceChainsInt (LinearMap.mem_range_self (chainIncl B k) w') κ),
      add_zero]
  have hcbInt : capInt (m := 0) a c
      = capInt (m := 0) a (chainBoundary X (k + 1)
          (D₁ + iterHomotopyInt X (k + 1) ν c))
        + capInt (m := 0) a b := by
    conv_lhs => rw [hbeqInt]
    rw [← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply]
  have hb3'Int : (chainBoundary X (k + 1) (iterHomotopyInt X (k + 1) κ b)
      + iterHomotopyInt X k κ (chainBoundary X k b))
      + (⇑(singularSdInt X (k + 1)))^[κ] b = b := by
    rw [hhbInt]; abel
  have hbcap : capInt (m := 0) a b
      = capInt (m := 0) a (chainBoundary X (k + 1)
          (iterHomotopyInt X (k + 1) κ b)) := by
    conv_lhs => rw [← hb3'Int]
    rw [← capIntₗ_apply, map_add, map_add, capIntₗ_apply, capIntₗ_apply, capIntₗ_apply,
      hkill2Int, hkill1Int, add_zero, add_zero]
  -- cocycle cap-map: `a ⌢ ∂Y = (-1)^(k+1) · ∂(a ⌢ Y)` for the degree-(k+1) cocycle `a`
  have hcocyc : ∀ (Y : SingularChainInt X (k + 1 + 1)),
      capInt (m := 0) a (chainBoundary X (k + 1) Y)
        = (-1 : ℤ) ^ (k + 1) • chainBoundary X 0 (capInt (m := 0 + 1) a Y) := by
    intro Y
    have hcm : chainBoundary X 0 (capInt (m := 0 + 1) a Y)
        = (-1 : ℤ) ^ (k + 1) • capInt (m := 0) a (chainBoundary X (k + 1) Y) :=
      capInt_cocycle_chainMap (m := 0) a hac Y
    rw [hcm, smul_smul, ← pow_add, show k + 1 + (k + 1) = 2 * (k + 1) from by ring, pow_mul,
      neg_one_sq, one_pow, one_smul]
  have hY₁P : (D₁ + iterHomotopyInt X (k + 1) ν c) ∈ subspaceChainsInt P (k + 1 + 1) :=
    Submodule.add_mem _ hD₁ (iterHomotopyInt_mem_subspaceChainsInt hcP ν)
  have hY₂P : iterHomotopyInt X (k + 1) κ b ∈ subspaceChainsInt P (k + 1 + 1) :=
    iterHomotopyInt_mem_subspaceChainsInt hbPInt κ
  have hEbd : chainBoundary X 0
        ((-1 : ℤ) ^ (k + 1) • (capInt (m := 0 + 1) a (D₁ + iterHomotopyInt X (k + 1) ν c)
          + capInt (m := 0 + 1) a (iterHomotopyInt X (k + 1) κ b)))
      = (-1 : ℤ) ^ (k + 1) • chainBoundary X 0
            (capInt (m := 0 + 1) a (D₁ + iterHomotopyInt X (k + 1) ν c))
        + (-1 : ℤ) ^ (k + 1) • chainBoundary X 0
            (capInt (m := 0 + 1) a (iterHomotopyInt X (k + 1) κ b)) := by
    rw [map_smul, map_add, smul_add]
  refine ⟨(-1 : ℤ) ^ (k + 1) • (capInt (m := 0 + 1) a (D₁ + iterHomotopyInt X (k + 1) ν c)
      + capInt (m := 0 + 1) a (iterHomotopyInt X (k + 1) κ b)),
    Submodule.smul_mem _ _ (Submodule.add_mem _
      (capInt_mem_subspaceChainsInt (m := 0 + 1) P a hY₁P)
      (capInt_mem_subspaceChainsInt (m := 0 + 1) P a hY₂P)), ?_⟩
  rw [hcbInt, hbcap, hcocyc (D₁ + iterHomotopyInt X (k + 1) ν c),
    hcocyc (iterHomotopyInt X (k + 1) κ b), hEbd]

/-- **The N2 δφ-kill at the bottom** (Brick L₀). `m = 0` mirror of `fact_i_n2_killInt` —
simpler than the parent: at the bot frame `N+1+0+1 ≡ N+1+1` is definitional, so the entire
cast-frame section (h/h'/hD, `subspaceChains_cast_memInt`) vanishes. K′ at `(k := N+1, m := 0)`
supplies `(D, ρ)`; the ∂c-legs come from the `hIsplit`-∂ rearrangement + `hFsplit`; Brick J₀ with
`(A, B, P) := (LUᶜ, LVᶜ, U∩V)` closes. -/
theorem fact_i_n2_kill₀Int {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N : ℕ}
    (g : LinearMap.ker (relCoboundaryIntₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChainInt X (N + 1 + 0 + 1))
    (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChainInt X (N + 1 + 0 + 1))
    (hf₁ : f₁ ∈ subspaceChainsInt (U ∩ LVᶜ) (N + 1 + 0 + 1))
    (hf₂ : f₂ ∈ subspaceChainsInt (V ∩ LUᶜ) (N + 1 + 0 + 1))
    (hf₃ : f₃ ∈ subspaceChainsInt (U ∩ V) (N + 1 + 0 + 1))
    (hIsplit : (⇑(singularSdInt X (N + 1 + 0 + 1)))^[μ]
        (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChainInt X (N + 1 + 0 + 1))
    (hF₂mem : F₂ ∈ subspaceChainsInt (U ∩ V) (N + 1 + 0 + 1))
    (η₂ : SingularChainInt X (N + 1 + 0 + 1 + 1)) (a₂ : SingularChainInt X (N + 1 + 0 + 1))
    (heq₂ : F₂ - z₀ = chainBoundary X (N + 1 + 0 + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (N + 1 + 0 + 1))
    (hF₂bd : chainBoundary X (N + 1 + 0) F₂
      ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (N + 1 + 0))
    (aF : SingularChainInt (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (bF : SingularChainInt (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (hFsplit : chainBoundary X (N + 1 + 0)
        ((⇑(singularSdInt X (N + 1 + 0 + 1)))^[jF] F₂)
      = chainIncl _ (N + 1 + 0) aF + chainIncl _ (N + 1 + 0) bF) :
    ∃ E : SingularChainInt X (0 + 1), E ∈ subspaceChainsInt (U ∩ V) (0 + 1)
      ∧ capInt (m := 0) (coboundary X (N + 1) (cochainSplitInt LUᶜ (N + 1) g.1.1))
          (f₃ - (⇑(singularSdInt X (N + 1 + 0 + 1)))^[jF] F₂)
        = chainBoundary X 0 E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 := by
    have hh := congrArg Subtype.val g.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  have hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ LUᶜ ∪ LVᶜ := by
    rw [hK₁]; exact fun x hx => Or.inl hx.1
  -- Brick K′ (− orientation, at m := 0): `f₃ − Sd^jF F₂ = ∂D + ρ`, `ρ ∈ C(LUᶜ ∪ LVᶜ)`
  obtain ⟨D, ρ, hρ, heq⟩ :=
    fund_pair_three_set_rel_comparison_freeInt (S := LUᶜ ∪ LVᶜ) (k := N + 1) (m := 0)
      (hU.union hV) z₀ hz₀ K₁ hK₁S μ jF f₁ f₂ f₃
      (subspaceChainsInt_mono (fun _ hx => Or.inr hx.2) _ hf₁)
      (subspaceChainsInt_mono (fun _ hx => Or.inl hx.2) _ hf₂)
      hIsplit F₂ η₂ a₂ heq₂ ha₂ hF₂bd
  -- ∂c-legs (− orientation): Sd^μ(∂fund₁) = ∂f₁ + ∂f₂ + ∂f₃
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + 0)) hIsplit
  rw [singularSdInt_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + 0) f₃
      = (⇑(singularSdInt X (N + 1 + 0)))^[μ]
          (chainBoundary X (N + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        - chainBoundary X (N + 1 + 0) f₁ - chainBoundary X (N + 1 + 0) f₂ := by
    -- re-ascribe hbdIsplit at the fresh spelling (binder-vs-fresh hidden-instance mismatch)
    rw [show (⇑(singularSdInt X (N + 1 + 0)))^[μ]
          (chainBoundary X (N + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        = chainBoundary X (N + 1 + 0) f₁ + chainBoundary X (N + 1 + 0) f₂
          + chainBoundary X (N + 1 + 0) f₃ from hbdIsplit]
    abel
  have hSdmem : (⇑(singularSdInt X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChainsInt LUᶜ (N + 1 + 0) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (singularSdInt_iterate_mem_subspaceChainsInt
        (hK₁ ▸ fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ)
  have hf2bdmem : chainBoundary X (N + 1 + 0) f₂ ∈ subspaceChainsInt LUᶜ (N + 1 + 0) :=
    subspaceChainsInt_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChainsInt (V ∩ LUᶜ) (N + 1 + 0) f₂ hf₂)
  have haFmem : chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0) aF
      ∈ subspaceChainsInt LUᶜ (N + 1 + 0) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (LinearMap.mem_range_self (chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0)) aF)
  have hf1bdmem : chainBoundary X (N + 1 + 0) f₁ ∈ subspaceChainsInt LVᶜ (N + 1 + 0) :=
    subspaceChainsInt_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChainsInt (U ∩ LVᶜ) (N + 1 + 0) f₁ hf₁)
  have hbFmem' : chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF
      ∈ subspaceChainsInt LVᶜ (N + 1 + 0) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (LinearMap.mem_range_self (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0)) bF)
  set u : SingularChainInt X (N + 1 + 0) :=
    (⇑(singularSdInt X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
    - chainBoundary X (N + 1 + 0) f₂
    - chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0) aF with hudef
  set w : SingularChainInt X (N + 1 + 0) :=
    -chainBoundary X (N + 1 + 0) f₁
    - chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF with hwdef
  have humem : u ∈ subspaceChainsInt LUᶜ (N + 1 + 0) :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hSdmem hf2bdmem) haFmem
  have hwmem : w ∈ subspaceChainsInt LVᶜ (N + 1 + 0) :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hf1bdmem) hbFmem'
  have hbd_uncast : chainBoundary X (N + 1 + 0)
      (f₃ - (⇑(singularSdInt X (N + 1 + 0 + 1)))^[jF] F₂) = u + w := by
    rw [map_sub, hFsplit, hf₃bd, hudef, hwdef]; abel
  rw [subspaceChainsInt, LinearMap.mem_range] at humem hwmem
  obtain ⟨uS, huS⟩ := humem
  obtain ⟨wS, hwS⟩ := hwmem
  have hcover : (U ∩ V) ∪ (LUᶜ ∪ LVᶜ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hxU : x ∈ LU
    · by_cases hxV : x ∈ LV
      · exact Or.inl ⟨hLUU hxU, hLVV hxV⟩
      · exact Or.inr (Or.inr hxV)
    · exact Or.inr (Or.inl hxU)
  -- Brick J₀ (no cast frame needed — the bot degrees are definitional)
  obtain ⟨E, hE, hcap⟩ :=
    cap_relCochains_pair_double_support_eq_boundary₀Int hLUc hLVc (hU.inter hV) hcover
      (k := N + 1)
      (coboundary X (N + 1) (cochainSplitInt LUᶜ (N + 1) g.1.1))
      (coboundary_comp_coboundary X (N + 1) _)
      (fun τ => relCochainInt_vanish LUᶜ
        ⟨_, cochainSplitInt_coboundary_mem_UInt LUᶜ (N + 1) g.1.1⟩ τ)
      (fun τ => relCochainInt_vanish LVᶜ
        ⟨_, cochainSplitInt_coboundary_mem_VInt LUᶜ LVᶜ (N + 1) g.1.1 g.1.2 hgc⟩ τ)
      (f₃ - (⇑(singularSdInt X (N + 1 + 0 + 1)))^[jF] F₂)
      (Submodule.sub_mem _ hf₃ (singularSdInt_iterate_mem_subspaceChainsInt hF₂mem jF))
      D ρ hρ heq uS wS (by rw [hbd_uncast, ← huS, ← hwS])
  exact ⟨E, hE, hcap⟩


/-- **The fact-(i) ambient core at the bottom** (Brick M₀, at the CONCRETE bot frame `N := 2`).
`∂(capInt g (f₂+f₃)) + capInt g bFamb = ∂E` with `E ∈ C(U∩V) (0+1)` (the `(-1)^N` of the generic
form is `+1` at `N = 2`) — the χ-explicit engine at `m := 0` + Brick L₀. CONCRETE degrees on purpose:
at `m := 0` with a VARIABLE `N`, `N+1+0`-terms are whnf-unstable (`Nat.add_zero` keeps firing) and
the unifier thrashes past the heartbeat budget; the bot consumer only ever needs `N = 2`
(`g` at degree `2+1`), where every frame is a stuck literal. -/
theorem fact_i_ambient_core₀Int {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    (g : LinearMap.ker (relCoboundaryIntₗ (LUᶜ ∩ LVᶜ) (2 + 1)))
    (z₀ : SingularChainInt X (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary X (2 + 1 + 0) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V)) (K₂ : CompactsIn (U ∩ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hK₂ : ((↑K₂.1 : Set ↑X))ᶜ = LUᶜ ∪ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChainInt X (2 + 1 + 0 + 1))
    (hf₁ : f₁ ∈ subspaceChainsInt (U ∩ LVᶜ) (2 + 1 + 0 + 1))
    (hf₂ : f₂ ∈ subspaceChainsInt (V ∩ LUᶜ) (2 + 1 + 0 + 1))
    (hf₃ : f₃ ∈ subspaceChainsInt (U ∩ V) (2 + 1 + 0 + 1))
    (hIsplit : (⇑(singularSdInt X (2 + 1 + 0 + 1)))^[μ]
        (fundCycleW (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChainInt X (2 + 1 + 0 + 1))
    (hF₂mem : F₂ ∈ subspaceChainsInt (U ∩ V) (2 + 1 + 0 + 1))
    (η₂ : SingularChainInt X (2 + 1 + 0 + 1 + 1)) (a₂ : SingularChainInt X (2 + 1 + 0 + 1))
    (heq₂ : F₂ - z₀ = chainBoundary X (2 + 1 + 0 + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (2 + 1 + 0 + 1))
    (hF₂bd : chainBoundary X (2 + 1 + 0) F₂
      ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (2 + 1 + 0))
    (aF : SingularChainInt (sub (LUᶜ ∩ (U ∩ V))) (2 + 1 + 0))
    (bF : SingularChainInt (sub (LVᶜ ∩ (U ∩ V))) (2 + 1 + 0))
    (hFsplit : chainBoundary X (2 + 1 + 0)
        ((⇑(singularSdInt X (2 + 1 + 0 + 1)))^[jF] F₂)
      = chainIncl _ (2 + 1 + 0) aF + chainIncl _ (2 + 1 + 0) bF) :
    ∃ E : SingularChainInt X (0 + 1), E ∈ subspaceChainsInt (U ∩ V) (0 + 1)
      ∧ chainBoundary X 0 (capInt (m := 0 + 1) g.1.1 (f₂ + f₃))
          + capInt (m := 0) g.1.1
              (chainIncl (LVᶜ ∩ (U ∩ V)) (2 + 1 + 0) bF)
        = chainBoundary X 0 E := by
  have hgvan : ∀ τ, g.1.1 (simplexIncl (LUᶜ ∩ LVᶜ) (2 + 1) τ) = 0 :=
    fun τ => relCochainInt_vanish (LUᶜ ∩ LVᶜ) g.1 τ
  have hgc : coboundary X (2 + 1) g.1.1 = 0 := by
    have hh := congrArg Subtype.val g.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  have hbdIsplit := congrArg (chainBoundary X (2 + 1 + 0)) hIsplit
  rw [singularSdInt_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (2 + 1 + 0) f₃
      = (⇑(singularSdInt X (2 + 1 + 0)))^[μ]
          (chainBoundary X (2 + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        - chainBoundary X (2 + 1 + 0) f₁ - chainBoundary X (2 + 1 + 0) f₂ := by
    rw [show (⇑(singularSdInt X (2 + 1 + 0)))^[μ]
          (chainBoundary X (2 + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        = chainBoundary X (2 + 1 + 0) f₁ + chainBoundary X (2 + 1 + 0) f₂
          + chainBoundary X (2 + 1 + 0) f₃ from hbdIsplit]
    abel
  have hSdKmem : (⇑(singularSdInt X (2 + 1 + 0)))^[μ]
      (chainBoundary X (2 + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChainsInt (LUᶜ ∩ LVᶜ) (2 + 1 + 0) :=
    singularSdInt_iterate_mem_subspaceChainsInt
      (hK₁ ▸ fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ
  set u : SingularChainInt X (2 + 1 + 0) :=
    (⇑(singularSdInt X (2 + 1 + 0)))^[μ]
      (chainBoundary X (2 + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
    - chainBoundary X (2 + 1 + 0) f₂
    - chainIncl (LUᶜ ∩ (U ∩ V)) (2 + 1 + 0) aF with hudef
  set w : SingularChainInt X (2 + 1 + 0) :=
    -chainBoundary X (2 + 1 + 0) f₁
    - chainIncl (LVᶜ ∩ (U ∩ V)) (2 + 1 + 0) bF with hwdef
  have humem : u ∈ subspaceChainsInt LUᶜ (2 + 1 + 0) :=
    Submodule.sub_mem _ (Submodule.sub_mem _
      (subspaceChainsInt_mono Set.inter_subset_left _ hSdKmem)
      (subspaceChainsInt_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChainsInt (V ∩ LUᶜ) (2 + 1 + 0) f₂ hf₂)))
      (subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self (chainIncl (LUᶜ ∩ (U ∩ V)) (2 + 1 + 0)) aF))
  have hwmem : w ∈ subspaceChainsInt LVᶜ (2 + 1 + 0) :=
    Submodule.sub_mem _ (Submodule.neg_mem _
      (subspaceChainsInt_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChainsInt (U ∩ LVᶜ) (2 + 1 + 0) f₁ hf₁)))
      (subspaceChainsInt_mono Set.inter_subset_left _
        (LinearMap.mem_range_self (chainIncl (LVᶜ ∩ (U ∩ V)) (2 + 1 + 0)) bF))
  have hbd_uncast : chainBoundary X (2 + 1 + 0)
      (f₃ - (⇑(singularSdInt X (2 + 1 + 0 + 1)))^[jF] F₂) = u + w := by
    rw [map_sub, hFsplit, hf₃bd, hudef, hwdef]; abel
  set capφc : SingularChainInt X (0 + 1) :=
    capInt (m := 0 + 1) (cochainSplitInt LUᶜ (2 + 1) g.1.1)
      (f₃ - (⇑(singularSdInt X (2 + 1 + 0 + 1)))^[jF] F₂) with hcapφc
  have hexplicit := capInt_coboundary_cochainSplit_eq_explicitInt (N := 2) (m := 0) LUᶜ LVᶜ g
    (f₃ - (⇑(singularSdInt X (2 + 1 + 0 + 1)))^[jF] F₂) u w humem hwmem hbd_uncast (by omega)
  obtain ⟨E₂, hE₂mem, hE₂⟩ := fact_i_n2_kill₀Int (N := 2) hU hV hLUc hLVc hLUU hLVV g z₀ hz₀
    K₁ K₂ hK₁ hK₂ μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit
  -- ∂E₂ = capg w + ∂capφc  ((-1)^2 = 1)
  have hED : chainBoundary X 0 E₂
      = capInt (m := 0) g.1.1 w + chainBoundary X 0 capφc := by
    have hcomb := hE₂.symm.trans hexplicit
    rwa [map_smul, show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_smul] at hcomb
  -- the fund-cycle kill, threaded WITHOUT pattern-matching the Sd^μ(∂fund) atom (binder-vs-fresh
  -- hidden-instance instability): push hbdIsplit through capInt by congrArg, splice the kill by
  -- defeq-`trans`, and split the sum
  have hkillsum : capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₁)
      + capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₂)
      + capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₃) = 0 := by
    have h0 : capInt (m := 0) g.1.1 ((⇑(singularSdInt X (2 + 1 + 0)))^[μ]
        (chainBoundary X (2 + 1 + 0) (fundCycleW (hU.union hV) z₀ hz₀ K₁))) = 0 :=
      capInt_subspaceChainInt_eq_zero (m := 0) (LUᶜ ∩ LVᶜ) g.1.1 hgvan hSdKmem
    have h1 := congrArg (capInt (m := 0) g.1.1) hbdIsplit
    have h2 : capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₁
        + chainBoundary X (2 + 1 + 0) f₂ + chainBoundary X (2 + 1 + 0) f₃) = 0 :=
      h1.symm.trans h0
    rw [← capIntₗ_apply, map_add, map_add, capIntₗ_apply, capIntₗ_apply, capIntₗ_apply] at h2
    exact h2
  -- ∂cap(f₂+f₃) = cap g ∂f₁  (cocycle chain-map at (-1)^(2+1) = -1 + the kill)
  have hstep : chainBoundary X 0 (capInt (m := 0 + 1) g.1.1 (f₂ + f₃))
      = capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₁) := by
    rw [capInt_cocycle_chainMap (m := 0) g.1.1 hgc (f₂ + f₃),
      show ((-1 : ℤ) ^ (2 + 1)) = -1 by norm_num, neg_smul, one_smul, map_add,
      ← capIntₗ_apply, map_add, capIntₗ_apply, capIntₗ_apply]
    linear_combination (norm := module) -hkillsum
  have hwcap : capInt (m := 0) g.1.1 w
      = -capInt (m := 0) g.1.1 (chainBoundary X (2 + 1 + 0) f₁)
        - capInt (m := 0) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (2 + 1 + 0) bF) := by
    rw [hwdef, ← capIntₗ_apply, map_sub, map_neg, capIntₗ_apply, capIntₗ_apply]
  refine ⟨capφc - E₂,
    Submodule.sub_mem _
      (hcapφc ▸ capInt_mem_subspaceChainsInt (m := 0 + 1) (U ∩ V) _
        (Submodule.sub_mem _ hf₃ (singularSdInt_iterate_mem_subspaceChainsInt hF₂mem jF)))
      hE₂mem, ?_⟩
  rw [hstep, map_sub, hED, hwcap]
  abel

omit [T2Space ↑X] in
/-- **The H₀ descent bridge** (degree-0 mirror of `homology_eq_of_ambient_boundaryInt`): two
`sub S` 0-cycles are homologous if their ambient realizations differ by the boundary of an
`S`-supported 1-chain — reflect `E` via `inclRangeEquiv.symm` (the chain map `chainIncl S` is
injective). -/
theorem homology_eq_of_ambient_boundary₀Int {S : Set ↑X}
    (cL cR : cycles (sub S) 0) (E : SingularChainInt X (0 + 1))
    (hE : E ∈ subspaceChainsInt S (0 + 1))
    (h : chainBoundary X 0 E
        = chainIncl S 0 (cL : SingularChainInt (sub S) 0)
          - chainIncl S 0 (cR : SingularChainInt (sub S) 0)) :
    Homology.mk (sub S) 0 cL = Homology.mk (sub S) 0 cR := by
  refine (Submodule.Quotient.eq _).2 ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  refine ⟨(inclRangeEquiv S (0 + 1)).symm ⟨E, hE⟩, ?_⟩
  apply chainIncl_injective S 0
  rw [chainIncl_chainBoundary, chainIncl_inclRangeEquiv_symm, map_sub]
  exact h

/-- **`legW₀Int` on a `Quotient.mk`** — the bottom duality-leg `mk`-rule (the ℤ analogue of the
mod-2 `legW₀_mk`; `rfl` via `relativeDualityK₀Int_mk`). -/
theorem legW₀Int_mk {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W)
    (a : LinearMap.ker (relCoboundaryIntₗ ((↑K.1 : Set ↑X)ᶜ) (k + 1))) :
    SKEFTHawking.SingularOpenDualityBotInt.legW₀Int hW z₀ hz₀ K
        (RelativeCohomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a)
      = Homology.mk (sub W) 0
          ⟨SKEFTHawking.SingularLocalDualityKBotInt.pullbackDualityIntₗ₀ ((↑K.1 : Set ↑X)ᶜ) W
              (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int hW z₀ hz₀ K)
              (SKEFTHawking.SingularOpenDualityBotInt.fundCycleW₀Int_mem_W hW z₀ hz₀ K) a,
            Submodule.mem_top⟩ :=
  rfl

end SKEFTHawking.SingularConnSquareCloseNCInt
