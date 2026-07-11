/-
# Phase 5q.H (E1 CSC-PD tower) — Route B, the fact-(i) subtree (integral)

The χ-term ("fact (i)") half of the mod-2 Route B close of the PD connecting square, ported to ℤ,
bottom-up. Builds on Brick J (`SingularConnSquareCloseNCInt`). The fact-(i) subtree runs
`fundCycleW_chain_relInt` → Brick K′ (`fund_pair_three_set_rel_comparison_freeInt`) → Brick L
(`fact_i_n2_killInt`, the direct Brick-J consumer, `relCochains→∀τ` bridge) → Brick M
(`fact_i_ambient_coreInt`, uses `capInt_coboundary_cochainSplit_eqInt`) → `fact_i_stage1Int` →
`fact_i_dischargeInt`.

* `fundCycleW_chain_relInt` — chain-level extraction of `fundCycleW_relHomologous`:
  `∃ η a, fundCycleW − z₀ = ∂η + a ∧ a ∈ C(Kᶜ)`.

Sign convention (recorded): over ℤ both fundamental cycles are rel-homologous to the SAME `+z₀`, so the
mod-2 `f₃ + Sd^jF F₂ ~ 2z₀` char-2 self-cancellation does NOT hold; the honest ℤ port targets the `−`
form (`f₃ − Sd^jF F₂`, `fundCycleW − z₀`), the module's documented `+`→`−` adaptation. This orientation
propagates up the subtree and is pinned at `subHomConnecting_openDualityInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularOpenDualityCycleInt
import SKEFTHawking.SingularConnSquareCloseNCInt
import SKEFTHawking.SingularChainCastHelpersInt
import SKEFTHawking.SingularCochainSplitInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_relHomologous fundCycleW_boundary)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt iterHomotopyInt_chainHomotopy
  singularSdInt_iterate_chainBoundary)
open SKEFTHawking.SingularExcisionIsoInt (iterHomotopyInt_mem_subspaceChainsInt
  singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularRelativeMVInt (subspaceChainsInt_mono)
open SKEFTHawking.SingularCochainSplitInt (cochainSplitInt cochainSplitInt_coboundary_mem_UInt
  cochainSplitInt_coboundary_mem_VInt)
open SKEFTHawking.SingularEuclideanCapIsoInt (relCoboundaryIntₗ relCoboundaryIntₗ_coe relCochainInt_vanish)

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat} [T2Space ↑X]

/-- **`fundCycleW` is chain-rel-homologous to `z₀`** (integral, chain-level extraction of
`fundCycleW_relHomologous`). ℤ port of the mod-2 `SingularConnSquareCloseNC.fundCycleW_chain_rel`.
Signs: the mod-2 witness `a := ∂η + (fund + z₀)` is a char-2 collapse (`∂η + ∂η = 0`); over ℤ we take
`η' := -η`, `a := fundCycleW - z₀ + ∂η ∈ C(Kᶜ)`, giving the honest `fundCycleW - z₀ = ∂η' + a`
(the module's documented `+`→`−` adaptation). -/
theorem fundCycleW_chain_relInt {W : Set ↑X} {k m : ℕ} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K : CompactsIn W) :
    ∃ (η : SingularChainInt X (k + m + 1 + 1)) (a : SingularChainInt X (k + m + 1)),
      fundCycleW hW z₀ hz₀ K - z₀ = chainBoundary X (k + m + 1) η + a ∧
        a ∈ subspaceChainsInt ((↑K.1 : Set ↑X)ᶜ) (k + m + 1) := by
  obtain ⟨w, hw⟩ := fundCycleW_relHomologous hW z₀ hz₀ K
  obtain ⟨η, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  erw [relBoundaryInt_mk] at hw
  refine ⟨-η, fundCycleW hW z₀ hz₀ K - z₀ + chainBoundary X (k + m + 1) η, ?_, ?_⟩
  · rw [map_neg]; abel
  · rw [← RelativeChainInt.mk_eq_zero_iff]
    simp only [RelativeChainInt.mk] at hw ⊢
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub, hw]
    abel

/-- **The FREE two-fund three-set rel-comparison** (Brick K′, integral). ℤ port of the mod-2
`SingularConnSquareCloseNC.fund_pair_three_set_rel_comparison_free`. **Sign:** over ℤ both funds are
rel-homologous to the *same* `+z₀`, so the mod-2 target `f₃ + Sd^jF F₂ ~ 2z₀` does NOT cancel; the
honest ℤ target is `f₃ − Sd^jF F₂ = ∂D + ρ` (`z₀` cancels), with
`D := η₁ − T_μ fund₁ − η₂ + T_jF F₂`, `ρ := a₁ − T_μ(∂fund₁) − f₁ − f₂ − a₂ + T_jF(∂F₂) ∈ C(S)`.
The chain-homotopy `∂Dₘ + Dₘ∂ = 1 − Sdᵐ` and `fundCycleW_chain_relInt` both carry the documented
`+`→`−` adaptation. -/
theorem fund_pair_three_set_rel_comparison_freeInt {W₁ S : Set ↑X} (hW₁ : IsOpen W₁)
    {k m : ℕ} (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (K₁ : CompactsIn W₁) (hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ S)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChainInt X (k + m + 1))
    (hf₁ : f₁ ∈ subspaceChainsInt S (k + m + 1)) (hf₂ : f₂ ∈ subspaceChainsInt S (k + m + 1))
    (hsplit : (⇑(singularSdInt X (k + m + 1)))^[μ] (fundCycleW hW₁ z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChainInt X (k + m + 1)) (η₂ : SingularChainInt X (k + m + 1 + 1))
    (a₂ : SingularChainInt X (k + m + 1))
    (heq₂ : F₂ - z₀ = chainBoundary X (k + m + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChainsInt S (k + m + 1))
    (hF₂bd : chainBoundary X (k + m) F₂ ∈ subspaceChainsInt S (k + m)) :
    ∃ (D : SingularChainInt X (k + m + 1 + 1)) (ρ : SingularChainInt X (k + m + 1)),
      ρ ∈ subspaceChainsInt S (k + m + 1)
      ∧ f₃ - (⇑(singularSdInt X (k + m + 1)))^[jF] F₂
        = chainBoundary X (k + m + 1) D + ρ := by
  obtain ⟨η₁, a₁, heq₁, ha₁⟩ := fundCycleW_chain_relInt hW₁ z₀ hz₀ K₁
  have hh₁ := iterHomotopyInt_chainHomotopy X μ (k + m) (fundCycleW hW₁ z₀ hz₀ K₁)
  have hh₂ := iterHomotopyInt_chainHomotopy X jF (k + m) F₂
  refine ⟨η₁ - iterHomotopyInt X (k + m + 1) μ (fundCycleW hW₁ z₀ hz₀ K₁) - η₂
      + iterHomotopyInt X (k + m + 1) jF F₂,
    a₁ - iterHomotopyInt X (k + m) μ (chainBoundary X (k + m) (fundCycleW hW₁ z₀ hz₀ K₁))
      - f₁ - f₂ - a₂ + iterHomotopyInt X (k + m) jF (chainBoundary X (k + m) F₂), ?_, ?_⟩
  · -- ρ ∈ C(S)
    refine Submodule.add_mem _
      (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _
        (subspaceChainsInt_mono hK₁S _ ha₁)
        (subspaceChainsInt_mono hK₁S _ (iterHomotopyInt_mem_subspaceChainsInt
          (fundCycleW_boundary hW₁ z₀ hz₀ K₁) μ)))
        hf₁) hf₂) ha₂)
      (iterHomotopyInt_mem_subspaceChainsInt hF₂bd jF)
  · -- the equation (honest ℤ signs; z₀/fund₁/F₂ and each rel-witness atom cancel)
    have e1 : chainBoundary X (k + m + 1) η₁
        = fundCycleW hW₁ z₀ hz₀ K₁ - z₀ - a₁ := by
      rw [eq_sub_iff_add_eq]; exact heq₁.symm
    have e2 : chainBoundary X (k + m + 1) η₂ = F₂ - z₀ - a₂ := by
      rw [eq_sub_iff_add_eq]; exact heq₂.symm
    have e3 : chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) μ (fundCycleW hW₁ z₀ hz₀ K₁))
        = fundCycleW hW₁ z₀ hz₀ K₁ - (⇑(singularSdInt X (k + m + 1)))^[μ] (fundCycleW hW₁ z₀ hz₀ K₁)
          - iterHomotopyInt X (k + m) μ (chainBoundary X (k + m) (fundCycleW hW₁ z₀ hz₀ K₁)) := by
      rw [eq_sub_iff_add_eq]; exact hh₁
    have e4 : chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) jF F₂)
        = F₂ - (⇑(singularSdInt X (k + m + 1)))^[jF] F₂
          - iterHomotopyInt X (k + m) jF (chainBoundary X (k + m) F₂) := by
      rw [eq_sub_iff_add_eq]; exact hh₂
    have hD : chainBoundary X (k + m + 1)
          (η₁ - iterHomotopyInt X (k + m + 1) μ (fundCycleW hW₁ z₀ hz₀ K₁) - η₂
            + iterHomotopyInt X (k + m + 1) jF F₂)
        = chainBoundary X (k + m + 1) η₁
          - chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) μ (fundCycleW hW₁ z₀ hz₀ K₁))
          - chainBoundary X (k + m + 1) η₂
          + chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) jF F₂) := by
      simp only [map_add, map_sub]
    rw [hD, e1, e2, e3, e4, hsplit]
    abel

/-- **The N2 δφ-kill** (Brick L, integral). ℤ port of the mod-2
`SingularConnSquareCloseNC.fact_i_n2_kill`, the direct Brick-J consumer. Uses the `−` orientation
(`c := f₃ − Sd^jF F₂`, `heq₂ : F₂ − z₀ = ∂η₂ + a₂`) throughout; the `∂c`-leg split flips sign
(`u := Sd^μ(∂fund₁) − ∂f₂ − aFᵃᵐᵇ`, `w := −∂f₁ − bFᵃᵐᵇ`). The `relCochainsInt → ∀τ` feed for Brick J's
`haA/haB` goes through `relCochainInt_vanish` on `cochainSplitInt_coboundary_mem_{U,V}Int`. -/
theorem fact_i_n2_killInt {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
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
      = chainIncl _ (N + 1 + (p + 1)) aF + chainIncl _ (N + 1 + (p + 1)) bF)
    (h : N + 1 + (p + 1) + 1 = N + 1 + 1 + (p + 1)) :
    ∃ E : SingularChainInt X (p + 1 + 1), E ∈ subspaceChainsInt (U ∩ V) (p + 1 + 1)
      ∧ capInt (m := p + 1) (coboundary X (N + 1) (cochainSplitInt LUᶜ (N + 1) g.1.1))
          (h ▸ (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂))
        = chainBoundary X (p + 1) E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 := by
    have hh := congrArg Subtype.val g.2
    simpa only [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] using hh
  have hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ LUᶜ ∪ LVᶜ := by
    rw [hK₁]; exact fun x hx => Or.inl hx.1
  -- Brick K′ (− orientation): `f₃ − Sd^jF F₂ = ∂D + ρ`, `ρ ∈ C(LUᶜ ∪ LVᶜ)`
  obtain ⟨D, ρ, hρ, heq⟩ :=
    fund_pair_three_set_rel_comparison_freeInt (S := LUᶜ ∪ LVᶜ) (k := N + 1) (m := p + 1)
      (hU.union hV) z₀ hz₀ K₁ hK₁S μ jF f₁ f₂ f₃
      (subspaceChainsInt_mono (fun _ hx => Or.inr hx.2) _ hf₁)
      (subspaceChainsInt_mono (fun _ hx => Or.inl hx.2) _ hf₂)
      hIsplit F₂ η₂ a₂ heq₂ ha₂ hF₂bd
  -- ∂c-legs (− orientation): Sd^μ(∂fund₁) = ∂f₁ + ∂f₂ + ∂f₃
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + (p + 1))) hIsplit
  rw [singularSdInt_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + (p + 1)) f₃
      = (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
          (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
        - chainBoundary X (N + 1 + (p + 1)) f₁ - chainBoundary X (N + 1 + (p + 1)) f₂ := by
    rw [hbdIsplit]; abel
  have hSdmem : (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChainsInt LUᶜ (N + 1 + (p + 1)) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (singularSdInt_iterate_mem_subspaceChainsInt
        (hK₁ ▸ fundCycleW_boundary (hU.union hV) z₀ hz₀ K₁) μ)
  have hf2bdmem : chainBoundary X (N + 1 + (p + 1)) f₂ ∈ subspaceChainsInt LUᶜ (N + 1 + (p + 1)) :=
    subspaceChainsInt_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChainsInt (V ∩ LUᶜ) (N + 1 + (p + 1)) f₂ hf₂)
  have haFmem : chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF ∈ subspaceChainsInt LUᶜ (N + 1 + (p + 1)) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (LinearMap.mem_range_self (chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1))) aF)
  have hf1bdmem : chainBoundary X (N + 1 + (p + 1)) f₁ ∈ subspaceChainsInt LVᶜ (N + 1 + (p + 1)) :=
    subspaceChainsInt_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChainsInt (U ∩ LVᶜ) (N + 1 + (p + 1)) f₁ hf₁)
  have hbFmem' : chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF ∈ subspaceChainsInt LVᶜ (N + 1 + (p + 1)) :=
    subspaceChainsInt_mono Set.inter_subset_left _
      (LinearMap.mem_range_self (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1))) bF)
  set u : SingularChainInt X (N + 1 + (p + 1)) :=
    (⇑(singularSdInt X (N + 1 + (p + 1))))^[μ]
      (chainBoundary X (N + 1 + (p + 1)) (fundCycleW (hU.union hV) z₀ hz₀ K₁))
    - chainBoundary X (N + 1 + (p + 1)) f₂
    - chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) aF with hudef
  set w : SingularChainInt X (N + 1 + (p + 1)) :=
    -chainBoundary X (N + 1 + (p + 1)) f₁
    - chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + (p + 1)) bF with hwdef
  have humem : u ∈ subspaceChainsInt LUᶜ (N + 1 + (p + 1)) :=
    Submodule.sub_mem _ (Submodule.sub_mem _ hSdmem hf2bdmem) haFmem
  have hwmem : w ∈ subspaceChainsInt LVᶜ (N + 1 + (p + 1)) :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hf1bdmem) hbFmem'
  have hbd_uncast : chainBoundary X (N + 1 + (p + 1))
      (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂) = u + w := by
    rw [map_sub, hFsplit, hf₃bd, hudef, hwdef]; abel
  -- cast to the (N+1+1)-frame
  have h' : N + 1 + (p + 1) = N + 1 + 1 + p := by omega
  have hD : N + 1 + (p + 1) + 1 + 1 = N + 1 + 1 + (p + 1) + 1 := by omega
  have hDcast : chainBoundary X (N + 1 + 1 + (p + 1)) (hD ▸ D)
      = h ▸ chainBoundary X (N + 1 + (p + 1) + 1) D :=
    chainBoundary_castInt hD h D
  have heq' : (h ▸ (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂)
        : SingularChainInt X (N + 1 + 1 + (p + 1)))
      = chainBoundary X (N + 1 + 1 + (p + 1)) (hD ▸ D) + (h ▸ ρ) := by
    rw [hDcast, ← singularChainInt_cast_add, ← heq]
  have hρ' : (h ▸ ρ : SingularChainInt X (N + 1 + 1 + (p + 1)))
      ∈ subspaceChainsInt (LUᶜ ∪ LVᶜ) (N + 1 + 1 + (p + 1)) :=
    subspaceChains_cast_memInt h hρ
  have hcP : (h ▸ (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂)
        : SingularChainInt X (N + 1 + 1 + (p + 1)))
      ∈ subspaceChainsInt (U ∩ V) (N + 1 + 1 + (p + 1)) :=
    subspaceChains_cast_memInt h (Submodule.sub_mem _ hf₃
      (singularSdInt_iterate_mem_subspaceChainsInt hF₂mem jF))
  have hbd' : chainBoundary X (N + 1 + 1 + p)
      (h ▸ (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂))
      = (h' ▸ u) + (h' ▸ w) :=
    (chainBoundary_castInt h h' _).trans (by rw [hbd_uncast, singularChainInt_cast_add])
  have humem' : (h' ▸ u : SingularChainInt X (N + 1 + 1 + p))
      ∈ subspaceChainsInt LUᶜ (N + 1 + 1 + p) := subspaceChains_cast_memInt h' humem
  have hwmem' : (h' ▸ w : SingularChainInt X (N + 1 + 1 + p))
      ∈ subspaceChainsInt LVᶜ (N + 1 + 1 + p) := subspaceChains_cast_memInt h' hwmem
  rw [subspaceChainsInt, LinearMap.mem_range] at humem' hwmem'
  obtain ⟨uS, huS⟩ := humem'
  obtain ⟨wS, hwS⟩ := hwmem'
  have hcover : (U ∩ V) ∪ (LUᶜ ∪ LVᶜ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hxU : x ∈ LU
    · by_cases hxV : x ∈ LV
      · exact Or.inl ⟨hLUU hxU, hLVV hxV⟩
      · exact Or.inr (Or.inr hxV)
    · exact Or.inr (Or.inl hxU)
  -- Brick J on the cast frame with the `relCochainsInt → ∀τ` bridge
  obtain ⟨E, hE, hcap⟩ :=
    cap_relCochains_pair_double_support_eq_boundaryInt hLUc hLVc (hU.inter hV) hcover
      (k := N + 1 + 1) (n := p)
      (coboundary X (N + 1) (cochainSplitInt LUᶜ (N + 1) g.1.1))
      (coboundary_comp_coboundary X (N + 1) _)
      (fun τ => relCochainInt_vanish LUᶜ
        ⟨_, cochainSplitInt_coboundary_mem_UInt LUᶜ (N + 1) g.1.1⟩ τ)
      (fun τ => relCochainInt_vanish LVᶜ
        ⟨_, cochainSplitInt_coboundary_mem_VInt LUᶜ LVᶜ (N + 1) g.1.1 g.1.2 hgc⟩ τ)
      (h ▸ (f₃ - (⇑(singularSdInt X (N + 1 + (p + 1) + 1)))^[jF] F₂))
      hcP (hD ▸ D) (h ▸ ρ) hρ' heq' uS wS (by rw [hbd', ← huS, ← hwS])
  exact ⟨E, hE, hcap⟩

end SKEFTHawking.SingularConnSquareCloseNCInt
