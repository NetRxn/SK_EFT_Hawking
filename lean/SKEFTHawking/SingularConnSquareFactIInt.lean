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

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_relHomologous)

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

end SKEFTHawking.SingularConnSquareCloseNCInt
