import SKEFTHawking.BHEntropyMicroscopic
import SKEFTHawking.SymTFTAudit.WittClass
import Mathlib

/-!
# Horizon boundary condition — Witt-invariant strengthening (Phase 6a Wave 8B)

Wave 8 gave `H_HorizonBoundaryCondition.anomalyMatch := chiralAnomalyVanishesMod8 c₋`
(`8 ∣ c₋`, the vanishing of the *perturbative* gravitational anomaly mod 8). For the ADW horizon
(`c₋ = 8 N_f`, Wave 8 `adw_chiral_charge_vanishes_mod8`) that condition is **trivially satisfied
for every `N_f`** (`8 ∣ 8 N_f` always) — see `horizon_wave8_anomalyMatch_always`. So as a constraint
on the ADW model it is vacuous.

This module sharpens it to the genuine **SymTFT Witt-class** condition by wiring the EXISTING
Witt-class machinery (`SymTFTAudit.WittClass`, ultimately the bulk-boundary correspondence
`SymTFT.BulkBoundaryCorrespondence.witt_triviality_iff_has_lagrangian_algebra` and DMNO 2010):

- `horizon_wittTrivial_iff_three_generations` — the SHARP condition `WittTrivial (8 N_f)`
  (equivalently `24 ∣ c₋`, the full framing-anomaly mod 24) holds **iff `3 ∣ N_f`**
  (UNCONDITIONAL; `SymTFTAudit.chiralCentralCharge_wittTrivial_iff_three_dvd_N_f`).
- `wittTrivial_implies_mod8` — `24 ∣ c ⟹ 8 ∣ c`: Wave 8's `anomalyMatch` is exactly the
  *necessary shadow* of the sharp Witt-class condition.
- `horizon_anomalyMatch_strictly_weaker_than_witt` — the **de-vacuization**: `N_f = 1` PASSES
  Wave 8's `chiralAnomalyVanishesMod8` but FAILS Witt-triviality (`24 ∤ 8`), so the strengthening
  genuinely constrains beyond the mod-8 anomaly.
- `horizon_three_generations_wittTrivial` — witness: three generations satisfy the sharp condition.

**Physical reading** (cited, not re-proven here): Witt-triviality of the boundary is *equivalent*
to the boundary admitting a gapped / Lagrangian-algebra (topological) boundary
(Davydov–Müger–Nikshych–Ostrik 2010; `SymTFT.BulkBoundaryCorrespondence`, DMNO-conditional). Thus
the sharp horizon consistency condition is the *necessary-and-sufficient* gapped-boundary condition,
of which Wave 8's `8 ∣ c₋` is only the perturbative necessary part. The `⟺ 3 ∣ N_f` leg proven here
is unconditional; the gapped-boundary equivalence is the cited DMNO correspondence.

Kernel-pure; no new axioms. `c₋ = 8 N_f` here is the ADW horizon charge of Wave 8.
-/

namespace SKEFTHawking
namespace HorizonWittBoundary

open SKEFTHawking.SymTFTAudit SKEFTHawking.BHEntropyMicroscopic

/-- Horizon chiral central charge for `N_f` ADW Dirac species: `c₋ = 8 N_f`
(Wave 8 `adw_chiral_charge_vanishes_mod8`). -/
def horizonChiralCentralCharge (N_f : ℕ) : ℤ := 8 * (N_f : ℤ)

/-- **Sharp horizon consistency ⟺ three-generation divisibility (unconditional).** The horizon's
chiral central charge `c₋ = 8 N_f` is Witt-trivial (in the trivial `ℤ/24` Witt class, i.e.
`24 ∣ c₋`) **iff `3 ∣ N_f`**. Wires `SymTFTAudit.chiralCentralCharge_wittTrivial_iff_three_dvd_N_f`
into the horizon boundary condition — the sharp form of Wave 8's `anomalyMatch`. -/
theorem horizon_wittTrivial_iff_three_generations (N_f : ℕ) :
    WittTrivial (horizonChiralCentralCharge N_f) ↔ 3 ∣ N_f :=
  chiralCentralCharge_wittTrivial_iff_three_dvd_N_f N_f

/-- **The sharp Witt condition implies Wave 8's mod-8 `anomalyMatch`** (`24 ∣ c ⟹ 8 ∣ c`): the
perturbative `8 ∣ c₋` is exactly the necessary shadow of the sharp Witt-class condition. -/
theorem wittTrivial_implies_mod8 (c : ℤ) (h : WittTrivial c) : (8 : ℤ) ∣ c := by
  rw [WittTrivial_iff_dvd] at h
  exact dvd_trans (by norm_num) h

/-- **Wave 8's `anomalyMatch` is vacuous for the ADW horizon.** `chiralAnomalyVanishesMod8 (8 N_f)`
holds for every `N_f` (witness `k = N_f`), so the mod-8 field never constrains the ADW model — the
motivation for the sharp Witt strengthening. -/
theorem horizon_wave8_anomalyMatch_always (N_f : ℕ) :
    chiralAnomalyVanishesMod8 (8 * (N_f : ℝ)) :=
  ⟨(N_f : ℤ), by push_cast; ring⟩

/-- **De-vacuization: the sharp Witt condition is strictly stronger than Wave 8's mod-8 field.**
`N_f = 1` PASSES `chiralAnomalyVanishesMod8` but FAILS Witt-triviality (`24 ∤ 8`) — the
strengthening genuinely constrains beyond the perturbative mod-8 anomaly. -/
theorem horizon_anomalyMatch_strictly_weaker_than_witt :
    chiralAnomalyVanishesMod8 (8 * (1 : ℝ)) ∧ ¬ WittTrivial (horizonChiralCentralCharge 1) := by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  unfold horizonChiralCentralCharge
  rw [WittTrivial_iff_dvd]
  omega

/-- **Witness: three generations satisfy the sharp Witt condition** (`24 ∣ 24`). -/
theorem horizon_three_generations_wittTrivial :
    WittTrivial (horizonChiralCentralCharge 3) := by
  unfold horizonChiralCentralCharge
  rw [WittTrivial_iff_dvd]
  omega

end HorizonWittBoundary
end SKEFTHawking
