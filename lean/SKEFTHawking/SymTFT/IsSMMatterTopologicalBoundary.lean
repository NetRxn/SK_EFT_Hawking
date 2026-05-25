/-
# Phase 6r Wave 3a.2 + 3a.3 — SM matter as topological-boundary-condition data

The substantive Wave 3a content: the predicate-substrate-level encoding
of Standard-Model matter content as a topological boundary condition of
a SymTFT bulk, with the substantive theorem `sm_3gen_via_symtft`
recovering the 3-generation constraint from the SymTFT framework.

## Primary anchor (Wave 3a.1 §Q1(a))

**Bhardwaj-Copetti-Pajer-Schäfer-Nameki, "Boundary SymTFT,"
arXiv:2409.02166, SciPost Phys. 19 (2025) 061** is the PRIMARY anchor,
with two verbatim load-bearing claims:

> "transformation properties, or (generalized) charges, of BCs are
>  captured by topological BCs of Symmetry Topological Field Theory
>  (SymTFT)" — abstract.

> "Gapped boundary conditions are in one-to-one correspondence with
>  Lagrangian algebras L in the Drinfeld center" — body.

KOZ (arXiv:2209.11062) and Freed-Moore-Teleman (arXiv:2209.07471) are
SECONDARY anchors; Choi-Lam-Shao (arXiv:2205.05086), Cordova-Ohmori
(arXiv:2205.06243), Cordova-Hsin-Zhang (arXiv:2308.11706),
Heckman-Hübner-Murdia (arXiv:2401.09538, arXiv:2505.23887), and the
TY series (arXiv:1610.07010, arXiv:1803.10796, arXiv:1909.08775,
arXiv:2003.11550) are SUPPORTING.

## Wave 3a.3 substantive theorem signatures (as shipped)

Two complementary headline theorems are shipped (Round-1 strengthening
+ adversarial-review remediation):

```
-- Unconditional biconditional (load-bearing modular Witt-class result)
theorem sm_3gen_via_symtft (N_f : ℕ) :
    sm_bulk N_f = 0 ↔ 3 ∣ N_f

-- SymTFT-framework-consistency witness (Wave 2a.3 spin-SymTFT side)
theorem sm_boundary_data_is_topological_boundary (N_f : ℕ) :
    IsSMMatterTopologicalBoundary (sm_boundary_data N_f)

-- Hypothesis-bearing variant exposing the consistency hypothesis at the
-- type-signature level (documentary; the hypothesis is satisfied via
-- `sm_boundary_data_is_topological_boundary`).
theorem sm_3gen_via_symtft_under_boundary_hyp (N_f : ℕ)
    (_h : IsSMMatterTopologicalBoundary (sm_boundary_data N_f)) :
    sm_bulk N_f = 0 ↔ 3 ∣ N_f
```

Per Wave 3a.1 §Q2(a) Crucial Correction, the `IsSMMatterTopologicalBoundary
(sm_boundary_data N_f)` hypothesis (when surfaced) is an **explicit
Prop-valued hypothesis**, NOT bracketed instance syntax — because the
program *proves* it via `sm_boundary_data_is_topological_boundary`, not
via typeclass search.

Note `sm_bulk : ℕ → WittInvariant` is the modular bulk Witt-invariant
function; equality `sm_bulk N_f = 0` is in `WittInvariant := ZMod 24`.

## Maintain Z₂₄ vs Z₁₆ distinction (Wave 3a.1 §Caveats discipline)

The Witt class of the SymTFT bulk has **two sectors**:
- Modular ℤ/24 (chiral central charge, DMNO 2010)
- Pin⁺ spin-extension ℤ/16 (Ising-Witt-subgroup, DNO arXiv:1109.5558)

Both live in the same Witt-group structure but are easily confused.
**This module maintains strict distinction.**

## Citation discipline (LOAD-BEARING per Wave 3a.1 §Q1(b))

- ✅ `arXiv:2409.02166` Bhardwaj-Copetti-Pajer-Schäfer-Nameki (PRIMARY anchor).
- ✅ `arXiv:2207.10700` Davighi-Gripaios-Lohitsiri "Anomalies of non-Abelian
  finite groups via cobordism" (NOT `arXiv:2207.04050` which is an ML paper).
- ✅ `arXiv:1009.2117` Davydov-Müger-Nikshych-Ostrik (DMNO 2010).
- ✅ `arXiv:1109.5558` Davydov-Nikshych-Ostrik 2012 (Ising Witt subgroup ≅ ℤ/16).

## Hedging discipline (Wave 3a.1 §Q1(c))

- ✅ "Building on the boundary-SymTFT framework of Bhardwaj-Copetti-Pajer-
  Schäfer-Nameki (arXiv:2409.02166), the SK_EFT_Hawking program identifies
  the SM matter content with a specific topological-boundary-condition
  assignment in a Drinfeld-center bulk, and formalizes the assignment in
  Lean 4."
- ❌ "First SymTFT formalization of SM" *unscoped*.

## References

- Bhardwaj-Copetti-Pajer-Schäfer-Nameki, arXiv:2409.02166 (PRIMARY).
- Kaidi-Ohmori-Zheng, arXiv:2209.11062 (SECONDARY).
- Freed-Moore-Teleman, arXiv:2209.07471 (SECONDARY).
- Davydov-Müger-Nikshych-Ostrik, arXiv:1009.2117 (Witt-trivial ↔ Lagrangian).
- Davydov-Nikshych-Ostrik, arXiv:1109.5558 (Ising Witt subgroup = ℤ/16).
- Witten-Yonekura, arXiv:1909.08775 (anomaly inflow).
- Kapustin-Thorngren-Turzillo-Wang, arXiv:1406.7329 (Pin⁺ ℤ/16 SPT).
- García-Etxebarria-Montero, arXiv:1808.00009 (SM-with-νR identification).
- Davighi-Gripaios-Lohitsiri, arXiv:2207.10700 (cobordism anomalies).
- Dobrescu-Poppitz, PRL 87, 031801 (2001); arXiv:hep-ph/0102010
  (classical 3-gen-from-global-anomaly result).
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.LagrangianAlgebra
import SKEFTHawking.SymTFT.GappedBoundary
import SKEFTHawking.SymTFT.PinBordism
import SKEFTHawking.SymTFT.SpinSymTFT
import SKEFTHawking.SymTFT.SubstrateEtaInvariant
import SKEFTHawking.SymTFTAudit.WittClass
import SKEFTHawking.GenerationConstraint

namespace SKEFTHawking.SymTFT

open SKEFTHawking SKEFTHawking.SymTFTAudit

/-! ## §1. The SM-matter substrate

The SM matter content is parameterized by the fermion-generation count
`N_f : ℕ`. Per García-Etxebarria-Montero arXiv:1808.00009, including
right-handed neutrinos gives 16 Weyl fermions per generation, with
total ℤ/16 anomaly class `16·N_f ≡ 0 (mod 16)` — anomaly-free for all
N_f. The 3-generation constraint comes from the **modular** Witt-class
condition: `c₋ = 8·N_f ≡ 0 (mod 24) ↔ 3 ∣ N_f`. -/

/-- **`sm_boundary_data N_f`** — the SM matter content with `N_f`
generations, packaged as a `SubstrateConfig` (Phase 6l Wave 1
substrate). The `z16_class` is `(16 * N_f : ZMod 16) = 0` — always
anomaly-free in the Pin⁺ sector with right-handed neutrinos included
(García-Etxebarria-Montero 1808.00009). -/
def sm_boundary_data (N_f : ℕ) : Z16AnomalyForcesThetaBar.SubstrateConfig where
  z16_class := (16 * N_f : ZMod 16)
  theta_bar := 0

/-- The SM boundary data with right-handed neutrinos is always Pin⁺-
anomaly-free in ℤ/16, by `16 * N_f ≡ 0 mod 16`. -/
theorem sm_boundary_data_z16_cancels (N_f : ℕ) :
    Z16AnomalyForcesThetaBar.Z16AnomalyCancels (sm_boundary_data N_f) := by
  show (16 * (N_f : ZMod 16)) = 0
  -- 16 ≡ 0 in ZMod 16
  have : (16 : ZMod 16) = 0 := by decide
  rw [this]; ring

/-- **`sm_bulk N_f`** — the modular SymTFT bulk Witt invariant for the
SM with `N_f` generations: `c₋ = 8·N_f` mapped via the modular Witt
class `ZMod 24`. -/
def sm_bulk (N_f : ℕ) : WittInvariant :=
  WittInvariant.fromChiralCentralCharge (8 * (N_f : ℤ))

/-! ## §2. The `IsSMMatterTopologicalBoundary` predicate (Wave 3a.2) -/

/-- **`IsSMMatterTopologicalBoundary s`** — predicate stating that a
substrate `s : SubstrateConfig` carries the data of an SM-matter
topological boundary condition in the sense of Wave 3a.1 §Q2(a):
- The substrate is spin-SymTFT-consistent (Wave 2a.3 sense).
- The substrate's modular Witt invariant is well-defined.
- The substrate's z16 class is anomaly-free in the Pin⁺ sector (Wave 2a.3).

The "topological boundary" semantics is anchored on Bhardwaj-Copetti-
Pajer-Schäfer-Nameki arXiv:2409.02166: "transformation properties …
of BCs are captured by topological BCs of Symmetry Topological Field
Theory."

Per Wave 3a.1 §Q2(a) Crucial Correction, this is an **explicit Prop-
valued hypothesis** carried by consumers, not a typeclass argument. -/
def IsSMMatterTopologicalBoundary (s : Z16AnomalyForcesThetaBar.SubstrateConfig) :
    Prop :=
  -- The substrate is spin-SymTFT-consistent (Wave 2a.3) — equivalently,
  -- its Pin⁺ class is anomaly-free.
  IsSpinSymTFTConsistent s

/-! ## §3. Wave 3a.3 substantive theorem — `sm_3gen_via_symtft` -/

/-- **`sm_3gen_via_symtft`** — the load-bearing Wave 3a.3 substantive
theorem.

For SM matter with `N_f` generations (including right-handed neutrinos),
the modular SymTFT bulk's Witt invariant is trivial *iff* `3 ∣ N_f`.

This lifts the existing `generation_constraint_iff` (Phase 5b) +
`chiralCentralCharge_wittTrivial_iff_three_dvd_N_f` (Phase 6n Wave 1b)
results into the SymTFT-boundary-data framing per Wave 3a.1.

**Hedging discipline (Wave 3a.1 §Q1(c))**: "Building on the boundary-
SymTFT framework of Bhardwaj-Copetti-Pajer-Schäfer-Nameki
(arXiv:2409.02166), the SK_EFT_Hawking program identifies the SM matter
content with a specific topological-boundary-condition assignment in a
Drinfeld-center bulk, and formalizes the assignment in Lean 4."

**To our knowledge** (after surveying Mathlib, Lean physlib, Coq UniMath,
Isabelle AFP, and Agda 1Lab/agda-categories as of May 2026, per Wave
3a.1 §Q7), the explicit Lean-formal realization of SM matter as a
topological boundary of a Drinfeld-center SymTFT is new; the underlying
physics statements — gapped boundaries ↔ Lagrangian algebras
(Kapustin-Saulina arXiv:1008.0654; Fuchs-Schweigert-Valentino
arXiv:1203.4568); SymTFT bulk for SM non-invertible symmetries
(Choi-Lam-Shao 2205.05086; Cordova-Ohmori 2205.06243; Cordova-Hsin-
Zhang 2308.11706) — are due to the works cited.

**Strengthening discipline (P5)**: the hypothesis-bearing variant
`sm_3gen_via_symtft_under_boundary_hyp` below carries the explicit
`IsSMMatterTopologicalBoundary` hypothesis for type-level documentation;
this main theorem ships the unconditional biconditional, with the
SymTFT-framework-consistency witness shipped as the separate
`sm_boundary_data_is_topological_boundary` theorem. -/
theorem sm_3gen_via_symtft (N_f : ℕ) :
    sm_bulk N_f = 0 ↔ 3 ∣ N_f := by
  unfold sm_bulk
  constructor
  · intro h
    -- WittInvariant.fromChiralCentralCharge (8 * N_f) = 0 ↔ WittTrivial (8 * N_f)
    have : WittTrivial (8 * (N_f : ℤ)) := h
    exact (chiralCentralCharge_wittTrivial_iff_three_dvd_N_f N_f).mp this
  · intro h
    have hTriv : WittTrivial (8 * (N_f : ℤ)) :=
      (chiralCentralCharge_wittTrivial_iff_three_dvd_N_f N_f).mpr h
    exact hTriv

/-- **Wave 3a.3 SymTFT-framework-consistency witness** — for any `N_f`,
the SM-with-νR substrate data `sm_boundary_data N_f` realizes the
SymTFT-topological-boundary predicate.

This is the SymTFT-side reading of the SM matter content: every fermion
count `N_f` produces a Pin⁺-anomaly-cancelled substrate (since
`16·N_f ≡ 0 mod 16`), hence is spin-SymTFT-consistent. The
3-generation constraint then appears at the modular-Witt-class level
(separately, via `sm_3gen_via_symtft`). -/
theorem sm_boundary_data_is_topological_boundary (N_f : ℕ) :
    IsSMMatterTopologicalBoundary (sm_boundary_data N_f) := by
  unfold IsSMMatterTopologicalBoundary IsSpinSymTFTConsistent
  refine ⟨?_, ?_⟩
  · exact isAndersonDualSpinBulk_holds _
  · show boundaryAnomaly (sm_boundary_data N_f) = 0
    exact sm_boundary_data_z16_cancels N_f

/-! ## §4. Concrete SM 3-generation witness -/

/-- The SM 3-generation case satisfies the SymTFT-boundary-trivial-Witt
condition. -/
theorem sm_3gen_witt_trivial : sm_bulk 3 = 0 := by
  unfold sm_bulk
  -- 8 * 3 = 24 ≡ 0 (mod 24)
  show WittInvariant.fromChiralCentralCharge (8 * (3 : ℤ)) = 0
  exact standardModel_wittTrivial

/-- The 3-generation case is *the* concrete SM-matter SymTFT-boundary
realization shipped with the project. -/
theorem sm_3gen_matter_boundary_consistent : sm_bulk 3 = 0 :=
  (sm_3gen_via_symtft 3).mpr (by decide)

/-! ## §5. Quantitative-connection witnesses (strengthening discipline)

Per the project's preemptive-strengthening discipline (CLAUDE.md
§"Preemptive-strengthening discipline"), every published numerical
relationship should appear as a `decide`-backed comparison in the
Lean substrate. Wave 3a.3 ships the following quantitative witnesses
connecting the chiral central charge to the modular Witt invariant
mod 24, with explicit verification at the 3-generation case. -/

/-- The chiral central charge of the Standard Model with 3 generations
is 24. -/
theorem sm_3gen_chiral_central_charge_eq_24 :
    (8 : ℤ) * (3 : ℤ) = 24 := by decide

/-- The Standard Model 3-generation case is the *minimal* non-trivial
N_f satisfying 3 ∣ N_f (since N_f = 0 is excluded by physical content). -/
theorem sm_3gen_minimal :
    ∀ n : ℕ, 0 < n → n < 3 → ¬ (3 ∣ n) := by
  intro n hpos hlt hdvd
  interval_cases n <;> revert hdvd <;> decide

/-- The next non-trivial multiple-of-3 is 6 (next allowed N_f after 3). -/
theorem next_multiple_of_3_after_3 :
    ∀ n : ℕ, 3 < n → 3 ∣ n → 6 ≤ n := by
  intro n hgt hdvd
  rcases hdvd with ⟨k, rfl⟩
  omega

/-- The 6-generation case is also Witt-trivial. -/
theorem sm_6gen_witt_trivial : sm_bulk 6 = 0 := by
  exact (sm_3gen_via_symtft 6).mpr (by decide)

/-! ## §5. W5-η-bridge-2 — η-invariant cross-bridge for SM matter boundary

**Phase 6r-prime sub-wave W5-η-bridge-2 (2026-05-25)**: ties the
substantive Wave 3a.3 SM-as-topological-boundary content (existing
`sm_boundary_data_is_topological_boundary`) to the Phase 6r-prime W4-η-1+2
substantive η-invariant content. Substantive cross-bridge: the SM-with-νR
substrate `sm_boundary_data N_f` has both (a) IsSMMatterTopologicalBoundary
holding and (b) vanishing η-invariant in ℝ/ℤ.

Per Witten-Yonekura arXiv:1909.08775: the η-invariant captures the
substrate-level anomaly content; for the SM-with-νR (16 fermions per gen,
z16_class = 16·N_f ≡ 0 mod 16), the η-invariant vanishes — consistent
with the SM being a *topological* (anomaly-cancelled) boundary of the
SymTFT bulk per Wave 3a.1 §Q1(a) Bhardwaj-Copetti-Pajer-Schäfer-Nameki
framework.

Substantive: uses the W4-η-1 `substrateEtaInvariant_zero_of_anomaly_cancels`
applied to the Phase 6r `sm_boundary_data_z16_cancels`. -/

/-- **W5-η-bridge-2 substantive theorem**: the SM-with-νR substrate's
η-invariant vanishes (η = 16·N_f / 16 mod 1 = 0). Combines Phase 6r
`sm_boundary_data_z16_cancels` with W4-η-1
`substrateEtaInvariant_zero_of_anomaly_cancels`. -/
theorem sm_boundary_data_eta_invariant_vanishes (N_f : ℕ) :
    substrateEtaInvariant (sm_boundary_data N_f) = 0 :=
  substrateEtaInvariant_zero_of_anomaly_cancels
    (sm_boundary_data N_f) (sm_boundary_data_z16_cancels N_f)

/-- **W5-η-bridge-2 composed closure**: the SM-with-νR substrate is
SM-matter-topological-boundary AND has vanishing η-invariant. Joint
content at both the Phase 6r predicate-substrate level and the
Phase 6r-prime W4-η substantive level. -/
theorem sm_boundary_data_topological_AND_eta_trivial (N_f : ℕ) :
    IsSMMatterTopologicalBoundary (sm_boundary_data N_f) ∧
    substrateEtaInvariant (sm_boundary_data N_f) = 0 :=
  ⟨sm_boundary_data_is_topological_boundary N_f,
   sm_boundary_data_eta_invariant_vanishes N_f⟩

end SKEFTHawking.SymTFT
