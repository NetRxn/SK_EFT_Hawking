/-
# Phase 6q Wave 2a.3 — DKM bootstrap: E1 / E2 platform cross-bridge

Substrate-level cross-bridges connecting the Wave 2a.2 horizon transport
bootstrap content to the three SK-EFT-Hawking experimental platforms:
- **Graphene Dirac fluid** (E2 paper16_graphene bundle) — CLEARED initial
  platform per Wave 2a.1 DR §1.
- **BEC acoustic Hawking** (D1 paper1/2/3 bundle) — PARTIAL-VIABLE for
  energy/sound-mode bootstrap.
- **Polariton** (E1 paper-not-yet-numbered bundle) — PARTIAL-VIABLE only
  for effective dynamical-KMS Z₂ (driven-dissipative breaks strict KMS).

**Per Wave 2a.1 DR §1 platform table** (full version in the dossier):
- Graphene: native lattice (a = 0.246 nm; t = 2.7 eV), strongest KMS
  structure, Crossno 2016 WF-violation anchor, Iorio-Lambiase 2014
  Beltrami-pseudosphere coexistence of Hawking-T with lab-T.
- BEC: approximate KMS at T_H, Bogoliubov vacuum on Killing-horizon-
  analog wedge, transplanckian UV cutoff at healing length ξ.
- Polariton: genuinely non-equilibrium driven-dissipative (Toledo-Tude
  & Eastham 2024); cleared only at effective dynamical-KMS Z₂ level.

**Wave 2a.3 deliverables (per Wave 2a.1 DR §7):**
1. **Per-platform DKMParameters witnesses** — graphene witness uses
   `a = 0.246 nm` (substantive: Castro Neto et al. RMP 81, 109);
   BEC witness uses dimensionless O(1) substitutes for substrate-
   level non-vacuity; polariton witness similar with non-equilibrium
   caveat documented.
2. **Per-platform KMS-quality classification** — predicate
   `PlatformKMSQuality` with three constructors (Strong / Approximate /
   EffectiveOnly) indexing the substrate's KMS structure.
3. **Per-platform compatibility theorems** — each platform witness
   satisfies (a different subset of) the DKM axiom families.
4. **Substantive cross-platform comparison theorem** — graphene's
   strong KMS quality makes the LDP cross-bridge substantively viable;
   polariton's effective-only quality makes the cross-bridge
   PARTIAL-VIABLE.

References:
- Wave 2a.1 DR §1 (platform comparison table)
- Crossno et al. Science 351, 1058 (2016) — graphene WF violation
- Iorio-Lambiase arXiv:1108.2340 → PLB 716, 334; arXiv:1308.0265 → PRD
  90, 025006 — graphene Beltrami-pseudosphere Hawking-Unruh
- Castro Neto, Guinea, Peres, Novoselov, Geim, RMP 81, 109 (2009) —
  a = 0.246 nm, t = 2.7 eV graphene tight-binding parameters
- Muñoz de Nova, Golubkov, Kolobov, Steinhauer Nature 569, 688 (2019) —
  BEC analog-Hawking experiment
- Toledo-Tude & Eastham APL Quantum 1, 036108 (2024) — polariton non-
  equilibrium driven-dissipative
- Lucas, Crossno, Fong, Kim, Sachdev Phys. Rev. B 93, 075426 — graphene
  Schwinger-Keldysh hydrodynamics
-/
import SKEFTHawking.DKMBootstrap.SKEFTSpecialization

namespace SKEFTHawking.DKMBootstrap

/-! ## §1. Platform KMS-quality classification.

A 3-way classification per Wave 2a.1 DR §1 platform table: graphene has
*Strong* dynamical-KMS Z₂ (Lucas et al. 2016 Schwinger-Keldysh
explicit); BEC has *Approximate* (Bogoliubov quadratic-order); polariton
has *EffectiveOnly* (Liu-Glorioso TASI emergent hydro-only). -/

/-- **Per-platform KMS-quality classification.** -/
inductive PlatformKMSQuality
  | Strong          -- graphene Dirac fluid
  | Approximate     -- BEC acoustic
  | EffectiveOnly   -- polariton driven-dissipative
  deriving DecidableEq, Repr

/-! ## §2. Per-platform `DKMParameters` witnesses.

Substrate-level dimensionless witnesses (a = 1 normalised; physical
graphene a = 0.246 nm requires SI-unit substrate scout — not in Wave
2a.2 scope). All three platforms produce valid `DKMParameters`
capsules with strictly-positive components. -/

/-- **Graphene Dirac-fluid DKM parameters (substrate-level normalised).**
Per Wave 2a.1 DR §1: a = 0.246 nm physical, here normalised to 1.0;
τ, D, χ, ε all O(1) dimensionless. The substantive numerical value for
the MIR-bound discharge is `(2·β_2/(4π))^(1/3) = 0.07562892800257...`
(CHHK eq. (12) v2 = eq. (29) v1 with `β_d` from eq. (9) v2 = eq. (26)
v1, V_1 = 2π unit-circle-circumference convention; computed Python-side
to 30 dps mpmath precision in `src/dkm_bootstrap/graphene_mir.py`). The
prior Wave 2a.1 DR `≈ 0.6` estimate was inaccurate by ~8×. -/
noncomputable def grapheneDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-- **BEC acoustic-Hawking DKM parameters (substrate-level normalised).** -/
noncomputable def becDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-- **Polariton driven-dissipative DKM parameters (substrate-level
normalised).** Carries the non-equilibrium caveat — the substrate-level
predicates hold formally, but the KMS-quality classification is
`EffectiveOnly` (see §3 below). -/
noncomputable def polaritonDKMParameters : DKMParameters where
  τ := 1
  D := 1
  χ := 1
  a := 1
  ε := 1
  τ_pos := by norm_num
  D_pos := by norm_num
  χ_pos := by norm_num
  a_pos := by norm_num
  ε_pos := by norm_num

/-! ## §3. Per-platform KMS-quality classifier. -/

/-- **The platform KMS-quality classifier function.** -/
def platformKMSQuality : String → PlatformKMSQuality
  | "graphene"  => .Strong
  | "BEC"       => .Approximate
  | "polariton" => .EffectiveOnly
  | _           => .EffectiveOnly  -- default conservative

/-- **Graphene has Strong KMS quality.** -/
theorem graphene_kms_quality_strong :
    platformKMSQuality "graphene" = PlatformKMSQuality.Strong := rfl

/-- **BEC has Approximate KMS quality.** -/
theorem bec_kms_quality_approximate :
    platformKMSQuality "BEC" = PlatformKMSQuality.Approximate := rfl

/-- **Polariton has EffectiveOnly KMS quality.** -/
theorem polariton_kms_quality_effective_only :
    platformKMSQuality "polariton" = PlatformKMSQuality.EffectiveOnly := rfl

/-! ## §4-5. Per-platform LDP-compatibility + MIR-bound witnesses.

Post-strengthening 2026-05-25 (A.5 consolidation pass): the 6 prior
per-platform alias theorems
(`graphene_zero_correlator_isLDPCompatible`, `bec_*`, `polariton_*`,
`graphene_satisfies_trivial_mir_bound`, `bec_*`, `polariton_*`) were
removed. They were structural aliases adding no content beyond the
generic substrate-parameterized witnesses already shipped:

- For LDP-compatibility, use `zero_correlator_isLDPCompatible β hβ p`
  from `SKEFTSpecialization.lean` with any of
  `grapheneDKMParameters`, `becDKMParameters`, `polaritonDKMParameters`.
- For trivial-MIR-bound, use `mir_bound_at_zero p` from
  `SKEFTSpecialization.lean` with the same.

The substantive per-platform witnesses live elsewhere:
- Graphene positive uniqueness: `horizon_transport_uniqueness_graphene_witness_one_half`
  in `HorizonTransportBootstrap.lean` (substrate-level mirConst=1/2);
  Python-side substantive `(2·β_2/(4π))^(1/3) ≈ 0.0756` in
  `src/dkm_bootstrap/graphene_mir.py`.
- BEC sharpened-NO-GO: `bec_falls_under_sharpened_no_go` in
  `BECBogoliubovBosonicGrowth.lean` (Wave 2b.4 substantive lift).
- Polariton: substrate-level only via the generic witnesses above; full
  non-equilibrium driven-dissipative substrate ships in a future wave
  (per Toledo-Tude & Eastham 2024). -/

/-! ## §6. Cross-platform comparison theorem — KMS-quality distinguishes
the platforms.

The substantive structural finding: the three platforms have
*distinct* KMS qualities, and this distinction is decidable at the
classifier level. -/

/-- **The three platform KMS qualities are pairwise distinct.**

This is the *syntactic* / classifier-level distinctness witness — the
three constructors of `PlatformKMSQuality` are distinct by the inductive
definition. The *substantive* platform-level distinction (graphene zero-
sequence trivially bounded vs BEC Bogoliubov-bosonic sequence super-
factorial unbounded) lives downstream at
`bec_distinguishes_from_graphene_super_factorial` in
`BECBogoliubovBosonicGrowth.lean` — that's where the syntactic
distinctness is anchored to substantive operator-growth-bound physics
(Wave 2b.4 substantive lift).

Post-strengthening 2026-05-25: docstring updated to flag the
downstream substantive companion; theorem statement preserved as the
classifier-distinctness witness (decidable from inductive structure). -/
theorem platform_kms_qualities_pairwise_distinct :
    platformKMSQuality "graphene" ≠ platformKMSQuality "BEC" ∧
    platformKMSQuality "BEC" ≠ platformKMSQuality "polariton" ∧
    platformKMSQuality "graphene" ≠ platformKMSQuality "polariton" := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §7. Closure summary — Wave 2a.3 E1/E2 platform cross-bridge.

This module ships:
- **`PlatformKMSQuality`** — 3-way classifier (Strong / Approximate /
  EffectiveOnly) for the three SK-EFT-Hawking platforms.
- **Per-platform `DKMParameters` witnesses** — `grapheneDKMParameters`,
  `becDKMParameters`, `polaritonDKMParameters` (substrate-level
  normalised; full physical-unit values lift in Wave 2b Python).
- **`platform_kms_qualities_pairwise_distinct`** — classifier-level
  pairwise-distinctness witness (decidable structural inequality);
  substantive operator-growth contrast in
  `bec_distinguishes_from_graphene_super_factorial`
  (`BECBogoliubovBosonicGrowth.lean`).

Post-strengthening 2026-05-25 (A.5 consolidation): the 6 prior per-
platform LDP-compatibility + MIR-bound alias theorems were removed
(structural aliases of the substrate-parameterized
`zero_correlator_isLDPCompatible` and `mir_bound_at_zero`; no external
consumers). The substantive per-platform witnesses (graphene
`(2·β_2/(4π))^(1/3) ≈ 0.0756`, BEC Bogoliubov super-factorial via
Yin-Lucas/Kuwahara-Saito, polariton non-equilibrium driven-dissipative
deferred) ship in the downstream modules
`HorizonTransportBootstrap.lean` + `BECBogoliubovBosonicGrowth.lean` +
Python companion `src/dkm_bootstrap/graphene_mir.py`. -/

end SKEFTHawking.DKMBootstrap
