# Phase 5x Wave 8 — Dark Sector Synthesis and Cross-Connections

**Wave status:** SHIPPED (2026-04-22 session 4)
**Lean module:** `lean/SKEFTHawking/DarkSectorSynthesis.lean` — 22 theorems, 0 sorry, 0 new axioms, 1 tracked `Prop` hypothesis
**Python module:** `src/dark_sector/synthesis.py`
**Tests:** `tests/test_dark_sector_synthesis.py` — 70 passing
**Gates:** Wave 9 (Paper 17 draft). Wave 5 (SFDM merger numerics) is consumed by Wave 9 in parallel — Wave 8 does not block on it.

---

## 1. Purpose

Waves 2, 2b, 3, 4 and 7 each landed one slice of the Phase 5x "emergent
gravity → dark sector" story. Wave 8 stitches them together. It is a
**synthesis** wave: no new physics, but the cross-sector relationships
(compatibility, distinctness, collective invisibility, ranking) are
made machine-checkable and recorded in one place.

The artifacts are a Lean module carrying the cross-connection theorems,
a Python module carrying the matching numerical constants + a
structured Python assessment, a test file pinning Python ↔ Lean
agreement, and this memo.

Nothing in this wave increases the Phase 5x claim surface. It
**decreases** it by making the connection relationships explicit, so
Paper 17 can cite specific theorems instead of hand-waving.

---

## 2. Inputs (already shipped)

| Wave | Lean module | Key consumed fact |
|---|---|---|
| W2 | `HiddenSectorClassification.lean` | `hidden_sector_anomaly_value` — +3 mod 16 requirement |
| W2b Track X | `HiddenSectorMixedCharge.lean` | `c1_wan_wang_joint_constraint` — mixed-charge cancellation |
| W3 (partial) | `CosmologicalConstant.lean` | `T_dS_double_TGH`, `lambda_magnitude_ratio_exact` |
| W4 | `FangGuTorsionDM.lean` | `fg_cdm_obstruction` — traceless T ⇒ w = 1/3 ⇒ not dust |
| W7 | `FractonDarkMatter.lean` | `fracton_sm_singlet_from_ym_incompat`, `fracton_cosmo_dust_pressureless`, `fracton_bullet_sigma_zero`, `fracton_gravity_attractive`, `fracton_ww_bypass` |

Upstream Phase 5 modules reused transitively: `FractonNonAbelian`
(`ym_compatibility`), `Z16AnomalyComputation`, `SMFermionData`,
`GenerationConstraint`.

---

## 3. Synthesis theorems (DarkSectorSynthesis.lean)

### 3.1 Equation-of-state distinctness across sectors

Three distinct sectors, three pairwise distinct EoS coefficients:

- `w_Λ = -1` (W3 cosmological-constant sector)
- `w_FG = 1/3` (W4 Fang-Gu torsion DM, tree-level kinematic obstruction)
- `w_fracton = 0` (W7 pressureless dust)

Theorems:

- **CC3** `fg_torsion_vs_fracton_dust_eos_distinct` — `1/3 ≠ 0`
- **CC4** `adw_cc_vs_fracton_dm_eos_distinct` — `-1 ≠ 0`
- **CC4'** `adw_cc_vs_fg_torsion_eos_distinct` — `-1 ≠ 1/3`

All three close by `native_decide` over ℚ.

The load-bearing content: no two of the three sectors can be
identified. Paper 17's §3 (CC), §5 (FG short section), §4 (fracton)
map to three disjoint stress-energy components.

### 3.2 Hidden sector × fracton compatibility (CC1)

A ℤ₁₆ hidden-sector singlet candidate carries the bordism charge and
no SM gauge charge. A fracton dark-matter field carries no SM gauge
charge at all (W7). Therefore the two sectors occupy orthogonal charge
labels and can coexist in the full dark-sector spectrum.

Theorem:

- **CC1** `hidden_sector_fracton_compatible` — for any Z16 singlet
  candidate and any fracton gauge type `f`, `ym_compatibility f = false`.

This is the direct composition of W2's singlet cancellation with W7's
fracton YM-singlet theorem. It is the cleanest single-theorem
expression of "emergent gravity DM from different sectors is
structurally compatible."

Witnesses: `s0_cancels` (3 sterile Weyl), `s1_cancels` (19 singlet
Weyl).

### 3.3 Collective invisibility to direct detection (CC2)

Every Phase 5x DM candidate is SM-singlet and below the current
LZ/XENONnT floor:

| Kind | log10(σ_DD, cm²) cap | Source |
|---|---|---|
| `Z16Topological_T0` (K-gauge TQFT) | -999 | no local operators |
| `Z16Singlet_S0` (3 sterile) | -50 | X-ray mixing < 10⁻¹⁰ at 7 keV |
| `Z16Mixed_C1` (Wan-Wang 7+1) | -50 | dark-SU(3) confining |
| `FGTorsion` (e-loops) | -90 | deep research σ~10⁻⁹⁰ cm² |
| `FractonPWave` (p-wave dipole) | -999 | σ_eff = 0 (W7) |

Theorem:

- **CC2** `emergent_gravity_dm_invisible_collective` — for every kind
  `k`, `direct_detection_sigma_log10_cap k ≤ -50`.

This is the formal expression of the Paper 17 thematic claim "every
emergent gravity DM candidate is invisible to nuclear-recoil direct
detection." Decidable over the five-element enum.

### 3.4 Cored-profile mechanism taxonomy (CC5)

Both SFDM and fracton DM produce cored profiles in the central regions
of galactic halos, but through orthogonal physics:

| Mechanism | Physics | Produces core? |
|---|---|---|
| `SolitonCondensate` | SFDM Thomas-Fermi condensate | ✓ |
| `Z4Subdiffusion` | Fracton dipole-conservation subdiffusion | ✓ |
| `NFWPseudoCusp` | Standard CDM | ✗ |

Theorem:

- **CC5** `cored_profile_mechanisms_distinct` —
  `SolitonCondensate ≠ Z4Subdiffusion`.

The distinctness is at the mechanism level: the two models are not
observationally degenerate. Paper 17 §4 discusses the distinguishing
signatures in outer-halo profile shape and in the HSF-driven diversity
prediction (fracton-specific).

### 3.5 Two-torsion-channel independence (CC7)

Torsion `T^μ_{νρ}` decomposes into three Lorentz-irreducible components:
totally antisymmetric (`S^μ = ε^{μνρσ} T_{νρσ}/6`), trace
(`V^μ = T^{νμ}_ν`), and pure tensor (the residual traceless-not-
antisymmetric part).

- Dirac axial current (Boos-Hehl Einstein-Cartan) → antisymmetric
- FG loop θ-term → trace
- NoSource placeholder → pure tensor

Theorems:

- **CC7** `torsion_channels_distinct_sources_distinct` — distinct
  `TorsionSource` values map to distinct `TorsionChannel` values under
  `channel_of_source`.
- **CC7'** `boos_hehl_orthogonal_to_fg_loop` — specialization.
- **`fg_loop_distinct_from_no_source`** — specialization.

The identification step (Dirac axial ↦ antisymmetric; FG loop-θ ↦
trace) is encoded in the definition `channel_of_source`. This is not
a tracked hypothesis but a modelling choice: a Phase 6 memo deriving
the channel assignments from first principles (Dirac-Lagrangian
variation + FG loop-θ variation) would promote these assignments from
definitional to derived. The memo is registered in the Phase 6 deferred
list as `FangGuTraceAnomaly.lean` adjacent work.

### 3.6 ℤ₁₆ × vestigial protection (CC6, hypothesis-parked)

Wave 6 vestigial relics are blocked on W6a (MC extension to L=10,12,16
with Binder cumulants). Wave 8 contributes only the conditional
statement:

If a vestigial relic carries the +3 mod 16 ℤ₁₆ anomaly charge required
by SM anomaly cancellation, then any ℤ₁₆-preserving decay channel
preserves that charge and in particular cannot land the relic in the
vacuum state. The charge assignment itself is parked as a tracked
`Prop` hypothesis `H_VestigialRelicCarriesZ16Charge`, following the
`CenterFunctor.H_CF1` / `HiddenSectorMixedCharge.H_MixedChannelZ16Cancels`
precedent.

Theorems (under the hypothesis):

- **CC6** `z16_vestigial_stability_under_hypothesis` — daughter retains
  +3 mod 16.
- **`z16_vestigial_no_vacuum_decay`** — daughter ≠ 0.

Discharge path (Phase 6):

1. W6a MC extension confirms transition order → determines relic class.
2. W6b Target 1 computes π₀..π₃ of `GL(4,ℝ)/SO(3,1)` — pins down the
   topological defect spectrum.
3. Phase 6 bordism infrastructure upgrades
   `Z16AnomalyComputation.dai_freed_spin_z4` from its existence-
   placeholder to a real homomorphism `Ω₅^{Spin×ℤ₄} → ZMod 16`.
4. A bridge theorem maps the relic's topological charge onto the ℤ₁₆
   bordism invariant under the Dai-Freed pairing.

All four Phase 6.

### 3.7 Candidate viability matrix (Synth2)

Five canonical candidates, one boolean verdict each:

| Candidate | Kind | Verdict | Source |
|---|---|---|---|
| T-0 | `Z16Topological_T0` | viable | W2 + deep research (preferred) |
| S-0 | `Z16Singlet_S0` | viable | W2 `three_singlets_satisfy_hidden_sector` |
| C-1 | `Z16Mixed_C1` | viable | W2b Track X `c1_wan_wang_joint_constraint` |
| FG torsion | `FGTorsion` | **not viable** | W4 `fg_cdm_obstruction` (tree-level) |
| Fracton p-wave @ μ=1 MeV | `FractonPWave` | viable | W7 Drilldown |

Theorem:

- **Synth2** `phase5x_candidates_viability_matrix` — exact 5-tuple
  matching the table, each case discharged by `decide`.

Net count: 4 of 5 basic-viable. FG is the one that fails — and it
fails at the kinematic-EoS level per W4, not at the gauge-consistency
level.

### 3.8 Empirical-hook ranking (Rank1, Rank2)

Five post-W1b+Drilldown empirical hooks, ranked by Phase 5x
detectability and timeline:

1. SFDM cluster-merger sonic boom (W5 pending — Paper 17 money plot)
2. Fracton DM core-cusp resolution (W7 phenomenology)
3. EP violation (STEP-class, Phase 6 vestigial relics)
4. DESI DR3 (2026-2027)
5. Direct nuclear-recoil detection

Theorems:

- **Rank1** `empirical_hook_ranking_strict` — adjacent pairs differ by
  exactly 1 in `hook_priority`.
- **Rank2** `merger_outranks_direct_detection`.
- **`merger_is_top_ranked`** — strict top.

These pin the Paper 17 §9 ranking table to Lean-decidable ground.

---

## 4. Cross-connection matrix

Seven cross-connections are recorded in
`src/dark_sector/synthesis.py::CROSS_CONNECTION_MATRIX`. Six have a
Lean theorem backing; the seventh is memo-only pending W5.

| ID | Waves | Strength | Lean backing |
|---|---|---|---|
| `Z16_x_fracton` | W2 × W7 | Medium | `hidden_sector_fracton_compatible` |
| `Z16_x_vestigial` | W2 × W6 | Medium-High | `z16_vestigial_stability_under_hypothesis` (conditional) |
| `ADW_CC_x_SFDM` | W3 × W5 | Conceptual | memo-only (W5 pending) |
| `FG_x_ADW_vestigial` | W4 × W6 | High | `torsion_channels_distinct_sources_distinct` |
| `SFDM_x_fracton` | W5 × W7 | Medium | `cored_profile_mechanisms_distinct` |
| `EoS_distinctness` | W3 × W4 × W7 | High | `fg_torsion_vs_fracton_dust_eos_distinct` (+CC4, +CC4') |
| `collective_invisibility` | All | Thematic | `emergent_gravity_dm_invisible_collective` |

Every record carries a `summary` prose field used by the memo and
Paper 17.

---

## 5. Empirical prediction ranking (Paper 17 §9)

Five hooks, strict order via `hook_priority`:

| # | Hook | Instrument / timeline | Phase 5x wave |
|---|---|---|---|
| 1 | SFDM cluster-merger sonic boom | Euclid/Roman stacking ≥30 mergers → 3.5-5.7σ; first 3σ ~2028 | W5 (pending numerics) |
| 2 | Fracton DM core-cusp resolution | next-gen dwarf galaxy kinematics | W7 (phenomenology in) |
| 3 | EP violation STEP | η ~ 10⁻¹⁸ | Phase 6 (vestigial relics) |
| 4 | DESI DR3 | 2026-2027 w(z) evolution | W3 |
| 5 | Direct nuclear-recoil | DARWIN | all kinds invisible (CC2) |

The top entry (#1) is the Paper 17 money plot. #5 is the null
prediction: no signal expected by any candidate in our program.

---

## 6. Honesty table

The strongest rhetorical move in Paper 17 is the explicit separation of
derived from heuristic content. Wave 8 codifies it as a per-claim
table:

| Claim | Status | Source |
|---|---|---|
| Every emergent-gravity DM candidate is SM-gauge singlet | DERIVED | CC1, W7 YM incompatibility + W2 singlet cancellation |
| Every emergent-gravity DM candidate is invisible to direct detection | DERIVED (within the stated σ log10 bounds) | CC2 |
| The three Phase 5x stress-energy sectors have distinct EoS | DERIVED | CC3, CC4, CC4' |
| Two-torsion-channel independence | DERIVED (mod channel identification) | CC7 / CC7' |
| SFDM and fracton DM produce cored profiles via distinct mechanisms | DERIVED (at the mechanism-taxonomy level) | CC5 |
| The Paper 17 money plot is the cluster-merger sonic boom | DERIVED (ranking) | Rank1, Rank2 |
| ℤ₁₆ anomaly forces vestigial relics to carry +3 mod 16 | HEURISTIC (Phase 6 conditional) | CC6 (conditional) |
| ADW Volovik Λ magnitude matches observed to ~20% | HEURISTIC (W3 memo) | `adw_predicted_vs_observed_energy_ratio` |
| KV oscillating vacuum is in 2.9-4.4σ tension with DESI DR2 | EMPIRICAL (W1b Task 7) | W3 memo |
| Fracton DM is VIABLE conditional on p-wave phase + Dark QCD UV | HEURISTIC (W7 Drilldown) + EMPIRICAL (BBN) | W7 |
| FG torsion DM is obstructed at the CDM level | DERIVED (tree-level) | W4 `fg_cdm_obstruction` |

---

## 7. What Wave 8 does NOT ship

- **No new figures.** Wave 8 is text + theorems + tests. The Paper 17
  figures come out of W5 (numerics) and W9 (paper draft).
- **No new Python numerics beyond mirroring Lean constants.** The
  synthesis module aggregates, it does not compute.
- **No SFDM merger forecast.** That is W5.
- **No full vestigial relic physics.** Blocked on W6a.
- **No Paper 17 prose draft.** That is W9.

---

## 8. Triggers to update this memo

- **W5 lands** → update `ADW_CC_x_SFDM` backing from memo-only to a
  Lean theorem (expect `sfdm_acoustic_metric`-backed connection).
  Update `SFDM_x_fracton` with quantitative outer-halo profile
  distinction.
- **W6a MC extension completes** → update `Z16_x_vestigial` — move
  the hypothesis to a narrower, conditional statement referencing the
  determined transition order.
- **Phase 6 torsion channel-assignment memo lands** → remove the
  "channel identification is a modelling choice" note from §3.5; cite
  the first-principles derivation.
- **Phase 6 bordism infrastructure lands** (upgrading
  `dai_freed_spin_z4`) → discharge `H_VestigialRelicCarriesZ16Charge`
  or convert to a narrower hypothesis.

---

## 9. References

- `docs/roadmaps/Phase5x_Roadmap.md` — Wave 8 specification
- `docs/roadmaps/Phase6_Deferred_Targets.md` — discharge paths
- `lean/SKEFTHawking/DarkSectorSynthesis.lean` — the theorems
- `src/dark_sector/synthesis.py` — the Python side
- `tests/test_dark_sector_synthesis.py` — cross-checks
- Per-wave memos/modules: `HiddenSectorClassification`,
  `HiddenSectorMixedCharge`, `CosmologicalConstant`, `FangGuTorsionDM`,
  `FractonDarkMatter`, `docs/dark_sector/W4_FangGu_Torsion_DM_Assessment.md`

---

## Appendix A — Theorem roster

22 theorems in `DarkSectorSynthesis.lean`:

**EoS distinctness (3):**
`fg_torsion_vs_fracton_dust_eos_distinct`, `adw_cc_vs_fracton_dm_eos_distinct`,
`adw_cc_vs_fg_torsion_eos_distinct`

**Hidden-sector × fracton (3):**
`hidden_sector_fracton_compatible`, `s0_cancels`, `s1_cancels`

**Collective invisibility (1):**
`emergent_gravity_dm_invisible_collective`

**Cored-profile taxonomy (3):**
`cored_profile_mechanisms_distinct`, `both_cored_mechanisms_produce_cores`,
`nfw_pseudo_cusp_not_cored`

**ℤ₁₆ × vestigial protection (2):**
`z16_vestigial_stability_under_hypothesis`, `z16_vestigial_no_vacuum_decay`

**Torsion-channel independence (3):**
`torsion_channels_distinct_sources_distinct`, `boos_hehl_orthogonal_to_fg_loop`,
`fg_loop_distinct_from_no_source`

**Candidate matrix (2):**
`phase5x_candidates_viability_matrix`, `phase5x_viable_candidate_count`

**Empirical-hook ranking (3):**
`empirical_hook_ranking_strict`, `merger_outranks_direct_detection`,
`merger_is_top_ranked`

**EoS helper (1):**
`eos_fracton_eq_zero`

**Summary marker (1):**
`dark_sector_synthesis_summary`

Also shipped: `EmergentGravityDMKind`, `CoredProfileMechanism`,
`TorsionChannel`, `TorsionSource`, `EmpiricalHook` inductives;
`Z16SingletCandidate`, `VestigialRelic`, `DarkSectorCandidate` structures;
`direct_detection_sigma_log10_cap`, `channel_of_source`, `hook_priority`,
and five canonical `DarkSectorCandidate` witnesses.
