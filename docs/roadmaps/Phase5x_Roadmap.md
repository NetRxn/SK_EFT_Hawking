# Phase 5x: Dark Sector Connections — Dark Matter & Dark Energy from Emergent Gravity

## Technical Roadmap — April 2026 (Updated post-Deep-Research)

*Prepared 2026-04-16 | Updated 2026-04-16 post-deep-research | Updated 2026-07-20 post-Wave-1b | Updated post-Fracton-DM-Kinetic-Stability-Drilldown | Triggered by: brainstorm session identifying 10 concrete-to-speculative connections between the fluid-based physics / SK-EFT-Hawking research program and dark matter (DM) / dark energy (DE). Updated after completion of all 6 Wave 1 deep research tasks and 3 Wave 1b follow-up tasks.*

**Scope:** Investigate how the emergent gravity, anomaly, and dissipative EFT infrastructure developed in Phases 1-5w connects to dark matter and dark energy. Three tracks: (A) anomaly-forced hidden sector + cosmological constant from condensation equilibrium (highest priority — builds on machine-verified theorems), (B) torsion dark matter + vestigial gravity relics (leverages ADW/MC infrastructure), (C) superfluid dark matter + fracton dark matter (new calculation territory, applies SK-EFT framework to DM phenomenology).

**Separate from:**
- Phase 1-4 (BEC-specific pipeline — complete, untouched)
- Phase 5u (paper revisions — content track)
- Phase 5v (knowledge graph / process — infrastructure track)
- Phase 5w (graphene Dirac fluid — analog gravity platform track)
- Phase 5d (ADW/RHMC — numerical gravity track)

**Why a separate phase:** The dark sector is a *distinct physical domain* from the analog gravity experiments (BEC, polariton, graphene) and the formal verification program. However, it connects to the same theoretical infrastructure — ℤ₁₆ anomaly computation, ADW tetrad condensation, vestigial gravity phase structure, SK-EFT dissipative framework, and fracton formalization. The research program has *already* produced results with dark sector implications (hidden_sector_required theorem, Volovik CC mechanism, Fang-Gu torsion DM reference) — Phase 5x systematically develops these connections.

**Strategic motivation:** The program's strongest results (3066+ Lean theorems, 0 sorry, 141 modules) are in formal verification of EFT structures. If any of these structures directly constrain dark sector phenomenology, the formal verification becomes uniquely valuable — no other DM/DE research program has machine-verified theoretical constraints. The ℤ₁₆ hidden sector constraint is the clearest example: a Lean-verified theorem that forces specific dark sector fermion content.

---

## Deep Research Key Findings Summary

> All 6 deep research tasks (Wave 1) and 3 follow-up tasks (Wave 1b) are **COMPLETE**. Results are in `Lit-Search/Phase-5x/`. The following key findings reshape the wave structure, deliverables, and priorities. **Wave 1b updates are marked with ⚡W1b.**

### Finding 1: Wang's Topological Order (T-0) Is the Preferred Hidden Sector
The ℤ₁₆ anomaly admits multiple solutions, but Wang's Ultra Unification identifies a **K-gauge TQFT with zero particle content** (solution T-0) as physically preferred when ν_R is absent. This means the hidden sector is a gapped anyon system — completely invisible to LZ, XENONnT, and all planned direct detection. The minimal *particle* solution is S-0 (3 sterile neutrinos). There are 24,576 total deformation classes of the SM. 7 near-term Lean theorems (T1-T3, T8, T10-T12) are achievable with existing Mathlib.
- **Source:** `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md`

### Finding 2: Volovik CC Mechanism Naturally Produces ρ_Λ ~ T⁴ ~ (meV)⁴ ⚡W1b: KV Level D Tension with DESI
The tetrad-determinant equilibrium gives Λ=0 exactly in perfect Minkowski vacuum. Perturbation by thermal matter yields residual ρ_vac ~ T⁴ — **tantalizingly close to the observed (2.3 meV)⁴**. The mechanism is heuristic (not a theorem), but the coincidence-problem resolution is structural. T_dS = H/π (twice Gibbons-Hawking) from modified spatial translations. ~~DESI DR2 2.8-4.2σ preference for evolving DE is marginally compatible with Klinkhamer-Volovik oscillating vacuum.~~
- ⚡**W1b CORRECTION (Level D tension):** KV oscillating vacuum predicts (w₀, wₐ) = (-1, 0) for the current epoch. DESI DR2 excludes this at **2.9σ (Pantheon+) to 4.4σ (DESY5)**. KV oscillations are Planck-scale (~10⁻⁴⁴ s), NOT cosmological — w_eff = 0 during oscillation (CDM-like), not phantom-crossing. RVM (Solà Peracaula) with ν~10⁻³ accommodates DESI but Volovik-motivated ν~10⁻¹²² is 10⁸² too small. **Strongest surviving empirical hook:** Λ magnitude prediction ρ_vac ~ (2.8 meV)⁴ vs observed (2.3 meV)⁴ (~20% accuracy). QCD topological DE (Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182) with 0 free parameters and phantom crossing is the strongest DESI-compatible bridge from the KV framework. **Paper 17 reframe: withdraw "KV explains DESI"; keep "KV predicts Λ magnitude"; add "ADW motivates exploring beyond frozen plateau."** Falsifiable: DESI DR3 (2026-2027) decisive.
- **Source (W1):** `Lit-Search/Phase-5x/ADW Emergent Gravity and the Cosmological Constant  Dark Energy from Condensation Equilibrium.md`
- **Source (W1b):** `Lit-Search/Phase-5x/5x-Klinkhamer-Volovik Oscillating Vacuum vs. DESI DR2  Quantitative w₀-wₐ Assessment.md`

### Finding 3: Fang-Gu Torsion DM Has σ ~ 10⁻⁹⁰ cm² (Completely Invisible)
FG e-loops source torsion but not Ricci curvature (traceless T^μν → R=0). Cross-section with nucleons is purely gravitational (~10⁻⁹⁰ cm²). Mass is **parametrically undetermined** without microscopic loop condensation model — this is a BLOCKER for quantitative predictions. Two independent torsion channels coexist in ADW+FG: fermion-sourced (Boos-Hehl) and loop-sourced (Fang-Gu). ADW structural compatibility is excellent.
- **Source:** `Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md`

### Finding 4: SFDM Hawking Temperature Is Completely Unobservable → Redirect to MOND Corrections ⚡W1b: Merger Forecast = CONDITIONAL GO
T_H for all SFDM astrophysical scenarios is 10⁻²³ to 10⁻²⁹ K. The **primary scientific payoff** is NOT the Hawking temperature but: (1) dissipative corrections to MOND force law, (2) FDR noise floor as irreducible scatter in RAR (~10⁻⁵-10⁻³), (3) sonic boom phenomenology in cluster mergers (detectable NOW via Euclid/Roman weak lensing), (4) backreaction driving core-cusp flattening. Full SK-EFT ↔ SFDM parameter mapping exists. 6 new Lean theorems (2 easy, 2 medium, 2 hard).
- ⚡**W1b QUANTITATIVE MERGER FORECAST (Conditional GO):** BK fiducial (m=0.6 eV, Λ=0.2 meV) → c_s=1,525 km/s at 10¹⁴ M☉. All 5 canonical mergers supersonic: Bullet M=1.77, Pandora M=2.23, A520 M=1.51, El Gordo M=1.64, MACS J0025 M=1.31. R-H density jump ~49% (corrected for condensate fraction). Single-merger S/N 0.3–1.0; stacking ≥30 mergers → 3.5–5.7σ (Euclid/Roman). First 3σ by ~2028. **Gap confirmed: BK 2025 Physics Reports (arXiv:2505.23900, 118 pages) has NO quantitative merger forecast — Paper 17 fills this gap.** Smoking gun: velocity-threshold step function at M=1 (SFDM-unique). Condensate fraction complication: 10¹⁵ M☉ clusters 0% superfluid; 10¹³ M☉ groups 96% — group-cluster mergers may be better targets. Abell 520 dark core (Jee+2012, >10σ, M/L=588) is contested but potentially SFDM signal. El Gordo cleanest SIDM discriminant. SK-EFT shock width Δr ~ (η/ρ)/(c_s(M²-1)) is unique program contribution. Recommended Paper 17 “money plot”: two-panel figure — DM-galaxy offset vs v/c_s (step function) + stacked κ profile.
- **Source (W1):** `Lit-Search/Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md`
- **Source (W1b):** `Lit-Search/Phase-5x/5x-SFDM Cluster Merger Sonic Boom  Observational Forecast for Euclid Roman.md`
- ⚡**H₀ Tension Assessment (April 2026):** H0DN Collaboration H₀ = 73.50 ± 0.81 (>5σ vs Planck). **Impact on merger forecast: verdict unchanged.** Σ_cr shifts ~8% higher at H₀ = 73.5 → S/N estimates drop ~4% → well within dominant Λ uncertainty. BK-Wang (2017) phonon-mediated late-time acceleration provides thematic hook connecting SFDM phonon EFT to H₀ tension. S₈ tension (σ₈ low in WL surveys) slightly benefits shock detection — suppressed κ_cluster makes fractional SFDM perturbation more prominent. EDE resolutions do not modify BK merger predictions (different physics/epoch).

### Finding 5: Fracton DM — Strong Phenomenology, Finite-T Vulnerability Resolved ⚡W1b→Drilldown: VIABLE (Conditional)
Pressureless fractonic dust from relativistic symmetry (arXiv:2503.14496). Core-cusp naturally resolved by z=4 subdiffusion. Bullet Cluster trivially satisfied (σ_eff = 0). HSF explains diversity problem. **CRITICAL VULNERABILITY RESOLVED:** 3D gapped fracton topological order is destroyed at any T > 0 (no-go theorem), BUT the cosmologically relevant phase is the **gapless p-wave dipole superfluid** — thermodynamically stable at all T > 0 in d=3 (Kapustin-Spodyneiko PRB 2022). Dipole SSB throughout entire phase diagram (Jensen-Raz PRL 2024). z=4 subdiffusion survives in p-wave phase (Głódkowski et al. 2024). YM incompatibility from `FractonNonAbelian.lean` proves fracton DM must be SM gauge singlet. 15 new Lean theorems proposed (theorem 13 → 13a-d split).
- ⚡**W1b BBN CONSTRAINT (originally NON-VIABLE, weak form — ⚡superseded by Drilldown):** ~~The Shen et al. 2022 no-go does NOT apply to gapless U(1) phases. BBN is the killer for eV-scale M_d. Arrhenius kinetics require M_d ≳ 10 MeV. Viable window 10 MeV–100 GeV. No UV completion predicts M_d there.~~
- ⚡**Drilldown REVISION (VIABLE, conditional):** Four papers fundamentally change the viability landscape. **(1)** Kapustin-Spodyneiko (PRB 2022): dipole SSB allowed in d≥3 at T>0 — the p-wave dipole superfluid is the stable phase. **(2)** Jensen-Raz (PRL 2024): dipole SSB throughout entire phase diagram — no disordered phase exists. **(3)** Głódkowski et al. (2024): z=4 subdiffusion survives in p-wave phase. **(4)** Feistl-Schraven-Warzel (arXiv:2601.23078, Jan 2026): multipole MW extension confirms dipole SSB allowed in d=3. **Revised BBN constraint:** For gapless p-wave condensate, stability is thermodynamic (not kinetic) — requires μ ≳ T_BBN ~ MeV, not the Arrhenius factor of 100×T_BBN. **Revised viable window: ~1 MeV ≲ M_d ≲ M_Pl (conservatively MeV–TeV, ~6–9 decades).** **Dark QCD UV completion** naturally places M_d ~ Λ_dark ~ MeV–GeV. Theorem 13 → **13a** (dipole SSB permanence, Medium), **13b** (p-wave phase stability, Hard), **13c** (BBN condensate condition, Medium), **13d** (gapped scenario lower bound, Hard). Rename `fracton_3d_kinetic_stability` → `fracton_3d_thermodynamic_stability`.
- **Source (W1):** `Lit-Search/Phase-5x/Fracton Dark Matter  Phenomenological Assessment.md`
- **Source (W1b):** `Lit-Search/Phase-5x/5x-Gapless Fracton Liquid Stability at Finite Temperature  The Kinetic Stability Window for Fracton Dark Matter/Fracton-DM-Thermal-Stability-Assessment.md`
- **Source (Drilldown):** `Lit-Search/Phase-5x/5x-Fracton DM Kinetic Stability  Deep Drilldown on the Viability Verdict/Fracton-DM-Kinetic-Stability-Drilldown.md`

### Finding 6: Vestigial Relics — Coherent but Requires Extended MC as Gate
L=6,8 MC data is **insufficient** to determine transition order (first vs second). Must extend to L=10,12,16 and compute Binder cumulants — this is the **decisive gate** for all downstream relic physics. GUT-scale transition (T_c ~ 10¹⁵ GeV) needed for correct relic abundance via KZ mechanism. EP violation (bosons ≠ fermions) is the unique distinguishing signature — below MICROSCOPE sensitivity but within reach of proposed STEP mission (η ~ 10⁻¹⁸). Homotopy groups of GL(4,ℝ)/SO(3,1) coset determine topological defect spectrum — formalizable in Lean.
- **Source:** `Lit-Search/Phase-5x/Vestigial Gravity Phase Relics as Dark Matter Candidates.md`

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments — especially the **Deep Research Key Findings Summary** above and the **Priority Revision** below
> 3. **Read the completed deep research results** (Wave 1 — COMPLETE). All 6 files in `Lit-Search/Phase-5x/`:
>    - `ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` → Waves 2, 8
>    - `ADW Emergent Gravity and the Cosmological Constant  Dark Energy from Condensation Equilibrium.md` → Waves 3, 8
>    - `Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md` → Waves 4, 8
>    - `SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md` → Waves 5, 8
>    - `Vestigial Gravity Phase Relics as Dark Matter Candidates.md` → Waves 6, 8
>    - `Fracton Dark Matter  Phenomenological Assessment.md` → Waves 7, 8
> 4. **Read existing Lean infrastructure** (see §Existing Program Assets below):
>    - `lean/SKEFTHawking/Z16AnomalyComputation.lean` — `hidden_sector_required`, `three_gen_is_neg3`, `dai_freed_spin_z4` (23 theorems)
>    - `lean/SKEFTHawking/SMFermionData.lean` — `sm_z4_all_odd`, `total_components_with_nu_R` (18 theorems)
>    - `lean/SKEFTHawking/GenerationConstraint.lean` — `generation_mod3_constraint` (4 theorems)
>    - `lean/SKEFTHawking/ADWMechanism.lean` — `critical_coupling_pos`, `vergeles_mode_count`, `zero_C_with_fluct_gives_vestigial` (21 theorems)
>    - `lean/SKEFTHawking/VestigialGravity.lean` — `vestigial_has_metric_no_tetrad`, `ep_violation_in_vestigial`, `phase_hierarchy` (18 theorems)
>    - `lean/SKEFTHawking/FractonGravity.lean` — `bootstrap_gap_order_2`, `dof_mismatch_4d`, `linearized_equivalence` (20 theorems)
>    - `lean/SKEFTHawking/FractonHydro.lean` — `conserved_charges_fracton`, `information_retention_monotone` (17 theorems)
>    - `lean/SKEFTHawking/FractonFormulas.lean` — `dipole_quadratic_dispersion`, `subdiffusive_relaxation` (45 theorems)
>    - `lean/SKEFTHawking/FractonNonAbelian.lean` — `no_fracton_is_ym_compatible`, `obstruction_count` (4 theorems → proves fracton DM must be SM singlet)
>    - `lean/SKEFTHawking/WKBAnalysis.lean` — `turning_point_shift`, `dissipative_occupation_planckian` (17 theorems)
>    - `lean/SKEFTHawking/HawkingUniversality.lean` — `hawking_universality`, `dissipative_correction_existence` (8 theorems)
>    - `lean/SKEFTHawking/SO4Weingarten.lean` — `fundamental_channel_nonneg`, `adjoint_channel_suppressed` (16 theorems)
>    - `src/core/gap_equation.py` — ADW mean-field computation
>    - `src/core/sm_anomaly.py` — anomaly cancellation check, hidden sector analysis
> 5. **Read cross-referenced deep research** (see §Cross-References below)

---

## Existing Program Assets Relevant to Dark Sector

### Machine-Verified Constraints (Lean 4, 0 sorry)

| Module | Theorems | Key Names | Dark Sector Relevance |
|---|---|---|---|
| **Z16AnomalyComputation.lean** | 23 | `hidden_sector_required`, `three_gen_is_neg3`, `dai_freed_spin_z4` | Forces hidden sector with anomaly +3 mod 16 (3 gen, no ν_R). Deep research confirms Wang's T-0 (topological order) is preferred solution. |
| **SMFermionData.lean** | 18 | `sm_z4_all_odd`, `total_components_with_nu_R` | Constrains what hidden sector can couple to; all SM fermions odd under ℤ₄ |
| **GenerationConstraint.lean** | 4 | `generation_mod3_constraint`, `chiral_central_charge_coeff` | N_f ≡ 0 mod 3 independent of ℤ₁₆ (deep research confirms independence: T12) |
| **ADWMechanism.lean** | 21 | `critical_coupling_pos`, `vergeles_mode_count`, `zero_C_with_fluct_gives_vestigial`, `pos_C_gives_full_tetrad` | CC from condensation equilibrium; vestigial phase DM epoch. Deep research: V_eff(C₀) = -Λ⁴/(4e), residual ρ_vac ~ T⁴ ~ (meV)⁴ |
| **VestigialGravity.lean** | 18 | `vestigial_has_metric_no_tetrad`, `ep_violation_in_vestigial`, `phase_hierarchy`, `phase_levels_ordered` | Vestigial relics, DM from phase transitions. Deep research: L=6,8 insufficient — MUST extend MC to L=10,12,16 |
| **FractonGravity.lean** | 20 | `linearized_equivalence`, `bootstrap_gap_order_2`, `dof_mismatch_4d`, `derivative_order_mismatch` | Fracton DM stability. Deep research: `bootstrap_divergence` → mass bounded from below; `DOF_gap` → σ_eff → 0 (Bullet Cluster) |
| **FractonHydro.lean** | 17 | `conserved_charges_fracton`, `fracton_exceeds_standard_3d_order2`, `information_retention_monotone` | Subdiffusion → cored profiles (core-cusp solution); HSF → diversity problem explanation |
| **FractonFormulas.lean** | 45 | `dipole_quadratic_dispersion`, `dipole_k4_damping`, `subdiffusive_relaxation`, `upper_crit_dim` | z=4 subdiffusion exponent; dispersion → fracton density evolution equation |
| **FractonNonAbelian.lean** | 4 | `no_fracton_is_ym_compatible`, `obstruction_count` | **Deep research highlight:** YM incompatibility → fracton DM must be SM gauge singlet (positive DM consequence from negative result) |
| **WKBAnalysis.lean** | 17 | `turning_point_shift`, `dissipative_occupation_planckian`, `bogoliubov_correction_bounded` | SK-EFT δ_diss corrections; deep research: SFDM T_H unobservable → redirect to MOND corrections |
| **HawkingUniversality.lean** | 8 | `hawking_universality`, `dissipative_correction_existence`, `spinSonic_enhancement_exact` | Universality under dissipation; deep research: de Sitter T=H/π test via SK-EFT |
| **WKBConnection.lean** | 18 | `unitarity_deficit_eq_decoherence`, `noise_floor_nonneg` | Decoherence parameter; extends to cosmological horizon decoherence |
| **AcousticMetric.lean** | ~12 | Painlevé-Gullstrand acoustic metric structure | SFDM acoustic metric specialization (Theorem L1 in deep research) |
| **SO4Weingarten.lean** | 16 | `fundamental_channel_nonneg`, `adjoint_channel_suppressed`, `attractive_bond_action_nonpos` | Phase transition order determination (first vs second) — affects KZ relic abundance |

### Numerical Results

| Computation | Result | Dark Sector Relevance | Deep Research Update |
|---|---|---|---|
| Vestigial MC (L=6,8) | Three phases, split transition Δ ≈ 0.63 | Phase transition cosmology | **INSUFFICIENT** — must extend to L=10,12,16 with Binder cumulants to determine transition order |
| Gap equation V_eff(C) | ~ C⁴ ln C | Vacuum energy → CC | C₀ = Λ·e^{-1/4}; V_eff(C₀) = -Λ⁴/(4e) ~ -M_P⁴/10 — Volovik self-tuning absorbs to leave ~T⁴ |
| SM anomaly computation | 45 ≡ 13 ≡ -3 mod 16 | Hidden sector fermion content | Confirmed: 24,576 deformation classes; Class B (n_νR=0, TQFT) is observationally motivated |

### Existing Deep Research References

| File | Connection | Status |
|---|---|---|
| `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` | ℤ₁₆ → hidden sector, Wang Ultra Unification, 24,576 deformation classes, T-0 topological order DM | **COMPLETE** |
| `Lit-Search/Phase-5x/ADW Emergent Gravity and the Cosmological Constant  Dark Energy from Condensation Equilibrium.md` | Volovik CC mechanism, T_dS = H/π, ~~DESI DR2 compatibility~~ ⚡Level D tension, SK-EFT for de Sitter | **COMPLETE** |
| `Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md` | e-loop DM, traceless T^μν, σ~10⁻⁹⁰ cm², two independent torsion channels in ADW+FG | **COMPLETE** |
| `Lit-Search/Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md` | SFDM parameter mapping, T_H unobservable, MOND corrections, FDR noise in RAR, cluster mergers | **COMPLETE** |
| `Lit-Search/Phase-5x/Vestigial Gravity Phase Relics as Dark Matter Candidates.md` | Phase transition order TBD, KZ relic abundance, EP violation, GL(4)/SO(3,1) homotopy, STEP mission | **COMPLETE** |
| `Lit-Search/Phase-5x/Fracton Dark Matter  Phenomenological Assessment.md` | z=4 subdiffusion, core-cusp solved, finite-T no-go, kinetic stability, 14 new Lean theorems | **COMPLETE** |
| `Lit-Search/Phase-5/Emergent gravity from topological order` | Fang-Gu (arXiv:2106.10242): uncondensed loops source torsion, not curvature → DM candidates | Prior |
| `Lit-Search/Phase-3/The ADW mean-field gap equation` | Gap equation, V_eff(C), cosmological constant as lowest-order invariant | Prior |
| `Lit-Search/Phase-5/Vestigial metric susceptibility` | Three-phase structure, Λ_cosm, EP violation in vestigial phase | Prior |
| `Lit-Search/Phase-5b/Bypassing the hydrodynamic wall` | Wang ℤ₁₆ → hidden sector, SMG threshold at 16 Weyl | Prior |
| `docs/Fluid-Based Approach...Consolidated Critical Review v3.md` | §2.2 gravity wall, Volovik CC, Berezhiani-Khoury, overall program assessment | Prior |

---

## Priority Revision Based on Deep Research (⚡Updated post-W1b)

The deep research findings substantially reshape the wave priorities:

1. **Track A confirmed highest priority.** Both ℤ₁₆ (Wave 2) and ADW CC (Wave 3) have concrete, formalizable results with Lean theorem targets identified. Track A alone could yield Paper 17. ⚡W1b: KV empirical hook weakened (Level D tension), but Λ magnitude prediction (~20% accuracy) and QCD topological DE bridge survive.
2. **Wave 5 (SFDM) reframed ⚡AND ELEVATED.** The original goal of computing T_H for galactic sonic horizons is moot — T_H is unobservable (10⁻²³-10⁻²⁹ K). Redirect entirely to: dissipative MOND corrections, FDR noise in RAR scatter, and cluster merger sonic boom phenomenology. ⚡**W1b: Merger forecast now CONDITIONAL GO with quantitative S/N (3.5–5.7σ stacked ≥30). Fills confirmed BK literature gap. Paper 17's "money plot." PROMOTED to co-primary with Track A.**
3. **Wave 6 (Vestigial Relics) BLOCKED by MC extension.** All downstream relic physics depends on determining the transition order. L=10,12,16 MC with Binder cumulants is the gate. Cross-reference Phase 5d (ADW/RHMC) for shared infrastructure.
4. **Wave 7 (Fracton DM) critical vulnerability resolved ⚡Drilldown: UPGRADED to VIABLE (conditional).** 3D gapped fracton topological order destroyed at T > 0, BUT p-wave dipole superfluid is thermodynamically stable at all T > 0 in d=3 (Kapustin-Spodyneiko PRB 2022, Jensen-Raz PRL 2024). ~~⚡W1b: NON-VIABLE (weak form).~~ ⚡**Drilldown: z=4 subdiffusion survives in p-wave phase (Głódkowski et al. 2024). BBN constraint relaxed from Arrhenius M_d ≳ 10 MeV to condensate condition μ ≳ 1 MeV. Dark QCD UV completion naturally places M_d ~ Λ_dark ~ MeV–GeV. Viable window expanded from 4 decades to ~6–9 decades (MeV–TeV, conservatively). Theorem 13 split into 13a-d (+1 net new).**
5. **Wave 4 (Fang-Gu) has limited formalization upside.** Mass parametrically undetermined; only 4 priority gaps identified. Best treated as a shorter assessment wave rather than a full 8-stage pipeline.
6. **NEW: Extend MC computation must be added** as a prerequisite to Wave 6. This can run in parallel with Track A.
7. ⚡**W1b NEW: DESI DR3 (2026-2027) is a decisive external milestone.** If DESI DR3 strengthens away from (-1,0), KV ruled out; if retreats toward (-1,0), KV less excluded. Paper 17 should be structured to accommodate either outcome.

---

## Wave 1 — Deep Research (6 parallel tasks) ✅ COMPLETE

**Goal:** Execute all 6 deep research tasks to establish the literature landscape, identify what's derivable vs speculative, and scope the subsequent waves.

**Status: ALL 6 TASKS COMPLETE.** Results filed in `Lit-Search/Phase-5x/`.

| # | Task File | Result File | Track | Key Outcome |
|---|---|---|---|---|
| 1 | `Tasks/Phase5x_z16_hidden_sector_dark_matter.md` | `Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` | A | T-0 (TQFT) preferred; 7 near-term Lean theorems; 24,576 classes |
| 2 | `Tasks/Phase5x_adw_cosmological_constant_dark_energy.md` | `Phase-5x/ADW Emergent Gravity and the Cosmological Constant  Dark Energy from Condensation Equilibrium.md` | A | ρ_vac ~ T⁴ ~ (meV)⁴; T_dS = H/π; 6 Lean targets; DESI compatible |
| 3 | `Tasks/Phase5x_fang_gu_torsion_dark_matter.md` | `Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md` | B | σ ~ 10⁻⁹⁰ cm²; R=0; mass undetermined; 4 priority gaps |
| 4 | `Tasks/Phase5x_superfluid_dark_matter_sk_eft.md` | `Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md` | C | T_H unobservable → redirect to MOND/FDR; 6 Lean theorems |
| 5 | `Tasks/Phase5x_vestigial_gravity_relics_dark_matter.md` | `Phase-5x/Vestigial Gravity Phase Relics as Dark Matter Candidates.md` | B | MC extension required; EP violation distinguishing; 5 priority questions |
| 6 | `Tasks/Phase5x_fracton_dark_matter_phenomenology.md` | `Phase-5x/Fracton Dark Matter  Phenomenological Assessment.md` | C | Finite-T no-go for 3D gapped; kinetic stability viable; 14 Lean theorems |

---

## Wave 1b — Targeted Follow-Up Deep Research (3 tasks, parallel) ✅ COMPLETE

**Goal:** Address the 3 highest-impact gaps identified by Wave 1 that require additional literature investigation before execution waves begin. These are questions where the first round noted the connection but did not extract numbers.

**Status:** All 3 tasks **COMPLETE** as of 2026-07-20. Results reshape Wave 3 (KV reframe), Wave 5 (merger GO), and Wave 7 (fracton BBN constraint).

| # | Task File | Result File | Feeds | Verdict | Key Outcome |
|---|---|---|---|---|---|
| 7 | `Tasks/Phase5x_klinkhamer_volovik_desi_w0wa.md` | `Phase-5x/5x-Klinkhamer-Volovik Oscillating Vacuum vs. DESI DR2  Quantitative w₀-wₐ Assessment.md` | W3, W9 | **LEVEL D TENSION** | KV predicts (w₀,wₐ)=(-1,0), excluded at 2.9-4.4σ by DESI DR2. No phantom crossing possible. Reframe Paper 17: keep Λ magnitude prediction (~20% accuracy), withdraw DESI compatibility claim. QCD topological DE (Van Waerbeke-Zhitnitsky 2025) is strongest DESI-compatible bridge. |
| 8 | `Tasks/Phase5x_gapless_fracton_finite_T_stability.md` | `Phase-5x/5x-Gapless Fracton Liquid Stability at Finite Temperature  The Kinetic Stability Window for Fracton Dark Matter/Fracton-DM-Thermal-Stability-Assessment.md` | W7 | ~~NON-VIABLE (weak form)~~ **⚡Drilldown: VIABLE (conditional)** | ~~BBN kills eV-scale M_d.~~ Drilldown: p-wave dipole superfluid thermodynamically stable at T>0 in d=3 (Kapustin-Spodyneiko, Jensen-Raz). BBN relaxed to μ ≳ MeV. Dark QCD UV completion viable. Theorem 13 → 13a/13b/13c/13d. |
| 9 | `Tasks/Phase5x_sfdm_cluster_merger_sonic_boom_forecast.md` | `Phase-5x/5x-SFDM Cluster Merger Sonic Boom  Observational Forecast for Euclid Roman.md` | W5, W9 | **CONDITIONAL GO** | Single S/N 0.3–1.0; stacked ≥30 mergers → 3.5–5.7σ. BK has no quantitative forecast (confirmed gap). Smoking gun: velocity-threshold step function at M=1. First 3σ ~2028. |

**Impact on downstream waves:**
- **Wave 3:** KV empirical hook weakened → pivot to Λ magnitude prediction + QCD topological DE bridge
- **Wave 5:** Merger forecast provides Paper 17's "money plot" with concrete stacking strategy
- **Wave 7:** ~~Fracton DM assessment must include M_d > 10 MeV BBN floor.~~ ⚡Drilldown: p-wave dipole superfluid resolves finite-T vulnerability; BBN relaxed to μ ≳ MeV; Dark QCD UV completion viable; verdict upgraded to VIABLE (conditional); theorem 13 → 13a-d split
- **Wave 9:** Paper 17 structure revised — KV claims downgraded, merger forecast elevated, fracton viability narrowed

---

## Track A: Anomaly-Forced Hidden Sector + Cosmological Constant (Critical Path)

### Wave 2 — ℤ₁₆ Hidden Sector DM Candidate Classification [Pipeline: Stages 1-5]

**Goal:** Enumerate all minimal hidden sector fermion representations satisfying +3 mod 16 anomaly. Formalize Wang's key results. Match against known DM candidate profiles.

**Prerequisites:** Wave 1 Task 1 ✅ COMPLETE.

**Deep Research Findings to Incorporate:**

- **T-0 (K-gauge TQFT) is the preferred hidden sector** when ν_R is absent — zero particle content, gapped anyon DM, invisible to LZ/XENONnT/DARWIN. This is the primary candidate.
- **S-0 (3 sterile neutrinos)** is the minimal particle solution. Warm DM at 1-50 keV; constrained by X-ray telescopes (sin²(2θ) < 10⁻¹⁰ at ~7 keV).
- **S-1 (19 singlet Weyl)** compatible with dark QCD (SU(N)_D with 19 quarks).
- **C-1 (7+1 mixed-charge fermions)** compatible with 8-flavor dark SU(3).
- **Mirror matter FAILS** (SM + mirror has index 26 ≡ 10 mod 16 ≠ 0).
- **24,576 deformation classes** of the SM; Class B (n_νR=0) is the observationally motivated starting point.
- **SMG threshold at 16 Weyl** — Hasenfratz-Witzel (Nov 2025) confirms SU(3) N_f=8 has genuine SMG phase in continuum limit.
- **Wang's N_f=3 uniqueness**: combination of topological DM + B+L faithfulness forces N_f=3 families — dark matter as constraint on visible sector.

**Lean Formalization Targets (from deep research §3.1):**

| ID | Theorem | Statement | Difficulty | Deps |
|---|---|---|---|---|
| T1 | `anomaly_index_weyl_singlet` | N SM-singlet Weyl fermions have ℤ₁₆ index = N mod 16 | Easy | Z16AnomalyComputation |
| T2 | `hidden_sector_anomaly_value` | 3-gen SM without ν_R → hidden sector needs +3 mod 16 | Easy | T1, `three_gen_anomaly_without_nuR` |
| T3 | `minimal_singlet_count` | Minimal SM-singlet hidden sector has exactly 3 Weyl fermions | Medium | T1, T2, number theory |
| T8 | `z16_strictly_stronger_z8` | Already verified as `z16_strictly_stronger` | Trivial | Existing |
| T10 | `all_singlet_solutions_bounded` | All SM-singlet solutions with ≤ 32 Weyl satisfying +3 mod 16 are enumerable | Medium | T1, T2, Finset |
| T11 | `z4x_singlet_constraint` | Hidden-sector fields with X ≠ 0 require additional perturbative anomaly cancellation | Medium | SMFermionData |
| T12 | `generation_independent_z16` | ℤ₉ generation constraint is independent of ℤ₁₆ constraint | Medium | GenerationConstraint |

**Deferred (Hard — require axiomatized bordism/η-invariant):**

| ID | Theorem | Difficulty | Note |
|---|---|---|---|
| T4 | `odd_count_no_extension` | Hard | 3 Weyl can't be trivialized by finite-K extension — needs APS η formalism |
| T5 | `tqft_anomaly_match` | Hard | ℤ₂/ℤ₄ gauge TQFT carries +3 mod 16 — TQFT not in Mathlib |
| T6 | `deformation_class_labeling` | Hard | SM class = (N_f, n_νR, p', q) — advanced algebraic topology |
| T7 | `smg_threshold_16_weyl` | Med-Hard | SMG requires fermion count divisible by 16 |
| T9 | `three_gen_uniqueness` | Hard | N_c = N_f = 3 forced by B+L faithfulness + topological DM |

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] `lean/SKEFTHawking/HiddenSectorClassification.lean` — theorems T1, T2, T3, T10, T11, T12 (~7 new theorems, Easy-Medium)
- [ ] `src/dark_sector/z16_hidden_sector.py` — enumerate all solutions ≤ 32 Weyl; compute anomaly index; match to DM types
- [ ] Hidden sector ↔ DM matching matrix (Table from deep research §1.4)
- [ ] Wang deformation class analysis summary (24,576 classes, focusing on Class B)
- [ ] `tests/test_z16_hidden_sector.py` — verify anomaly cancellation for each solution

**Lean infrastructure reuse:** Z16AnomalyComputation (23 direct), SMFermionData (18 direct), GenerationConstraint (4 direct). **Estimated: 7 new theorems (near-term) + 5 deferred.**

---

### Wave 3 — ADW Cosmological Constant & Dark Energy [Pipeline: Stages 1-8] ⚡W1b: KV REFRAMED

**Goal:** Assess the ADW-derived cosmological constant mechanism quantitatively. Formalize the Volovik equilibrium argument and T_dS = H/π. Compute Λ from the gap equation. Map vestigial correlator onto dark energy equation of state. **W1b update:** KV oscillating vacuum empirical hook demoted from "compatible with DESI" to "Level D tension" — Λ magnitude prediction and QCD topological DE bridge are the surviving empirical connections.

**Prerequisites:** Wave 1 Task 2 ✅ COMPLETE. Wave 1b Task 7 ✅ COMPLETE.

**Deep Research Findings to Incorporate:**

- **Volovik mechanism is heuristic, not theorem** — the crucial unproven step is that the UV completion self-tunes e → e_eq without fine-tuning. Central gap in the argument.
- **Residual ρ_vac ~ T⁴ ~ (2.8 meV)⁴** — tantalizingly close to observed (2.3 meV)⁴. Coincidence problem structurally solved: Λ tracks dominant energy density.
- **T_dS = H/π (twice Gibbons-Hawking)** from de Sitter modified spatial translations r → r - e^{Ht}a. Universal across dimensions. The KMS condition at this temperature governs local processes (ionization, proton decay), not horizon radiation.
- ~~**Klinkhamer-Volovik oscillating vacuum**: vacuum energy oscillates at period ~ H₀⁻¹ — effective w varies on cosmological timescales, **compatible with DESI DR2** signal (2.8-4.2σ evolving DE).~~
- ⚡**W1b KV/DESI CORRECTION:** KV oscillating vacuum predicts (w₀,wₐ) = (-1,0) for the current epoch — **excluded at 2.9σ (Pantheon+) to 4.4σ (DESY5)** by DESI DR2. No phantom crossing is possible in KV. The oscillations are Planck-scale (~10⁻⁴⁴ s) with w_eff=0, not cosmological. RVM with Volovik-motivated ν~10⁻¹²² is 10⁸² orders too small for DESI. **Surviving hooks:** (a) Λ magnitude prediction ρ_vac ~ (2.8 meV)⁴ vs (2.3 meV)⁴ (~20% accuracy); (b) QCD topological DE (Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182) — 0 free parameters, phantom crossing, DESI-compatible, strongest bridge from KV framework. Paper 17 recommended claims (from W1b §Block 8): keep "KV predicts Λ magnitude," withdraw "KV explains DESI dynamics," add "ADW motivates exploring beyond frozen plateau." Falsifiable by DESI DR3 (2026-2027).
- **Vladimirov-Diakonov lattice result**: Einstein gravity realized exactly at phase transition critical surface; CC "probably automatically zero" at criticality.
- **SK-EFT for de Sitter is feasible** but requires 3 new ingredients: (1) replace acoustic metric with de Sitter in SK path integral, (2) identify gravitational viscosities as transport coefficients, (3) verify T_dS = 2T_GH from SK doubling of time contour. Stochastic inflation noise kernel (Burgess-Holman-Tasinato) is the closest existing analog to δ_diss.
- **Anderson-Mottola**: de Sitter unstable to particle creation → cosmological analog of our acoustic BH cooling toward extremality.

**Lean Formalization Targets (from deep research §7):**

| ID | Theorem | Statement | Difficulty |
|---|---|---|---|
| T1 | `double_temperature_dS` | T_dS = 2 × T_GH exactly, given modified translation symmetry | Medium (needs de Sitter axioms + KMS condition) |
| T2 | `volovik_equilibrium` | ρ_vac(e_eq) = 0 given δS/δe = 0 in Minkowski vacuum | Medium |
| T3 | `v_eff_critical_point` | C₀ = Λ·e^{-1/4} and V_eff(C₀) = -Λ⁴/(4e) | Easy |
| T4 | `vestigial_ep_violation` | In vestigial phase: bosons follow g_μν geodesics; fermions have no gravitational coupling | Medium-Hard |
| T5 | `holographic_consistency` | S_volume(V_H) = S_horizon(A) in 3+1 de Sitter at T = H/π | Hard |
| T6 | `transition_sequence` | disorder → GR → ECSK is strict hierarchy as symmetry breaking | Hard |

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] `lean/SKEFTHawking/CosmologicalConstant.lean` — T2, T3 (near-term); T1, T4 (medium-term)
- [ ] `src/dark_sector/adw_cosmological_constant.py` — Λ from gap equation equilibrium; w(z) from phase transition parametrization; Klinkhamer-Volovik oscillation model
- [ ] `src/dark_sector/de_sitter_sk_eft.py` — SK-EFT transport coefficients for cosmological horizon; δ_diss mapping to stochastic inflation noise
- [ ] ΛCDM compatibility table (from deep research §4.2 — ADW vs DESI DR2 vs Planck). ⚡**W1b: Must now include KV Level D tension column — ADW plateau gives w=-1 (consistent with Planck), KV oscillations give w_eff=0 (CDM-like, inconsistent with DESI). Add QCD topological DE row as DESI-compatible bridge.**
- [ ] Assessment memo: is the CC problem "solved" or "reframed" by ADW? (Answer from deep research: **reframed** — heuristic argument, not theorem, but quantitatively compelling). ⚡**W1b addendum: honest statement that KV oscillating vacuum does NOT explain DESI DR2, but Λ magnitude prediction stands.**
- [ ] Priority computation: vestigial susceptibility χ_v from gap equation at one loop (feeds Paper 10/11)
- [ ] ⚡**W1b NEW:** Comparative DE model table from W1b §Block 5 — 6 alternative models (pNGB, RVM, QCD topological, Quintom, oscillating w(z)) with DESI compatibility assessment
- [ ] ⚡**W1b NEW:** Revised Paper 17 claims table (from W1b §Block 8) — 5 claims with status (keep/withdraw/add)

**Lean infrastructure reuse:** ADWMechanism (21), VestigialGravity (18), HawkingUniversality (8). **Estimated: 6 new theorems.**

---

## Track B: Torsion DM + Vestigial Relics (Parallel with Track A)

### Wave 4 — Fang-Gu Torsion Dark Matter Assessment [Pipeline: Stages 1-5, shortened]

**Goal:** Document the FG torsion DM phenomenology and ADW compatibility. Identify the 4 priority gaps. This is an **assessment wave** (not full 8-stage pipeline) because the mass is parametrically undetermined — a BLOCKER for quantitative predictions.

**Prerequisites:** Wave 1 Task 3 ✅ COMPLETE.

**Deep Research Findings to Incorporate:**

- **e-loops source torsion, not Ricci curvature**: traceless T^μν → R = 0. The Einstein tensor is G_μν = R_μν (no R/2 correction). Gravitational lensing proceeds normally; modification only in Weyl tensor sector.
- **σ ~ 10⁻⁹⁰ cm²**: purely gravitational coupling. Completely invisible to LZ, XENONnT, CTA, IceCube, Fermi-LAT. No SM gauge vertex.
- **Two independent torsion channels in ADW+FG**: (1) Fermion-sourced torsion (Boos-Hehl 4-fermion contact, standard EC); (2) Loop-sourced torsion (T^a = l_p σ^a, FG-specific). These coexist independently in the tetrad phase.
- **Mass parametrically undetermined**: m_DM ~ (θ/2π) · L/l_p². Without microscopic loop condensation model, no mass prediction possible. This is the fundamental limitation.
- **YM incompatibility (from existing FractonNonAbelian results)** does NOT directly apply to FG e-loops (which are not fractons), but the structural argument that topological objects cannot carry non-abelian gauge charges transfers.
- **Vestigial phase mapping**: FG e-loops exist as topological objects of pre-condensation TQFT; become torsion-sourcing in tetrad phase. The phase hierarchy (disorder → vestigial → tetrad) maps directly.
- **Key distinction from standard EC DM**: In FG, Dirac fermions do NOT source torsion — only e-loops do. This is a radical departure requiring reconciliation with ADW fermionic condensate.

**Priority Gaps (from deep research Assessment Summary):**
1. FG-DM mass distribution and cosmological relic density computation (requires microscopic loop condensation model — currently unavailable)
2. Reconciliation of FG "no torsion from fermions" with standard EC/ADW fermion-torsion coupling
3. Gravitino-pair condensate DM candidates from 2023 supergravity construction (arXiv:2312.17196)
4. EP-violation signature of vestigial-phase DM in precision cosmological observables

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] ADW compatibility assessment memo (from deep research §5 — structurally excellent, but 2 reconciliation questions)
- [ ] Detection signatures table (from deep research §Block 4 — FG-DM vs WIMP vs axion vs sterile ν)
- [ ] `src/dark_sector/torsion_dm.py` — torsion DM cross-sections (gravitational only), R=0 cosmological constraint assessment

**Note:** No Lean formalization targets identified for Wave 4. The FG results are phenomenological assessments, not formalizable theorems given the parametric underdetermination. The two-torsion-channel observation is a conceptual insight, not a computation.

---

### Wave 5 — Superfluid DM with SK-EFT Framework [Pipeline: Stages 1-8] ⚡ REFRAMED ⚡W1b: MERGER CONDITIONAL GO

**Goal:** ~~Map the SK-EFT dissipative framework onto Berezhiani-Khoury superfluid dark matter. Compute analog Hawking temperature for galactic sonic horizons.~~ **REVISED:** Apply SK-EFT framework to compute dissipative corrections to MOND force law, FDR noise floor in RAR scatter, and cluster merger sonic boom dynamics. T_H computation retained for completeness but deprioritized (all values 10⁻²³-10⁻²⁹ K, unobservable). ⚡**W1b: Cluster merger sonic boom now has QUANTITATIVE forecast — Conditional GO for Paper 17's "money plot."**

**Prerequisites:** Wave 1 Task 4 ✅ COMPLETE. Wave 1b Task 9 ✅ COMPLETE.

**Deep Research Findings to Incorporate:**

- **Full SK-EFT ↔ SFDM parameter mapping exists** (deep research §Block 2 table): c_s → √(2Λ(2m)^{3/2}√ρ₀/m), ξ → ℏ/(mc_s), κ → surface gravity of NFW+BH profile, all transport coefficients expressible in terms of (m, Λ, α, ρ₀).
- **T_H completely unobservable**: All astrophysical scenarios give 10⁻²³ to 10⁻²⁹ K. The scientific payoff is NOT Hawking radiation but the dissipative EFT consequences:
  1. **MOND force with FDR noise** (Rank 1 payoff): irreducible scatter in RAR at ~10⁻⁵-10⁻³ level from phonon FDR
  2. **Cluster merger sonic boom** (Rank 1 observable): Landau criterion threshold — subsonic (pass-through) vs supersonic (friction); spatial density wave ~100 kpc scale visible in Euclid/Roman weak lensing
  3. **Backreaction → core-cusp**: Hawking emission extracts energy from condensate, reducing μ and c_s, flattening density profile (acoustic BH extremality direction)
  4. **Two-fluid transport coefficients**: SK-EFT counting formula for superfluid-normal 2-fluid SFDM gives N_coeff = ⌊(N+1)/2⌋ + 1 + N_v
- **SFDM vs Fuzzy DM discriminator**: healing length ξ_SFDM ~ sub-mm vs ξ_FDM ~ 1 kpc — SK-EFT dispersive correction δ_disp ∝ (κξ/c_s)² is negligible for SFDM but O(1) for FDM at galactic scales

**⚡W1b Deep Research Findings — Cluster Merger Sonic Boom Forecast (CONDITIONAL GO):**

- **BK fiducial parameters (m=0.6 eV, Λ=0.2 meV)** → c_s = 1,525 km/s at 10¹⁴ M☉. All 5 canonical mergers supersonic: Bullet M=1.77, Pandora M=2.23, A520 M=1.51, El Gordo M=1.64, MACS J0025 M=1.31.
- **Λ sensitivity:** Λ=0.1 meV → all subsonic (no signal); Λ=0.5 meV → all highly supersonic. Paper 17 must present predictions as function of Λ.
- **Condensate fraction complication:** 10¹⁵ M☉ clusters are 0% superfluid; 10¹⁴ M☉ subclusters 59%; 10¹³ M☉ groups 96%. **Group-cluster mergers may be better targets than cluster-cluster mergers.**
- **R-H density jump:** δρ/ρ₀ ≈ 83% (Bullet, γ=2), corrected to 49% for condensate fraction. κ_shock ≈ 0.004–0.025 (4–25% of cluster κ~0.1). Inverse of baryonic shock signature: **lensing-bright, X-ray dark.**
- **S/N:** Single merger: Bullet 0.83/1.03 (Euclid/Roman); A520 best at 1.00/1.25. **Stacking: ≥30 mergers → 3.5–5.7σ; ≥50 → 4.6–5.7σ.** 3σ threshold: N≈27 (Euclid), N≈19 (Roman). **First 3σ by ~2028, 5σ by 2029–2030.**
- **Gap confirmed:** BK 2025 Physics Reports (arXiv:2505.23900, 118 pages) has **NO quantitative merger forecast** — Paper 17 fills this genuine literature gap.
- **SFDM-unique smoking gun:** Velocity-threshold step function at M=1 — DM-galaxy offset is zero below c_s, jumps discontinuously above. No other DM model produces this.
- **Abell 520 dark core (Jee+2012):** >10σ detection, M/L=588. Contested but potentially SFDM signal — BK (2015) identify it as normal-phase DM decelerated while superfluid cores pass through.
- **El Gordo:** Cleanest SIDM discriminant — SIDM needs σ/m ≈ 4–5 cm²/g (above Bullet upper limit ~1 cm²/g); SFDM has no such tension.
- **SK-EFT unique contribution:** Shock width Δr ~ (η/ρ)/(c_s(M²-1)) from dissipative transport coefficients. Existing `transonic_background.py` adaptable. `AcousticMetric.lean` (12 theorems) applies directly. FDR noise sets theoretical lower bound on shock sharpness.
- **Recommended Paper 17 structure (8 sections from W1b §Block 12):** BK review → R-H analysis → condensate fraction → 5-target forecast → stacking statistics → SIDM/CDM discriminants → SK-EFT shock width → predictions timeline.
- **Money plot:** Two-panel figure — DM-galaxy offset vs v/c_s (step function) + stacked κ profile for N=30/50 mergers.
- ⚡**H₀ Tension Impact (H0DN April 2026: H₀ = 73.50 ± 0.81, >5σ vs Planck):**
  - **Σ_cr = c²D_S/(4πG D_L D_LS):** All angular diameter distances are H₀-dependent. Shifting from Planck H₀=67.4 to H0DN H₀=73.5 increases Σ_cr by ~8% at Bullet Cluster z_L=0.296 → κ_shock estimates ~8% smaller → S/N shifts ~4%. **Not meaningful for go/no-go — well within dominant Λ uncertainty (factor of several).**
  - **BK-Wang 2017 connection:** Berezhiani-Khoury-Wang (2017) proposes DM-baryon phonon-mediated late-time cosmic acceleration — superfluid DM approach to H₀ tension via the same phonon EFT underpinning as the merger sonic boom. As H₀ tension strengthens (>5σ confirmed April 2026), this mechanism becomes more phenomenologically interesting. **Paper 17 introduction hook: one paragraph linking phonon EFT → merger observables → H₀ tension motivation.**
  - **S₈ tension benefit:** If σ₈ genuinely low (as in Euclid/Roman WL surveys), background κ_cluster suppressed ~5–10%, making SFDM shock perturbation fractionally *more* prominent. Minor benefit.
  - **EDE independence:** Early Dark Energy resolutions reduce sound horizon at recombination but do not modify BK merger predictions (different physics, different epoch). BK 2015 explicitly avoided this coupling.
  - **SFDM is NOT an H₀ resolution:** BK SFDM is pressureless on cosmological scales → inherits ΛCDM Hubble tension. The model does not help with H₀.

**Lean Formalization Targets (from deep research §Block 5):**

| ID | Theorem | Difficulty | Note |
|----|---------|-----------|------|
| L1 | `sfdm_acoustic_metric` | Easy | Specialize Painlevé-Gullstrand to BK SFDM with P~ρ³ |
| L2 | `sfdm_hawking_positivity` | Easy | T_H > 0 for transonic flow with correct sign of κ |
| L3 | `sfdm_transport_count` | Medium | 2-fluid coefficient counting with vortex-phonon coupling |
| L4 | `mond_force_derivation` | Hard | Phonon-mediated a_φ = √(a_N a₀) from MOND action in strong-field limit |
| L5 | `fdr_noise_bound_rar` | Hard | FDR stochastic fluctuations ≥ ℏΓ_H/c_s → lower bound on RAR scatter |
| L6 | `sfdm_backreaction_direction` | Medium | Hawking emission drives c_s ↓, horizon outward, profile flattens (extremality direction) |

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] `src/dark_sector/sfdm_sk_eft.py` — **PRIMARY**: dissipative MOND force correction; FDR noise floor in RAR; cluster merger Landau threshold dynamics. **SECONDARY**: T_H for completeness
- [ ] `lean/SKEFTHawking/SFDMAcousticMetric.lean` — theorems L1, L2 (near-term); L3, L6 (medium-term); L4, L5 (hard, stretch)
- [ ] `notebooks/sfdm_parameter_sweep.ipynb` — contour plots: MOND force correction vs (m, Λ, α); RAR scatter vs T_phonon; merger velocity threshold vs halo mass
- [ ] Observable signatures ranked by detectability (from deep research §Block 4):
  - **Rank 1**: Cluster merger sonic boom (DETECTABLE NOW — Euclid/Roman)
  - **Rank 2**: Galaxy rotation curve diversity (CURRENT DATA — but SK-EFT correction ~10⁻³, below precision)
  - **Rank 3**: Gravitational wave from DM phase transitions (FUTURE — h ~ 10⁻³⁰, undetectable)
  - **Rank 4**: CMB spectral distortions (MARGINAL — below PIXIE)
  - **Rank 5**: 21cm (INDIRECT — HERA/SKA, second-order)
- [ ] SFDM vs Fuzzy DM vs SIDM comparison table (from deep research §Block 4 table)
- [ ] ⚡**W1b NEW:** `src/dark_sector/sfdm_merger_forecast.py` — Rankine-Hugoniot jump conditions for SFDM; 5-target S/N table as function of (m, Λ); stacking statistics; condensate fraction model
- [ ] ⚡**W1b NEW:** `notebooks/sfdm_merger_money_plot.ipynb` — two-panel figure: DM-galaxy offset vs v/c_s (step function) + stacked κ profile at N=30/50
- [ ] ⚡**W1b NEW:** El Gordo / A520 / Bullet detailed comparison worksheet (SIDM tension analysis from W1b §Block 9)
- [ ] ⚡**H₀ Tension NEW:** Σ_cr sensitivity table: S/N at Planck H₀=67.4 vs H0DN H₀=73.5 for all 5 canonical targets. Include in Paper 17 §5 systematic error budget. Add BK-Wang (2017) phonon-mediated acceleration as introduction paragraph.

**Lean infrastructure reuse:** WKBConnection (18), WKBAnalysis (17), HawkingUniversality (8), AcousticMetric (~12). **Estimated: 6 new theorems (2 easy, 2 medium, 2 hard).**

**Lean infrastructure reuse:** WKBConnection (17 theorems), HawkingUniversality (9 theorems), AcousticMetric (for SFDM acoustic metric). Estimated ~6-10 new theorems.

---

### Wave 6 — Vestigial Gravity Relics as DM [Pipeline: Stages 1-8] 🚧 BLOCKED by MC Extension

**Goal:** Analyze the vestigial → tetrad phase transition cosmologically. Compute relic abundance from Kibble-Zurek mechanism. Assess EP-violating signatures.

**Prerequisites:** Wave 1 Task 5 ✅ COMPLETE. **GATE: MC extension to L=10,12,16 with Binder cumulants** (see Wave 6a below).

**Deep Research Findings to Incorporate:**

- **L=6,8 MC INSUFFICIENT** to determine transition order. The Δ ≈ 0.63 split could be (a) two second-order transitions, (b) one first-order with volume-split peaks, or (c) crossover. **Binder cumulant analysis at L=10,12,16 is the decisive gate.**
- **GUT-scale transition (T_c ~ 10¹⁵ GeV)** required for correct relic abundance via KZ mechanism. Planck-scale → DM overproduction + domain wall problem.
- **Relic type:** Point-like topological solitons (monopoles, skyrmions from GL(4)/SO(3,1) coset) rather than domain walls. Domain wall route viable only with rapid annihilation mechanism (requires explicit Z₂ breaking at collision interface).
- **Relic mass:** m ~ x_c · T_c ~ 10-50 × T_c ~ 10¹⁶-10¹⁷ GeV (super-heavy, cold).
- **EP violation is the UNIQUE distinguishing signature**: bosons and fermions see different effective metrics. Differential coupling to spin-connection sector.
  - MICROSCOPE: η < 2.7 × 10⁻¹⁵ (2σ) — **below sensitivity** for diffuse relic halo (η_vestigial ~ 10⁻²¹ for ΔG/G ~ 1)
  - Proposed STEP mission: η ~ 10⁻¹⁸ — would probe ΔG/G ~ 10⁻³
- **Homotopy groups of GL(4,ℝ)/SO(3,1)**: determines topological defect spectrum (strings, monopoles, skyrmions). Not yet computed for this specific coset — **natural Lean formalization target** using existing ADWMechanism + SO4Weingarten.
- **ℤ₁₆ cross-connection**: if hidden sector fermions carry Z₁₆ anomaly charges, vestigial relics could be identified with predicted hidden sector particles. The 5:1 DM:baryon ratio is calculable from gap equation parameters + KZ density formula.
- **Isocurvature constraint**: KZ-produced relics are isocurvature by nature — Planck constrains Δ²_I < 0.099. Post-inflation production at T_c ~ 10¹⁵ GeV requires early decoupling.
- **Self-interaction**: σ/m ~ 10⁻⁴⁰ cm²/g for super-heavy point-like relics — far below Bullet Cluster bound. Not constraining.
- **GW signature**: First-order transition at T_c ~ 10¹⁵ GeV → f_peak ~ 10⁵ Hz (MHz range, beyond LIGO/LISA/ET/BBO). Only observable if transition at T_c ~ 10⁸ GeV (LISA band).

#### Wave 6a — MC Extension (PREREQUISITE, parallel with Track A)

**Goal:** Extend vestigial MC to L=10,12,16. Compute Binder cumulants for susceptibility peaks. Determine transition order definitively.

**Deliverables:**
- [ ] MC runs at L=10, 12, 16 (leverage Phase 5d RHMC infrastructure)
- [ ] Binder cumulant analysis: crossing point and finite-size scaling exponents
- [ ] Transition order determination: first-order (peak height ~ V) vs second-order (peak height ~ V^{γ/ν}) vs crossover
- [ ] If first-order: domain wall tension estimate from latent heat
- [ ] If second-order: universality class identification (Ising? XY? New?)

**Note:** This shares infrastructure with Phase 5d (ADW/RHMC). Coordinate to avoid duplication.

#### Wave 6b — Relic Physics (after Wave 6a gate passes)

**Lean Formalization Targets (from deep research §7.2):**

| ID | Target | Statement | Difficulty |
|----|--------|-----------|-----------|
| 1 | `adw_coset_homotopy` | Compute π₀, π₁, π₂, π₃ of GL(4,ℝ)/SO(3,1) | Medium (pure math, existing Lean group theory) |
| 2 | `kz_relic_density` | KZ mechanism density: n_relic ~ (τ_Q/τ₀)^{-dν/(1+zν)} | Medium |
| 3 | `ep_violation_bound` | η_vestigial ≤ (ΔG/G) × f_DM × (ρ_DM/ρ_nuclear) | Easy |
| 4 | `skyrmion_lifetime` | τ ~ 8π M_GUT⁴/m⁵ >> t_Hubble for m < 10 TeV | Easy |
| 5 | `relic_self_int_bound` | σ/m < Bullet Cluster bound for m > 10¹⁵ GeV (trivially satisfied) | Easy |

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] `src/dark_sector/vestigial_relics.py` — relic abundance from KZ mechanism, EP violation parametrization, coset homotopy analysis
- [ ] Phase transition analysis memo: order, universality class, energy scale (depends on Wave 6a)
- [ ] Relic properties table: mass (~10¹⁶-10¹⁷ GeV), topological charge, stability mechanism, EP violation magnitude
- [ ] Comparison to Murayama-Shu topological DM, King et al. QG fermionic DM, dark quark nuggets (from deep research §5.1)
- [ ] ℤ₁₆ ↔ vestigial cross-constraint analysis: can 5:1 DM:baryon ratio emerge from ADW gap parameters?

**Lean infrastructure reuse:** VestigialGravity (18), ADWMechanism (21), SO4Weingarten (16). **Estimated: 5 new theorems.**

---

## Track C: Fracton DM + Extended Phenomenology (SFDM now reframed above)

### Wave 7 — Fracton Dark Matter Phenomenology [Pipeline: Stages 1-8] ⚡W1b→Drilldown: VIABLE (Conditional)

**Goal:** Assess fracton restricted mobility, topological stability, and gravitational attraction as DM properties. Compute density profiles and compare to small-scale structure observations. Address the critical finite-T vulnerability. ~~⚡W1b: NON-VIABLE (weak form).~~ ⚡**Drilldown: VIABLE (conditional). p-wave dipole superfluid (Kapustin-Spodyneiko PRB 2022, Jensen-Raz PRL 2024) is thermodynamically stable at all T > 0 in d=3. BBN constraint relaxed to μ ≳ MeV. Dark QCD UV completion provides natural M_d ~ Λ_dark ~ MeV–GeV. z=4 subdiffusion preserved in p-wave phase (Głódkowski et al. 2024). Viable window expanded to ~MeV–TeV (conservatively 6–9 decades). Theorem 13 → 13a-d split.**

**Prerequisites:** Wave 1 Task 6 ✅ COMPLETE. Wave 1b Task 8 ✅ COMPLETE.

**Deep Research Findings to Incorporate:**

- **Pressureless fractonic dust** from relativistic fracton symmetry on FRW (arXiv:2503.14496) — separately conserved, pressureless. Dust equation of state emerges from symmetry, not assumption.
- **Core-cusp naturally resolved**: z=4 subdiffusion from dipole conservation → 4th-order diffusion equation → flat central density analytically (core predicted, cusp impossible).
- **Bullet Cluster trivially satisfied**: σ_eff = 0 for isolated fracton from dipole conservation + locality. No free parameter.
- **HSF → diversity problem**: Krylov sector memory → exponential number of distinct final profiles at fixed total charge. Explains observed diversity of dwarf galaxy rotation curves without baryonic feedback.
- **CRITICAL VULNERABILITY: 3D gapped fracton topological order DESTROYED at any T > 0** (Shen et al. 2022 no-go theorem). The 4D X-cube model supports finite-T order, but this requires Euclidean interpretation, not cosmological dynamics.
  - **Escape route:** The cosmologically viable DM candidate is a **gapless (U(1)) fracton liquid in 3D** with KINETIC stability: τ ~ τ₀ exp(M_d/T). For M_d ~ eV and T_CMB: τ/τ₀ ~ e^{4000} — spectacularly long. For M_d ~ meV: τ/τ₀ ~ e^{4} — only mildly long. The required M_d is not predicted by the EFT. ⚡**Drilldown: Better escape route identified — p-wave dipole superfluid is THERMODYNAMICALLY stable (not merely kinetically) at all T>0 in d=3. See drilldown findings below.**

**⚡W1b Deep Research Findings — Fracton Finite-T Stability (originally NON-VIABLE, weak form — ⚡superseded by Drilldown below):**

- **Shen et al. 2022 no-go does NOT apply to gapless U(1) phases** — smooth crossover with screening length λ ~ exp(M_d/2T), not sharp destruction.
- **BBN IS THE KILLER for eV-scale M_d:** At T_BBN ≈ 0.1 MeV, M_d/T_BBN ~ 10⁻⁵ for eV-scale M_d → **zero kinetic protection**. The spectacular CMB lifetime (τ/τ₀ ~ e⁴⁰⁰⁰) is meaningless if the phase cannot survive BBN.
- **Arrhenius kinetics:** M_d ≳ 10 MeV required for BBN survival.
- **Haah superexponential (type II):** τ ~ exp(c(M_d/T)²) relaxes constraint to M_d ≳ 1 MeV.
- **Viable window: 10 MeV ≲ M_d ≲ 100 GeV** (4 decades in log-space). All desirable DM signatures (σ_eff=0, z=4 subdiffusion, HSF diversity) are preserved.
- **Fatal weakness (weak-form non-viability):** No known UV completion naturally predicts M_d in this window. The Pretko 2017 gapless U(1) fracton liquid is the only phase with finite-T analysis; 5 other gapless fracton phases surveyed leave finite-T open.
- **Glassy dynamics (Prem-Haah-Nandkishore 2017):** Type I → doubly exponential; type II → superexponential relaxation. Both provide stronger protection than simple Arrhenius.
- **Self-consistent thermal history:** Scenario 1 (M_d ~ 10 MeV, form at T_cond ~ M_d) works; Scenario 3 (M_d ~ eV) fails.
- **N_eff constraint:** Fracton DM is SM-singlet (from FractonNonAbelian.lean) → no direct BBN N_eff constraint.
- **Lean theorem recommendation:** Split `fracton_3d_kinetic_stability` (theorem 13) into: **13a** (no-go exemption for gapless phases, Hard), **13b** (BBN lower bound on M_d, Very Hard — requires thermodynamic axioms), **13c** (Arrhenius/superexponential lifetime bound, Hard).
- **Fracton-GR coupling**: Linearized coupling well-defined (Pretko 2017); nonlinear remains open. Extra gapless modes beyond GR's 2 polarizations. Graviton dispersion: linear ω~k, quadratic ω~k², or cubic ω~k³ (formulation-dependent). Weinberg-Witten circumvented by Lorentz-breaking.
- **YM incompatibility → SM singlet DM**: The 4 obstructions in `FractonNonAbelian.lean` have direct phenomenological consequence: fracton DM carries no SU(3)_c, SU(2)_L charges. Only viable channels: gravitational, dark U(1), or higher-dimensional operators. Deep research notes this is a **strength**: SM-singlet nature derived from Lean-verified consistency theorem, not assumed.
- **Distinguishing signatures vs CDM/SIDM**: Fracton DM is MORE collisionless than CDM but produces CORED profiles — the opposite combination from SIDM. This is unique and testable. Halo anisotropy from Lorentz-breaking framid. Kination fluid secondary component in early universe.
- **BBN constraint**: Kination fluid + fracton dust → μ > few keV bound.

**⚡Drilldown Deep Research Findings — Fracton DM Thermodynamic Stability (VIABLE, conditional):**

> **This section supersedes the W1b NON-VIABLE (weak form) verdict.** See `Lit-Search/Phase-5x/5x-Fracton DM Kinetic Stability  Deep Drilldown on the Viability Verdict/Fracton-DM-Kinetic-Stability-Drilldown.md`.

- **Kapustin-Spodyneiko theorem (PRB 106, 245125, 2022):** Generalized Hohenberg-Mermin-Wagner for dipole symmetry. Dipole SSB allowed for d ≥ 3 at T > 0. Charge SSB forbidden for d ≤ 4. → The stable T > 0 phase in 3D is the **p-wave dipole superfluid** (dipole SSB, charge preserved).
- **Jensen-Raz large-N solution (PRL 2024):** Exact solution at finite T and μ. Dipole SSB throughout entire phase diagram — no disordered (normal) phase exists. p-wave phase: immobile fractons, mobile dipoles — all DM properties preserved.
- **Głódkowski-Peña-Benítez-Surówka (2024):** Full dissipative hydrodynamics of fracton superfluids. p-wave phase retains ω ~ -ik⁴ subdiffusion. z=4 transport survives at finite T — not thermally degraded.
- **Feistl-Schraven-Warzel (arXiv:2601.23078, Jan 2026):** Multipole MW extension confirms Kapustin-Spodyneiko. Higher multipole symmetries protect lower-order ones.
- **Revised stability mechanism:** For gapless p-wave condensate, stability is **thermodynamic** (phase is the equilibrium state at all T > 0 in d=3), not kinetic (no Arrhenius barrier to surmount). The Arrhenius analysis applies only to the gapped scenario.
- **Revised BBN constraint:** Condensate condition μ ≳ T_BBN ~ MeV (factor ~100 weaker than Arrhenius M_d ≳ 10 MeV). No activation barrier argument needed.
- **Dark QCD UV completion:** Dark confinement scale Λ_dark ~ MeV–GeV naturally places M_d in viable range. Fracton-elasticity duality maps dark QCD phase transition to fracton condensation. SU(N_dark) × U(1)_fracton gauge structure compatible with FractonNonAbelian.lean (separate dark gauge group, not coupled to SM SU(3)). Resolves the W1b "no UV completion" problem.
- **Revised viable window:** Gapless p-wave: ~1 MeV ≲ μ ≲ M_Pl (formally ~22 decades; **conservatively MeV–TeV, ~6–9 decades** accounting for production mechanism and N_eff constraints). Gapped Arrhenius: 10 MeV–100 GeV (4 decades, unchanged from W1b).
- **Remaining threats:** (1) Explicit dipole symmetry breaking from gravity — suppressed by (H₀/M_d)² ~ 10⁻⁶⁰, negligible. (2) First-order p-wave→s-wave transition — suppressed to T=0 by Kapustin-Spodyneiko. (3) Stahl-Lake-Nandkishore generalized MW — reconciled: p-wave Goldstone has z=2, not z=4; Kapustin-Spodyneiko Bogoliubov inequality gives d ≤ 2 for dipole SSB prohibition. (4) **Production mechanism — genuinely the top remaining gap** (how does the universe enter the p-wave condensate phase?).
- **Lean formalization update:** Theorem 13 → 13a–d split. Rename from `fracton_3d_kinetic_stability` to `fracton_3d_thermodynamic_stability`. New theorem 13d (gapped scenario lower bound, Hard). Priority: 13a + 13c first (Medium), then 13b (Hard), then 13d (Hard).
- **Verdict: VIABLE (conditional)** on p-wave dipole superfluid being the equilibrium phase with μ ≳ 1 MeV.

**Lean Formalization Targets (from deep research §6, ⚡Drilldown: 15 proposed theorems):**

| ID | Theorem | Statement | Difficulty |
|---|---|---|---|
| 1 | `fracton_subdiffusion_core` | z=4 diffusion → flat central density (core, no cusp) | Medium |
| 2 | `fracton_bullet_sigma_zero` | σ_eff = 0 for isolated fracton from dipole conservation + locality | Easy |
| 3 | `fracton_thermal_lifetime` | τ >> τ₀ exp(M_d/T) for T << M_d | Medium |
| 4 | `fracton_sm_singlet` | From YM incompatibility + gauge structure → no SM coupling | Easy (combines existing results) |
| 5 | `fracton_mach_inertia` | t = αρ_bg with bound on mass vs density scaling | Medium |
| 6 | `fracton_krylov_diversity` | Exponential distinct profiles at fixed charge → diversity | Medium |
| 7 | `fracton_dipole_tidal_resistance` | Dipole conservation → energy cost for tidal stripping | Medium |
| 8 | `fracton_cosmo_dust` | Fractonic symmetry on FRW → pressureless dust (2503.14496) | Medium |
| 9 | `fracton_bbn_constraint` | Kination + fracton dust → μ > few keV | Easy |
| 10 | `fracton_sound_speed_bound` | c_s² << 1 on scales > 100 km | Easy |
| 11 | `fracton_gravity_attractive` | Specialization of Pretko_graviton; halo formation necessary condition | Easy |
| 12 | `fracton_ww_bypass` | Emergent gravity circumvents Weinberg-Witten via Lorentz-breaking | Medium |
| 13 | `fracton_3d_kinetic_stability` | Gapless fracton: topological protection fails → kinetic stability bound | Hard | ⚡W1b: SPLIT → 13a/13b/13c |
| 13a | `fracton_nogo_exemption` | Gapless U(1) fracton liquid exempt from Shen et al. 2022 no-go | Hard |
| 13b | `fracton_bbn_md_lower_bound` | BBN survival requires M_d ≳ 10 MeV (Arrhenius) or M_d ≳ 1 MeV (Haah) | Very Hard |
| 13c | `fracton_lifetime_arrhenius` | τ ≥ τ₀ exp(M_d/T) (Arrhenius) or τ ≥ τ₀ exp(c(M_d/T)²) (superexponential) | Hard |
| 13d | `fracton_bbn_condensate_condition` | ⚡Drilldown: p-wave condensate with μ >> T_BBN survives all cosmic epochs without Arrhenius barrier | Hard |
| 14 | `fracton_nfw_core_comparison` | Formal comparison to NFW/Burkert; core-cusp theorem | Medium |

**Deliverables:**
- [x] Deep research gap analysis (completed)
- [ ] `lean/SKEFTHawking/FractonDarkMatter.lean` — theorems 1-4, 8-11 (near-term, 8 theorems); 5-7, 12, 14 (medium-term, 5 theorems); 13a, 13c (medium); 13b, 13d (hard); ⚡Drilldown: rename module theorem from `fracton_3d_kinetic_stability` to `fracton_3d_thermodynamic_stability`
- [ ] `src/dark_sector/fracton_dm.py` — subdiffusion density profiles, Bullet Cluster constraint (σ=0 automatic), thermal lifetime as function of M_d/T, BBN constraint
- [ ] Small-scale structure predictions: core-cusp resolution, satellite problem, diversity from HSF
- [ ] Density profile comparison: fracton (analytical) vs NFW vs Burkert vs observed (Oman et al. 2015)
- [ ] Finite-T risk assessment: gapless fracton liquid stability window (M_d vs T_CMB parameter space). ⚡**W1b: Now quantitative — viable window is 10 MeV ≲ M_d ≲ 100 GeV, with Arrhenius and Haah superexponential lifetime curves.**
- [ ] Lab analog opportunities table (Adler et al. 2024 Nature — 2D observation of HSF + fractonic excitations)
- [ ] ⚡**W1b NEW:** BBN survival phase diagram: M_d vs T_BBN with Arrhenius/Haah/superexponential contours marking τ > τ_BBN
- [ ] ⚡**W1b NEW → Drilldown RESOLVED:** UV completion survey → **Dark QCD is the preferred UV completion** (Λ_dark ~ MeV–GeV); fracton-elasticity duality maps dark QCD confinement to fracton condensation. Memo: assess SU(N_dark) × U(1)_fracton gauge structure compatibility with FractonNonAbelian.lean

**Lean infrastructure reuse:** FractonGravity (20), FractonHydro (17), FractonFormulas (45), FractonNonAbelian (4). **Estimated: ⚡18 new theorems (14 original + 4 from theorem 13 → 13a-d split, bringing FractonDM.lean to largest module in fracton suite).**

---

### Wave 8 — Synthesis & Cross-Connections [Pipeline: Stages 1-5]

**Goal:** Synthesize results from Waves 2-7. Identify cross-connections. Assess overall dark sector picture. Produce unified ranking.

**Prerequisites:** Waves 2-7 (at least Waves 2-3 + one of Waves 4-7).

**Cross-Connections Identified by Deep Research:**

| Connection | Waves | Deep Research Source | Strength |
|---|---|---|---|
| **ℤ₁₆ × vestigial relics**: hidden sector fermions with Z₁₆ charges → vestigial relics carry discrete topological charge → relic decay forbidden by charge conservation | W2 + W6 | Vestigial §5.2 | Medium-High |
| **ℤ₁₆ × fracton DM**: YM incompatibility (FractonNonAbelian) means fractons cannot carry non-abelian hidden sector charges; T-0 (TQFT) hidden sector is compatible with fracton extended objects | W2 + W7 | ℤ₁₆ §2.1 + Fracton §5.3 | Medium |
| **ADW CC × SFDM**: Volovik residual Λ ~ T⁴ mechanism + SFDM condensate → dark energy and dark matter from same fermionic vacuum substrate | W3 + W5 | ADW §1.2, SFDM §Block 5 | Conceptual (not quantitative) |
| **Fang-Gu × ADW vestigial**: Two independent torsion channels coexist in tetrad phase — both fermion-sourced (Boos-Hehl) and loop-sourced (FG) | W4 + W6 | Fang-Gu §5.3 | High (structural) |
| **SFDM × fracton**: Both produce cored profiles via different mechanisms — SFDM from soliton, fracton from z=4 subdiffusion. Observationally distinguishable by outer halo profile and diversity predictions | W5 + W7 | SFDM §Block 4, Fracton §4 | Medium |
| **5:1 DM:baryon ratio**: Calculable from ADW gap equation + KZ density formula IF vestigial relic mass, transition temperature, and baryon asymmetry are all known | W3 + W6 + W2 | Vestigial §5.2 | High (if parameters known) |
| **All invisible to direct detection**: Wang T-0 (no local operators), FG e-loops (σ~10⁻⁹⁰), fracton DM (σ_eff=0) — consistent picture: emergent gravity DM is fundamentally undetectable by nuclear recoil | All | Multiple | Thematic |

**Key questions for synthesis:**
- Do the 6 DM/DE candidates form a consistent picture, or are they mutually exclusive?
  - Deep research answer: **Mostly consistent.** T-0 (topological), FG (torsion), fracton (subdiffusive), and vestigial (solitonic) are structurally different and could coexist. SFDM is phenomenological (not directly tied to emergent gravity).
- Can the 5:1 DM:baryon ratio be explained by any combination?
  - Deep research answer: **Vestigial relics + ℤ₁₆ cross-constraint is the most promising route** (definite prediction once ADW gap eq parameters known).
- What is the strongest experimentally testable prediction?
  - Deep research ranking (⚡**updated with W1b quantitative results**):
    1. **SFDM cluster merger sonic boom** (detectable NOW with Euclid/Roman) — ⚡W1b: **quantified S/N: stacked ≥30 → 3.5–5.7σ, first 3σ ~2028.** BK has no competing forecast. Paper 17 money plot.
    2. Fracton DM core-cusp resolution (testable with next-gen dwarf galaxy kinematics) — ⚡W1b: survives only if M_d > 10 MeV (BBN floor)
    3. EP violation from vestigial relics (requires STEP mission at η ~ 10⁻¹⁸)
    4. N_eff constraint separating Class A vs B (CMB-S4 at σ(N_eff) ~ 0.03)
    5. ⚡**W1b NEW:** DESI DR3 (2026-2027) — if w₀ strengthens away from -1, KV ruled out decisively; if retreats, KV less excluded
- Which connections survive adversarial scrutiny?
  - **Strongest:** ℤ₁₆ + ADW CC (machine-verified constraints + quantitative coincidence). ⚡W1b: KV w₀-wₐ dynamics demoted to Level D tension, but Λ magnitude prediction survives.
  - **Strong phenomenology, ⚡foundations upgraded:** Fracton DM (no finite-T topological protection in 3D for gapped phases, BUT p-wave dipole superfluid is thermodynamically stable). ~~⚡W1b: NON-VIABLE (weak form).~~ ⚡**Drilldown: VIABLE (conditional)** — p-wave phase resolves finite-T vulnerability; Dark QCD UV completion viable; BBN relaxed to μ ≳ MeV.
  - **Elevated:** SFDM cluster merger — ⚡W1b: Now **strongest empirical prediction** with quantitative forecast and confirmed literature gap.
  - **Coherent but speculative:** Vestigial relics (needs MC extension gate)
  - **Structurally sound, parametrically undetermined:** Fang-Gu torsion DM

**Deliverables:**
- [ ] Synthesis document: unified assessment of all 6 dark sector connections with cross-connection matrix
- [ ] Priority ranking for further development. ⚡**W1b: SFDM merger likely promoted to co-equal with Track A.**
- [ ] Experimental prediction summary table (ranked by detectability and timeline)
- [ ] "Which combinations are consistent?" analysis document

---

### Wave 9 — Paper 17: Dark Sector Connections from Emergent Gravity [Pipeline: Stages 1-12] ⚡W1b: Structure Revised

**Goal:** Draft a paper presenting the dark sector connections. Focus on the strongest, most concrete results (Track A: ℤ₁₆ hidden sector + ADW cosmological constant + fracton DM phenomenology). ⚡**W1b: SFDM cluster merger forecast elevated from "shorter section" to co-primary (fills confirmed BK literature gap with quantitative predictions). KV/DESI section reframed. Fracton M_d window narrowed.**

**Prerequisites:** Waves 2-8 (at minimum: Waves 2-3 + Wave 8 synthesis).

**Paper structure (⚡revised based on W1b outcomes):**
1. Introduction: emergent gravity programs and the dark sector — the unique position of machine-verified constraints. ⚡**H₀ tension hook: BK-Wang (2017) phonon-mediated acceleration connects SFDM phonon EFT to H₀ tension; >5σ (H0DN April 2026) strengthens motivation for phonon-sector observational testing**
2. **Machine-verified anomaly constraints on the hidden sector** (ℤ₁₆): 3 gen → +3 mod 16; minimal solutions (S-0, T-0); Wang T-0 as preferred candidate; 24,576 deformation classes
3. **Cosmological constant from tetrad condensation equilibrium** (ADW): Volovik mechanism; ρ_vac ~ T⁴ ~ (meV)⁴; ~~DESI DR2 compatibility~~ ⚡**honest assessment: Λ magnitude prediction is compelling (~20% accuracy), but KV oscillating vacuum is in Level D tension with DESI DR2 (2.9–4.4σ)**; T_dS = H/π; QCD topological DE as DESI-compatible bridge
4. **Fracton dark matter from machine-verified gauge constraints**: YM incompatibility → SM singlet; z=4 subdiffusion → core-cusp; σ_eff = 0 → Bullet Cluster; ⚡**Drilldown: p-wave dipole superfluid thermodynamically stable in d=3 at T>0 (Kapustin-Spodyneiko, Jensen-Raz); BBN relaxed to μ ≳ MeV; Dark QCD UV completion; VIABLE (conditional)**
5. ⚡**PROMOTED: SFDM cluster merger sonic boom forecast** — Rankine-Hugoniot analysis; 5 canonical targets; stacking strategy for 3–5σ detection; condensate fraction; Euclid/Roman S/N; **Paper 17's "money plot"** (fills confirmed BK literature gap)
6. SK-EFT for superfluid dark matter — dissipative MOND corrections and FDR noise (complementary to §5)
7. Torsion dark matter from topological gravity — ADW compatibility, two torsion channels (shorter section)
8. Speculative connections: vestigial relics, EP violation, ℤ₁₆ × vestigial cross-constraint
9. Experimental tests and observational predictions (ranked table — ⚡W1b: merger #1, DESI DR3 #5 NEW, ⚡H₀ tension: H0DN >5σ strengthens overall Phase 5x motivation)
10. Formal verification summary: which claims are Lean-verified, which are heuristic
11. Discussion and outlook

**Deliverables:**
- [ ] `papers/paper17_dark_sector/paper_draft.tex`
- [ ] All figures via `src/dark_sector/visualizations.py`
- [ ] All claims traced to Lean theorems where applicable
- [ ] Full 12-stage pipeline closure

---

## Dependencies and Sequencing (Updated post-W1b)

```
Wave 1 (6 deep research tasks — parallel) ✅ COMPLETE
  │
  ├──→ Wave 1b (3 follow-up tasks — parallel) ✅ COMPLETE
  │     ├──→ Task 7 (KV w₀-wₐ) ✅ LEVEL D ─→ Wave 3 (KV reframed: Λ magnitude survives, DESI dynamics withdrawn)
  │     ├──→ Task 8 (fracton finite-T) ✅ ~~NON-VIABLE (weak)~~ ⚡VIABLE (conditional) ─→ Wave 7 (p-wave phase stable, μ ≳ MeV, theorem 13→13a-d)
  │     └──→ Task 9 (merger forecast) ✅ CONDITIONAL GO ─→ Wave 5 (money plot confirmed, fills BK gap)
  │
  ├──→ Task 1 ✅──→ Wave 2 (ℤ₁₆ hidden sector) ──────────────────┐
  ├──→ Task 2 ✅──→ Wave 3 (ADW CC/DE — KV reframed) ─────────────┤
  │                                                                 ├──→ Wave 8 (synthesis)
  ├──→ Task 3 ✅──→ Wave 4 (torsion DM — short assessment) ───────┤         │
  ├──→ Task 4 ✅──→ Wave 5 (SFDM — merger PROMOTED) ──────────────┤    Wave 9 (paper)
  ├──→ Task 5 ✅──→ Wave 6a (MC extension — GATE) ──→ Wave 6b ────┤
  └──→ Task 6 ✅──→ Wave 7 (fracton DM — ⚡Drilldown: VIABLE conditional) ─┐
```

**Critical path:** W2 → W3 → W5 → W8 → W9 (⚡W1b: W5 added to critical path — merger forecast is now co-primary with Track A)
**Parallel operations:**
- Wave 6a (MC extension) can run in parallel with W2-W3 — coordinate with Phase 5d
- Wave 4 (Fang-Gu assessment) is short, can slot anywhere
- Wave 5 (SFDM reframed + merger) and Wave 7 (fracton DM) are independent
**Earliest publishable result:** W2 alone (ℤ₁₆ hidden sector classification with Lean-verified constraints)
**⚡W1b alternative earliest result:** W5 merger forecast alone (fills confirmed BK literature gap with quantitative predictions)
**Blocked:** Wave 6b (vestigial relics) blocked on Wave 6a (MC extension gate)
**⚡Drilldown RE-PRIORITIZED:** Wave 7 fracton DM — upgraded to VIABLE (conditional); p-wave phase + Dark QCD UV completion substantially increase upside; consider elevating to co-secondary with Wave 5

---

## Cross-References to Existing Deep Research (Updated post-W1b)

### Phase 5x Deep Research — Wave 1 (COMPLETE)

| Deep Research Result | Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-5x/ℤ₁₆ Anomaly-Forced Hidden Sector  Dark Matter Candidate Constraints.md` | W2, W8, W9 | T-0 preferred; 24,576 classes; 7 near-term Lean theorems; SMG threshold; Wang N_f=3 uniqueness |
| `Lit-Search/Phase-5x/ADW Emergent Gravity and the Cosmological Constant  Dark Energy from Condensation Equilibrium.md` | W3, W8, W9 | ρ_vac ~ T⁴; T_dS = H/π; Klinkhamer-Volovik oscillating vacuum; ~~DESI DR2 compatibility~~ ⚡Level D tension; 6 Lean targets |
| `Lit-Search/Phase-5x/Fang-Gu Torsion Dark Matter  Phenomenology from Topological Gravity.md` | W4, W8, W9 | σ~10⁻⁹⁰; R=0 from traceless T^μν; two torsion channels; mass undetermined; 4 priority gaps |
| `Lit-Search/Phase-5x/SK-EFT Dissipative Framework Applied to Superfluid Dark Matter  Feasibility Study.md` | W5, W8, W9 | T_H unobservable → MOND/FDR/merger payoff; full parameter mapping; 6 Lean theorems; distinction from FDM |
| `Lit-Search/Phase-5x/Vestigial Gravity Phase Relics as Dark Matter Candidates.md` | W6, W8, W9 | MC extension needed; GUT-scale T_c; EP violation unique; GL(4)/SO(3,1) homotopy; 5 priority questions |
| `Lit-Search/Phase-5x/Fracton Dark Matter  Phenomenological Assessment.md` | W7, W8, W9 | z=4 core-cusp; σ=0 Bullet; finite-T no-go; kinetic stability; 14 Lean theorems; 2503.14496 dust result |

### Phase 5x Deep Research — Wave 1b (COMPLETE) ⚡NEW

| Deep Research Result | Waves | Verdict | Key Content |
|---|---|---|---|
| `Lit-Search/Phase-5x/5x-Klinkhamer-Volovik Oscillating Vacuum vs. DESI DR2  Quantitative w₀-wₐ Assessment.md` | W3, W9 | **LEVEL D TENSION** | KV predicts (w₀,wₐ)=(-1,0), excluded at 2.9–4.4σ by DESI DR2; no phantom crossing; RVM ν~10⁻¹²² too small by 10⁸²; Λ magnitude ~20% accuracy survives; QCD topological DE (arXiv:2506.14182) is DESI-compatible bridge; 6 alternative DE models compared; Paper 17 claims table (5 claims) |
| `Lit-Search/Phase-5x/5x-Gapless Fracton Liquid Stability at Finite Temperature  The Kinetic Stability Window for Fracton Dark Matter/Fracton-DM-Thermal-Stability-Assessment.md` | W7 | ~~NON-VIABLE (weak form)~~ ⚡**Drilldown: VIABLE (conditional)** | Shen no-go exempt for gapless U(1); ~~BBN kills eV-scale M_d~~ Drilldown: p-wave phase thermodynamically stable; Arrhenius applies only to gapped scenario; condensate condition μ ≳ MeV; Dark QCD UV completion; theorem 13 → 13a/13b/13c/13d split; 6 gapless phases surveyed |
| `Lit-Search/Phase-5x/5x-SFDM Cluster Merger Sonic Boom  Observational Forecast for Euclid Roman.md` | W5, W9 | **CONDITIONAL GO** | c_s=1525 km/s; all 5 mergers supersonic; S/N 0.3–1.0 single, 3.5–5.7σ stacked ≥30; BK has no forecast (confirmed gap); velocity-threshold smoking gun; condensate fraction complication; A520 dark core; El Gordo SIDM discriminant; SK-EFT shock width; first 3σ ~2028 |
| `Lit-Search/Phase-5x/5x-Fracton DM Kinetic Stability  Deep Drilldown on the Viability Verdict/Fracton-DM-Kinetic-Stability-Drilldown.md` | W7 | **⚡VIABLE (conditional)** | Kapustin-Spodyneiko (PRB 2022) dipole SSB allowed d≥3; Jensen-Raz (PRL 2024) SSB throughout phase diagram; Głódkowski et al. (2024) z=4 in p-wave; Feistl-Schraven-Warzel (2026) multipole MW; Dark QCD UV completion; μ ≳ MeV replaces Arrhenius; theorem 13→13a-d; supersedes W1b NON-VIABLE |

### Prior Deep Research (HIGH relevance — must read before corresponding wave)

| Deep Research File | Phase 5x Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-5/Emergent gravity from topological order` | W4 | Fang-Gu (arXiv:2106.10242): uncondensed loops source torsion, not curvature → DM candidates |
| `Lit-Search/Phase-3/The ADW mean-field gap equation` | W3 | Gap equation, V_eff(C), cosmological constant as lowest-order invariant |
| `Lit-Search/Phase-5b/Bypassing the hydrodynamic wall` | W2 | Wang ℤ₁₆ → hidden sector, SMG threshold at 16 Weyl fermions |
| `Lit-Search/Phase-5/Vestigial metric susceptibility from ADW tetrad condensation` | W3, W6 | Three-phase structure, Λ_cosm, EP violation in vestigial phase |
| `docs/Fluid-Based Approach...Consolidated Critical Review v3.md` | All | §2.2 gravity wall, Volovik CC, Berezhiani-Khoury superfluid DM, overall program assessment |

### MEDIUM relevance

| Deep Research File | Phase 5x Waves | Key Content |
|---|---|---|
| `Lit-Search/Phase-4/The fracton-gravity route to emergent spin-2` | W7 | Pretko fracton-graviton attraction, Mach principle, DOF counting |
| `Lit-Search/Phase-4/From string-nets to fracton hydrodynamics` | W7 | Fracton subdiffusion, Hilbert space fragmentation |
| `Lit-Search/Phase-5/ADW tetrad condensation lattice formulation` | W3, W6 | MC phase diagram, finite-size scaling |
| `Lit-Search/Phase-2/Dynamical KMS symmetry and the FDR in SK-EFT` | W5 | CGL/FDR framework applicable to SFDM |

---

## Risk Assessment (Updated with Deep Research Outcomes)

| Risk | Pre-Research | Post-Research | Impact | Mitigation | Status |
|------|-------------|---------------|--------|------------|--------|
| ℤ₁₆ hidden sector has no unique DM candidate | Medium | **Confirmed: non-unique** | Medium | T-0 (TQFT, preferred) and S-0 (3 ν_R) both viable. Non-uniqueness IS publishable: "anomaly constrains but does not determine" with Lean-verified bounds | Mitigated |
| ADW CC mechanism is heuristic, not rigorous | High | **Confirmed: heuristic** | Medium | Quantitative ρ_vac ~ T⁴ ~ (meV)⁴ compelling even without proof. Honest assessment is the deliverable. | Accepted |
| Fang-Gu torsion DM mass scale is Planck-scale (unobservable) | Medium | **Confirmed: mass undetermined** | High | Mass parametrically undetermined → BLOCKER for quant. predictions. Wave 4 shortened to assessment. | Partially mitigated |
| SFDM sonic horizons impossible | Medium | **Resolved: T_H real but unobservable** | Low | T_H exists (10⁻²³-10⁻²⁹ K) but too cold. Redirect to MOND corrections, FDR noise, cluster mergers → HIGHER payoff. | Fully mitigated |
## Risk Assessment (Updated with Deep Research + ⚡W1b Outcomes)

| Risk | Pre-Research | Post-Research | ⚡Post-W1b | Impact | Mitigation | Status |
|------|-------------|---------------|-----------|--------|------------|--------|
| ℤ₁₆ hidden sector has no unique DM candidate | Medium | **Confirmed: non-unique** | Unchanged | Medium | T-0 (TQFT, preferred) and S-0 (3 ν_R) both viable. Non-uniqueness IS publishable: "anomaly constrains but does not determine" with Lean-verified bounds | Mitigated |
| ADW CC mechanism is heuristic, not rigorous | High | **Confirmed: heuristic** | Unchanged | Medium | Quantitative ρ_vac ~ T⁴ ~ (meV)⁴ compelling even without proof. Honest assessment is the deliverable. | Accepted |
| ⚡**KV oscillating vacuum incompatible with DESI** | Medium | "Marginally compatible" | **LEVEL D TENSION (2.9–4.4σ)** | High | Λ magnitude prediction (~20% accuracy) survives. QCD topological DE (Van Waerbeke-Zhitnitsky 2025) provides DESI-compatible bridge. Paper 17: withdraw dynamics claim, keep magnitude claim. DESI DR3 (2026-2027) falsifiable. | **Reframed** |
| Fang-Gu torsion DM mass scale is Planck-scale (unobservable) | Medium | **Confirmed: mass undetermined** | Unchanged | High | Mass parametrically undetermined → BLOCKER for quant. predictions. Wave 4 shortened to assessment. | Partially mitigated |
| SFDM sonic horizons impossible | Medium | **Resolved: T_H real but unobservable** | Unchanged | Low | T_H exists (10⁻²³-10⁻²⁹ K) but too cold. Redirect to MOND corrections, FDR noise, cluster mergers → HIGHER payoff. | Fully mitigated |
| ⚡**SFDM merger forecast not competitive** | — | Rank 1 observable (qualitative) | **CONDITIONAL GO (quantitative)** | Low | S/N 3.5–5.7σ stacked ≥30; fills confirmed BK literature gap; first 3σ ~2028; Paper 17 money plot. H₀ tension (H0DN >5σ) shifts Σ_cr ~8%, S/N ~4% — not meaningful. | **Fully mitigated** |
| Vestigial relics too speculative for publication | Medium-High | **Narrowed: coherent but gated** | Unchanged | Medium | MC extension gate (Wave 6a) resolves. If transition is 2nd order → KZ relics viable. If crossover → no relics. | Downstream resolution |
| Fracton DM incompatible with 3+1D gravity | Medium | **Clarified: finite-T no-go for gapped 3D** | ⚡**Drilldown: VIABLE (conditional)** | **Medium** | ⚡Drilldown: p-wave dipole superfluid thermodynamically stable at T>0 in d=3 (Kapustin-Spodyneiko, Jensen-Raz). BBN relaxed to μ ≳ MeV. Dark QCD UV completion viable. Remaining gap: production mechanism. Phenomenology (σ=0, z=4, HSF) all survive. Theorem 13 → 13a-d split. | **⚡Substantially mitigated** |
| No single connection strong enough for a focused paper | Low | **Resolved: Track A is paper-ready** | ⚡**Strengthened: Track A + W5 merger** | N/A | ℤ₁₆ + ADW CC + merger forecast + fracton DM → Paper 17 with 4 strong sections. Merger fills genuine literature gap. | Fully mitigated |
| **NEW: MC extension computationally expensive** | — | Medium | Unchanged | Medium | L=10,12,16 requires significant HPC time. Coordinate with Phase 5d RHMC infrastructure. Can run in parallel. | Plan exists |
| **NEW: Deep research invisible DM candidates unpublishable** | — | Low | Unchanged | Medium | "All emergent gravity DM is invisible to direct detection" is itself a thematic result — unified by theoretical structure. | Thematic framing |

---

## Lean Formalization Targets (Revised from Deep Research + ⚡W1b)

| Wave | Module | Near-Term Theorems | Deferred/Hard | LOC (est.) | Reused Theorems |
|---|---|---|---|---|---|
| W2 | HiddenSectorClassification.lean | 7 (T1-T3, T8, T10-T12) | 5 (T4-T7, T9 — need bordism/TQFT) | 300-500 | Z16Anomaly (23), SMFermionData (18), GenConstraint (4) |
| W3 | CosmologicalConstant.lean | 3 (T2-T3 easy/med; T1 med) | 3 (T4-T6 hard) | 200-400 | ADWMechanism (21), VestigialGravity (18), HawkingUniv (8) |
| W4 | (no new module) | 0 | 0 | 0 | ADWMechanism, VestigialGravity (assessment only) |
| W5 | SFDMAcousticMetric.lean | 4 (L1-L2 easy, L3 L6 med) | 2 (L4-L5 hard) | 200-400 | WKBConnection (18), WKBAnalysis (17), HawkingUniv (8), AcousticMetric (12) |
| W6b | VestigialRelics.lean | 4 (coset homotopy, EP bound, skyrmion τ, self-int) | 1 (KZ density) | 150-300 | VestigialGravity (18), ADWMechanism (21), SO4Weingarten (16) |
| W7 | FractonDarkMatter.lean | 8 (theorems 1-4, 8-11) | ⚡**10** (theorems 5-7, 12, 13a, 13b, 13c, 13d, 14) | 500-700 | FractonGravity (20), FractonHydro (17), FractonFormulas (45), FractonNonAbelian (4) |
| **Total** | | **26 near-term** | ⚡**21 deferred/hard** | **1350-2300** | **~190 reused across waves** |

**⚡W1b changes:** Wave 7 deferred count increased from 6 to 9 (theorem 13 split into 13a/13b/13c adds 2 net new). ⚡**Drilldown:** +1 theorem (13d: BBN condensate condition). Total deferred/hard: 21. Total theorems: 47 (26 near-term + 21 deferred).

---

## Success Criteria (Updated post-W1b)

**Minimum viable (Waves 2-3, ~2-3 months):**
- [x] All 6 deep research tasks completed with gap analysis documents ✅
- [x] ⚡All 3 Wave 1b follow-up tasks completed ✅ (KV Level D, fracton NON-VIABLE weak, merger CONDITIONAL GO)
- [ ] ℤ₁₆ hidden sector classification: 7 new Lean theorems (T1-T3, T8, T10-T12) + hidden sector enumeration code
- [ ] ADW CC quantitative assessment: V_eff critical point formalized, Volovik equilibrium formalized, ΛCDM compatibility table. ⚡W1b: include KV Level D tension, QCD topological DE bridge, revised claims table.
- [ ] Clear, honest assessment of which connections are derivable vs speculative

**High-impact deliverable (+ Waves 4-5, ~4-6 months):**
- [ ] ADW cosmological constant fully assessed with SK-EFT de Sitter connection mapped
- [ ] Fang-Gu assessment document with ADW compatibility analysis and two-torsion-channel insight
- [ ] SFDM MOND corrections computed with FDR noise floor bound (L5 hard theorem — stretch)
- [ ] ⚡**W1b PROMOTED:** SFDM merger forecast with 5-target S/N table, stacking strategy, and money plot (fills BK literature gap)
- [ ] Sufficient for a focused Track A paper (Paper 17 draft, sections 1-3 + ⚡merger section 5)

**Full scope (all 9 waves, ~10-14 months):**
- [ ] All 6 connections developed to full depth
- [ ] MC extension (Wave 6a) completed → vestigial relic physics resolved
- [ ] Synthesis document with cross-connections and unified experimental prediction table
- [ ] Paper 17 through full 12-stage pipeline (⚡W1b: now 11 sections, merger section promoted)
- [ ] 26 near-term Lean theorems verified (+ up to ⚡21 deferred), ~1350-2300 LOC
- [ ] FractonDarkMatter.lean at ⚡~18 theorems (theorem 13 split into 13a/13b/13c/13d)

---

## Connection to Existing Phases (Updated)

| Phase | Connection | Deep Research Update |
|-------|-----------|---------------------|
| Phase 1-2 (SK-EFT) | Dissipative framework directly applicable to superfluid DM (W5) and de Sitter horizon (W3) | SFDM deep research confirmed full parameter mapping: CGL coefficients → BK DM mass/Λ/α. FDR noise floor is new observable. |
| Phase 3 (WKB/ADW) | Gap equation → CC (W3); WKB → SFDM sonic horizons (W5) | ADW deep research: Volovik equilibrium mechanism validated; T_H exists but unobservable (10⁻²³ K). MOND corrections are higher-payoff. |
| Phase 4 (fractons) | Fracton formalization → fracton DM (W7); string-net excitations → DM candidates | Fracton deep research: 86 existing theorems directly reusable. NEW: finite-T 3D no-go (Krishna et al. 2024) — kinetic stability is the viable path. |
| Phase 5 (topological gravity) | Fang-Gu torsion DM (W4); emergent gravity → dark sector | FG deep research: σ~10⁻⁹⁰ rules out direct detection; two torsion channels (FG + Boos-Hehl); mass undetermined = BLOCKER. |
| Phase 5b (hydrodynamic wall) | Wang ℤ₁₆ → hidden sector (W2); SMG threshold | ℤ₁₆ deep research: T-0 (TQFT) preferred; 24,576 deformation classes; N_f=3 uniqueness proof. |
| Phase 5d (ADW MC) | Vestigial phase diagram → relics (W6); finite-size scaling → transition order | Vestigial deep research: L=6,8 data insufficient for transition order → MC extension to L≥10 is GATE for Wave 6b. |
| Phase 5e (ℤ₁₆ anomaly) | Z16AnomalyComputation.lean → hidden sector DM (W2) | 23 existing theorems + 18 SMFermionData + 4 GenConstraint provide foundation; 7 new near-term, 5 deferred. |
| Phase 5w (graphene) | Independent — but both use SK-EFT framework; graphene results may inform SFDM phonon EFT (W5) | SFDM phonon-roton EFT (Berezhiani-Khoury) structurally identical to SK-EFT phonon sector formalized in Phase 5w. |

---

## Key References (Updated from Deep Research)

**Anomaly / Hidden Sector (Wave 2):**
- Wang, J., "Ultra Unification," arXiv:2006.16996
- Wang, Wan, You, "Deformation class of the SM," arXiv:2112.14765, PRD 106 (2022)
- García-Etxebarria, Montero, "Dai-Freed anomalies," arXiv:1808.00009
- Hasenfratz, Witzel, "SMG on the lattice," arXiv:2503.04789 (2025)
- Razamat, Tong, "Gapped chiral fermions," arXiv:2009.05037
- You, He, Xu, "Symmetric Mass Generation," arXiv:2204.14271
- Freed, Hopkins, "Reflection positivity and invertible topological phases," arXiv:1604.06527

**ADW / Cosmological Constant (Wave 3):**
- Diakonov, "Towards lattice-regularized quantum gravity," arXiv:1109.0091
- Volovik, "Dimensionless physics," arXiv:2312.09435, JETP Lett. 119 (2024)
- Volovik, "de Sitter thermodynamics," arXiv:2307.14370; arXiv:2310.05754
- Klinkhamer, Volovik, "Self-tuning vacuum variable and cosmological constant," PRD 77 (2008)
- DESI Collaboration, "DESI DR2 baryon acoustic oscillations," arXiv:2503.14738 (2025)

**Fang-Gu Torsion DM (Wave 4):**
- Fang, Gu, "Topological gravity from quantum entanglement," arXiv:2106.10242
- Fang, Gu, "Emergent Einstein gravity," arXiv:2312.17196
- Boos, Hehl, "Gravity-induced four-fermion contact interaction," IJMPD 28 (2019)
- Alexander, Yunes, "Chern-Simons modified general relativity," Phys. Rept. 480 (2009)

**SFDM / SK-EFT (Wave 5):**
- Berezhiani, Khoury, "Theory of dark matter superfluidity," arXiv:1507.01614, PRD 92 (2015)
- Berezhiani, Khoury, "Dark matter superfluidity and galactic dynamics," arXiv:1602.05961, PLB 753 (2016)
- Ferreira, "Ultra-light dark matter," Astron. Astrophys. Rev. 29, 7 (2021) — distinguishes SFDM from FDM
- Sharma, Reddy, Mukhopadhyay, "Phonon Hawking radiation from acoustic black holes," PRD 107 (2023)

**Vestigial Relics (Wave 6):**
- Kibble, "Topology of cosmic domains and strings," J. Phys. A9 (1976)
- Zurek, "Cosmological experiments in superfluid helium?", Nature 317 (1985)
- Damour, "Experimental tests of gravitational theory," RPP (2012) — EP violation bounds
- Schwarz, "The dark side of the Higgs boson," arXiv:1306.0543 — vestigial soliton parallels

**Fracton DM (Wave 7):**
- Pretko, "Emergent gravity of fractons," arXiv:1702.07613, PRD 96 (2017)
- Pretko, "Fracton-elasticity duality," PRB 98-2 (2018)
- Adler et al., "Observation of fracton subdiffusion," Nature (2024)
- Krishna, Bridgeman, Bartlett, "Gapped fracton phases at finite T: 3D no-go," arXiv:2407.09625 (2024)
- Bidussi, Doshi, Hofman, Stremoukhov, "Fractons as dust," arXiv:2503.14496 (2025)
- Oman et al., "The unexpected diversity of dwarf galaxy rotation curves," MNRAS 452 (2015) — core-cusp
- ⚡**Drilldown:**
- Kapustin, Spodyneiko, "Hohenberg-Mermin-Wagner-type theorems for systems with continuous symmetries and dipole symmetry," PRB 106, 245125 (2022) — dipole SSB allowed in d≥3
- Jensen, Raz, "Large-N dipole superfluid," PRL (2024) — SSB throughout entire phase diagram, p-wave phase dominates at T>0 in d=3
- Głódkowski, Peña-Benítez, Surówka, "Hydrodynamics of dipole-conserving superfluids" (2024) — z=4 subdiffusion survives in p-wave phase
- Feistl, Schraven, Warzel, "Mermin-Wagner-type theorems for quantum lattice systems with multipole symmetries," arXiv:2601.23078 (Jan 2026) — confirms Kapustin-Spodyneiko, extends to multipoles

**⚡W1b Additional References:**
- DESI Collaboration, "DESI DR2 baryon acoustic oscillations: measurement of the expansion rate and geometry at z < 2.1," arXiv:2503.14738 (2025) — KV Level D tension source
- Berezhiani, Khoury, "Superfluid dark matter," Physics Reports (2025), arXiv:2505.23900 — 118-page review with NO quantitative merger forecast
- Van Waerbeke, Zhitnitsky, "QCD topological dark energy," arXiv:2506.14182 (2025) — 0 free parameters, phantom crossing, DESI-compatible
- Shen, Cheng, Hu, et al., "3D fracton topological order destroyed at any T > 0," arXiv:2203.09298 (2022) — no-go theorem (gapped phases only)
- Prem, Haah, Nandkishore, "Glassy quantum dynamics in translation invariant fracton models," PRB 95, 155133 (2017) — superexponential relaxation
- Jee et al., "The dark core in Abell 520," ApJ 747, 96 (2012) — >10σ dark core detection, M/L=588
- Solà Peracaula, "Running vacuum model," Int. J. Mod. Phys. D 24 (2015) — RVM with ν~10⁻³

**⚡H₀ Tension References (April 2026):**
- H0 Distance Network (H0DN) Collaboration, H₀ = 73.50 ± 0.81 km/s/Mpc (April 10, 2026) — >5σ vs Planck, ~1% precision
- Berezhiani, Khoury, Wang, "DM-baryon phonon-mediated late-time cosmic acceleration," (2017) — SFDM approach to H₀ tension via phonon EFT; thematic hook for Paper 17
- ACT DR6 (March 2025) — no statistically significant departure from ΛCDM; cannot pull H₀ above ~69.9 even with EDE
