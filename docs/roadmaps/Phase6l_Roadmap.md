# Phase 6l: Strong-CP θ̄ Direct Dynamics

## Technical Roadmap — April 2026

*Prepared 2026-04-28 | **New phase, complementary to Phase 6c.1.** Sources: Phase 6c.1 `StrongCPTopologicalDE.lean` (8 thms, 2026-04-27 ship — Zhitnitsky topological-DE absorption only); user gap-analysis (2026-04-28 Research Overview): "Phase 6c W1 absorbs strong-CP via Zhitnitsky topological DE, but `θ̄`'s dynamics — axion misalignment, Peccei-Quinn — is unmodeled. The substrate's ℤ_16 anomaly framework is unusually well-suited to address why `θ̄` is small."; Phase 5b `Z16AnomalyComputation.lean` (ℤ_16 anomaly framework available).*

**Trigger condition (no gate — autonomous):** Phase 6l can dispatch any time. It builds on shipped Phase 5b and Phase 6c.1 infrastructure and is independent of any latent phase.

**Status (2026-04-28):** **OPEN** for user authorization Gate L.1 (Wave 1 dispatch).

**Scope reframing vs Phase 6c.1.** Phase 6c Wave 1 (`StrongCPTopologicalDE.lean`) shipped the Zhitnitsky topological-DE *absorption* mechanism: "if QCD θ-vacuum sources DE via Zhitnitsky mechanism, then θ must be dynamically small," with the structural punchline that combined Zhitnitsky + KV q-theory exceeds observation by ×240 (forcing single-DE-mechanism commitment). Phase 6c.1 does *not* derive how θ̄ becomes small (the underlying dynamics — axion misalignment, Peccei-Quinn relaxation, anthropic selection, symmetry-based suppression). Phase 6l fills this gap: Direct Strong-CP Dynamics on the SK-EFT substrate.

**Entry state (2026-04-28 Inventory_Index snapshot):** ~187 active modules, ~4,385 theorems, 0 sorry, 1 axiom. Phase 6c CLOSED at 4 of 5 waves shipped.

**Anchors carried forward into Phase 6l:**
- `StrongCPTopologicalDE.lean` (Phase 6c.1) — θ-smallness CONSTRAINT via Zhitnitsky absorption.
- `Z16AnomalyComputation.lean` (Phase 5b) — ℤ_16 anomaly framework, the substrate's natural setting for instanton-counting / anomaly-derived θ-dynamics.
- `RokhlinBridge.lean` (Phase 5b) — Rokhlin ↔ ℤ_16 convergence; instanton-related topological invariants.
- `CenterSymmetryConfinement.lean` (Phase 6d.1) — confinement = ℤ_N 1-form center unbreaking; θ-vacuum dynamics couple naturally to center-symmetry sector.
- `ChiralSSB_QCD.lean` (Phase 6d.2) — quark-condensate substrate channel (relevant for θ-rotation by chiral redefinition).
- `InstantonZeroModes.lean` (Phase 5s) — instanton zero-mode counting infrastructure (4D index theorem bypass via Cl(4) decomposition).

**Thesis.** The SK-EFT substrate's ℤ_16 anomaly framework + the lattice ADW tetrad-channel structure together provide a natural setting for *deriving* (rather than postulating) why θ̄ is small. Three classical proposals exist in the literature:
1. **Peccei-Quinn solution** (PQ symmetry → axion → dynamical relaxation to θ̄ = 0).
2. **Massless-quark solution** (excluded experimentally — `m_u ≠ 0`).
3. **Anthropic / cosmological-selection** solution (less satisfying; not a derivation).

The SK-EFT substrate offers a possible *fourth* route: **θ̄ smallness from substrate symmetry / ℤ_16 anomaly cancellation**, where the substrate's discrete topological structure forces θ̄ to a fixed (small or zero) value via the same anomaly framework that forces N_f ≡ 0 mod 3.

**Three-branch verdict structure (each publishable):**
- **Branch α (substrate forces θ̄ = 0):** ℤ_16 anomaly framework + tetrad-channel constraint forces θ̄ = 0 mod (small correction); strong-CP problem solved by substrate symmetry. Most ambitious.
- **Branch β (substrate forces a Peccei-Quinn-like axion):** substrate predicts an axion-like dynamical field that relaxes θ̄ → 0; substrate-derived axion mass and coupling.
- **Branch γ (substrate-silent):** ℤ_16 framework does not constrain θ̄; strong-CP problem stays open under SK-EFT substrate; structural-no-go analog of Phase 5y.

**Correctness-push framing.** Quantitative anchors:
1. **(Wave 1)** θ̄ smallness from ℤ_16 anomaly: derive `θ̄ ≤ ε(Λ_UV/Λ_QCD)` for some explicit small ε; falsifiable against neutron-EDM bound `|θ̄| ≤ 10⁻¹⁰` (Abel et al., PRL 124, 081803, 2020).
2. **(Wave 2)** Substrate-derived axion: if branch β fires, axion mass `m_a ~ Λ_QCD² / f_a` with substrate-derived `f_a` band; falsifiable against ADMX direct-detection bounds + cosmological constraints.
3. **(Wave 3)** ℤ_16 instanton counting: substrate's instanton spectrum on the lattice ADW; cross-validation with `InstantonZeroModes.lean` (Phase 5s) zero-mode counting.
4. **(Wave 4)** θ̄-vacuum thermodynamics: θ-vacuum free energy on substrate at finite temperature; cross-bridge to Phase 6c.1 Zhitnitsky topological DE.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap.**
> 2. Read this roadmap end-to-end before claiming any wave assignment.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/StrongCPTopologicalDE.lean` (Phase 6c.1).
>    - `lean/SKEFTHawking/Z16AnomalyComputation.lean` (Phase 5b).
>    - `lean/SKEFTHawking/RokhlinBridge.lean` (Phase 5b).
>    - `lean/SKEFTHawking/InstantonZeroModes.lean` (Phase 5s).
>    - `lean/SKEFTHawking/CenterSymmetryConfinement.lean` (Phase 6d.1).
>    - `lean/SKEFTHawking/ChiralSSB_QCD.lean` (Phase 6d.2).
> 4. **Critical deep-research dossiers required** (file under `Lit-Search/Tasks/` at user authorization):
>    - `Phase6l_W1_z16_anomaly_forces_theta_bar.md` — request synthesis on whether the ℤ_16 anomaly framework constrains θ̄ in 4D non-Abelian gauge theory; primary literature: Wan-Wang-Zheng; Witten's Z_2 anomaly paper; Garcia-Saenz, Garcia-Garcia 2024 substrate-instanton work.
>    - `Phase6l_W2_substrate_axion_mass_coupling.md` — request synthesis on whether SK-EFT substrate dynamics (vestigial gravity, ADW tetrad) produce an axion-like field; primary literature: Peccei-Quinn 1977; Weinberg 1978; Wilczek 1978; Kim 1979; Shifman-Vainshtein-Zakharov 1980 (KSVZ); Dine-Fischler-Srednicki 1981 (DFSZ).
>    - `Phase6l_W3_substrate_instanton_spectrum.md` — request synthesis on the instanton spectrum on lattice ADW substrate; primary literature: 't Hooft 1976; Csaki et al. 2024 (Abelian instantons in ADW); Phase 5s `InstantonZeroModes.lean` cross-reference.
>    - `Phase6l_W4_theta_vacuum_finite_T_substrate.md` — request synthesis on θ-vacuum thermodynamics in substrate-emergent QCD.
> 5. **Apply preemptive-strengthening checklist** before each theorem.
> 6. **Do not delegate Lean theorem proving to subagents.**
> 7. **User authorization gates:** Gate L.1 (Wave 1 start). Subsequent waves run autonomously.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6l:**
- Direct dynamics of θ̄ on SK-EFT substrate: how θ̄ becomes small.
- ℤ_16 anomaly route to θ̄ smallness or θ̄-quantization (analog to N_f ≡ 0 mod 3 derivation).
- Substrate-derived axion (Peccei-Quinn-like field), if predicted.
- Substrate instanton spectrum cross-validation against Phase 5s zero-mode counting.
- θ-vacuum thermodynamics on substrate.
- Cross-bridge to Phase 6c.1 Zhitnitsky topological DE absorption (sharpens "θ must be small" to "θ becomes small via mechanism Y").
- One paper (target: PRD): "Strong-CP Dynamics on the SK-EFT Substrate."

**OUT OF SCOPE for Phase 6l:**
- Detailed axion phenomenology (DM relic abundance, ADMX detection rates) — Phase 5x dark-matter territory if substrate-derived axion is a DM candidate.
- Full QCD lattice with dynamical θ — Phase 6d Track B (deferred / HPC) territory.
- Anthropic / cosmological selection mechanisms — outside SK-EFT scope by design.
- Massless-quark solution — experimentally excluded; not in scope.
- BSM CP violation beyond θ̄ — Phase 6k Wave 5 territory (CKM δ phase).

**Phase 6c.1 relationship.** Phase 6l *complements* Phase 6c.1: 6c.1 ships the absorption "θ̄ must be small if Zhitnitsky DE active"; 6l ships the dynamics "θ̄ becomes small via mechanism Y." 6c.1 modules are not modified.

**Phase 5x relationship.** If branch β fires (substrate-derived axion), the axion is a candidate ultra-light DM particle and Phase 5x classification table gets a new entry. Cross-reference but no module edits.

**Phase 6k relationship.** Phase 6k Wave 5 (CP phase δ_CKM) may cross-bridge to Phase 6l if `δ_CKM = f(θ̄)` is the substrate prediction (Phase 6k branch C).

---

## Wave 1 — `Z16AnomalyForcesThetaBar.lean` [6l.1] [Pipeline: Stages 1–13]

**Goal.** Investigate whether the ℤ_16 anomaly framework + the SK-EFT substrate's tetrad-channel structure forces θ̄ to a fixed (small or zero) value, analogously to how it forces N_f ≡ 0 mod 3. Three sub-branches: (α) substrate forces θ̄ = 0; (α') substrate forces θ̄ ∈ {0, π} discrete (and π is excluded by experiment); (γ) substrate-silent.

**Prerequisites:**
- Deep-research dossier `Phase6l_W1_z16_anomaly_forces_theta_bar.md` returned.
- Phase 5b `Z16AnomalyComputation.lean` shipped.

**Module structure:**
- `lean/SKEFTHawking/Z16AnomalyForcesThetaBar.lean` — new module, ~16 substantive theorems target, 0 sorry, 0 new axioms.
- `src/strong_cp/z16_theta_bar.py` — numerical θ̄ constraint from ℤ_16 anomaly + tetrad-channel.
- `tests/test_z16_theta_bar.py` — falsifiability tests vs neutron EDM; 12+ tests.
- `figures/fig_theta_bar_z16_constraint.{png,html}`.

**Headline theorems (one branch fires; document alternatives):**

**Branch α (substrate forces θ̄ = 0):**
1. `theta_bar_locked_by_z16_anomaly` — ℤ_16 anomaly cancellation forces `θ̄ ≡ 0 mod 2π` on substrate.
2. `neutron_edm_bound_satisfied_by_z16_lock` — `|θ̄| ≤ 10⁻¹⁰` (Abel et al. 2020) trivially satisfied.
3. `z16_lock_explains_strong_cp` — substrate-symmetry resolution of strong-CP without PQ.

**Branch α' (substrate forces θ̄ ∈ {0, π}):**
1. `theta_bar_z2_quantized_by_substrate` — substrate forces `θ̄ ∈ {0, π}` discrete.
2. `theta_bar_pi_violates_neutron_edm_by_factor` — concrete computation: `θ̄ = π` predicts `|d_n|` ~ 10⁻⁵ e·cm vs experiment `|d_n| < 1.8 × 10⁻²⁶ e·cm`, falsifying θ̄ = π by ~10²¹.
3. `theta_bar_zero_only_consistent_choice` — only θ̄ = 0 is experimentally compatible.

**Branch γ (substrate-silent):**
1. `z16_anomaly_does_not_constrain_theta_bar` — anomaly-matching argument for θ̄ smallness fails on substrate; structural-no-go.
2. `strong_cp_remains_open_under_skeft` — analog of Phase 5y dark-energy scope-recalibration; θ̄ smallness not explained by SK-EFT substrate.

**Strengthening checklist:**
- (P5 trivial-discharge): if branch α fires, is `theta_bar_locked_by_z16_anomaly` substantive? — yes, requires explicit construction of the anomaly-matching argument; not a definitional consequence.
- (Quantitative): branch α' must `norm_num`-check `|d_n|(θ̄=π) ≈ 10⁻⁵ e·cm` against neutron-EDM bound.

**Stage 13 anchors:**
- Abel et al., PRL 124, 081803 (2020) — neutron EDM bound.
- Wan, Wang, Zheng — ℤ_16 anomaly framework.
- Witten — Z_2 anomaly.
- Phase 5b deep-research literature.

**Deliverables.** `Z16AnomalyForcesThetaBar.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 2 — `SubstrateAxion.lean` [6l.2] [Pipeline: Stages 1–13]

**Goal.** Investigate whether the SK-EFT substrate produces an axion-like field (Peccei-Quinn analog) emergent from the substrate's vestigial gravity / ADW tetrad / ℤ_16 structure. If so, derive substrate-predicted axion mass `m_a` and decay constant `f_a`, falsifiable against ADMX bounds + cosmological constraints + recent CASPEr / DM Radio searches.

**Prerequisites:**
- Wave 1 SHIPPED (informs whether Phase 6l proceeds in branch α or branch β).
- Deep-research dossier `Phase6l_W2_substrate_axion_mass_coupling.md` returned.

**Module structure:**
- `lean/SKEFTHawking/SubstrateAxion.lean` — new module, ~14 substantive theorems target.
- `src/strong_cp/substrate_axion.py` — numerical m_a / f_a from substrate parameters.
- `tests/test_substrate_axion.py` — falsifiability tests vs experimental bounds; 10+ tests.
- `figures/fig_substrate_axion_mass_coupling_window.{png,html}`.

**Headline theorems (branch β only — fires only if Wave 1 branches γ or partial):**
1. `substrate_axion_field_definition` — substrate's Goldstone mode of (some emergent symmetry) is axion-like.
2. `axion_decay_constant_from_substrate` — `f_a ~ Λ_UV` (or some substrate-channel-derived value), falsifiable.
3. `axion_mass_QCD_anomaly` — `m_a = (m_π f_π / f_a) · √(m_u m_d / (m_u + m_d)²)` with substrate-derived f_a.
4. `axion_window_consistent_with_admx_caspr` — predicted (m_a, g_aγγ) lies in / near current ADMX + CASPEr search windows; falsifiable.
5. `axion_relic_abundance_substrate_window` — substrate-predicted relic abundance Ω_a h² compatible with Planck Ω_DM h² ≈ 0.12 in narrow band.
6. `axion_solves_strong_cp_dynamically` — axion VEV relaxation `⟨a⟩ → 0` mod 2π f_a forces θ̄ → 0.

**Strengthening checklist:**
- (Quantitative): `m_a` and `f_a` must `norm_num`-check against ADMX exclusion (m_a ∈ [2, 4] μeV currently excluded; f_a ∈ [10⁹, 10¹²] GeV "axion window").
- (P2 bundle): keep axion mass + decay constant as separate theorems even though they're algebraically related.

**Stage 13 anchors:**
- Peccei, Quinn, PRL 38, 1440 (1977).
- Weinberg, PRL 40, 223 (1978); Wilczek, PRL 40, 279 (1978).
- Kim, PRL 43, 103 (1979); Shifman-Vainshtein-Zakharov, NPB 166, 493 (1980) (KSVZ).
- Dine-Fischler-Srednicki, PLB 104, 199 (1981) (DFSZ).
- ADMX, Du et al., PRL 120, 151301 (2018).
- CASPEr-ZULF, Garcon et al., Sci. Adv. 5, eaax4539 (2019).

**Deliverables.** `SubstrateAxion.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 3 — `SubstrateInstantonSpectrum.lean` [6l.3] [Pipeline: Stages 1–13]

**Goal.** Derive the instanton spectrum on the lattice ADW substrate; cross-validate against Phase 5s `InstantonZeroModes.lean` zero-mode counting (which already proves 2|qn| = 4 zero modes per flavor for N_f=4, machine-checked via Cl(4) ≅ Cl(2) ⊗̂ Cl(2)). Wave 3 extends to: (a) instanton density spectrum (1-instanton, 2-instanton, ..., n-instanton sectors); (b) θ-vacuum susceptibility `χ_top = ⟨θ̄⟩/V`; (c) cross-bridge to Phase 6c.1 Zhitnitsky topological DE (Zhitnitsky uses `χ_top` as the load-bearing quantity).

**Prerequisites:**
- Phase 5s `InstantonZeroModes.lean` shipped.
- Phase 6c.1 `StrongCPTopologicalDE.lean` shipped.

**Module structure:**
- `lean/SKEFTHawking/SubstrateInstantonSpectrum.lean` — new module, ~12 substantive theorems target.
- `src/strong_cp/instanton_spectrum.py` — numerical instanton density from substrate.
- `tests/test_instanton_spectrum.py` — golden tests; 8+ tests.
- `figures/fig_instanton_spectrum_substrate.{png,html}`.

**Headline theorems:**
1. `instanton_density_substrate_form` — `n_inst(ρ) = e^{−8π²/g²(ρ)} · f(ρ)` with substrate-channel correction `f(ρ)`.
2. `topological_susceptibility_substrate` — `χ_top = ⟨Q²⟩/V` derived from substrate; falsifiable against lattice QCD `χ_top^lat ≈ (76 MeV)⁴`.
3. `chi_top_consistent_with_zhitnitsky_DE` — cross-bridge: `χ_top` from Wave 3 substrate matches `χ_top` consumed by Phase 6c.1's Zhitnitsky absorption (`ρ ~ Λ_QCD⁶/M_P²`), validating the coupling.
4. `instanton_zero_modes_consistent_with_phase5s` — cross-bridge: zero-mode count from Wave 3 matches Phase 5s `InstantonZeroModes.lean` 2|qn|=4 result.

**Strengthening checklist:**
- (Quantitative): `χ_top^substrate ≈ (76 MeV)⁴` PDG-anchored.
- (P6 cross-module bridge): `chi_top_consistent_with_zhitnitsky_DE` must `import` Phase 6c.1 module and `call` the relevant theorem.

**Stage 13 anchors:**
- 't Hooft, PRL 37, 8 (1976) — instanton.
- Csaki et al. 2024 — Abelian instantons in ADW.
- Phase 5s deep-research literature.

**Deliverables.** `SubstrateInstantonSpectrum.lean`; numerical module; figure suite; section in flagship paper.

---

## Wave 4 — `ThetaVacuumFiniteT.lean` [6l.4] [Pipeline: Stages 1–13]

**Goal.** θ-vacuum thermodynamics on substrate at finite temperature: how does the θ̄ smallness mechanism interact with thermal evolution? At early-universe temperatures, was θ̄ randomized or fixed? Cross-bridge to Phase 5z W3 EW phase transition (which proved EW transition is a crossover) — the analogous QCD chiral-restoration transition at T ≈ 150 MeV affects θ-vacuum dynamics.

**Prerequisites:**
- Waves 1–3 SHIPPED.
- Phase 5z W3 `EWPhaseTransition.lean` shipped (architectural template for finite-T physics).

**Module structure:**
- `lean/SKEFTHawking/ThetaVacuumFiniteT.lean` — new module, ~10 substantive theorems target.
- `src/strong_cp/theta_finite_T.py` — finite-T θ-vacuum free energy.
- `tests/test_theta_finite_T.py` — finite-T tests; 8+ tests.
- `figures/fig_theta_vacuum_free_energy_finite_T.{png,html}`.

**Headline theorems:**
1. `theta_vacuum_free_energy_finite_T` — `F(θ̄, T) = − χ_top(T) · cos(θ̄) + ...` derived from substrate.
2. `theta_smallness_persists_above_qcd_transition` — if branch α fires, `θ̄ = 0` is an exact-symmetry consequence preserved at all T.
3. `axion_misalignment_at_qcd_transition` — if branch β fires, axion field starts at random initial `⟨a⟩_init` and relaxes to `⟨a⟩ = 0` at `T < T_QCD ≈ 150 MeV`; predicts axion DM relic abundance.
4. `cross_bridge_to_ew_phase_transition` — analog: θ-vacuum dynamics at QCD chiral-restoration transition compared to scalar-rung dynamics at EW transition.

**Strengthening checklist:**
- (Quantitative): T_QCD ≈ 150 MeV PDG-anchored.

**Stage 13 anchors:**
- Phase 5z W3 finite-T literature.
- Pisarski-Yaffe, PRD 21, 1768 (1980) — instanton suppression at finite T.
- Borsanyi et al., Nature 539, 69 (2016) — lattice QCD axion mass at high T.

**Deliverables.** `ThetaVacuumFiniteT.lean`; numerical module; figure suite; section in flagship paper.

---

## Paper deliverable

**Paper 44** (target: PRD): "Strong-CP Dynamics on the SK-EFT Substrate." 6–10 pages. Structure:
- §2 ℤ_16-anomaly route to θ̄ smallness (Wave 1) — three branches.
- §3 Substrate-derived axion (Wave 2) — only if branch β.
- §4 Substrate instanton spectrum + topological susceptibility (Wave 3).
- §5 θ-vacuum thermodynamics + cross-bridge to QCD chiral-restoration transition (Wave 4).
- §6 Cross-bridge to Phase 6c.1 Zhitnitsky DE absorption (sharpens "θ must be small" → "θ becomes small via mechanism Y").
- §7 Verdict: branch α / β / γ + falsifiability summary.

**Submission readiness:** target Stage 13 closure ~6–10 weeks post-Wave 4.

---

## Cross-phase impact

- **Phase 6c.1**: Phase 6l sharpens 6c.1's absorption ("θ̄ must be small") into a derivation ("θ̄ becomes small via mechanism Y"); 6c.1 module not modified.
- **Phase 5b**: Phase 6l Wave 1 leverages but does not modify `Z16AnomalyComputation.lean`.
- **Phase 5s**: Phase 6l Wave 3 cross-validates `InstantonZeroModes.lean` Cl(4) zero-mode counting; no module edit.
- **Phase 6d**: Phase 6l Wave 3 and 4 cross-bridge to QCD-sector Phase 6d modules (`CenterSymmetryConfinement`, `ChiralSSB_QCD`).
- **Phase 5z W3**: Phase 6l Wave 4 uses 5z.3 finite-T architecture as template; no edits.
- **Phase 5x**: if branch β fires (substrate-derived axion), axion is a new DM candidate and the dark-sector classification table acquires an entry. Coordination only, no current Phase 5x edit.
- **Phase 6k Wave 5**: if Phase 6k branch C fires (`δ_CKM` correlated with `θ̄`), Phase 6l outputs are consumed by the Phase 6k cross-bridge.

---

## Total LOE estimate

- Wave 1 (ℤ_16 → θ̄): 3–4 PM Lean + 2–3 PM derivation
- Wave 2 (substrate axion): 2–3 PM Lean + 1–2 PM derivation (only fires under branch β)
- Wave 3 (instanton spectrum): 2 PM Lean + 1 PM derivation
- Wave 4 (finite-T): 2 PM Lean + 1 PM derivation
- Paper 44 drafting: 2 PM
- **Total: 12–18 PM** (~3–4.5 months at full intensity, depending on which branches fire)

---

*Last updated: 2026-04-28. Status: OPEN, awaiting Wave 1 deep-research dispatch + user authorization Gate L.1.*
