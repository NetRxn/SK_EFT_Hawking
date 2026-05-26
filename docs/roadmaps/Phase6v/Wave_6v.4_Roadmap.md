# Wave 6v.4 — Penn TMD polariton regime demarcation

**Bundle target:** E1 §2 (Paris-LKB polariton paper) — additive scope demarcation paragraph.

**Status:** ✅ SHIPPED 2026-05-26 (commits `9e99ab1` Stage 1; final commit Stage 3a/5/6/7/10/12).

**Source paper (canonical, primary-source cached):**
Z. Wang, B. Kim, B. Zhen, L. He, "Strongly nonlinear nanocavity exciton-polaritons in gate-tunable monolayer semiconductors," **Phys. Rev. Lett. 136, 146901 (2026)** — Editor's Suggestion + cover article. arXiv:2411.16635 (submitted 2024-11-25). DOI: `10.1103/gc15-qsvf`. Primary-source cache: `Lit-Search/Phase-6v/primary-sources/WangKimBZHe2026PennTMDPolariton.pdf`. Bibkey: `WangKimBZHe2026PennTMDPolariton`.

**Wave goal.** Add the UPenn nanocavity-polariton MoSe₂ platform to `POLARITON_PLATFORMS`, ship its parameter provenance entries, and prove a small Lean theorem demarcating it as **outside** the Tier 1 perturbative-dissipation patch validity domain. The result is a *positive scope statement* for E1: Tier 1 covers Paris-LKB / GaAs polariton fluids in the smooth-horizon regime; it does NOT cover ultrafast TMD-polariton nanocavities like the UPenn device, where the lower-polariton linewidth (γ_LP = 1.8 meV ≈ 2.74 × 10¹² s⁻¹) so dominates any plausible analog-horizon surface gravity that `Γ_pol/κ ≫ 0.1`.

## Key parameters from the source paper (LLM-verified against arXiv full text 2026-05-26)

| Symbol | Value | Unit | Source location | Notes |
|---|---:|---|---|---|
| g (exciton-photon coupling) | 16.8 | meV | "Based on the coupled oscillator model, we estimate the exciton-photon coupling strength in the charge-neutral regime is g=16.8 meV" | Vacuum Rabi coupling. |
| γ_LP (lower-polariton linewidth) | 1.8 | meV | "The measured linewidths are 2.3 meV for the UP state and 1.8 meV for the LP state." | Sets `Γ_pol = γ_LP / ℏ`. |
| γ_UP (upper-polariton linewidth) | 2.3 | meV | same sentence | Cross-check. |
| γ_cav (cavity linewidth) | 1.9 | meV | "the radiative coupling to the waveguides on both sides (γ_rad∼0.7 meV) and optical loss due to scattering from fabrication disorders and material absorption (γ_nonrad∼1.2 meV)" | At resonance energy 1.736 eV. |
| Q (cavity Q-factor) | ≈ 914 | dimensionless | derived: 1.736 eV / 1.9 meV | |
| τ_photon | ≈ 348 | fs | derived: ℏ/γ_cav | |
| switching energy | ≈ 4 | fJ | "all-optical switching of the cavity spectrum at an energy level as low as ∼4 fJ" | On picosecond timescales. |
| TMD material | MoSe₂ monolayer | — | "charge-tunable MoSe₂ monolayer" coupled to "planar photonic crystal nanocavity" | |

**Derived quantities for the Tier-1 demarcation argument:**
- `Γ_LP ≡ γ_LP/ℏ = 1.8e-3 eV × (1.602176634e-19 J/eV) / 1.054571817e-34 J·s ≈ 2.735 × 10¹² s⁻¹`.
- For *any* analog-horizon κ comparable to the Falque-smooth-horizon scale `κ ≈ 7 × 10¹⁰ s⁻¹` (the actual measured LKB Paris value, the highest-leverage prior data point in the polariton family), the validity ratio is `Γ_LP/κ ≈ 39.1 ≫ 0.1`. This is `>> 1`, placing the platform in the "intractable" Tier-1 regime of `constants.py:tier1_regime`.
- Even at the steep-horizon Falque maximum `κ ≈ 1.1 × 10¹¹ s⁻¹` (`FALQUE_STEEP_HORIZON_KAPPA`), the ratio is `Γ_LP/κ ≈ 24.9`, still `>> 0.1`.
- Conclusion: the UPenn nanocavity-polariton platform is OUTSIDE Tier 1 validity for *any* analog-horizon configuration one could imagine building from this type of device. This is a positive scope demarcation for E1 — Tier 1 covers GaAs / Paris-LKB long-lifetime polaritons, NOT TMD ultrafast nanocavities.

## Deliverables (14-stage pipeline)

| Stage | Action | Status |
|---:|---|:---:|
| 1 | (a) Add `WangKimBZHe2026PennTMDPolariton` bibkey to `CITATION_REGISTRY`. (b) Add `Penn_TMD_MoSe2` to `POLARITON_PLATFORMS` in `src/core/constants.py`. (c) Add 8 provenance entries to `PARAMETER_PROVENANCE` (g_meV, γ_LP_meV, γ_UP_meV, γ_cav_meV, Q_factor, switching_energy_fJ, tau_cav, derived Γ_pol). (d) Confirm primary-source cache file exists. | ✅ SHIPPED |
| 2 | (skipped) No new formula helper needed — `tier1_valid` post-processing already in `POLARITON_PLATFORMS` loop. | SKIP |
| 3a | Ship Lean theorems `polariton_tier1_fails_tmds` + `polariton_tier1_predicate_fails_tmds` in `lean/SKEFTHawking/PolaritonTier1.lean`. Construct `pennTmdPolaritonParams` using exact rationals `Γ_pol = 27347 × 10⁸` and `κ = 11 × 10¹⁰` (Falque steep-horizon max as the most generous κ), prove `1/10 ≤ Γ_pol/κ` via `norm_num`. Kernel-only (no axioms, no tracked Props). MCP diagnostic clean; file-level `lake env lean` clean. | ✅ SHIPPED |
| 3b | (not needed) — 3a closed via direct `norm_num` discharge; no sorry stub. | SKIP |
| 4 | (not needed) — Aristotle fallback not invoked. | SKIP |
| 5 | `lake env lean SKEFTHawking/PolaritonTier1.lean` clean (exit 0); full project `lake build` deferred to end-of-phase since module diff is local + MCP diagnostic returns zero errors. | ✅ SHIPPED (file-gate) |
| 6 | Add `tests/test_polariton_tier1_tmds.py` regression (16 tests). All PASS: registration, source-of-truth params, derived Γ_pol matches ℏ-conversion, validity-ratio at steep + smooth κ, intractable tag, 8 provenance entries LLM-verified, bibkey present, primary source cache file present. | ✅ SHIPPED |
| 7 | `validate.py --check parameter_provenance` PASS (205 params, all LLM-verified). `validate.py --check citation_primary_sources_present` PASS (416 bibkeys / 288 cached / 30 inprep-exempt / 98 textbook-exempt / 0 missing). `validate.py --check paper_provenance` PASS. `validate.py --check provenance_doi_in_registry` PASS. | ✅ SHIPPED |
| 8 | (not needed) — No new figures. | SKIP |
| 9 | (not needed) — No new figures. | SKIP |
| 10 | E1 §2 "Scope demarcation" paragraph added to `papers/E1/paper_draft.tex` citing Wang et al. 2026 with Eq. \\eqref{eq:gamma_lp_penn} (Γ_LP ≈ 2.735×10¹² s⁻¹), the Γ_LP/κ_max ≈ 24.86 calculation, and a direct reference to the Lean theorem `polariton_tier1_fails_tmds`. New bibitem entry added to thebibliography. 2-pass `pdflatex` clean (4 pages, 415 KB PDF). | ✅ SHIPPED |
| 11 | (not needed) — No new notebooks. | SKIP |
| 12 | (a) `Phase6v_Roadmap.md` wave-status updated to ✅ SHIPPED. (b) This per-wave roadmap finalized. (c) Phase-level stakeholder docs (`Phase6v_Implications.md` + `Phase6v_Strategic_Positioning.md`) DEFERRED to Phase 6v close per project convention (per-phase not per-wave; see `Phase6q_Implications.md` precedent). (d) Inventory_Index update DEFERRED to Phase 6v close per cross-agent coordination boundary. | ✅ SHIPPED (per-wave portion) |
| 13 | Stage 13 adversarial review — DEFERRED to end of Phase 6v per user directive (single Phase-6v-close adversarial pass). | DEFERRED |
| 14 | QI — no systemic findings identified in this wave. | ✅ NO-FINDINGS |

## Substrate touched (planned)

- **New files:** none (all extensions to existing modules).
- **Modified Python:** `src/core/constants.py`, `src/core/citations.py`, `src/core/provenance.py`, `src/core/formulas.py` (small helper), new `tests/test_polariton_tier1_tmds.py`.
- **Modified Lean:** `lean/SKEFTHawking/PolaritonTier1.lean` (+1 platform record def + 1 theorem; ~30 LoC).
- **Modified paper:** `papers/E1/paper_draft.tex` §2 (one paragraph + cite).
- **New stakeholder:** `docs/stakeholder/Phase6v_Wave6v.4_Implications.md`, `Phase6v_Wave6v.4_Strategic_Positioning.md`.
- **Primary-source cache:** `Lit-Search/Phase-1-and-Background/primary-sources/WangKimBZHe2026PennTMDPolariton.pdf` (1.15 MB, downloaded 2026-05-26). Phase-1-and-Background is the canonical home for bundle-cited bibkeys (per the `bibkey_phase` FALLBACK; bundle keys are not yet registered in `PAPER_TO_PHASE`). The initial Phase-6v/primary-sources/ placement was reverted to align with this convention.

## Cross-wave dependencies

- **Predecessors:** none — Wave 6v.4 is the warmup; no Phase-6v wave dependency.
- **Successors:** Wave 6v.3 (DKM F3 polariton occupancy bound) benefits from this wave's parameter pass — the Penn TMD record is one of the platforms the DKM F3 axiom will be evaluated against.
- **Bundle absorption:** E1 §2 absorbs additively (Branch D.2 of the absorption protocol is not needed — E1 is currently GREEN with one minor advisory; this is a pure additive scope-paragraph lift).

## No-axiom discipline

Per Pipeline Invariant #15: **zero new project-local `axiom` declarations** in this wave. The Lean theorem ships as a direct algebraic consequence of `validityRatio` definition + a `norm_num` discharge of `Γ_LP / κ_max ≥ 0.1`. No tracked Props introduced.
