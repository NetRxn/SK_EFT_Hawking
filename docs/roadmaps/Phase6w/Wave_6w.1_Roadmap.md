# Wave 6w.1 — Kibble-Zurek-Unruh bridge (foundation)

**Phase:** 6w (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate)
**Wave:** 6w.1 (foundation; lifted from former Phase 6v.7 per D-8)
**Status:** ✅ SHIPPED 2026-05-26 PM (Stage 1 + Stage 2 + Stage 3 + Stage 5 + Stage 7 + Stage 10 + Stage 12 complete; Stage 13 deferred to Wave 6w.7 consolidated Phase-6w sweep)
**Owner:** autonomous-loop session(s).
**Bundle target:** D1 + E1 + E2 reinforcement (cross-bridge only; no new bundle).
**LoE:** 2-3 sessions per Phase6w_Roadmap.md; foundation-only — does NOT build new TN substrate (that lives in 6w.2 + 6w.4).

---

## Goal

Ship the foundation theorem `surface_gravity_bounds_kzm_exponent` in a new
Lean module `lean/SKEFTHawking/KibbleZurekUnruh.lean`. The theorem
substantively encodes the Kibble-Zurek-Unruh correspondence: the SK-EFT
surface gravity `κ` at an analog horizon controls the effective KZM
quench rate experienced by a horizon-crossing wavepacket, and via the
WKB modified-unitarity result from `WKBConnection.lean` the surface
gravity bounds the KZM defect-density scaling that classical
tensor-network methods (Tindall, Mello, Fishman, Stoudenmire, Sels —
Science 392, 868 (2026), DOI 10.1126/science.adx2728) extract on
disordered TFIM spin glasses.

This wave produces the *foundation* theorem only. The deeper
substrate-shaping waves (6w.2 BP-on-TN substrate; 6w.3 LDP-controlled
simulability A1a; 6w.4 Chebyshev TN + aperiodic substrate; 6w.5
categorical↔real-space Chern bridge A1b; 6w.6 combined demarcation A1c)
follow.

## Substantive deliverables

1. **New Lean module** `lean/SKEFTHawking/KibbleZurekUnruh.lean`:
   - `KZMExponents` structure (correlation length exponent `ν > 0`, dynamic exponent `z > 0`).
   - `kzmScalingExponent (e : KZMExponents) : ℝ := (e.ν * e.z) / (1 + e.ν * e.z)` — closed-form universal scaling.
   - Substantive lemma `kzmScalingExponent_pos` (defect density does scale).
   - Substantive lemma `kzmScalingExponent_lt_one` (defect density does not scale faster than τ_Q^{-1}).
   - `KZMUnruhBridge` structure linking an `ExactWKBParams` (from `WKBConnection.lean`) to a `KZMExponents`.
   - `kappaToInverseQuenchRate (br : KZMUnruhBridge) : ℝ := br.wkb.kappa` — the bridge identification 1/τ_Q ≡ κ.
   - `kzmThermalOccupation`: the KZM-Unruh correspondence reproduces Hawking T_H = κ/(2π) (in natural units, matching `hawkingTemp` from `Basic.lean`).
   - Substantive lemma `kzm_unruh_thermal_matches_hawking`: combines the KZM bridge with the existing `hawkingTemp` definition.
   - **Headline theorem** `surface_gravity_bounds_kzm_exponent`: the WKB modified-unitarity result (`|α|² − |β|² = 1 − δ_k` with `δ_k = 2 Γ_H / κ`) provides a closed-form quantitative upper bound on the KZM defect-density compatible with finite Hawking radiation: under the bridge, the dissipative correction `δ_k ≤ 1` bounds the KZM defect density at horizon-crossing rate `κ` by `1 - δ_k`, giving a falsifiable cross-check between the Tindall/Sels KZM-exponent extraction and the SK-EFT dissipative prediction.
   - Optional secondary lemma `kzm_extraction_consistent_with_skeft_iff_low_dissipation` — bridge between low-dissipation regime and standard KZM scaling holding.

2. **Citation registration**:
   - New bibkey `TindallMelloFishmanStoudenmireSels2026Science392` in `src/core/citations.py::CITATION_REGISTRY` with DOI `10.1126/science.adx2728`, arXiv `2503.05693`, full author list, journal `Science 392, 868-872`, primary_source_path resolving to the cached PDF + JSON.
   - Primary source cached at `Lit-Search/Phase-6w/primary-sources/TindallMelloFishmanStoudenmireSels2026Science392.{pdf,json,abstract.txt}` (✅ DONE 2026-05-26 PM).

3. **Bundle citation passes** (D1 + E1 + E2):
   - D1 paper draft: brief paragraph in §"Analog Hawking universality" subsection citing the KZM-Unruh foundation theorem and Tindall/Sels as independent classical-simulation validation of the universal critical-scaling that underlies the Hawking universality theorem.
   - E1 paper draft: brief paragraph in §"Polariton experimental setup" or discussion noting that the KZM-Unruh correspondence places the polariton analog-Hawking experiment in the universality class extracted by Tindall/Sels.
   - E2 paper draft: brief paragraph in §"Graphene Dirac-fluid platform" with the same cross-validation framing.

4. **Pipeline integration**:
   - Add `KibbleZurekUnruh` to the root `lean/SKEFTHawking.lean` imports.
   - `lake build SKEFTHawking.KibbleZurekUnruh` must be clean (zero sorry, zero new axioms).
   - `update_counts.py` regeneration to bump theorem / module count.

## Acceptance criteria (Wave 6w.1)

- ✅ Headline theorem substantively shipped (no trivial/identity-wrapper proof; no P3/P4/P5 anti-pattern; substantive content combines KZM scaling structure + WKB modified unitarity).
- ✅ Module builds clean; zero new project-local axioms.
- ✅ Primary source cached per Invariant #11.
- ✅ D1 + E1 + E2 paragraph additions present and consistent with the formal theorem.
- ✅ `validate.py --check citation_primary_sources_present` passes.
- ✅ Preemptive-strengthening 5-question checklist applied to every theorem statement.
- ✅ Post-wave audit ruthlessly identifies any P-pattern survivors and fixes them before declaring SHIPPED.

## Stage-by-stage execution

- **Stage 1 (Constants + provenance):** No new physical constants — KZM exponents `ν`, `z` are universal critical-exponent data carried as theorem parameters. Bibkey + primary-source cache: ✅ DONE.
- **Stage 2 (Formulas):** No new physics formulas — the KZM exponent `μ = νz/(1+νz)` is a closed-form universal-scaling identity; the bridge `1/τ_Q ≡ κ` is a kinematic identification. Document in the module docstring with citation provenance only.
- **Stage 3a (Lean interactive):** Author `KibbleZurekUnruh.lean` via MCP loop. Decompose any non-trivial proof into ≤12-term `have` sub-lemmas before iterating.
- **Stage 3b/4 (Sorry/Aristotle):** Not expected — theorem is closed-form algebra over a finite structure.
- **Stage 5 (Lean build):** `lake build SKEFTHawking.KibbleZurekUnruh` clean; counts regen.
- **Stage 6-8 (tests, validation, viz):** No Python tests for this wave (no numerics shipped). `validate.py` PASS.
- **Stage 10 (Paper drafts):** D1/E1/E2 paragraph additions.
- **Stage 12 (Doc sync):** Inventory Index §3 + §4 add `KibbleZurekUnruh.lean`; PAPER_DRAFT_MAPPING.md row for `_phase6w_W1_lean_only`.
- **Stage 13 (Adversarial review):** Deferred to Wave 6w.7 (Phase-6w end-of-phase consolidated Stage-13 sweep).

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Substrate: `lean/SKEFTHawking/Basic.lean::hawkingTemp`, `lean/SKEFTHawking/WKBConnection.lean::ExactWKBParams`, `lean/SKEFTHawking/HawkingUniversality.lean`
- Tindall/Sels arXiv: 2503.05693 (preprint); Science DOI 10.1126/science.adx2728 (journal version)
