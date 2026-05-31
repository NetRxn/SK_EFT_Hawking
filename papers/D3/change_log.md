# Bundle D3 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-31 — Stage-13 finding remediation: 🔴 RED → 🟢 GREEN

Closed the 5 pre-existing blocker-class findings holding D3 at RED (CitationIntegrity / NarrativeGrounding on source papers paper22, paper36; never recorded in the supersession ledger):

- **`…paper22_ew_phase_transition:1.2` (×3 review rounds, CitationIntegrity major):** FIXED — `doi_verified` flipped None→True for CsikorFodorHeitger1999, KLRS1996, ButtazzoEtAl2013, ShaposhnikovWetterich2010 after **Crossref API** verification (title+author+year match).
- **`…paper36_center_symmetry:1.4` (CitationIntegrity major):** FIXED — `doi_verified` flipped for Polyakov1978, SvetitskyYaffe1982, PelissettoVicari2002, KovtunSonStarinets2005, KitaevAnyons2003 (Crossref-verified); KosPolandSimmonsDuffin2016 + HofmanIqbal2018 already verified.
- **`…paper36_center_symmetry:4.1` (NarrativeGrounding major):** FIXED — QGP η/s ≈ 0.10–0.20 value grounded by registering Crossref-verified primary source `HeinzSnellings2013` (Annu. Rev. Nucl. Part. Sci. 63, 123 (2013)); the notebook already attributes it.

All recorded in `docs/review_finding_supersessions.json`. Post-remediation: D3 open=5 (all minor), blockers=0 → 🟢 GREEN.

## 2026-05-04 — Lift-letter from `paper25_gravitational_waves` (§6)

- Source title: GW170817 vs vestigial graviton
- Lift action: Lift-letter
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: GW170817 vestigial-graviton falsification (cross-bridge to L1 already GREEN); same numerical Δc/c constraint

## 2026-05-04 — Lift-section from `paper3_gauge_erasure` (§3)

- Source title: Gauge erasure
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper5_adw_gap` (§4)

- Source title: ADW gap equation
- Lift action: Lift-section
- Insertion point: §4
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper23_linearized_efe` (§5)

- Source title: Linearized EFE + FLRW
- Lift action: Lift-section
- Insertion point: §5
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-letter from `paper27_bh_thermodynamics_four_laws` (§8)

- Source title: BCH four laws by regime
- Lift action: Lift-letter
- Insertion point: §8
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper26_bh_entropy` (§9)

- Source title: BH entropy from MTC counting
- Lift action: Lift-section
- Insertion point: §9
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper44_riemannian_connection` (§22.5)

- Source title: Lorentzian metric typeclass + Levi-Civita Christoffel uniqueness + full coord...
- Lift action: Lift-section
- Insertion point: §22.5
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper40_higher_curvature` (§16)

- Source title: Higher-curvature Stelle-basis structure at order a₄
- Lift action: Lift-section
- Insertion point: §16
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper42_nonlinear_efe` (§17)

- Source title: Variational nonlinear EFE Decision Gate biconditional + multi-channel PPN
- Lift action: Lift-section
- Insertion point: §17
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper41_diff_invariance` (§18)

- Source title: Nonlinear diff invariance order-by-order
- Lift action: Lift-section
- Insertion point: §18
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper39_heat_kernel_expansion` (§15)

- Source title: Heat-kernel a₀, a₂, a₄ from Christensen-Duff Dirac
- Lift action: Lift-section
- Insertion point: §15
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper22_ew_phase_transition` (§13)

- Source title: EW phase transition
- Lift action: Lift-section
- Insertion point: §13
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper33_ewbg_chirality_wall` (§13.5)

- Source title: EW baryogenesis ↔ chirality wall
- Lift action: Lift-section
- Insertion point: §13.5
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper20_scalar_rung` (§11)

- Source title: Scalar rung
- Lift action: Lift-section
- Insertion point: §11
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper21_majorana_rung` (§12)

- Source title: Majorana rung
- Lift action: Lift-section
- Insertion point: §12
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper36_center_symmetry` (§19)

- Source title: Confinement
- Lift action: Lift-section
- Insertion point: §19
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper37_chiral_ssb` (§19.5)

- Source title: Chiral SSB / GMOR
- Lift action: Lift-section
- Insertion point: §19.5
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper38_cfl` (§19.7)

- Source title: CFL color-flavor locking
- Lift action: Lift-section
- Insertion point: §19.7
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper35_qec_holography` (§9.5)

- Source title: QEC-Holography bridge
- Lift action: Lift-section
- Insertion point: §9.5
- Stage-13 redo required: yes
- Notes: Phase 7c stub

## 2026-05-04 — Lift-section from `paper42b_cc_emergent` (§21)

- Source title: Cosmological constant in emergent form
- Lift action: Lift-section
- Insertion point: §21
- Stage-13 redo required: yes
- Notes: Cosmological-constant reproduction; Phase 7c stub

## 2026-05-04 — Lift-section from `paper43_einstein_cartan` (§22)

- Source title: Einstein-Cartan torsion from ADW spin current
- Lift action: Lift-section
- Insertion point: §22
- Stage-13 redo required: yes
- Notes: Einstein-Cartan torsion; Phase 7c stub

## 2026-05-06 — Lift-section from `_phase6n_W1a_lean_only` (§6)

- Source title: BEC SK-EFT geometric envelope (NOT Gevrey-1)
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W1a transport NO-GO landscape (substrate IS geometric envelope, not Gevrey-1; decouples asymptotic verdict from explicit γ_2^(loop))

## 2026-05-06 — Lift-section from `_phase6n_W2c_lean_only` (§3)

- Source title: LDP linear-response framework
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2c Crooks-on-analog-Hawking entry-point + W-form GC structural anchor + IsLDPRateFunction abstract

## 2026-05-06 — Lift-section from `_phase6o_W1a_lean_only` (§3)

- Source title: Boostless / Carrollian soft-theorem program: `SoftTheorems/Boostless.lean` (I...
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1a analog-horizon Strominger triangle closure + ADW graviton subleading factor with Goldstone-broken-boost content

## 2026-05-06 — Lift-section from `_phase6o_W1b_lean_only` (§6)

- Source title: G4 Kerr-Schild double-copy on Petrov-D analog gravity
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1b vestigial-graviton landscape: Kerr-Schild double-copy on Petrov-D acoustic + 3-obstruction strong-form BCJ NO-GO theorem-pair

## 2026-05-06 — Lift-section from `_phase6o_W3b_lean_only` (§6)

- Source title: I3 Itô + LDP-α + LDP-β substrate (`Itô/StochasticIntegral.lean` + `Itô/Quadra...
- Lift action: Lift-section
- Insertion point: §6
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W3b Itô-time form W-form GC + Glorioso-Liu monotonicity cross-bridge via LDPCompatibleSKEFT typeclass

## 2026-05-06 — Lift-section from `_phase6o_W1c_writeup` (§10)

- Source title: G1 NO-GO writeup at `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`...
- Lift action: Lift-section
- Insertion point: §10
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W1c G1 NO-GO writeup (parallel to 6n.η) — 3 structural obstructions: unitarity→KMS replacement breaks EFT-positivity; crossing has no doubled-contour analog; SDP feasibility breaks on complex contour

## 2026-05-06 — Lift-section from `_phase6o_W2a_lean_only` (§17)

- Source title: APS-η for analog horizons
- Lift action: Lift-section
- Insertion point: §17
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6o W2a heat-kernel APS-η substrate cross-bridge (BEC + ADW parity-symmetric → η = 0; ³He-A non-degenerate cell → substantive APS boundary correction)

## 2026-05-11 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event for Stage-13-sweep freshness cleanup)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-11 Stage-13-sweep freshness cleanup: paper40_higher_curvature tables (c_riem_anchor_at_Nf_27.tex, c_riem_pulsar_orders_below.tex) regenerated at 12:56. D3 bundle paper_draft.tex does NOT \input source paper tables; bundle compile path unaffected. No bundle content change required; last_lift bumped.

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 first-claim-removal: paper5_adw_gap conclusion ('first such derivation in the published literature' removed), paper20_scalar_rung abstract + conclusion rewritten to descriptive + prior-art paragraph reframed as 'Relation to existing libraries' (kept the survey content, dropped 'no prior formalization' framing), paper44_riemannian_connection signature-falsifier wording softened.

## 2026-05-31 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Freshness-bookkeeping (LATE_PHASE6_ABSORPTION_PROTOCOL §3d case 1): source-paper mtime drift is ENTIRELY from auto-regenerated tables/*.tex artifacts (verified: the only files newer than last_lift in each stale source are tables/*.tex; every source paper_draft.tex mtime is OLD <= last_lift; git status clean so regenerated tables match committed content byte-for-byte = zero content change). Bundle compile path is decoupled: this bundle \input's only ../../docs/counts.tex, never any source-paper tables/ dir. No content lift warranted; no Stage-13 redo; reviewer triple remains valid (bundle stays GREEN).
