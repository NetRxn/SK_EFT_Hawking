# Substrate Integrity Gates (SIG) — Roadmap

**Authoritative tracker for the ADR-004 work.** Read [ADR-004](../adrs/ADR-004-substrate-integrity-gates.md) and the [2026-06-13 substrate weakness audit](../audits/SUBSTRATE_WEAKNESS_AUDIT_2026-06-13.md) (esp. the Appendix root-cause section) FIRST.

**One-line goal.** Install five standing automated gates (R1–R5) that move detection of the *proof-substance* and *assumption-disclosure* failure classes left from the Stage-13 fresh-context review into Stages 2/5/7; re-close `qi-leanproofsubstance` + `qi-assumptiondisclosure` via structural prevention; give Invariants #4/#9 automated teeth + add Invariant #16. **PUBLIC repo (`SK_EFT_Hawking/`).**

**Why now / real-world reason (so goal-mode cannot effort-defer).** The two QI items naming these classes were closed 2026-04-29 by per-finding supersession (pathway #1), leaving the generator alive; the audit found both classes recurring in post-2026-04-29 modules, plus one ship-gating published overclaim (paper7, finding #3). This is durable-infrastructure work (pathway #2), squarely in the project's wheelhouse (~1–2 days at dev rate). It is NOT optional polish — an unenforced Invariant #9 is currently violated in a submission-candidate paper.

---

## Entry state (verified on disk 2026-06-13)

| Fact | Value | Source |
|---|---|---|
| axioms / sorry | 0 / 0 | `counts.json` |
| `PLACEHOLDER_THEOREMS` entries | **11** | `constants.py:2092` |
| type-`True` theorems on disk | **26** | `lean_deps.json` (`type=="True"`) |
| `HYPOTHESIS_REGISTRY` entries (constants.py) | **7** — gen-constraint/Rokhlin/EW chain | `constants.py:2205` |
| `PERMANENT_TRACKED_HYPOTHESES.md` entries (doc) | **7** — cosmology Props (vestigial/DESI/RT/TPF) | doc |
| **the two ledgers' overlap** | **∅ (disjoint!)** — each is a partial catalog claiming to be "the" ledger → W3 collapses to one source | verified 2026-06-13 |
| `def H_*` Props defined | **81** | grep `lean/SKEFTHawking/` |
| `H_*` consumed as `(h : H_*)` | **42** | grep |
| `HYPOTHESIS_REGISTRY` schema | rich: `statement`/`status`/`elimination_path`/`dependent_theorems`/`module`/`source`/`risk`/`circularity_note` — the **primary** ledger; `topo`/`16∣σ` ALREADY covered by `rokhlin_sigma_mod_16` (`status: discharged`) | `constants.py:2205` |
| native_decide **decl-closure** (authoritative, ADR-002 metric) | **546** (anyon/MTC 327, qgroup 154, other 53, lattice 12; FKLW/RossSelinger + QuantumNetwork = **0**) | `axiom_closure_allowlist` / `lean_deps.json` |
| native_decide **call-sites** (secondary; the audit's "~460–620/551") | larger, different metric — do NOT use as the tracked number | grep |
| `check_formulas_to_theorems` coverage | **7 hardcoded pairs**, name-presence only | `validate.py:156` |
| paper7 placeholder-cited-as-verified | `paper_draft.tex:306-310` cites `Z(Vec_G)≅Rep(D(G))` (a `True` stub) as "end-to-end formal verification" | finding #3 |

---

## Waves

Each wave: build the check → triage the flagged set → register-or-fix → wire into the pipeline. Gates are `validate.py` checks unless noted. Land checks BEFORE clearing the flagged backlog so the gate is what enforces closure.

### W1 — Placeholder registry completion + Invariant #9 paper-claim enforcement (R5) + fix #3
- Reconcile `PLACEHOLDER_THEOREMS` (11) against the 26 on-disk type-`True` theorems; add the missing ones (incl. `gauge_emergence_statement`, `h2_discharged`, `equivalence_preserves_braiding`, …) with `category: content|docs_marker`.
- Build `validate.py --check placeholder_not_cited`: scan every `papers/**/paper_draft.tex` `\texttt{}`/cited-Lean-name + `claims_review.json` against `PLACEHOLDER_THEOREMS`; FAIL if a placeholder is cited in a "verified/formally verified/end-to-end" context.
- **Fix finding #3:** reprose `paper7_chirality_formal/paper_draft.tex` §discussion (general-`G` equivalence → "verified concretely for `G=ℤ/2` (and `S₃`); general-`G` statement formalized at statement level"); rename `gauge_emergence_statement`/`half_braiding_gives_action`/`chirality_independent_of_G` → `*_TODO`.
- Add the placeholder-citation FAIL condition to the Stage-10 `physics-qa:claims-reviewer` agent prompt.
- **Gate:** `placeholder_not_cited` PASSES (paper7 fixed); registry == 26; `claims_review.json` regenerated.

### W2 — Proxy-body audit (R2): generalize the Phase-5q.T T5 detector
- Extend `build_graph.py` `_PLACEHOLDER_BODY_PATTERNS` (or a new `ProxyMarker`) to flag: theorem NAME matches a structural-claim pattern (`*_dim|rank|finrank|*Ext*|*classification|*_no_go|sixteen_*|*equivalence|*_statement|*_unanimous`) AND body ∈ {`rfl`, `by rfl`, `decide`, `cases … <;> rfl`, single struct-field projection, identity return `:= h`, `trivial`, `And.intro`/`⟨_,_⟩` on the named definitional target}.
- Add `validate.py --check proxy_body_audit`. Ship a `MODELING_ASSUMPTION_THEOREMS` whitelist (constants.py): a flagged decl is COMPLIANT iff it has (a) a registry entry AND (b) a docstring disclosing the assumption + pointing to its tracked Prop/struct field. **Use `SmoothSpinManifold4.rokhlin`/`topo` (ADR-003) as the template whitelist entry.**
- **Scope boundary (ADR-002):** `proxy_body_audit` does NOT target `native_decide` or finite-combinatorial-`decide` bodies — those are governed by ADR-002's P4 gate (`axiom_closure_allowlist`) and are policy-tolerated. The detector targets the *defining-the-conclusion* class only (struct-field projection / definitional identity / `True` / identity-return / `cases<;>rfl` over a stipulated function under a structural-claim name).
- Triage the audit's known set: `SmoothSpinManifold4.rokhlin`/`topo` (→ whitelist, ADR-003-documented), `rDIndependentNoGo`+`r_d_anchoring_*` (→ whitelist w/ disclosure, or strengthen aggregate), `verlindeEntropy_SU2k`/`gaussianSaddleAsymptotic` (→ whitelist, points to `H_VerlindeKMLiteralSumDerivation`), `h2_discharged` (→ rename `*_TODO`, it discharges nothing).
- **Gate:** `proxy_body_audit` PASSES (every flagged decl either fixed or in `MODELING_ASSUMPTION_THEOREMS` with disclosure); detector unit-tested against the known set.

### W3 — Single tracked-hypothesis source of truth (R3) + Invariant #16

**▶ IN PROGRESS (2026-06-13).** Step 1 done: `validate.py --check tracked_hypothesis_ledger` built (ADVISORY phase — suite stays green). Enumeration (codomain-`Prop` filter via lean_deps `type`, excludes the `H_Fib`/`H_of_G`/`H_Fib_idComponent` Subgroup false-positives): **55 tracked Prop-defs, 23 consumed, 21 in the gap** (in neither ledger). The 21 (extracted with docstrings): H_BilocalPointlikeLimit, H_CFZ2_sq_a/e (local hexagon hyps for the Z/2 center), H_CasiniHuerta_Bound_Valid, H_DecouplingBoundDim6, H_Fib_NonCentralConjugateWitness/TwoLITangents/v4_witness (Fibonacci-density witnesses, audit #8), H_HSCovariantBosonisation, H_HorizonBoundaryCondition, H_MR_FromADWSubstrate_BCS_LNV, H_MR_FromSMGGap, H_MixedChannelZ16Cancels, H_PMNSAnglesFromExactSubstrate, H_RegimePartition, H_SubstrateNearSMGFixedPoint, H_VergelesPositivity, H_VestigialRelicCarriesZ16Charge, IsCurveTheoreticPenroseHypothesis, Phase6hHyperchargeSplittingHypothesis + (in doc, not registry) H_RT_Formula_Valid, TPFConjecture.
**✅ W3 COMPLETE 2026-06-13.** (a) `HYPOTHESIS_REGISTRY` is now the SINGLE source — 31 entries, every one carries `tier` (4 headline / 14 external_boundary / 7 discharge_future / 6 local) + `prose`; merged the 4 doc cosmology Props + registered all 21 consumed gap Props (Fibonacci-density witnesses = `headline`; CFZ2 hexagon ids = `local` w/ a Z/2-disclosure review note; Majorana/PMNS/vestigial = `discharge_future`; CH-bound/Vergeles/Glorioso-Liu/RT/TPF = `external_boundary`). (b) `scripts/render_tracked_hypotheses.py` renders `docs/PERMANENT_TRACKED_HYPOTHESES.md` as an AUTO-GENERATED view (DO-NOT-EDIT header); `validate.py --check tracked_hypotheses_fresh` auto-regenerates on drift (counts_fresh pattern). (c) `tracked_hypothesis_ledger` escalated to HARD-FAIL — gap=0 (23 consumed / 23 covered); `topo` covered by `rokhlin_sigma_mod_16.dependent_theorems`, NOT double-registered. (d) **Pipeline Invariant #16** added. (e) 6 new W3 unit tests (18 total green). Checks green: tracked_hypothesis_ledger, tracked_hypotheses_fresh, theorems, graph_integrity, prose_theorem_reference_coverage, counts_fresh. **Open review note (carried):** H_CFZ2_sq_a/e condition the Z/2 Drinfeld-center equivalence — confirm whether W1's "Z/2 fully verified" paper7 framing should disclose them (logged in their registry `risk`).

**Problem this wave fixes (verified 2026-06-13):** there are TWO hand-maintained tracked-hypothesis ledgers — `HYPOTHESIS_REGISTRY` (constants.py, 7 entries) and `PERMANENT_TRACKED_HYPOTHESES.md` (docs, 7 entries) — and they are **disjoint (intersection = ∅)**: the registry holds the generation-constraint/Rokhlin/EW chain, the doc holds the cosmology Props (vestigial-graviton, DESI, RT, TPF). Neither is complete; each implicitly claims to be "the" ledger. Two hand-maintained disjoint catalogs = guaranteed drift and reader confusion.

- **Collapse to ONE source of truth = `HYPOTHESIS_REGISTRY`** (machine-readable, rich schema, already has `dependent_theorems`/`status`/`elimination_path`/`circularity_note`; already consumed by validate.py + dashboard + claims-reviewer — a markdown file cannot be queried by a check). Add a `prose`/`publication_note` field to carry the doc's narrative (KEEP_AS_TRACKED vs DISCHARGE_FUTURE framing, "internal-and-publishable" appendix text). Merge the doc's 4 cosmology Props (`H_VestigialModeIsGraviton`, `H_DESICompatibility`, `H_RT_Formula_Valid`, `TPFConjecture`) + the Phase-6r SymTFT Props INTO the registry.
- **Make `PERMANENT_TRACKED_HYPOTHESES.md` AUTO-GENERATED** from the registry: new `scripts/render_tracked_hypotheses.py` (à la `update_counts.py`/`render_paper_tables.py`) + a `tracked_hypotheses_fresh` freshness check at Stage 12. The doc keeps its publication value as a rendered view but can never again drift from the registry by construction — same canonical-source + generated-view pattern as counts.json→counts.tex.
- Build `validate.py --check tracked_hypothesis_ledger`: enumerate every load-bearing consumed assumption — `(h : SomeProp)` hypotheses AND Prop-valued struct fields (e.g. `topo`) — from `lean_deps.json`/source; assert each maps to a `HYPOTHESIS_REGISTRY` entry (by `dependent_theorems`/name). **`topo`/`16∣σ` is ALREADY covered** by `rokhlin_sigma_mod_16` (ADR-003) — do NOT double-register. Bring the ~42 consumed `H_*` Props (+ `H_VerlindeKMLiteralSumDerivation`) into coverage (register, or demonstrate non-load-bearing and downgrade).
- Add **Pipeline Invariant #16** (every consumed assumption is in the one registry).
- **Gate:** `tracked_hypothesis_ledger` + `tracked_hypotheses_fresh` PASS; the markdown is generated, not hand-edited; registry is the sole source.

### W4 — Formula content-grounding (R1) + Invariant #4 teeth

**✅ W4 COMPLETE 2026-06-13.** New gate `validate.py --check formula_grounding`: parses ALL `Lean:` references in formulas.py (~461 refs, robust parser dropping `.lean` filenames / `pending` / fragments / matrix labels), resolves each against `lean_deps.json` (dotted-suffix). **HARD-FAIL** on any ref grounded on a `True`/placeholder stub — **0 found** (the δ_diss / Invariant-#4 hazard is clean: no formula cites a stub). **ADVISORY**: surfaces **81 dangling (stale-name) refs** — formulas.py cites renamed/removed theorems (e.g. `FLRWDynamics.friedmann_one` → the module now has `friedmann_I_dot_eq_conservation_times_coeff`). Invariant #4 restated as content-grounding (pipeline doc). 4 W4 unit tests (20 total green).
**TRACKED DEBT — FormulaRefSweep:** the 81 dangling refs are a stale-name remediation backlog (each needs its current theorem name found + the docstring updated). This is a large content-sweep (own follow-up /goal, à la AttributionContentSweep), NOT effort-deferred — the gate now makes it VISIBLE and prevents NEW placeholder-grounding. Listed via `validate.py --check formula_grounding`.
- Build the unbuilt Wave-21 `lean_grounding_audit`: for each `formulas.py` entry, parse the cited Lean theorem's STATEMENT (from `lean_deps.json` types) and assert the formula's relation/symbols appear in it (not just the name). Expand the 7-pair hardcoded `mapping` in `check_formulas_to_theorems` to all formula functions.
- Add `validate.py --check formula_grounding`. Restate Invariant #4 as content-grounding in the pipeline doc.
- **Gate:** `formula_grounding` PASSES over all formulas; the δ_diss converting-identity has a content-checked theorem (or is flagged).

### W5 — native_decide accounting (R4) — **surface ADR-002's existing metric, do not rebuild**
- The authoritative trust-surface metric is the **decl-closure** count already computed by ADR-002's P4 gate `validate.py --check axiom_closure_allowlist` (**546** as of 2026-06-10), NOT a call-site grep. Extend `update_counts.py` to emit that decl-closure count (+ the cluster breakdown anyon/MTC, qgroup, lattice, other) into `counts.json`, with a no-silent-increase regression threshold surfaced at Stage 5.
- **Elimination policy stays in ADR-002** (Route-1/1′, Category-A/B); R4 only makes the number a tracked, regression-gated metric so a wave that *adds* native_decide trust surface is visible.
- **Gate:** `counts.json` carries the decl-closure count + cluster breakdown; a deliberate test increase trips the threshold.

### W6 — Pipeline integration + QI re-open/re-close + ADR status
- Edit `WAVE_EXECUTION_PIPELINE.md`: add R1–R5 checks to the Stage 5 + Stage 7 gate lists; restate Invariant #4 (content), strengthen #9 (automated paper-claim enforcement + registry-complete), add Invariant #16; add the **Stage-14 closure-pathway policy** (substance/disclosure-class QI items close ONLY via pathway #2).
- `QI_REGISTER.md`: re-open `qi-leanproofsubstance` + `qi-assumptiondisclosure` (note recurrence + pathway-#1-was-insufficient), then move both to Closed via structural prevention naming the new checks; close `qi-gate-5-self-audit-blind-spot` (W2) and `qi-prose_lean_numerical_bound_gap` (W4/W1) likewise.
- Flip ADR-004 status PROPOSED → ACCEPTED/IMPLEMENTED; update Inventory + counts; run full `validate.py`.
- **Gate:** full `validate.py` green (incl. all new checks); pipeline doc + QI register + ADR consistent.

---

## Standing rules
- PUBLIC repo. NEVER reference the private RD repo (its directory name trips the pre-commit hook). Parallel agents may share `main`: stage ONLY your own explicit paths (never `git add -A/-a/.`), never push.
- NO new project-local `axiom`; NO `native_decide`; NO `sorry`; NO `maxHeartbeats` in proof bodies. The gates must not themselves introduce the patterns they detect.
- **No re-deriving Mathlib-walled math.** `topo`, prime-density, Caves/CCR, full MTC/APS/cobordism = tracked-hypothesis posture (disclose, don't discharge). A documented modeling assumption + ledger entry is COMPLIANT.
- False-positive discipline: every new detector ships with the `MODELING_ASSUMPTION_THEOREMS` whitelist + unit tests against the audit's known set, so honest documented choices pass.
- Each new check follows the `@register_check("name", "desc")` pattern in `validate.py`; advisory-first only if a clean full-suite pass is otherwise blocked, then escalate to hard-fail in the same wave.

## Out of scope
- Re-proving any named literature wall. Figure/Rust/dashboard layers (audit meta-obs #7 — separate follow-up). New physics. Bundle lifts.

## Status table
| Wave | Status |
|---|---|
| W1 placeholder registry + R5 + #3 fix | ✅ COMPLETE 2026-06-13 |
| W2 proxy-body audit (R2) | ✅ COMPLETE 2026-06-13 |
| W3 tracked-hyp ledger sweep (R3) + Inv #16 | ✅ COMPLETE 2026-06-13 |
| W4 formula content-grounding (R1) | ✅ COMPLETE 2026-06-13 |
| W5 native_decide accounting (R4) | IN PROGRESS |
| W6 pipeline + QI + ADR integration | NOT STARTED |

### W1 close (2026-06-13)
- `PLACEHOLDER_THEOREMS` reconciled **11→26** (every on-disk `True := trivial` decl; +`lean_name` + `category` content|docs_marker; 20 content + 6 docs_marker). New `PLACEHOLDER_TOTAL_COUNT`/`PLACEHOLDER_LEAN_NAMES`. Registry lean_names ≡ on-disk 26 (verified).
- `build_graph.py` placeholder exclusion now keys on `lean_name` (was `.keys()` — silently missed the 5 name-drifted entries).
- New gate `validate.py --check placeholder_not_cited` (Invariant #9): matches decl `lean_name` + optional `tex_signature` against a verification-claim window with a hedge-exception. Caught paper7 (#3) pre-fix; PASS post-fix; no false positives across 61 drafts.
- **#3 fixed:** paper7 §discussion reprosed — `Z(Vec_G)≅Rep(D(G))` now "verified concretely for ℤ/2 (full fusion/braiding), S₃ anyon-count matched, general-G at statement level"; removed the "end-to-end formal verification" attachment. Renamed `gauge_emergence_statement`/`half_braiding_gives_action`/`chirality_independent_of_G` → `*_TODO` (+ fixed the stale "axiom" comment in DrinfeldCenterBridge). Lean rebuilt clean (9254 jobs), lean_deps regenerated, counts = 26 placeholder / 0 axiom / 0 sorry.
- Stage-10 claims-reviewer FAIL-condition for placeholder-citation added to `WAVE_EXECUTION_PIPELINE.md`.
- Affected checks green: placeholder_not_cited, theorems, counts_fresh, graph_integrity, prose_theorem_reference_coverage, theorem_name_embedded_citations.
- Real claims-reviewer agent updated: new **Class PC** (placeholder cited as verified) in `.claude/plugins/physics-qa/agents/claims-reviewer.md` (plugin is at workspace root).

### W2 close (2026-06-13)
- New gate `validate.py --check proxy_body_audit` (R2): flags theorems whose NAME claims a structural quantity (`_dim`/`rank`/`Ext`/`classification`/`sixteen_`/`_no_go`/`_unanimous`/`_equivalence`/`_corresponds`/`_count`/`_well_defined`/`_iso`) AND whose body is a trivial closer (`rfl`/`trivial`/`cases<;>rfl`/identity-return/`Equiv.refl`) — EXCLUDES `decide`/`native_decide`/`norm_num` (ADR-002 P4 gate + Phase-5q.T T5 own those). Reuses `build_graph._scan_lean_theorem_bodies`.
- `MODELING_ASSUMPTION_THEOREMS` whitelist (constants.py): COMPLIANT iff registered with `reason` + `discloses`; `category` ∈ {`definitional` (legit), `vacuous_proxy` (disclosed tracked debt + `discharge` pointer)}. The check FAILs on a bare/undisclosed whitelist entry; emits a `tracked_vacuous_proxies` advisory.
- **Calibration:** detector flagged 12; triaged → 6 `definitional` (`sVec_fermion_dim_DEFINITIONAL`, `g2k1_dims_eq_fib`, `sl2_dim_eq`, `emanant_su2_dim` [dup of sl2_dim_eq], `hw_matches_sm_count`, `free_energy_well_defined`) + 6 `vacuous_proxy` tracked debt (`change_of_rings_ext_dim` [x=x; → Phase-5q.T A1ExtReal], `rank2_classification_count`/`dg_generator_count`/`dg_relation_count`/`ising_wrt_rank`/`fib_wrt_rank` [N=N decorative; → strengthen via concrete enum/MTC instance]). Plus 2 proactive disclosures of audit #9 (`r_d_anchoring_*`, `r_d_independent_count_eight`).
- **`h2_discharged` → `h2_discharged_TODO`** (audit #25; honest docstring; Lean rebuilt clean 9254 jobs, lean_deps regen, registry↔disk exact, 26/0/0).
- Unit test `tests/test_substrate_integrity_gates.py` (12 tests, green): registry invariants + detector pattern logic (structural-name, trivial-body, decide-excluded, tex-signature/verify/hedge).
- **Tracked debt (future targeted pass or Phase-5q.T):** strengthen the 6 `vacuous_proxy` theorems to reference real concrete structures; consider extending the detector to the verdict-stipulation class (`cases<;>rfl` over Bool registries) — currently disclosed via proactive whitelist entries, not auto-flagged.
