# ADR-010's open decisions, re-filed as queue items — D2 / D5 / D7, 2026-08-12

**What this is.** ADR-012 §D21. ADR-010 carries three decisions its own §"What remains" lists as
outstanding — **D2** (per-target purpose statements), **D5** (homing dispositions for the un-homed
substrate) and **D7** (the roster-drift change-set). Per D21's synchronization rule — *"the ADR
stays the decision record; the queue becomes the work record"* — each is filed here as a
`ReviewFinding` carrying its lane and target and pointing back at ADR-010.

**Every number below was RE-MEASURED at HEAD before filing.** ADR-010's own standing warning is
the reason: *"Re-derive an item before acting on it, including its evidence line."* That
re-measurement changed the answer for one of the three decisions outright and moved the headline
figure on a second.

| item | re-measured verdict | filed |
|---|---|---|
| **ADR-010 §D2** — 21 per-target purpose statements | ✅ **DISCHARGED 2026-08-06/07** — all 21 exist, each carrying all five required fields plus the boundary-failure verdict D2 demands | **not filed** (see §Not filed) |
| **ADR-010 §D5** — the un-homed substrate | **OPEN.** Live closure predicate: **1,449 of 2,040 modules** un-homed, **26,652 of 32,443** author-written declarations. No disposition record exists and nothing can hold one | findings 1–5 |
| **§D5 sub-item** — the Pin⁺ ℤ/16 arc | **OPEN, and 100% un-homed** — 2,893 declarations across 166 modules, **zero** in any bundle closure, **zero** `PinPlus` occurrences across all 21 drafts | finding 2 |
| **§D5 sub-item** — `GenericSUd*` | ⚠️ **PARTLY DISCHARGED** — D8's apex closure now homes **377 of 537** declarations across **80 of 104** modules. ADR-010's *"four filenames and a wildcard"* line is stale | finding 4 |
| **§D5 sub-item** — the 8 fully-closed phases | **dispositioned by ADR-010 itself** (§Context: *"D5 should therefore be keyed to modules … not phases"*), and a hand-maintained join now exists (`BUNDLE_SUBPHASE`) | **not filed** (see §Not filed) |
| **ADR-010 §D7** — the roster-drift change-set | **OPEN.** 26 of the audit's 36 sites still live, 10 fixed, and **≥9 live sites the audit never listed** | finding 6 |
| **§D7 residue** — `PAPER_STRATEGY.md:341` | **OPEN, and false on both halves** against a heatmap regenerated today | finding 7 |
| **§D7 residue** — `CITATION_REGISTRY['Roehm2026Strategy']` | **OPEN** — the registry describes its own source as a *"14-bundle publication architecture"* | finding 8 |

⚠️ **ADR-012 §D21's D5 row quotes a figure ADR-010 itself WITHDREW.** The row reads *"measured at
1,403–1,633 modules, not the charter's ~340"* and then *"the 4–5× scope change"*. ADR-010's
CORRECTION box (line 54, 2026-08-06) says verbatim: *"**'the audit's ~340 is low by 4–5×' was a
UNIT SWAP.**"* The withdrawn ratio survives in ADR-010 §Context:193 and §What-remains:699, and
ADR-012 D21 inherited it from there — twice in one row. **This document does not restate any
ratio to ~340**, because ADR-010 also records that ~340 *"had no recoverable predicate"*, and a
ratio between a measured number and a predicate-free one is not a measurement.

⚠️ **These are PRE-EXISTING decisions of an ACCEPTED ADR, not new growth.** Every one was written
down between 2026-08-05 and 2026-08-09, before ADR-012 P5 froze its ratchet baselines on
2026-08-12. **Every finding below is filed at `minor`. The blocking count is ZERO**, which is
deliberate and is reasoned per finding: none of these items falsifies a claim any manuscript
makes. Finding 7 is the one where a lead could argue otherwise; its Fix says so explicitly rather
than leaving the call implicit.

---

## Not filed — measured as discharged

**§D2 is DISCHARGED, and three documents disagree about it.** All 21 bundles carry a
`## 1b. ADR-010 §D2 purpose statement — re-derived from the draft and the Lean` section in their
apex-retrofit `FINDINGS.md` (`docs/audits/2026-08-06-{d6,d12}-retrofit/` and
`docs/audits/2026-08-07-*-retrofit/`). Measured: **21 of 21** carry every field D2 names —
*Audience · Venue · the claim only this container can make · Substrate (named Lean modules) ·
Honest size vs charter* — plus the **Boundary failure?** verdict D2's second paragraph requires,
and **four are named as boundary failures** (D6 outbound-and-unresolved, D10 partial, D4 in both
directions, F by construction). Each was written under C4 with the draft read in full.

`ADR-011:130` already records this — *"✅ exists for all 21 … the ADR-010 §D2 purpose statements
authored during the apex retrofit (2026-08-06/07)"* — while `ADR-010:10`/`:677` and
`ADR-012:830` still read OPEN. **ADR-012 D21's "21 findings, `lane=prose`, one per bundle" would
have re-commissioned work that is done.** That is the correction this re-measurement bought, and
it is the reason the rule exists.

**The 8 fully-closed phases (6h, 6j, 6k, 6l, 6q, 6r, 6r′, 6s) are not filed either.** ADR-010's
own §Context disposes of them: *"a phase has no bundle home is **not machine-answerable today** …
D5 should therefore be keyed to **modules**, which are measurable, not phases, which are not."*
Re-measured: a join now exists — `bundle_registry.BUNDLE_SUBPHASE` maps all 21 bundles to a
subphase string — and **none of the eight appears in it**. But its values are hand-maintained
range strings (`6AA-AQ`, `6CA-CE+6ED`) that no consumer parses, so it is a record, not a
derivation, and ADR-010's ruling stands unchanged. Filed as a module-keyed item (findings 1–5),
never a phase-keyed one.

---

## Findings

### 1 — 🔵 D5's un-homed substrate has no disposition record, and nothing exists that could hold one

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `CrossPaperConsistency`
- **Location:** `docs/adrs/ADR-010-publication-portfolio-reassessment.md` §D5 · `scripts/bundle_closure.py`
- **Observed:** ADR-010 §D5 requires that un-absorbed work *"is homed or its absence is
  justified"*, and is explicit that *"'No home' is an acceptable outcome … but it must be a
  decision, not an omission."* **There is no place to record such a decision.** A repo-wide scan
  of `scripts/` and `src/` for `un_homed` / `unhomed` / `un-homed` returns only
  `bundle_closure.py`'s own arithmetic and `build_graph.py`'s closure overlay — a *measurement*
  of the population and a *colouring* of it, with no field, registry or check anywhere that
  distinguishes "not yet dispositioned" from "dispositioned as no-home". The two states are
  currently indistinguishable, which is precisely the ADR's "omission" failure mode.
- **Evidence:** re-measured at HEAD from `lean/lean_deps.json` via
  `bundle_closure.build_closures` + `homing_index`: **2,040 author-written project modules, 591
  in at least one bundle closure, 1,449 in none**; **32,443 author-written project declarations,
  5,791 homed, 26,652 un-homed (82.2 %)**. All 21 bundles declare apexes and **zero apexes fail
  to resolve**, so the measurement is not degraded by a broken input.
  ⚠️ **The population moved against the last published measurement.** The 2026-08-06 closure
  probe (`docs/audits/2026-08-06-closure-probe/FINDINGS.md:111`) recorded **631 homed / 1,405
  un-homed** over a 2,036–2,039 denominator. Six days later the homed set has **shrunk by 40**
  and the un-homed set has **grown by 44**. I did not bisect the cause and this finding does not
  claim one; what it claims is that the number is live and drifting in the direction ADR-010
  §Consequences names as the risk of not acting.
  ⚠️ **A second truncation channel exists that no published warning covers.** ADR-010 §D5a warns
  only about `private` truncation. Aggregated at HEAD: `truncated_private` = **259**,
  `truncated_other` = **4,868**. Resolving the second set independently gives 1,885 distinct
  targets, 1,878 of them `SKEFTHawking`-namespaced, and every one inspected is a constructor
  (`ZOmega.mk`, `CliffordTGate.T`) or a `_proof_N` term — so the truncation is almost certainly
  correct. It is disclosed because *"a size reported alone reads as complete when it is not"* is
  §D5a's own rule, and 19× the disclosed channel travelling undisclosed violates it.
- **Expected:** every un-homed arc carries an explicit disposition — absorb into a named bundle,
  found a new target, or publish defensively with no paper — and a check fails while any arc has
  none, so that "not yet decided" cannot read as "decided: no home".
- **Fix:** ⚠️ **The registry is the deliverable, not the dispositions.** Add a disposition store
  keyed by a **derived** arc identifier and a check that asserts total coverage of the un-homed
  set. The arc key must be derived from `lean_deps.json`, never hand-listed: ADR-010 §D5a
  **RETRACTED** the arc-map idea precisely because *"neither directories nor name prefixes
  partition the substrate"*. That retraction is about partitioning the **whole** substrate; the
  **un-homed residue** does concentrate, measurably — 1,197 of the 1,449 un-homed modules are
  flat `SKEFTHawking.X`, and their two-word name families are led by `PinPlus` (162 modules),
  `SingularRelative` (76), `PoincareLefschetz` (46), `SingularConn` (38), `KummerK3` (26),
  `SphereProd` (25); the other 252 sit under `FKLW` (95), `SymTFT` (46), `QuantumNetwork` (31)
  and a long tail. Read `scripts/build_graph.py`'s extractor contract before fixing the shape —
  §D5a's hard constraint requires the dispositions to emit graph nodes/edges.
- **Verify:** `uv run python scripts/validate.py --check bundle_unhomed_disposition_recorded`
- **Needs-operator:** queue

⚠️ **This is the root of D5's tree and every arc finding below blocks on it**, because a
per-arc disposition written before there is anywhere to write it is a paragraph in a document,
which is the state ADR-010 is already in.

### 2 — 🔵 The Pin⁺ ℤ/16 arc is the largest single un-homed body in the program, at exactly zero coverage

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `CrossPaperConsistency`
- **Location:** `lean/SKEFTHawking/PinPlus*.lean` (164 files) · `docs/adrs/ADR-010-publication-portfolio-reassessment.md` §D5
- **Observed:** **2,893 author-written declarations across 166 modules**, of which **zero** appear
  in any of the 21 bundles' apex closures and **zero** modules are touched by one. The literal
  token `PinPlus` occurs **zero times across all 21 `papers/*/paper_draft.tex`**. ADR-010's
  *"zero `papers/` hits"* reproduces exactly.
- **Evidence:** re-measured at HEAD. ADR-010 §Context recorded *"2,914 `PinPlus*` declarations
  across 180 modules (not 162)"*; the live figures are **2,893 / 166**, with **164 `PinPlus*.lean`
  files** on disk — which matches ADR-010's own CORRECTION box (*"the audit said 162 … there are
  164"*) and not §Context's 180. The module count exceeds the file count by 2 because two modules
  live below a directory segment. ⚠️ **Do not carry §Context's 180 forward.**
- **Expected:** the arc has a written destination or a written reason it has none — ADR-010's
  named example of a legitimate one is *"defensive publication of the substrate, not a paper"*.
- **Fix:** the disposition is genuinely open and this finding deliberately does not pre-judge it.
  What it does assert is that the *default* is currently the worst option: the arc is neither
  published nor recorded as deliberately unpublished, so nothing distinguishes it from work
  nobody got to. Note before deciding that **L2 already sits on a 40-module, depth-14 closure of
  adjacent 5q material** and that `L2 ∩ D2 = 391` (91 % of L2's closure) — an absorption route
  exists and needs measuring rather than assuming.
- **Verify:** `uv run python scripts/validate.py --check bundle_unhomed_disposition_recorded`
- **Blocked-by:** `review:2026-08-12-adr010-queue:adr010-queue:1`
- **Needs-operator:** queue

### 3 — 🔵 The Phase-5q topology families are the second un-homed block, and they are 5× the size the arc list suggests

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `CrossPaperConsistency`
- **Location:** `lean/SKEFTHawking/Singular*.lean`, `Kummer*.lean`, `SphereProd*.lean`, `RP2*.lean`, `RP4*.lean`, `PoincareLefschetz*.lean`, `CharSurface*.lean`
- **Observed:** ADR-010 §D5 names four objects — the modules, the closed phases, the Pin⁺ arc and
  `GenericSUd*`. Measured, the un-homed residue holds a **fifth body larger than three of those
  four**: the singular-homology / Kummer-K3 / sphere-product / projective-space families that back
  the Phase 5q programme. Leading families by module count among the 1,197 flat un-homed modules:
  `SingularRelative` 76 (899 declarations), `PoincareLefschetz` 46 (476), `SingularConn` 38 (248),
  `SingularOpen` 28 (113), `KummerK3` 26 (378), `SphereProd` 25 (482), `KummerSeam` 16 (502),
  `KummerR` 16 (384), `RP4` 16 (246), `RP2` 11 (205), `CharSurface` 10 (236). None of these
  appears anywhere in ADR-010.
- **Evidence:** re-measured at HEAD. The grouping predicate is stated so it can be re-run and
  disagreed with: a module is un-homed iff no author-written declaration in it appears in any
  bundle's apex closure; a *family* is the first two CamelCase words of a flat
  `SKEFTHawking.X` module name. 375 families cover the 1,197 flat un-homed modules — a long tail,
  but the head is concentrated enough for arc-level dispositions to be a real reduction rather
  than a relabelling of the per-module problem.
- **Expected:** these families carry dispositions alongside the four objects ADR-010 names.
- **Fix:** disposition, not homing-by-default. ⚠️ **A material fraction of this substrate is
  known-dead** — see finding 5 — so "absorb into a bundle" is the wrong default here in a way it
  is not for finding 2. Decide finding 5 first for the modules it covers.
- **Verify:** `uv run python scripts/validate.py --check bundle_unhomed_disposition_recorded`
- **Blocked-by:** `review:2026-08-12-adr010-queue:adr010-queue:1`

### 4 — 🔵 `GenericSUd*` is now 77 % homed to D8, and ADR-010's D5 line for it is stale

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `CrossPaperConsistency`
- **Location:** `docs/adrs/ADR-010-publication-portfolio-reassessment.md` §Context (*"Work that has no home"*) · `lean/SKEFTHawking/GenericSUd*.lean`
- **Observed:** ADR-010 records *"Against **556 declarations across 106 modules**, D8's advertised
  headline substrate reaches the manuscript as four filenames and a wildcard."* Re-measured at
  HEAD through the closure predicate D5a made canonical: **537 declarations across 104 modules,
  of which 377 declarations across 80 modules are homed — all of them to D8.** The residue is
  **160 declarations and 24 fully un-homed modules**, not 556 and 106.
- **Evidence:** the two statements are not in conflict; they use different predicates and that is
  the point. ADR-010's figure counts **direct textual reference** in the manuscript (still true:
  five `\lean{}` filenames plus one glob). The live figure counts **apex closure**, the predicate
  §D5a adopted and the probe validated at 2.3× the reach of direct reference. Acting on the
  textual figure would commission homing work for 80 modules that closure already homes.
- **Expected:** ADR-010's §Context bullet states which predicate its 556/106 uses, and D5's
  residue for this object is the 24 modules, not the whole family.
- **Fix:** two steps and the first is a measurement. Establish whether the 24 modules are
  substrate D8 *should* reach (an apex is missing) or substrate D8 deliberately does not claim
  (a disposition is missing). ⚠️ **Do not close this by adding apexes to widen the closure** —
  §D5a gates apex declaration on the operator's per-bundle full-context review, and widening a
  closure to make an un-homed count fall is the same move as lowering a charter floor to make a
  length gap close.
- **Verify:** `uv run python scripts/validate.py --check bundle_unhomed_disposition_recorded`
- **Blocked-by:** `review:2026-08-12-adr010-queue:adr010-queue:1`

### 5 — 🔵 45 of the 49 modules that host the program's kernel-checked no-go refutations are un-homed

- **Severity:** minor
- **Lane:** substrate
- **Gate:** `LeanProofSubstance`
- **Location:** `src/core/constants.py` `KERNEL_NOGO_REGISTRY` · the 45 modules it names that no bundle closure reaches
- **Observed:** `KERNEL_NOGO_REGISTRY` holds **45 settled forks backed by 126 kernel-pure
  refutation theorems across 49 distinct modules**. Measured against the apex closures: **6 of
  the 126 theorems are homed** (one to D2 — `RokhlinArfNoGo.lattice_arf_bridge_refuted`; five to
  D11 — the `GrapheneBand` spectrum/chirality refutations), and **45 of the 49 modules are in no
  bundle's closure at all**. D3 §242 states, citing the strategy document, that the program
  *"treat[s] NO-GO results as first-class publishable content"* — a posture 92 % of the
  kernel-backed no-go corpus does not currently receive.
- **Evidence:** re-measured at HEAD; every one of the 126 backing theorems resolves in
  `lean_deps.json` (zero dangling), so the un-homed verdict is about publication reach and not
  about a broken registry. The un-homed 45 fall predominantly inside findings 2 and 3's families —
  `KummerK3ForallOrientationFalse`, `KummerK7SeamCoverNoGo`, `GMPinTorsorCeiling`,
  `CharSurfacePDBundled`, `HandleTradeAtomVacuity`, `FGDualityNoGo` and the rest.
- **Expected:** the modules whose content is a **refutation** are dispositioned as refutations —
  published as negative results, or recorded as deliberately unpublished — and never absorbed
  into a bundle as though they were supporting substrate for a positive claim.
- **Fix:** this is the module-level layer of D5's tree and it **constrains its parents**: for
  these 45 modules the arc-level menu is not "absorb / found / defensively publish" but
  "publish as a no-go / retire", because absorbing a refutation into a bundle that argues the
  refuted statement's neighbourhood is how a settled-dead fork gets re-seeded. Route the
  disposition through `docs/dev-loops/SETTLED_FORKS.md` and the registry, not through a bundle's
  apex list.
- **Verify:** `uv run python scripts/validate.py --check bundle_unhomed_disposition_recorded`
- **Blocked-by:** `review:2026-08-12-adr010-queue:adr010-queue:2`, `review:2026-08-12-adr010-queue:adr010-queue:3`
- **Needs-operator:** queue

⚠️ **This is the most citable thing in the un-homed pile and the easiest to lose.** A
kernel-checked refutation is a result a referee can verify in one command; it is also the class
that reads as "failed work" to anyone scanning module names, which is exactly why the disposition
has to be written down rather than inferred.

### 6 — 🔵 D7's roster-drift change-set: 26 of 36 sites still live, and the change-set has no mechanism

- **Severity:** minor
- **Lane:** infra
- **Gate:** `CrossPaperConsistency`
- **Location:** `README.md`, `SK_EFT_Hawking_Inventory_Index.md`, `SK_EFT_Hawking_Inventory.md`, `docs/RESEARCH_STATUS_OVERVIEW.md`, `docs/agents/claims-reviewer-bundle-prompts.md`, `docs/ARXIV_DEPOSIT_PLAN.md`, `docs/QI_REGISTER.md`, `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`, `docs/BUNDLE_LIFT_PROCEDURE.md`, `docs/PAPER_DRAFT_MAPPING.md`, `docs/PAPER_STRATEGY.md`, `src/core/citations.py`, `scripts/build_graph.py`, `scripts/review_runner.py`
- **Observed:** ADR-010's status header says *"§D7's roster-drift change-set is **applied**
  (fifteen live sites corrected 2026-08-09, TODO-D15)"*, while its own §What-remains item 5 says
  *"**D7** — the roster-drift change-set, **unchanged**."* **Both cannot be true, and neither is.**
  Re-measured against `CROSS-portfolio-coherence.md` §5.2's 36-site table: **10 are fixed, 26 are
  live.** TODO-D15's fifteen corrections were to **paper prose** — a different population, closed
  and correctly closed. The doc/script population was not touched.
- **Evidence:** the scan predicate is a roster count word or digit immediately qualifying
  `bundle(s)` / `publication target(s)`, plus stale membership enumerations (`D1–D5`, `D1–D8`,
  `D1–D9`, `D1–D10`), with the audit's own dated-historical-snapshot exemptions honoured.
  **Fixed:** `WAVE_EXECUTION_PIPELINE.md:80` and Invariant #14's own text (which now reads *"one
  of the codes in `validate.BUNDLE_CODES`, the roster's single source of truth"*);
  `LATE_PHASE6_ABSORPTION_PROTOCOL.md:68,269` (the Stage-B "13 bundles" authorization rule);
  `SK_EFT_Hawking_Inventory_Index.md:406,411` (now "21 publication targets");
  `DASHBOARD.md:98,162` (moved under `docs/architecture/` and corrected per ADR-012 D22);
  `BUNDLE_DIRECTORY_SCHEMA.md:197` (rewritten to reference the registry rather than copy it);
  the workspace `CLAUDE.md`.
  ⚠️ **And at least NINE live sites the audit never listed**, found by scanning for the claim
  rather than the list — the failure mode D15's own box diagnoses:
  `docs/agents/claims-reviewer-bundle-prompts.md:58`, `docs/BUNDLE_LIFT_PROCEDURE.md:342,344`,
  `docs/PAPER_DRAFT_MAPPING.md:221`, `docs/PAPER_STRATEGY.md:333`, `scripts/build_graph.py:1635`
  and `:1679`, `scripts/review_runner.py:333` and `:336`. **Four of those are rule texts** that
  say Tier 1 is `D1–D5` when `bundle_registry.TIER_OF` says Tier 1 is `D1–D12`, and one —
  `claims-reviewer-bundle-prompts.md:21` — tells the reviewer agents the roster is *"one of the
  17 bundle codes: `F`, `D1`–`D8`, …"* in a document whose own body carries D9–D12 sections.
  ⚠️ **The existing gate is green over all of it.** `bundle_registry_consistency` passes with all
  four legs clean, including `no_rehardcoded_rosters — 136 scripts/*.py scanned — no literal
  bundle roster outside scripts/bundle_registry.py`, while `review_runner.py:336` carries
  `help="bundle code (one of F, D1-D9, L1-L3, I1-I3, E1-E2)"` — a live string literal, not a
  comment.
- **Expected:** a roster claim in prose, a docstring, a comment or a CLI help string is either
  derived from `bundle_registry` or fails a check — X-14's own recommendation, unimplemented:
  *"`bundle_registry.py` becomes the doc source too … or add a `validate.py` check that greps
  prose for `\d+[- ]bundle` and diffs against the registry."*
- **Fix:** **build the check, then sweep — not the reverse.** This population has now been
  hand-swept twice (2026-08-09 twice over, per TODO-D15's own two nested corrections) and both
  sweeps missed sites the next scan found, because each keyed on the previous finding's site list.
  A third hand-sweep is the same instrument. The check needs two legs — the roster count/membership
  claim, and the status claim of finding 7 — and its file set must include `src/` and `scripts/`
  string literals, which `no_rehardcoded_rosters` demonstrably does not reach. Honour the audit's
  dated-snapshot exemptions explicitly in the check rather than by omission, or it will fire on
  correct historical narration and get switched off.
- **Verify:** `uv run python scripts/validate.py --check bundle_roster_prose_drift`

### 7 — 🔵 `PAPER_STRATEGY.md` claims every bundle cleared its reviewer triple GREEN; the heatmap it cites says zero did

- **Severity:** minor
- **Lane:** prose
- **Gate:** `NarrativeGrounding`
- **Location:** `docs/PAPER_STRATEGY.md:341`
- **Observed:** *"**Status note (2026-05-07).** All 14 bundles have shipped Stage 9 + Stage 10 +
  Stage 13 reviewer triples GREEN per `BUNDLE_READINESS_HEATMAP.md` … the now-shipped state is
  'all 14 bundles cleared per-bundle reviewer triple, awaiting submission gates'."* Measured
  against `docs/BUNDLE_READINESS_HEATMAP.md`, **auto-generated 2026-08-12**: **0 GREEN, 17 RED,
  4 YELLOW.** Both halves fail — the roster is 21, and no bundle has cleared its triple.
- **Evidence:** this is the same compound falsehood the closure reviewer corrected in F on
  2026-08-09 (`ARCHITECTURE_TODOs.MD` D15: *"It claimed the program 'has shipped 17 bundles to
  reviewer-triple-closed Stage-13 GREEN status'. Both halves were false."*). The correction landed
  in the manuscript and not in the charter document the manuscript's own architecture derives
  from — the one-site-correction defect D15's box names, recurring one document over.
  ⚠️ `CROSS-portfolio-coherence.md` §5.2 **exempts this line** as a dated historical snapshot,
  and for the *count* that is right. It is not right for the GREEN claim: a 2026-05-07 date stamp
  does not make *"the now-shipped state is …"* a statement about 2026-05-07, and the heatmap it
  cites has never carried a GREEN verdict for the 21-bundle roster.
- **Expected:** the charter says what the heatmap says, or says nothing about verdicts.
- **Fix:** state the roll-out cadence without the status claim, exactly as F's §11.1 was
  corrected — *"describes the intended shipping architecture rather than an achieved state."*
  ⚠️ **Severity is a judgment call and this finding does not hide it.** Filed `minor` because no
  manuscript reproduces the claim: D3's and I3's `\bibitem{Roehm2026Strategy}` were read in full
  and both carry *"SK-EFT Hawking publication architecture"* with **no count and no status**, so
  no publication claim rests on it. The argument for `major` is that `PAPER_STRATEGY.md` is a
  **cited source** (`used_in: papers/D3, papers/I3`) *and* the document Invariant #14 sends every
  wave to for charters, so a reader could take "reviewer triple cleared" as licence to skip
  review. If the lead takes that reading, escalate deliberately — the unattributed blocking
  ratchet is at **52/52, zero headroom**, so an escalation is a ceiling decision, not a wording
  one.
- **Verify:** `uv run python scripts/validate.py --check bundle_roster_prose_drift`

### 8 — 🔵 The citation registry describes its own source document as a "14-bundle publication architecture"

- **Severity:** minor
- **Lane:** prose
- **Gate:** `CitationIntegrity`
- **Location:** `src/core/citations.py:8351` (`CITATION_REGISTRY['Roehm2026Strategy']`)
- **Observed:** the entry's `title` reads *"SK-EFT Hawking **14-bundle** publication architecture
  (project paper-strategy frame)"* and its `provides` reads *"**14-bundle** publication
  architecture (1 flagship + **5** Tier-1 deep + 3 Tier-2 PRL + 3 Tier-3 infrastructure + 2
  Tier-4 experimental)"*. The source it names, `docs/PAPER_STRATEGY.md`, opens with *"The new
  structure is **twenty-one** publication targets … one flagship + **twelve** themed deep
  papers"*. The entry's own `notes` records the staleness mechanism verbatim: *"Bundle count
  updated 13->14 at I3 … Verified against PAPER_STRATEGY.md 2026-05-11."*
- **Evidence:** re-measured at HEAD; `used_in` names `papers/D3/paper_draft.tex` and
  `papers/I3/paper_draft.tex`, and both were read — **the rendered bibitems are clean**, carrying
  no count. So the defect is confined to the registry record, which is why this is `minor` and
  not a manuscript finding. ⚠️ **No existing check can see it:** `bibitem_title_primary_source`
  compares registry titles against a cached primary-source PDF, and this entry carries
  `primary_source_path: None`, so it is outside that check's population entirely — a
  self-referential in-repo citation has no PDF to diff against.
- **Expected:** a citation to an in-repo document describes that document as it currently reads,
  or describes it without a count.
- **Fix:** drop the count from `title` and `provides` — the entry's substantive content, *"NO-GO
  results as first-class publishable content"*, is what D3 §242 actually cites and it is correct.
  ⚠️ While in the entry, note but do **not** silently fix two duplicate keys in the same dict
  literal (`'inprep'` given twice, `'primary_source_path'` twice); the neighbouring
  `Roehm2026I2` entry has the same shape, so it is a pattern in the registry rather than a typo
  in one record, and it belongs to whoever owns that file.
- **Verify:** `uv run python scripts/validate.py --check bundle_roster_prose_drift`
