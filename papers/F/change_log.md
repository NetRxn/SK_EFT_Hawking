# Bundle F — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-11 — Stage-13 sweep re-lift (REVISION)

Post-Wave-1-7 absorption: F bundle synced with sibling Tier-1 fix-pass corrections.

**Substantive prose synchronisations:**
- §6 (Topological QC, lines ~1240 and ~1789): `DoublonGate.lean` phantom-module references replaced with `FermiHubbardDimer.lean` citations (per Wave 5 D4 fix-pass — Lean module verified non-existent; FermiHubbardDimer ships `darkVec` + `dark_state_in_kernel` + sign-flip $U_{SWAP}\cdot\mathrm{darkVec}=-\mathrm{darkVec}$).
- §4 (Closure 2, line ~908): `wen_adw_factor_6000`-named-lemma in-flight reference replaced with `EmergentGravityBounds.coupling_deficit` + `coupling_ratio_small` (per Wave 2 D3 fix-pass — substantive theorems exist).
- §1 / §6 (lines ~76 / ~173 / ~366-373 / ~1352-1385): 8/8 entropic-DE Bayes-decisive $|\log B|\geq 5$ universal claim downgraded to mixed-threshold (3 quantitative Bayes-decisive + Barrow at $\Delta\!\mathrm{AIC}=4.7$ Burnham-Anderson moderate) per Wave 4 D5 Sessions 4+5 honest correction. Tsallis attribution softened to framework-aggregate $\Delta\!\log\mathcal{B}\sim-8$ to $-13$ (not Tsallis-isolated 6.2).
- §5 / §10.4 (lines ~390 / ~1418-1422): Sakharov four-condition criterion biconditional with $\Lambda_J=\Lambda_{HK}$ retired in favour of one-way implication $\Lambda_J=\Lambda_{HK}\Rightarrow$ four-condition; load-bearing depletion-factor witness on `SakharovExtended` per Phase 6o Wave 4a Track 4 verdict-(B) closure.

**Policy-driven prose cleanup:**
- 8 project-side "to our knowledge ... the first" / "first machine-checked X" / "first formally verified X" instances fully removed (8 sites across §1, §4, §6, §10.4, §11, §13). Line ~462 "first of three" retained as sequence enumeration. Policy: priority established by literature, not by declaration.

**PDF:** 22 pages, 478206 bytes (was 21 pages, 476570 bytes post-first-claim-only-cleanup).

**Stage gate state:** `stage13_redo_required=true` flipped pending re-invocation. Adversarial-reviewer agent must re-clear before bundle close.

## 2026-05-12 - Prose-revision-bookkeeping (bookkeeping)

- Source: (none - project-wide first-claim-removal prose revision)
- Lift action: Prose-revision-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-05-12 project-wide first-claim-removal pass: 15 source paper drafts (paper1, paper2, paper5, paper7, paper8, paper9, paper10, paper11, paper14, paper16_graphene_sk_eft, paper16_wrt_tqft, paper17_dark_sector, paper18, paper20, paper44) had primacy-framing prose ('We present the first ...', 'the first machine-checked', 'the first such', 'first formalization') rewritten to descriptive content-first prose. paper14 + paper16_wrt_tqft titles changed (dropped leading 'First'). No claims added; no numerical results changed; bibliographies + citations preserved. F bundle prose was not directly edited but inherits the per-source revisions via the flagship-bundle aggregation; the next F lift cycle will fold the new descriptive prose into bundle text.

## 2026-05-31 — Freshness-bookkeeping (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Freshness-bookkeeping
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: Freshness-bookkeeping (LATE_PHASE6_ABSORPTION_PROTOCOL §3d case 1): source-paper mtime drift is ENTIRELY from auto-regenerated tables/*.tex artifacts (verified: the only files newer than last_lift in each stale source are tables/*.tex; every source paper_draft.tex mtime is OLD <= last_lift; git status clean so regenerated tables match committed content byte-for-byte = zero content change). Bundle compile path is decoupled: this bundle \input's only ../../docs/counts.tex, never any source-paper tables/ dir. No content lift warranted; no Stage-13 redo; reviewer triple remains valid (bundle stays GREEN).

## 2026-06-10 — Review-finding remediation F-R1 + F-Y1 (REVISION)

- Source: external review 2026-06-05, findings F-R1 (stale "one true axiom" posture; submission blocker) + F-Y1 (bundle-count/architecture drift vs `docs/PAPER_STRATEGY.md` 17-target frame)
- Lift action: Prose-correction (in-place; no new sections)
- Insertion point: (in-place edits across abstract, §1.1–§1.3, §2, §4 Phase-6m totals, §5 pillar synthesis + axiom subsection, §6 inheritance, §9, §11, §12, bibliography self-cite)
- Stage-13 redo required: yes (substantive posture + architecture prose changed; adversarial reviewer must re-clear before bundle close)
- Notes:
  - **F-R1 (zero-axiom posture).** All 11 grep hits of the stale "one true axiom" / `gapped_interface_axiom`-as-live-axiom prose corrected to the D2-model tracked-hypothesis posture: `axiom gapped_interface_axiom` was retired into the tracked-hypothesis `Prop` `TPFConjecture` (`SPTClassification`) on 2026-05-19 (commit d282677d); project ships `\axiomcount{}` (=0) project-local axioms, 0 sorries. Sites: abstract (~83), §2 Layer-3 scope (~310), §5 pillar synthesis (~804), §5 subsection retitled "The tracked-hypothesis `Prop` `TPFConjecture`" with body rewritten mirroring D2 lines 894–906 (~809–824), §6 D4 inheritance (~1259), §11 close-out totals (~1906), §11 outlook item 3 (~1994), §12 conclusion (~2094). Remaining 4 mentions of the axiom name are all "formerly `axiom gapped_interface_axiom`" historical attributions. Adjacent `$\axiomcount$ axiom` macro grammar normalised to `\axiomcount{} project-local axioms` (renders "0 project-local axioms") at ~354, ~440, ~1543, ~1905, ~1980.
  - **F-Y1 (17-target architecture).** §1.2 architecture table extended 13 → 17 targets: Tier 1 5 → 8 deep papers (+D6 formally-verified fault-tolerant QC substrate, +D7 classical simulability/quantum advantage via tensor networks, +D8 kernel-verified universal quantum gate compilation — canonical titles/tiers per `PAPER_STRATEGY.md` §2.2); Tier 3 2 → 3 infrastructure (+I3 verified stochastic calculus/LDP for Mathlib4 — required for the table to sum to 17; I3 was already cited in §12 but absent from the §1.2 table). All bundle-count phrases normalised: "13/14-bundle" → "17-bundle", "$13$ publication targets" → "$17$", "twelve/thirteen sibling" → "sixteen sibling"/"seventeenth bundle", §11 tiers "D1--D5 five deep / I1--I2 two infra" → "D1--D8 eight deep / I1--I3 three infra", submission roll-out "(D1, D2, D3, D4, D5)" → "(D1--D8)", "all 12 siblings" → "all 16 siblings", "shipped 13 bundles ... Stage-13 GREEN" → "17" (verified against `docs/BUNDLE_READINESS_HEATMAP.md`: all 17 GREEN), strategy bibitem title → "17-bundle publication architecture". §1.1 sibling enumeration head reworded "take that substrate and read off its predictions" → "build on that substrate and its verification stack", with D6/D7/D8 attributed via the FKLW/horizon-MTC line (NOT claimed as direct ADW-prediction readers).
  - **ADW-coupling-count hedging (per F-Y1 caution).** Physics-coupling claims dropped hard counts rather than inflating 13 → 16: synthesis claim (~219) now "the same ADW substrate with $N_f = 16$ drives the program's sibling threads"; "its thirteen faces are thirteen bundles' worth" metaphor (abstract ~67, §1.3 ~261, §12 ~2052 + abstract comment block) now "its faces are the sibling bundles' worth of predictive register". Rationale: D6/D7/D8 are verification-native bundles connected through the FKLW/horizon-MTC line; PAPER_STRATEGY does not establish them as direct ADW-substrate-prediction readers, so a hard "sixteen faces" coupling count is not verifiable. Architecture counts (how many targets exist) remain hard 17/16.
  - Untouched by design: `sixteen left-handed Weyl fermions` (~738/~754, physics $N_f=16$, not a bundle count); "all 13 sub-phases" (~438, counts Phase-6 sub-phases); 93%/106/114 reuse numbers (separate agent's fix).
  - **PDF:** 23 pages, 489666 bytes (was 22 pages). LaTeX compile gate clean ×2 passes (zero errors, zero Undefined references/citations).

## 2026-06-10 — Source-reconciliation pass post external-review remediation (REVISION)

- Source: `bundle_source_freshness` flag (17 of 59 sources modified after F's 2026-05-31 last_lift); committed real-delta set = paper10 [RESTRICTED to Phase 5q.B], paper11, paper12, paper15, paper17, paper18, paper20, paper21, paper26, paper4, paper6, paper7, paper8, paper9 (commits `f6048c48`/`6ac6ef89` paper10; `3036ffd7` paper8; `5207b72b` 11 drafts' zero-axiom/TPFConjecture phrasing + CHECK 24/25/26 calibration; `8b68fe13` paper11 table1_chain regen; `6ca06607`+`43919c53` paper15 table2_checks regen). Remaining flagged sources are mtime noise (auto-regen artifacts).
- Lift action: Inline-absorption-record (in-place reconciliation edits; no new sections)
- Insertion point: (in-place edits: abstract, §5 Pillar 1, §6 Closure 3, §9 NO-GO register ×2, §10 pipeline stage list)
- Stage-13 redo required: yes (substantive prose changed in abstract + body)
- Verified-consistent (no edit needed):
  - Zero-axiom / `TPFConjecture` posture (paper4/6/7/8/9/11/12/17/18/20/21/26 delta theme): F already carries `\axiomcount{}` + "formerly `gapped_interface_axiom`" historical framing at all sites (073d0e1e sweep); zero stale "one axiom" hits.
  - Halenka–Miller PRD **102**, 084007 (2020) relaxed-cluster framing: already present at §1 contribution list, §4 Track-B ledger, §4 candidate list, bibliography (f1a0829f sweep).
  - Verlinde 2-of-4 ledger at §1 (~195), §4 (~386), §4 Track-B subsection (~1457–1500): already corrected (both_decisive 2-conjunct aggregator language).
  - D5 module theorem counts (CausalSet 12 / EntropicGravity 17 / JacobsonThermoGR 22 / DarkSectorClassificationExtension 11): already current.
  - Vergeles propositions naming (Gates E.1, open-register item): matches current D3 §2/§5 "Vergeles unitarity propositions" framing — no fabricated eq-level provenance present in F.
  - L2/D2 external-hypothesis description (Ω₅^{Spin^Z4} ≅ Z₁₆ as Mathlib-deferral external input): still accurate vs current D2 §1/§5 + L2 — the bordism-group identification remains an external input post-`f6048c48`.
  - No SU2kSMatrix per-module counts in F (paper11 table 18→253 regen has no F counterpart).
- Fixed (residual divergence, mirrored at flagship register):
  - **Abstract (~74–79):** stale "three of four quantitative mechanisms exceed Jeffreys-decisive" → corrected 2-of-4 ledger with Verlinde 2017 ≥5σ galaxy-cluster mass-density exclusion under nominal profile assumptions (mirrors f696c0a0/f1a0829f honest downgrade; 2026-06-10 unit-coherence correction).
  - **§9 cleared NO-GO register (~1829–1836):** same 3-of-4 → 2-of-4 fix + Halenka–Miller `\cite{HalenkaMiller2020}` attribution.
  - **§5 Pillar 1 (~800–808):** "Golterman–Shamir no-go / cannot exist / evades this obstruction" → GS conditional-constraints framing (nine kinematical conditions delimiting Nielsen–Ninomiya applicability; TPF *exits the applicability scope* rather than contradicting a theorem), mirroring 1bb62842 D2 §4 reframe; cross-ref "(D2 §4)" added.
  - **§6 Closure 3 (~975–983):** χ_vest∈[0.1,10] window given honest provenance ("project-adopted order-unity naturalness window about the RPA bubble-integral scale — a modeling choice of this project, not a published derivation") + GW170817 bound stated asymmetrically (−3×10⁻¹⁵ ≤ Δc/c ≤ +7×10⁻¹⁶, conservatively two-sided), mirroring ca0d0f36 D3/L1 corrections.
  - **§9 falsified register (~1792–1800):** "over the Volovik vestigial natural range" misattribution → mode attributed to Volovik, window flagged project-adopted.
  - **§10 stage list (~1631):** "validate.py; 22+ checks" → "29+ checks" (paper15 table2_checks regen now enumerates 29 checks; validate.py at 33).
- **Paper10 / Rokhlin / 16∣σ divergences DOCUMENTED, NOT FIXED (owned by active Phase 5q.B session):**
  1. F §5 (~756–761) states the Rokhlin 16-convergence as "the signature divides by 16 on a Spin^Z4 4-manifold" with no proven/hypothesis status marker. Post-`f6048c48`, D2/L2/paper10 present 16∣σ as the *unconditional kernel-pure theorem* `SmoothSpinManifold4.rokhlin` (van der Blij 8∣σ + topological 2∣σ/8), headline `sixteen_convergence_unconditional`; F could be upgraded to cite the unconditional theorem (and "closed smooth spin 4-manifold" is the precise hypothesis class, vs F's "Spin^Z4" wording).
  2. F §5 L2-splash paragraph (~861–870) describes the L2/D2 shared external hypothesis as the Ω₅ ≅ Z₁₆ cobordism input only — consistent today, but if 5q.B's unconditional-16∣σ reframe propagates further (e.g., L2 abstract-level claims), F's "carries the Rokhlin 16-convergence" sentence may want the "now a proved theorem, not an assumed input" qualifier. Handoff to 5q.B / next F lift.
- **Compile gate:** pdflatex ×2 clean — 23 pages, 491788 bytes; zero errors, zero Missing $/Misplaced &/Undefined control sequence, zero undefined citations/references.
- **Registry additions needed:** none (HalenkaMiller2020 bibitem + CITATION_REGISTRY entry pre-existing; no new bibkeys introduced).
- **Freshness flag intentionally NOT cleared** (paper10-driven divergence remains open under the 5q.B restriction; a future lift/absorption event closes it).

## 2026-06-10 — Inline-absorption-record (bookkeeping)

- Source: (none — bookkeeping event)
- Lift action: Inline-absorption-record
- Insertion point: (n/a)
- Stage-13 redo required: no
- Notes: 2026-06-10 source-reconciliation pass post external-review remediation: real-delta set (paper4/6/7/8/9/11/12/15/17/18/20/21/26 + paper10 RESTRICTED) reconciled against F. Verified-consistent: zero-axiom/TPFConjecture posture, Halenka-Miller PRD 102 084007 (2020) framing, 2-of-4 Bayes-decisive Track-B ledger at the three already-swept sites, D5 module counts, Vergeles-propositions naming, L2/D2 external-hypothesis description. Fixed residuals: abstract + Section-9 register stale 3-of-4 Bayes-decisive -> 2-of-4 with Verlinde >=5-sigma Halenka-Miller exclusion; Pillar-1 GS no-go -> conditional-constraints/applicability framing (mirrors D2); chi_vest window given project-adopted-window provenance + asymmetric GW170817 bound (mirrors D3/L1); Volovik natural-range misattribution; 22+ -> 29+ validate checks. Paper10/Rokhlin 16|sigma unconditional-theorem upgrade DOCUMENTED NOT FIXED (Phase 5q.B ownership) - see change_log.md. Compile gate clean x2 (23pp). stage13_redo_required=true (substantive prose changed); freshness_stale intentionally retained.
