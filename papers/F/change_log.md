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
