# GOAL — ADR-010 apex retrofit: the remaining 17 bundles, and the portfolio layer in architecture

This is a **definition of done**, not a procedure. How to get there is yours to work out from the
documents named below — read them before producing anything.

---

## DONE means every one of these holds

1. **`UNDECLARED_APEX_CEILING == 0`** in `scripts/validation/checks/bundles_readiness.py`, with
   all 21 bundles carrying declared `apex_theorems` in `bundle_metadata.json`, and
   `validate.py --check bundle_apex_resolves` green. The ceiling is lowered in the same commit as
   each bundle it covers — never in advance, never in a batch.

2. **Every retrofitted bundle has a FINDINGS document** under `docs/audits/2026-08-<dd>-<bundle>-retrofit/`
   that records, at minimum: what was read in full before anything was declared; the apexes
   declared and the claim each backs; the derived closure (declarations / modules / depth); and
   anything the closure contradicted. `docs/audits/2026-08-06-d6-retrofit/FINDINGS.md` and
   `2026-08-06-d12-retrofit/FINDINGS.md` are the shape.

3. **Each bundle's ADR010-D2 purpose statement exists** — audience, venue, the claim only this
   container can make, the substrate that backs it, and its honest size against charter —
   re-derived from what the draft and the Lean actually contain, never inherited from
   `PAPER_STRATEGY.md`.

4. **The evidence for ADR010-D4 is assembled but the recommendation is NOT made.** For each
   proposed merge (D6+D9, D10+D11, E1+E2, D4→D8) the closure evidence either supports it, refutes
   it, or is recorded as not deciding it. A target whose purpose cannot be stated without another
   target's substrate is named as a boundary failure.

5. **`docs/architecture/` maps the portfolio layer.** A document owning *"what are we publishing,
   what state is it in, and what is outstanding?"*, registered in `README.md`'s ownership table,
   pointing at `docs/audits/2026-08-01-publication-readiness/`, `PAPER_STRATEGY.md`, ADR-010's
   open items and the retrofit state. Its absence is why a full day was spent on infrastructure
   while the retrofit was already running, unmentioned by any architecture document.

6. **`ACCURACY_LEDGER.md` covers every new assertion** at the granularity it already uses — one
   row per proposition, naming the decider and the verbatim result; set claims verified for
   completeness; number-cited invariants resolved to their actual subject; statements with no
   truth value marked NOT-AN-ASSERTION with a reason.

7. **The `D`-namespace collision is resolved** in every document touched: `ADR010-D2`, `SYN-D-1`,
   `TODO-D5`, `ADR009-D3`, with bare `D6`/`D9`/`D11` reserved for bundles.

8. **`validate.py` green, `uv run python -m pytest tests/ -q` green**, and every commit carries
   the work of one bundle or one document — not a sweep.

---

## HARD CONSTRAINTS — violating any of these fails the goal regardless of output

- **C4 (ADR-010).** No apex, merge, split or retirement rests on a summary, a bundle name, an
  audit table, or a subagent report. The draft is read **in full**, directly, by you. Where a
  conclusion rests on something not read, it says so.
- **C5 (ADR-010).** The schedule is the flexible variable; claim strength is not. A container is
  resized only because the substrate is genuinely a different shape — never because resizing
  makes a shortfall disappear.
- **§6a (REMEDIATION_PLAN).** No new check, gate, script or infrastructure without approval.
  Sequence: identify the defect → establish what existing machinery covers it *by reading the
  code* → describe the residue → **ask** → only then build. Never build before asking.
- **One bundle at a time.** Never a sweep. An apex asserted without reading the substrate is the
  authorization-before-measurement pattern that produced the D-tier problem.

## STOP AND ASK — these are not yours to decide

The roster number · D10's scope · L1's disposition · the `native_decide` posture · the graphene
`Γ_H` dimensional question · ADR010-D6 step 4 (the Lean-module-mtime absorption trigger). Each
changes a container's charter. They come due when the ADR010-D4 recommendation is assembled, not
before — do not ask early, and do not assume a resolution.

---

## READ FIRST — before producing anything

`docs/architecture/README.md` and the seven documents it indexes ·
`docs/audits/2026-08-01-publication-readiness/` (README, SYNTHESIS, REMEDIATION_PLAN — **all of
it**, it is the authoritative state and predicts most of what a fresh pass will "discover") ·
`docs/adrs/ADR-010-*.md` · `docs/architecture/.working-docs/PUBLICATION_INTAKE_SHAPE.md` §3b and
§5 (the retrofit method and queue — **D11 is next**, and why) ·
`docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD`.

## FAILURE MODES MEASURED ON 2026-08-07 — do not reproduce them

- **Producing before orienting.** An audit directory was created beside an existing one six days
  older containing the same findings; a remediation plan with a standing ruling in it went unread
  until after it was violated. **Read what exists on a subject before generating anything about
  it — reflexively, not on permission.**
- **A second mechanism beside a working one.** A check shipped with its own resolver next to
  `chain_canonicalize.canonicalize_link`, and disagreed with it (156 vs the real 121).
- **The proxy accepted as a decider.** `grep` where the AST decides; a reference counted as a
  write; `ast.Assign` missing `AnnAssign`; `was wrong` missing `were wrong`; a raw identifier
  scan missing the LaTeX-escaped `gapped\_interface\_axiom` in 14 drafts. ⚠️ **Drafts escape
  underscores inside `\thm{}` — a bare grep for a theorem name returns 0.** Use the
  underscore-aware scan; this is the artifact class behind two withdrawn ADR-010 figures.
- **Reading partial state as failure.** "4 of 21 apexes declared" is retrofit *progress*, not a
  deficiency. Check whether something is in flight before calling it broken.
- **Set claims verified by a named member.** "the only blocking figure assertion" survived four
  passes because legibility does block — the atom was *"the only"*.
- **Quoting a superseded number.** 156 for the chain links; 515 for the naive resolver; ~340 for
  un-homed modules (measured 1,403–1,633). Re-derive before quoting, including your own figures.

## NOTES

- Each retrofit has already paid: D12's killed the D6+D9+D12 merge hypothesis (D6∩D12 = 0,
  D9∩D12 = 3) and **relocated** the D6/D9 finding — the 78 shared theorems reproduce, but the
  declared closures are disjoint; D6 cites 133 declarations from D9's namespace and claims none,
  covering 19% of its own citations. Borrowing, not duplication — a different fix from a merge.
- Re-tiering waits on the retrofit. Closure shape says where to look; tier is a claim about
  audience and framing, and that is the operator's call.
