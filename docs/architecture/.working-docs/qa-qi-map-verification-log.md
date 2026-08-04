# QA/QI map — verification log

Working notes behind `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md`. This is the audit trail for how that
map was built and which claims were rejected along the way. **It is not reference material** — the map
states what is true; this file records how that was established.

**Method.** `scripts/validate.py` read in full by the author (7,778 lines, 2026-08-03). Four read-only
reconnaissance sweeps over the artifact-generation, readiness/bundle, agent/hook/register, and test-coverage
subsystems. Every load-bearing claim re-verified against source by the author before entering the map.

---

## Claims that did not survive verification

**1. `atlas_hypothesis_discipline` "contradicts its own description" — WITHDRAWN.**
Reconnaissance reported its `passed=False` as a live gate contradicting a registered description reading
"INFO … NEVER a gate". Reading the function: the `passed=False` sits in the **exception handler**. It fails
only when it cannot build the atlas and passes unconditionally on content — fail-on-cannot-measure, which is
the *correct* pattern and the one the rest of the suite has been retrofitting toward. Not a defect. Removed
from the map before publication.

**2. `aggregate_by_bundle` "never reads `stage13_status`" — PARTIALLY REFUTED.**
The function body never touches it, but its `review_info` argument does: `resolve_stage13_reviews` reads
`stage13_status` and lifts any non-enum value into a display-only `status_caveat`. The GREEN/YELLOW/RED
verdict is genuinely independent of all three stage-status fields; the heatmap's review-date cell is weakly
influenced. The map states the narrower, accurate claim.

**3. The 121 `theorem-absent` chain links — ROOT-CAUSED, and my own caveat was wrong.**
I had cautioned that the count was inflated by name-ambiguity artifacts. That was **wrong on mechanism** —
ambiguous names have their own bucket (`theorem-ambiguous`). The real split is **~71 genuine / ~50 artifact**
across four classes: kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) that have no graph node
though the claims-reviewer spec instructs agents to emit them; `module:` prefix double-mangling; by-design
inductive-constructor filtering; and mis-tagged link kinds. The substantive half of this finding now lives
in the map body (§"Claim lineage"), not here.

---

## Author errors, caught mid-flight

Recorded because the map's credibility rests on the same discipline it measures others by.

**A. A `grep` run from the wrong working directory** reported every Tier-1 and Tier-2 file absent —
including `axiom_closure_allowlist`, which I had read myself at `validate.py:1894`. The shell was in the
workspace parent, so `grep` found no `validate.py` at all and every lookup returned "absent". Redone with
absolute paths; the corrected result (Tier-1 files genuinely absent, 1 of 9 Tier-2 checks registered) is
what the map carries. This is precisely the measure-the-wrong-thing failure the map documents in others.

**B. A registry count of 60** against an authoritative `validate.py --list` count of **59** — my regex
double-counted one multi-line `@register_check` decorator. Caught before it reached the map.

---

## Line-number baseline

Every `validate.py:NNNN` citation in the map and in ADR-009 is anchored to the file **as read at 7,778
lines**. The `stage13_status` guard shipped 2026-08-03 inserted 35 lines at `:4355`, so the live file is
**7,813** at the time.

⚠️ **The re-anchor never happened, and it is now MOOT** (audit finding QI-26). This paragraph ended
"Phase 1 re-anchors mechanically and deletes the note". Phase 1 did not, and Phase 2 then moved all 59
check bodies out of `validate.py`, which is now ~740 lines of framework — so every citation to a CHECK
BODY is dangling by construction. **Locate the check by NAME in its `validation/checks/*.py` module.**
Citations to the framework (registry, `run_checks`, reporting, CLI, `main`) still resolve, at new line
numbers. Silently renumbering ~25 citations across a module boundary was judged a larger correctness risk
than stating plainly that they are historical; ADR-009's line-citation preamble carries the same note.

---

## Scope boundary

The Codex control plane (`scripts/lean_slots/*`, `.codex/*`, ADR-008) was checked for coupling and has
**zero references** to `validate.py`, `register_check`, `gate_precheck`, `bundle_readiness`, or
`build_graph`. Verified non-overlapping; parked in `tangential-items.md`.
