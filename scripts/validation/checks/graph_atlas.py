"""Provenance-graph and derived-atlas checks — ADR-009 Phase 2.

`graph_integrity` (orphans, conflicts, broken chains, the roster round-trip, the
findings-reach-the-graph guard and the supersession-ledger integrity scan),
`atlas_integrity` (ADR-005 D-F) and `atlas_hypothesis_discipline` (INFO-only
PD-2 visibility, ADR-007).

MOVED VERBATIM from `scripts/validate.py` — extracted by script from AST-verified
line ranges, not retyped. No body edited, no policy unified, no threshold retuned
(ADR-009 D4).

`check_atlas_integrity` is in the frozen external surface
(`tests/test_substrate_integrity_gates.py` imports it by name), so `validate`
re-exports it — see ADR-009 D2 item 8.

Import rules (identical in every module here): framework from
`validation._registry`; paths as `_H.<NAME>` at each use, NEVER a module-level
alias and never from `__file__` (H1 + the monkeypatch trap documented in
`checks/physics.py`); runtime flags by attribute on `validation._config`. No check
in this module reads a flag.

Execution order is owned by `validate._CANONICAL_ORDER` (H3), not by this file's
position in any import list.
"""
from __future__ import annotations

import json
from typing import List

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check


# ═══════════════════════════════════════════════════════════════════════
# CHECK 16: Knowledge graph integrity
# ═══════════════════════════════════════════════════════════════════════

@register_check("graph_integrity",
                "Knowledge graph integrity — orphans, conflicts, broken chains")
def check_graph_integrity() -> CheckResult:
    """CHECK 16: Build provenance graph and run integrity queries.

    Includes a roster round-trip guard (added 2026-07-31): every canonical
    bundle code must resolve through `build_graph._infer_bundle_from_text`.
    Without it, `D[1-9]` silently failed on every TWO-DIGIT code (D10/D11/D12,
    authorized 2026-06-29): the FLAGS-edge builder resolved no bundle, the
    readiness heatmap counted zero findings for all three, and D12 rendered
    "Blockers 0" while carrying 36 open ReviewFindings. It also produced FALSE
    FLAGS edges, since the paper-key text matcher fired in the bundle matcher's
    place. Any future roster extension now fails here rather than silently.
    """
    roster_details = []
    try:
        from build_graph import _infer_bundle_from_text
        _roster_is_derived = True
        try:
            from bundle_registry import VALID_BUNDLE_TARGETS as _roster
        except Exception:
            # ⚠️ A hardcoded roster validates the round-trip against a frozen
            # literal instead of the registry — which is the hand-maintained list
            # this check exists to replace. Defensible as a fallback; invisible
            # is not, so it now says so.
            _roster_is_derived = False
            _roster = frozenset(
                [f"D{i}" for i in range(1, 13)] + [f"L{i}" for i in range(1, 4)]
                + [f"I{i}" for i in range(1, 4)] + ["E1", "E2", "F"]
            )
        unresolved = sorted(c for c in _roster if _infer_bundle_from_text(c) != c)
        if unresolved:
            roster_details.append(Detail(
                "bundle_code_roundtrip", False,
                f"{len(unresolved)} roster bundle code(s) do not round-trip through "
                f"build_graph._infer_bundle_from_text: {', '.join(unresolved)}. "
                f"Review findings for these bundles are invisible to the FLAGS-edge "
                f"builder and the readiness heatmap will under-report them as zero.",
            ))
        else:
            roster_details.append(Detail(
                "bundle_code_roundtrip", True,
                f"all {len(_roster)} roster bundle codes resolve through the graph's "
                f"bundle inference (incl. two-digit D10-D12)"
                + ("" if _roster_is_derived else
                   " — ⚠️ measured against a HARDCODED fallback roster, not the "
                   "registry, because bundle_registry could not be imported"),
                warning=not _roster_is_derived,
                measured=_roster_is_derived,
            ))
    except Exception as exc:  # pragma: no cover
        # ⚠️ `passed=False`. This read `passed=True` with a comment saying "Was
        # `passed=True`" — i.e. the comment asserted a fix that had not been made,
        # which is precisely the defect this branch spent three rounds auditing
        # for. Caught by the closure reviewer. Skipping the round-trip for the
        # bundles the guard exists to protect (D10-D12 silently failed it) is not
        # evidence they round-trip.
        roster_details.append(Detail(
            "bundle_code_roundtrip", False,
            f"roster round-trip SKIPPED ({type(exc).__name__}: {exc}) — not "
            f"evidence the codes resolve", measured=False))

    # ── Orphaned-finding guard (added 2026-07-31, D11 round-5 BLOCKER 4.1) ────
    # A ReviewFinding that resolves to a bundle but emits no FLAGS edge is
    # INVISIBLE to Gate 11 FixPropagation and to the "a BLOCKER flips the
    # ReadinessGate to blocked" mechanism — so the gate passes vacuously. Ten
    # bundles were in exactly that state (D6-D12, I2, I3) because their only
    # PAPER_DRAFT_MAPPING sources are synthesis stubs with no Paper node, and
    # the fan-out silently skipped them. readiness_submission_gate reported
    # "D11 — all P1 passed" while six Stage-13 BLOCKERs sat unclosed on disk.
    # An unrecordable finding is indistinguishable from no finding, so make it
    # fail loudly.
    try:
        from build_graph import build_graph_json
        _g = build_graph_json()
        _edges = _g.get("edges") or _g.get("links") or []
        # ⚠️ PREDICATE STRENGTHENED 2026-07-31 (D11 round-6 BLOCKER 4.1). The first
        # version asked only "does this finding emit SOME FLAGS edge", which a
        # reviewer showed passes green under three mutations — including one that
        # reproduced the original defect exactly (retarget D11's 39 edges to a
        # source-paper stub: still "some edge", still PASS). It now asserts the
        # property that matters: a finding about bundle X flags `paper:X`.
        _tgt = {}
        for e in _edges:
            if e.get("type") == "FLAGS":
                _tgt.setdefault(e["source"], set()).add(e["target"])
        _findings = [n for n in _g.get("nodes", [])
                     if isinstance(n, dict) and n.get("type") == "ReviewFinding"]
        _orphans = [
            n["id"] for n in _findings
            if (n.get("meta") or {}).get("inferred_bundle")
            and f"paper:{n['meta']['inferred_bundle']}" not in _tgt.get(n["id"], set())
        ]
        # Second leg (closes mutation B): a finding whose bundle inference FAILS is
        # excluded from the scan above by construction, so the guard was blind to the
        # very layer-1 defect that started this class. Assert instead that every
        # review file named after a roster bundle yields findings that resolve.
        _by_file = {}
        for n in _findings:
            m = n.get("meta") or {}
            rf = m.get("review_file", "")
            stem = rf.rsplit("/", 1)[-1].removesuffix(".md")
            if stem in _roster:
                _by_file.setdefault(stem, []).append(m.get("inferred_bundle"))
        _unresolved_files = sorted(
            f for f, vals in _by_file.items() if not any(v == f for v in vals))
        if _orphans or _unresolved_files:
            _msgs = []
            if _orphans:
                _msgs.append(
                    f"{len(_orphans)} ReviewFinding(s) resolve to a bundle but emit no FLAGS "
                    f"edge to `paper:<that bundle>`: {', '.join(sorted(_orphans)[:3])}")
            if _unresolved_files:
                _msgs.append(
                    f"{len(_unresolved_files)} review file(s) named after a roster bundle "
                    f"yield no finding resolving to it: {', '.join(_unresolved_files[:3])}")
            roster_details.append(Detail("findings_reach_the_graph", False, "; ".join(_msgs)))
        else:
            roster_details.append(Detail(
                "findings_reach_the_graph", True,
                f"all {sum(1 for n in _findings if (n.get('meta') or {}).get('inferred_bundle'))} "
                f"bundle-resolved findings flag their own bundle, and every bundle-named review "
                f"file resolves",
            ))
    except Exception as exc:  # pragma: no cover
        # FAIL, not pass: this guard exists to make invisible findings visible, so a
        # build error in the scan must not be indistinguishable from a clean scan
        # (D12 round-6 finding 8.2 — the original `warning=True` failed open).
        roster_details.append(Detail(
            "findings_reach_the_graph", False,
            f"orphan scan could not run ({type(exc).__name__}: {exc}) — treat as unverified"))

    # ── Supersession-ledger referential integrity (D12 round-6 finding 4.1) ──
    # Findings raised in rounds whose review document was never written to disk
    # were filed under an EARLIER review's IDs. That both collides with live
    # findings (a still-open finding rendered `fixed`) and mints dangling IDs
    # naming no node. Neither is detectable from the ledger alone.
    try:
        _led = json.loads(
            (_H.DOCS_DIR / "review_finding_supersessions.json")   # ADR-009 H1
            .read_text(encoding="utf-8"))
        _entries = _led.get("supersessions", [])
        _known = {n["id"] for n in _g.get("nodes", [])
                  if isinstance(n, dict) and n.get("type") == "ReviewFinding"}
        # Scope to the `review:<date-dir>:<name>:<section>` scheme, which is the one
        # extract_review_finding_nodes mints nodes for. Legacy Stage-9/10 records use
        # an unrelated `bundle-stage10:...` scheme and were never graph nodes, so
        # flagging them would be noise, not signal.
        _dangling = sorted({e["finding_id"] for e in _entries
                            if e.get("finding_id", "").startswith("review:")
                            and e["finding_id"] not in _known})
        # Baseline re-measured 2026-08-01 (D11 Stage-13 round-13 finding 2220:4.5). It was
        # pinned at 67 against a population of 66, i.e. it carried one slot of headroom in
        # which a NEW dangling record could be filed without failing — in the one guard
        # whose whole purpose is to catch newly-filed closures that name nothing.
        #
        # Its justifying comment was also wrong about the population it describes. Measured:
        # of the 66, 53 use annotated IDs and 13 do not — the comment claimed all 67 were
        # annotated. 67 was the count of ledger ids MENTIONING stage9/stage10, a different
        # population that happened to be one larger.
        #
        # Pinned to the exact count, so any growth fails on the first record.
        _LEDGER_DANGLING_BASELINE = 66
        #
        # ⚠️ A CLAIM I MADE HERE WAS WRONG, retracted 2026-08-01. I wrote that this guard
        # "does not run" and reported it as a twelfth defect, on the strength of a mutation
        # test that planted a dangling record and saw no `ledger_ids_resolve` detail. The
        # test was invoking `check_bundle_registry_consistency`. This guard lives in
        # `check_graph_integrity` (line ~3261) — a different check entirely — so of course
        # it emitted nothing there.
        #
        # Re-tested against the right host: baseline reports "66 dangling ... no growth" and
        # PASSES; planting one dangling record reports "67 ... above the pinned baseline of
        # 66" and FAILS. The guard works, and the baseline correction above is what makes
        # the growth case fail at exactly one record.
        #
        # I found a real defect (the 67-vs-66 headroom), then manufactured a second one out
        # of my own testing error and committed it as a finding. Diagnosing by running the
        # wrong function is the same class of mistake as measuring the wrong quantity, which
        # is what produced the eleven genuine instances this session.
        if len(_dangling) > _LEDGER_DANGLING_BASELINE:
            _s = ", ".join(_dangling[:4])
            roster_details.append(Detail(
                "ledger_ids_resolve", False,
                f"{len(_dangling)} supersession finding_id(s) name no ReviewFinding node, "
                f"above the pinned baseline of {_LEDGER_DANGLING_BASELINE} — a closure filed "
                f"against a nonexistent finding closes nothing: {_s}",
            ))
        elif _dangling:
            roster_details.append(Detail(
                "ledger_ids_resolve", True,
                f"{len(_dangling)} dangling supersession finding_id(s) (pre-existing annotated-ID "
                f"debt, baseline {_LEDGER_DANGLING_BASELINE}); no growth",
                warning=True,
            ))
        else:
            roster_details.append(Detail(
                "ledger_ids_resolve", True,
                f"all review:-scheme supersession finding_ids resolve to ReviewFinding nodes "
                f"({len(_entries)} entries scanned)",
            ))
    except Exception as exc:  # pragma: no cover
        # FAIL, not warn (2026-08-01). This handler returned passed=True, so ANY exception
        # in the scan made the guard silently absent — which is exactly the state a
        # mutation test found it in: planting a dangling record left the check green with
        # no `ledger_ids_resolve` detail emitted at all. A guard that cannot run must say
        # so loudly; this one exists to catch closures naming nothing, and three such
        # records were filed this session while it was inert.
        roster_details.append(Detail(
            "ledger_ids_resolve", False,
            f"ledger integrity scan FAILED TO RUN ({type(exc).__name__}: {exc}) — the "
            f"dangling-closure guard did not execute, so its silence is not evidence"))

    try:
        from graph_integrity import run_integrity_checks
    except ImportError as exc:
        # ⚠️ UNMEASURED, not passing. `run_integrity_checks` IS this check's
        # substantive body; without it the roster legs are all that ran, and a
        # passing `Detail("import", True, ...)` made the whole thing count as a
        # full measurement toward the `--ci` coverage floor.
        # ⚠️ `passed=False`, not `all(roster_details)`. The verdict was computed
        # over the roster legs only, and the failing `import` Detail was appended
        # AFTERWARDS — so a plain `validate.py` run printed `✓ PASS
        # graph_integrity` while `run_integrity_checks`, this check's entire
        # substantive body, had not run. `measured=False` covered the `--ci` path
        # but `all_passed` is computed on EVERY path.
        #
        # `warning` dropped: `_registry.Detail` documents it as "passed but with
        # an advisory warning", and `passed=False, warning=True` is outside that
        # contract. `passed=False` + `measured=False` already carry the meaning.
        return CheckResult(
            passed=False,
            measured=False,
            details=roster_details + [
                Detail("import", False,
                       f"graph_integrity not available ({exc}) — the integrity "
                       f"scan DID NOT RUN, so its silence is not evidence",
                       measured=False),
            ])

    report = run_integrity_checks()
    s = report['summary']

    details = []

    # Graph size (informational)
    details.append(Detail(
        "graph_size", True,
        f"{s['total_nodes']} nodes, {s['total_edges']} edges",
    ))

    # Conflicts are hard failures
    if s['conflicts'] > 0:
        conflict_names = ', '.join(c['name'] for c in report['conflicts'][:5])
        suffix = f" (+{s['conflicts'] - 5} more)" if s['conflicts'] > 5 else ""
        details.append(Detail(
            "conflicts", False,
            f"{s['conflicts']} verification conflicts: {conflict_names}{suffix}",
        ))
    else:
        details.append(Detail("conflicts", True, "No verification conflicts"))

    # Orphan CLAIM nodes are a HARD FAIL (R-06 regression guard). Every discovered
    # paper claim must be CLAIMS-connected to its paper; a non-zero count means
    # paper/claim discovery drifted out of sync. Distinct from generic orphans
    # below (unconnected Lean declaration nodes are expected substrate).
    orphan_claims = s.get('orphan_claims', 0)
    if orphan_claims > 0:
        oc_sample = ', '.join(o['id'] for o in report.get('orphan_claims', [])[:5])
        oc_suffix = f" (+{orphan_claims - 5} more)" if orphan_claims > 5 else ""
        details.append(Detail(
            "orphan_claims", False,
            f"{orphan_claims} orphan paper-claim nodes (no CLAIMS edge to a paper) — "
            f"paper/claim discovery is out of sync: {oc_sample}{oc_suffix}",
        ))
    else:
        details.append(Detail("orphan_claims", True,
                              "No orphan paper-claim nodes (all claims CLAIMS-connected)"))

    # Generic orphans (mostly unconnected Lean declaration nodes) are warnings.
    if s['orphans'] > 0:
        orphan_sample = ', '.join(o['id'] for o in report['orphan_nodes'][:5])
        suffix = f" (+{s['orphans'] - 5} more)" if s['orphans'] > 5 else ""
        details.append(Detail(
            "orphan_nodes", True,
            f"{s['orphans']} orphan nodes: {orphan_sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("orphan_nodes", True, "No orphan nodes"))

    # Ungrounded claims are warnings
    if s['ungrounded'] > 0:
        sample = ', '.join(u['id'] for u in report['ungrounded_claims'][:5])
        suffix = f" (+{s['ungrounded'] - 5} more)" if s['ungrounded'] > 5 else ""
        details.append(Detail(
            "ungrounded_claims", True,
            f"{s['ungrounded']} ungrounded claims: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("ungrounded_claims", True, "All claims grounded"))

    # Broken chains are warnings
    if s['broken_chains'] > 0:
        sample = ', '.join(b['formula'] for b in report['broken_chains'][:5])
        suffix = f" (+{s['broken_chains'] - 5} more)" if s['broken_chains'] > 5 else ""
        details.append(Detail(
            "broken_chains", True,
            f"{s['broken_chains']} broken provenance chains: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("broken_chains", True, "No broken provenance chains"))

    # Missing provenance are warnings
    if s['missing_provenance'] > 0:
        sample = ', '.join(m['name'] for m in report['missing_provenance'][:5])
        suffix = f" (+{s['missing_provenance'] - 5} more)" if s['missing_provenance'] > 5 else ""
        details.append(Detail(
            "missing_provenance", True,
            f"{s['missing_provenance']} params without SOURCED_FROM: {sample}{suffix}",
            warning=True,
        ))
    else:
        details.append(Detail("missing_provenance", True,
                              "All non-projected params have provenance sources"))

    # Hard failures: verification conflicts and orphan claim nodes (R-06 guard).
    passed = s['conflicts'] == 0 and s.get('orphan_claims', 0) == 0

    details = roster_details + details
    passed = passed and all(d.passed for d in roster_details)
    # ⚠️ M-D: the roster leg can fall back to a HARDCODED literal instead of the
    # registry (`_roster_is_derived`), and it marked only its own Detail. With no
    # derivation at the CheckResult, validating the round-trip against a frozen
    # list rather than the registry was invisible to the `--ci` floor and to the
    # JSON summary. Under this codebase's one policy — `measured=False` means the
    # POPULATION WAS UNREACHABLE — a roster read from a literal is exactly that:
    # the registry, which is the population, was not reached.
    return CheckResult(passed=passed,
                       measured=all(d.measured for d in roster_details),
                       details=details)


# ═══════════════════════════════════════════════════════════════════════
# CHECK: Derived proof-atlas integrity (ADR-005 D-F)
# ═══════════════════════════════════════════════════════════════════════

@register_check("atlas_integrity",
                "Derived proof-atlas (ADR-005) is consistent: no kind conflicts, no undisclosed "
                "project axioms, open nodes registry-backed, no apex silently closed")
def check_atlas_integrity() -> CheckResult:
    """Gate the derived atlas VIEW (``scripts/atlas_view.py``) — a projection of
    ``lean_deps.json`` ∪ ``HYPOTHESIS_REGISTRY`` ∪ ``AXIOM_METADATA``. ``native_decide`` compiler
    axioms are excluded from the axiom-taint leg (ADR-002 owns that surface). The
    ``apex_not_closed`` leg is ACTIVE as of Phase 2 (apexes = HEADLINE-tier open targets from the
    hypothesis registry; ADR-005 D-H)."""
    try:
        import atlas_view
        from src.core.constants import AXIOM_METADATA, HYPOTHESIS_REGISTRY
        lean_deps = atlas_view.load_lean_deps_file()
        atlas = atlas_view.build_atlas(lean_deps)
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, error=f"atlas build failed: {exc}")

    details: List[Detail] = []
    nodes = atlas["nodes"]
    unknowns = atlas["unknowns"]

    # (1) Kind consistency: no FQN classified as more than one atlas kind.
    seen: dict = {}
    conflicts = []
    for n in nodes:
        prev = seen.setdefault(n["fqn"], n["atlas_kind"])
        if prev != n["atlas_kind"]:
            conflicts.append(n["fqn"])
    details.append(Detail("kind_consistency", not conflicts,
        "no FQN has conflicting atlas kinds" if not conflicts
        else f"{len(conflicts)} FQNs with conflicting kinds: {conflicts[:5]}"))

    # (2) No undisclosed project axiom: every GENUINE project axiom (native_decide excluded) in any
    #     closure must be disclosed in AXIOM_METADATA. Currently 0 — catches a future stray axiom.
    allow = set(AXIOM_METADATA.keys())
    untracked = []
    for r in lean_deps:
        for a in atlas_view._genuine_project_axioms(r):
            if a.split(".")[-1] not in allow:
                untracked.append(f"{r['name']} <- {a}")
    details.append(Detail("no_undisclosed_project_axiom", not untracked,
        "all genuine project axioms disclosed in AXIOM_METADATA (or none)" if not untracked
        else f"{len(untracked)} undisclosed: {untracked[:5]}"))

    # (3) Every open (UNKNOWN) atlas node is registry-backed. The converse — no consumed
    #     unregistered Prop — is enforced by the tracked_hypothesis_ledger check.
    malformed = [u.get("id") for u in unknowns
                 if not str(u.get("id", "")).startswith("hyp:") or u.get("atlas_kind") != "UNKNOWN"]
    details.append(Detail("open_nodes_registry_backed", not malformed,
        f"{len(unknowns)} open nodes, all from HYPOTHESIS_REGISTRY" if not malformed
        else f"{len(malformed)} malformed open nodes: {malformed[:5]}"))

    # (4) Apex closure integrity (ADR-005 D-F/D-H). Apexes = HEADLINE-tier registry
    #     targets (`is_apex`). A discharge theorem's short name may be SUFFIXED
    #     (`H_Fib_v4_witness_unconditional` discharges key `H_Fib_v4_witness`), so
    #     exact-name matching alone misses silent discharges (R-07, 2026-07-20). Two
    #     failure modes:
    #       (a) SILENT closure — the apex is still marked OPEN but a producer theorem
    #           (exact key, or key + a recognized discharge suffix) already proves it;
    #       (b) BOGUS closure — the apex is marked DISCHARGED/SUPERSEDED but NO producer
    #           theorem is found (a closure with nothing behind it).
    #     An EXPLICITLY discharged apex backed by a real producer is correct → passes.
    apexes = [u for u in unknowns if u.get("is_apex")]
    proved = {n["fqn"] for n in nodes if n.get("atlas_status") == "PROVED"}
    proved_last = {fqn.split(".")[-1] for fqn in proved}
    _DISCHARGE_SUFFIXES = ("", "_unconditional", "_discharged", "_proven")

    def _apex_producer(key: str):
        for suf in _DISCHARGE_SUFFIXES:
            if (key + suf) in proved_last:
                return key + suf
        return None

    _OPEN_ST = ("STATED", "PLANNED", "ACTIVE", "OPEN")
    _CLOSED_ST = ("DISCHARGED", "SUPERSEDED")
    bad_apex = []
    open_apex_n = 0
    for u in apexes:
        key = str(u.get("id", ""))[len("hyp:"):]
        st = str(u.get("atlas_status", "")).upper()
        producer = _apex_producer(key)
        if st in _OPEN_ST:
            open_apex_n += 1
            if producer:
                bad_apex.append(f"{u.get('id')} (open but producer {producer} exists)")
        elif st in _CLOSED_ST and not producer:
            bad_apex.append(f"{u.get('id')} (marked {st} but no producer theorem found)")
    details.append(Detail("apex_not_closed", not bad_apex,
        (f"{len(apexes)} headline apex(es): {open_apex_n} open (none silently discharged), "
         f"{len(apexes) - open_apex_n} explicitly discharged (producer-verified)")
        if apexes and not bad_apex
        else ("no apex (headline-tier) nodes" if not apexes
              else f"{len(bad_apex)} apex integrity failure(s): {bad_apex[:5]}")))

    # (5) Every declared `dependent_theorems` FQN resolves to a real declaration.
    #     A short name absent from the ENTIRE declaration set is a PHANTOM target
    #     (hard fail; R-07 caught `SKEFTHawking.central_charge_from_sm`). A short name
    #     that exists but under a different full namespace is namespace DRIFT
    #     (advisory warning — the theorem exists, only the registry FQN prefix is stale).
    #     Resolve against the FULL declaration set (raw lean_deps), NOT the classified
    #     atlas `nodes` subset (which excludes many real decls and would false-flag them).
    all_fqns = {r.get("name") for r in lean_deps if isinstance(r, dict) and r.get("name")}
    all_short = {fqn.split(".")[-1] for fqn in all_fqns}
    phantoms, drift = [], []
    for hkey, h in HYPOTHESIS_REGISTRY.items():
        for dt in (h.get("dependent_theorems") or []):
            if dt in all_fqns:
                continue
            (drift if dt.split(".")[-1] in all_short else phantoms).append(f"{hkey}:{dt}")
    details.append(Detail("dependent_theorems_resolve", not phantoms,
        f"all {sum(len(h.get('dependent_theorems') or []) for h in HYPOTHESIS_REGISTRY.values())} "
        f"dependent_theorems FQNs resolve to a declaration"
        if not phantoms else f"{len(phantoms)} phantom target(s): {phantoms[:5]}"))
    if drift:
        details.append(Detail("dependent_theorems_namespace_drift", True,
            f"{len(drift)} ref(s) resolve by short name but the FQN namespace prefix "
            f"has drifted (advisory, not gating): {drift[:8]}", warning=True))

    passed = all(d.passed for d in details)
    return CheckResult(passed=passed, details=details)


def _hyp_module_stem(module):
    """Leading module-path token of an atlas ``module`` field (often annotated "Foo (Phase X...)")."""
    if not module:
        return "(none)"
    head = str(module).split("(", 1)[0].strip()
    toks = head.split()
    return toks[0] if toks else "(none)"


@register_check("atlas_hypothesis_discipline",
                "INFO: tracked-hypothesis distribution (total / gating vs orphan-landmark / per-module) "
                "for PD-2 visibility — NEVER a gate; the bank-or-grind discipline lives in the coach")
def check_atlas_hypothesis_discipline() -> CheckResult:
    """PD-2 visibility (``docs/dev-loops/proposals/hypothesis-banking-discharge.md``; reshaped
    2026-06-22 against live data + a deliberate design ruling). A tracked hypothesis is a DISCLOSED
    ASSUMPTION (a liability the project leans on), DISTINCT from accrued proved work (assets — PROVED /
    OBSTRUCTION nodes, which this check NEVER touches). On a clean tree most tracked hypotheses are
    legitimately ORPHAN (external-boundary / future landmarks that gate no current theorem — precise
    parked statements, not debt), so this is INFO-ONLY: it NEVER fails the build and NEVER culls
    anything. The real PD-2 discipline is PER-DECISION — the coach's bank-or-grind unlock-check (does a
    NEW assumption actually unlock the load-bearing residual?) + the stall-detector's route-proliferation.
    This check just reports the distribution so ``/debrief`` can SEE scatter developing without
    auto-failing."""
    try:
        import atlas_view
        atlas = atlas_view.build_atlas(atlas_view.load_lean_deps_file())
    except Exception as exc:  # noqa: BLE001
        return CheckResult(passed=False, error=f"atlas build failed: {exc}")
    unknowns = atlas["unknowns"]
    gating = [u for u in unknowns if (u.get("dependent_theorems") or [])]
    orphan = [u for u in unknowns if not (u.get("dependent_theorems") or [])]
    by_mod: dict = {}
    for u in unknowns:
        s = _hyp_module_stem(u.get("module"))
        by_mod[s] = by_mod.get(s, 0) + 1
    top = sorted(by_mod.items(), key=lambda kv: (-kv[1], kv[0]))[:3]
    details: List[Detail] = [
        Detail("tracked_hypotheses_total", True,
               f"{len(unknowns)} tracked hypotheses (disclosed assumptions; accrued PROVED/no-go assets are NOT counted here)"),
        Detail("gating_vs_orphan", True,
               f"{len(gating)} gate >=1 downstream theorem; {len(orphan)} orphan landmarks "
               f"(external-boundary / future — legitimately gate nothing yet; NOT debt, NOT culled)"),
        Detail("per_module_distribution", True,
               (f"open hypotheses over {len(by_mod)} modules; densest: " +
                ", ".join(f"{m}={c}" for m, c in top)) if by_mod else "no tracked hypotheses"),
    ]
    return CheckResult(passed=True, details=details)   # INFO-ONLY: never fails the build


#: Edge types a readiness gate may query while NO extractor emits them. Empty is the
#: target state, and the ratchet is the point: an entry here is a gate that returns a
#: verdict it did not compute.
#:
#: ⚠️ Both current entries are LIVE DEFECTS, kept only so the check reports them without
#: turning the whole suite red before the gates are repaired. `readiness_gates.py` queries
#: `PRODUCES` (Gate 8 ProductionRunHealth) and `SUPPORTS` (Gates 7/12 NarrativeGrounding,
#: FirstClaimSupport); `build_graph.py` emits neither, and the live graph contains zero of
#: each. Measured 2026-08-06: 18 ProductionRun nodes (17 status `unknown`) with ZERO
#: outgoing edges, so ProductionRunHealth's run-linkage leg cannot fire; and 9
#: `interesting` ProseClaims across 7 papers with zero outgoing edges, so
#: NarrativeGrounding blocks exactly those 7 — including D6, D8 and D10, whose ONLY P1
#: blocker it is — and passes vacuously for every other paper. One dead edge type
#: produces a false blocker and a silent pass at the same time.
#: `CONTRADICTS` is a THIRD instance, found by this check on its first run and NOT by the
#: audit that prompted it — which is the argument for deriving the population rather than
#: enumerating it. `extract_contradiction_nodes` is a documented stub (`return []`), so the
#: live graph holds 0 `Contradiction` nodes and 0 `CONTRADICTS` edges, and Gate
#: `ContradictionFree` computes `total = 0` and passes for every paper, always.
#: The lone `CONTRADICTS` string in `build_graph.py` is inside that stub's docstring.
GATE_EDGE_TYPES_WITHOUT_EMITTERS: dict[str, str] = {
    "PRODUCES": "readiness_gates Gate 8 (ProductionRunHealth); no extractor emits it",
    "SUPPORTS": "readiness_gates Gates 7/12 (NarrativeGrounding, FirstClaimSupport); "
                "no extractor emits it",
    "CONTRADICTS": "readiness_gates ContradictionFree; extract_contradiction_nodes is a "
                   "stub returning [], so the gate passes unconditionally",
}


@register_check(
    "gate_edge_types_are_emitted",
    "Every edge type a readiness gate queries is actually emitted by a graph extractor")
def check_gate_edge_types_are_emitted() -> CheckResult:
    """A gate that queries an edge type nothing emits does not measure anything.

    Both halves are wrong, and they arrive together. Where the gate's default is `passed`,
    the missing edge makes it pass unconditionally — absence of measurement rendered as
    success, the defect this whole audit exists to close, inside the P1 submission set.
    Where the default is `blocked`, it manufactures a blocker no evidence supports, and a
    bundle sits red for a reason nobody can act on.

    DERIVED on both sides, deliberately. The consumed set is read by walking
    `readiness_gates.py`'s AST for `idx.outgoing(...)` / `idx.incoming(...)` literals; the
    emitted set is read by walking `build_graph.py`'s AST for `'type': <literal>` in the
    edge dicts. Hand-listing either side is how the NEXT gate ships unguarded — the same
    enumerate-vs-derive failure the reachability and autogen work removed elsewhere.
    """
    import ast

    details: List[Detail] = []
    gates_py = _H.SCRIPT_DIR / "readiness_gates.py"
    graph_py = _H.SCRIPT_DIR / "build_graph.py"
    if not gates_py.exists() or not graph_py.exists():
        return CheckResult(passed=True, measured=False, details=[Detail(
            "sources_present", True,
            "readiness_gates.py or build_graph.py absent — nothing to measure",
            warning=True)])

    consumed: dict[str, int] = {}
    tree = ast.parse(gates_py.read_text())
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr in ("outgoing", "incoming")):
            for arg in node.args:
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str) \
                        and arg.value.isupper():
                    consumed.setdefault(arg.value, node.lineno)

    emitted: set[str] = set()
    gtree = ast.parse(graph_py.read_text())
    for node in ast.walk(gtree):
        if not isinstance(node, ast.Dict):
            continue
        # An EDGE dict, structurally: it carries `source` and `target` alongside
        # `type`. Without that clause this scan also collected every NODE dict's
        # `'type'`, since node dicts use the same key — 40 "emitted edge types"
        # against a true 22, the extra 18 being `Paper`, `Formula`, `AuditEvent`
        # and the rest of the node taxonomy (measured 2026-08-06).
        #
        # It read as harmless because no CamelCase node-type name collides with a
        # gate-queried edge name today, so the verdict was right by luck rather
        # than by scope. That is the failure mode this check exists to catch,
        # in the check itself: a guard whose population is wider than its
        # subject cannot fail on the case it was built for — here, an edge type
        # that never gets emitted but shares a name with some node type would
        # read as emitted forever.
        keys = {k.value for k in node.keys
                if isinstance(k, ast.Constant) and isinstance(k.value, str)}
        if not {"source", "target"} <= keys:
            continue
        for k, v in zip(node.keys, node.values):
            if (isinstance(k, ast.Constant) and k.value == "type"
                    and isinstance(v, ast.Constant) and isinstance(v.value, str)):
                emitted.add(v.value)
    # An extractor may also build the literal into a variable it appends; catch the
    # `edges.append({... 'type': X})` shape above plus any bare uppercase assignment to a
    # name ending in _TYPE, which is the other idiom in this file.
    for node in ast.walk(gtree):
        if isinstance(node, ast.Assign) and isinstance(node.value, ast.Constant) \
                and isinstance(node.value.value, str) and node.value.value.isupper():
            for t in node.targets:
                if isinstance(t, ast.Name) and t.id.endswith("_TYPE"):
                    emitted.add(node.value.value)

    if not consumed or not emitted:
        return CheckResult(passed=True, measured=False, details=[Detail(
            "ast_scan", True,
            f"AST scan found {len(consumed)} consumed / {len(emitted)} emitted edge types "
            "— one side is empty, so the comparison would be vacuous", warning=True)])

    dead = {t: ln for t, ln in sorted(consumed.items()) if t not in emitted}
    known = set(GATE_EDGE_TYPES_WITHOUT_EMITTERS)
    new = {t: ln for t, ln in dead.items() if t not in known}
    fixed = sorted(known - set(dead))

    details.append(Detail(
        "populations_derived", True,
        f"{len(consumed)} edge type(s) queried by gates, {len(emitted)} emitted by "
        f"extractors — both read from the AST, neither hand-listed"))

    details.append(Detail(
        "no_new_dead_edge_type", not new,
        f"{len(dead)} gate-queried edge type(s) have no emitter, all disclosed: "
        f"{sorted(dead)}"
        if not new else
        f"gate queries an edge type NO extractor emits, so the gate returns a verdict it "
        f"did not compute: {new} (disclosed already: {sorted(known)})",
        warning=bool(dead) and not new))

    if fixed:
        details.append(Detail(
            "stale_disclosure", False,
            f"{fixed} is listed in GATE_EDGE_TYPES_WITHOUT_EMITTERS but IS now emitted — "
            f"remove it, or the ratchet stops biting on the ones that remain"))

    return CheckResult(passed=not new and not fixed, details=details)
