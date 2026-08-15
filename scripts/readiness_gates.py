"""
SK-EFT Paper Readiness Gates (Phase 5v Wave 4)
==============================================

Implements the 11 readiness gates defined in
`docs/roadmaps/Phase5v_Roadmap.md`. Each gate evaluates a single paper
against one correctness dimension and returns a GateResult with state,
evidence, and blockers.

Gates (priority order — P1 before P2):

  P1 (correctness):
    1. CitationIntegrity       — arXiv/DOI / bibkey registry coverage
    2. CrossPaperConsistency   — no same-construct contradictions
    3. ParameterProvenance     — every referenced param human-verified
    4. ComputationCorrectness  — no bounds-only test coverage
    5. LeanProofSubstance      — no placeholder theorems cited
    6. AssumptionDisclosure    — hypothesis deps named in paper
    7. NarrativeGrounding      — "interesting" prose claims supported
    8. ProductionRunHealth     — no failed runs backing claims

  P2 (UX / trust):
    9. NumericalFreshness      — REPORTS edges fresh + autogen tables fresh + no inline literals
   10. FirstClaimVerification  — "first in proof assistant" ledger-backed
   11. FixPropagation          — ReviewFindings fixed/propagated

Paper aggregate: red if any P1 blocked, yellow if any P2 open, green otherwise.

The module is self-contained: takes a graph dict produced by
`build_graph.build_graph_json()` and returns a list of ReadinessGate node
payloads that `build_graph.extract_readiness_gate_nodes()` can emit.
"""

from __future__ import annotations

import logging
import re
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Literal

# ONE definition of the inline-literal predicate, shared with the
# `numerical_literals` check (audit QI-02). `validation._tex` imports nothing from
# the validation suite — same leaf property as `_config` / `_registry` — so this
# import cannot close a cycle with `validation.checks.bundles_readiness →
# readiness_gates`. Reaching this module requires `scripts/` on `sys.path`, which is
# already true of every importer of `readiness_gates` itself.
from validation._tex import find_inline_numerical_literals

logger = logging.getLogger(__name__)

GateState = Literal['open', 'in-review', 'passed', 'blocked', 'needs-recheck']

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"


@dataclass
class GateResult:
    """Per-(paper, gate) evaluation outcome."""
    gate: str
    paper: str
    priority: int
    state: GateState = 'open'
    evidence: list[str] = field(default_factory=list)
    blockers: list[str] = field(default_factory=list)
    notes: str = ''
    last_evaluated: str = ''
    #: False = this gate's evaluator COULD NOT MEASURE — an unreadable draft, an
    #: absent artifact. Additive with a True default, exactly as `CheckResult.
    #: measured` is, and for the identical reason one layer down.
    #:
    #: ⚠️ `state='open'` was carrying two meanings: "measured, and genuinely
    #: outstanding" and "the evaluator read nothing". `paper_aggregate_state` maps
    #: both to YELLOW, so a paper whose draft could not be opened was
    #: indistinguishable from one with real work left — the same defect
    #: `CheckResult.measured` was added to fix, in the sibling layer.
    #:
    #: ⚠️ NOT a sixth `GateState`. ADR-009 §Deferred item 4 declined `UNEVALUATED`
    #: on `passed` for the same D2-contract reason: `state` is read by consumers
    #: that would break on a new value. An additive field leaves them correct.
    measured: bool = True
    #: Identity of each blocker, for evaluators that had a node in hand (ADR-012 D15 S1).
    #:
    #: ⚠️ `blockers` is PROSE and always has been — a 60-character label slice. The finding
    #: id exists only inside the evaluator, which holds the whole `ReviewFinding` and then
    #: keeps the label. That single lossy step is why a blocker cell has nothing to drill
    #: through to, and why every `FLAGS` edge in the graph is invisible to the operator.
    #:
    #: ⚠️ ADDITIVE, deliberately. `blockers` keeps its meaning, so every evaluator that
    #: builds a prose list keeps working untouched and only the ones resolving real nodes
    #: populate this. Replacing `blockers` would have changed a field eleven evaluators and
    #: the node payload already agree on.
    blocker_refs: list[dict] = field(default_factory=list)

    #: Findings at BLOCKING severity that carry `status: accepted` — a recorded decision
    #: to live with the defect rather than a repair.
    #:
    #: ⚠️ THESE ARE DELIBERATELY NOT IN `blockers`, and that is exactly why they need
    #: their own field. `_eval_fix_propagation` partitions `accepted` out before the
    #: severity filter runs, so none of them reaches `r.blockers`, sets `state='blocked'`,
    #: or drives `needs-recheck` — correctly, because an accepted finding is a decision,
    #: not unclosed work. What was wrong is that they then appeared NOWHERE: a gate could
    #: read `passed` / "all review findings fixed" over a bundle carrying accepted
    #: criticals. Measured 2026-08-15: 31 project-wide, 12 critical and 19 major.
    #:
    #: Surfacing is not blocking. The state is unchanged; only the disclosure is added,
    #: so a reader sees "0 open, N accepted at blocking severity" rather than silence.
    #: (D12 Stage-13 rounds 8/9/10 finding 8.5.)
    accepted_blockers: list[dict] = field(default_factory=list)

    def to_node_payload(self) -> dict:
        shape_map = {'blocked': 'diamond', 'passed': 'square',
                     'needs-recheck': 'triangle', 'in-review': 'circle',
                     'open': 'square'}
        return {
            'id': f'gate:{self.paper}:{self.gate}',
            'type': 'ReadinessGate',
            'label': f'{self.gate} [{self.state}]',
            'name': self.gate,
            'verification': 'verified' if self.state == 'passed' else 'unverified',
            'detail': self.notes or f'{len(self.evidence)} evidence, {len(self.blockers)} blockers',
            'meta': {
                'paper': self.paper,
                'gate': self.gate,
                'priority': self.priority,
                'state': self.state,
                'measured': self.measured,
                'evidence': self.evidence[:50],
                # ⚠️ DISCLOSE THE CAPS, AND THESE TOTALS ARE NOW EXACT FOR ALL ELEVEN GATES.
                # `evidence[:50]` / `blockers[:50]` truncated silently since this method was
                # written. The first fix moved the cap out of `_eval_fix_propagation` ONLY,
                # which left ten evaluators slicing [:10] or [:20] BEFORE assigning — so
                # `blockers_total` was a post-truncation length for them, i.e. exactly the
                # "disclosure that lies" the sibling comment says must never exist, and
                # `blockers_truncated` (> 50) was structurally unreachable for all ten.
                # Nothing was wrong on screen — measured max was 16 against a cap of 20 —
                # but the headroom was four. Every evaluator now assigns its full list and
                # the cap lives here, at the one layer that can still see what it cut.
                'blockers': self.blockers[:50],
                'blockers_total': len(self.blockers),
                'blockers_truncated': len(self.blockers) > 50,
                'evidence_total': len(self.evidence),
                'evidence_truncated': len(self.evidence) > 50,
                'blocker_refs': self.blocker_refs[:50],
                'blocker_refs_total': len(self.blocker_refs),
                'blocker_refs_truncated': len(self.blocker_refs) > 50,
                'accepted_blockers': self.accepted_blockers[:50],
                'accepted_blockers_total': len(self.accepted_blockers),
                'accepted_blockers_truncated': len(self.accepted_blockers) > 50,
                'notes': self.notes,
                'last_evaluated': self.last_evaluated,
                'shape': shape_map.get(self.state, 'square'),
            },
        }


# ═══════════════════════════════════════════════════════════════════════
# Graph index helper — precomputes lookups used by every gate evaluator
# ═══════════════════════════════════════════════════════════════════════

class GraphIndex:
    """Precomputed lookups over the build_graph JSON so gate evaluators
    don't each re-scan the edge list."""

    def __init__(self, graph: dict):
        self.nodes = graph.get('nodes', [])
        self.edges = graph.get('links', [])
        self.by_id = {n['id']: n for n in self.nodes}
        self.by_type: dict[str, list[dict]] = defaultdict(list)
        for n in self.nodes:
            self.by_type[n['type']].append(n)
        self.out_edges: dict[str, list[dict]] = defaultdict(list)
        self.in_edges: dict[str, list[dict]] = defaultdict(list)
        for e in self.edges:
            self.out_edges[e['source']].append(e)
            self.in_edges[e['target']].append(e)

    def papers(self) -> list[dict]:
        return self.by_type.get('Paper', [])

    def outgoing(self, node_id: str, edge_type: str | None = None) -> list[dict]:
        edges = self.out_edges.get(node_id, [])
        return [e for e in edges if edge_type is None or e.get('type') == edge_type]

    def incoming(self, node_id: str, edge_type: str | None = None) -> list[dict]:
        edges = self.in_edges.get(node_id, [])
        return [e for e in edges if edge_type is None or e.get('type') == edge_type]

    def paper_tex(self, paper_key: str) -> str | None:
        """`paper_draft.tex` contents, or **None** when it cannot be read.

        ⚠️ This returned `''` for missing, unreadable, and genuinely-empty alike.
        **Seven call sites consume it; six reached a positive verdict on `''`, and
        `_eval_citation_integrity` is the only one that already branched.** Two of
        the six stated it outright: `_eval_parameter_provenance` concluded "no
        inline unit-bearing literals in body prose" and `_eval_narrative_grounding`
        emitted "and the draft has no abstract block" — a false statement about the
        draft, offered as the gate's own evidence. `None` forces each caller to
        decide.

        (This docstring said "two consumers" and `_unreadable_draft`'s said "three
        evaluators", in the same commit, for the same defect. Neither was the
        count. Enumerated here once, authoritatively.)
        """
        tex_path = PAPERS_DIR / paper_key / "paper_draft.tex"
        try:
            return tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            return None


def _unreadable_draft(r: GateResult) -> GateResult:
    """The one shape every evaluator uses when `paper_tex` returns None.

    ⚠️ `measured=False` is the load-bearing part. Without it an unreadable draft is
    a YELLOW gate indistinguishable from real outstanding work. For the count of
    affected consumers see `GraphIndex.paper_tex`, which owns that enumeration —
    this docstring used to carry a second, different count of the same thing.
    """
    r.state = 'open'
    r.measured = False
    r.notes = 'paper_draft.tex not readable — gate UNMEASURED, not outstanding'
    return r


# ═══════════════════════════════════════════════════════════════════════
# Gate evaluators (11 total — each returns a GateResult)
# ═══════════════════════════════════════════════════════════════════════

def _eval_citation_integrity(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 1 (P1): CitationIntegrity.

    Passes if every \\bibitem in the paper .tex has a matching
    CITATION_REGISTRY entry. Blocks when bibkeys appear that aren't
    registered. (DOI fetch-and-verify is deferred to Stage 13; this is
    the registry-coverage check.)
    """
    # ⚠️ A dead first assignment was removed here 2026-08-04 (audit QI-05):
    # `paper_key = paper['meta'].get('topic') or paper['name'] or ''` was computed
    # and then overwritten on the very next line by the `paper['id']` form. Every
    # other evaluator uses only the `paper['id']` form, which is the correct one —
    # `meta.topic` is a description, not a key.
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='CitationIntegrity', paper=paper_key, priority=1)

    tex = idx.paper_tex(paper_key)
    if tex is None:
        return _unreadable_draft(r)
    if not tex:
        r.state = 'open'
        r.notes = 'paper_draft.tex is empty'
        return r

    # `\bibitem[Label]{key}` carries an optional argument; the un-bracketed form
    # missed it entirely.
    bibkeys = set(re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}', tex))
    if not bibkeys:
        # ⚠️ NO BIBITEMS IS NOT NO CITATIONS. Measured 2026-08-09 across 67 drafts:
        # 61 use `\bibitem`, and 3 do not — D8, D10 and paper45. D8 and D10 each
        # carry SEVENTEEN distinct `\cite{}` keys via a bibtex `\bibliography{}`,
        # so their registry coverage was never checked and a P1 gate reported
        # `passed` on two Tier-1 bundles. `_eval_parameter_provenance` and
        # `_eval_narrative_grounding` were both given this corroborate-before-
        # passing branch on 2026-08-05; this sibling, directly above them, was not.
        cited = set(re.findall(r'\\cite[tp]?\*?(?:\[[^\]]*\])*\{([^}]+)\}', tex))
        cited = {k.strip() for group in cited for k in group.split(',') if k.strip()}
        if cited:
            r.state = 'open'
            r.notes = (f'no \\bibitem block, but {len(cited)} distinct \\cite key(s) '
                       f'are used — citation coverage NOT ESTABLISHED (the paper '
                       f'cites through \\bibliography{{}}; this gate can only read '
                       f'\\bibitem)')
            r.evidence.append(f'{len(cited)} cited keys, 0 verifiable here')
            return r
        r.state = 'passed'
        r.notes = 'no bibitems and no \\cite keys (paper has no bibliography)'
        return r

    # CITATION_REGISTRY entries via PrimarySource nodes (id = 'source:{key}')
    registered_keys = {n['id'].replace('source:', '', 1)
                       for n in idx.by_type.get('PrimarySource', [])}

    missing = sorted(bibkeys - registered_keys)
    r.evidence.append(f'{len(bibkeys)} bibitems, {len(bibkeys) - len(missing)} registered')
    if missing:
        r.blockers = [f'unregistered bibkey: {k}' for k in missing]
        r.state = 'blocked'
        r.notes = f'{len(missing)} bibkeys missing from CITATION_REGISTRY'
    else:
        r.state = 'passed'
        r.notes = 'all bibkeys registered'
    return r


def _eval_cross_paper_consistency(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 2 (P1): CrossPaperConsistency.

    Passes if this paper has no incoming/outgoing CONTRADICTS edges.
    Additionally flags when two papers REPORT different values for the
    same CountMetric (same metric, both stale).
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='CrossPaperConsistency', paper=paper_key, priority=1)

    contradicts_out = idx.outgoing(paper['id'], 'CONTRADICTS')
    contradicts_in = idx.incoming(paper['id'], 'CONTRADICTS')
    total = len(contradicts_out) + len(contradicts_in)

    # Compare this paper's REPORTS edges against other papers' REPORTS
    # for the same CountMetric — flag when two papers report different
    # values for the same metric
    my_reports = {e['target']: e.get('paper_value')
                  for e in idx.outgoing(paper['id'], 'REPORTS')}
    inconsistencies = 0
    for metric_id, my_val in my_reports.items():
        for other_paper in idx.papers():
            if other_paper['id'] == paper['id']:
                continue
            for e in idx.outgoing(other_paper['id'], 'REPORTS'):
                if e['target'] == metric_id and e.get('paper_value') != my_val:
                    inconsistencies += 1
                    r.evidence.append(
                        f'{metric_id.replace("count:","",1)}: this={my_val} '
                        f'vs {other_paper["id"]}={e.get("paper_value")}'
                    )
                    break

    if total > 0:
        r.blockers = [f'{e["target"]}: {e.get("conflict_detail","")}' for e in contradicts_out]
        r.state = 'blocked'
        r.notes = f'{total} CONTRADICTS edges'
    elif inconsistencies > 0:
        r.state = 'needs-recheck'
        r.notes = f'{inconsistencies} inter-paper count disagreements'
    else:
        r.state = 'passed'
        r.notes = 'no contradictions detected'
    return r


def _eval_parameter_provenance(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 3 (P1): ParameterProvenance.

    Every Parameter the paper DEPENDS_ON must have a human_verified_date.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='ParameterProvenance', paper=paper_key, priority=1)

    deps = idx.outgoing(paper['id'], 'DEPENDS_ON')
    param_ids = [e['target'] for e in deps if e['target'].startswith('param:')]
    unverified = []
    verified = []
    for pid in param_ids:
        p = idx.by_id.get(pid)
        if not p:
            continue
        human_date = p.get('meta', {}).get('human_verified_date')
        if human_date:
            verified.append(pid)
        else:
            unverified.append(pid)

    r.evidence.append(f'{len(param_ids)} parameters depended on; {len(verified)} human-verified')
    if not param_ids:
        # ⚠️ CORROBORATE BEFORE PASSING VACUOUSLY (2026-08-05, PR-review pass 2).
        # `param_ids` comes from GRAPH edges, so an empty list means either "this
        # paper genuinely depends on no parameters" or "the extraction failed to
        # link them" — and this branch could not tell them apart. It passed either
        # way, so a physics paper full of numbers whose parameters were never
        # linked read as PROVENANCE-CLEAN.
        #
        # That is exactly the case a referee raises and the author should not have
        # to discover unaided, which is what this gate family exists for. So:
        # cross-check the paper's OWN .tex, as `_eval_citation_integrity` already
        # does. Unit-bearing numerical literals with zero parameter edges is a
        # linkage failure, not a clean bill.
        #
        # `open`, not `blocked`: the paper may be fine and the GRAPH at fault, so
        # this surfaces to the reviewer (YELLOW) without reddening a corpus where
        # 61 papers are already red. "Not established" is the honest state.
        tex = idx.paper_tex(paper_key)
        if tex is None:
            return _unreadable_draft(r)
        # ⚠️ Returns (stripped_text, matches) — a 2-tuple, ALWAYS truthy. My first
        # draft wrote `literals = find_inline_numerical_literals(tex)` and tested it
        # for truth, so this branch fired for every paper regardless of content, and
        # the "58 papers carry unit-bearing numbers" figure I reported was an
        # artifact of tuple truthiness, not a measurement. The sibling caller at
        # :635 already unpacks correctly.
        _, literals = find_inline_numerical_literals(tex) if tex else ("", [])
        if literals:
            r.state = 'open'
            r.notes = (f'NOT ESTABLISHED — no parameter dependencies in the graph, but '
                       f'the draft carries {len(literals)} unit-bearing numerical '
                       f'literal(s). Either the paper declares no parameters (clean) or '
                       f'the extraction did not link them (nothing was checked).')
            r.evidence.append(f'{len(literals)} unit-bearing literals in the draft')
        else:
            r.state = 'passed'
            # ⚠️ "no INLINE literals", which is narrower than "no numbers". By design
            # `find_inline_numerical_literals` strips `\input{tables/...}` and
            # `\caption{}` — generated tables are the compliant mechanism, so counting
            # them would penalise compliance. MEASURED 2026-08-05: **31 of 64 drafts**
            # read as literal-free while pulling numbers through `\input`. For
            # generated tables that is defensible (their provenance is structural, from
            # `render_paper_tables.py`), and `counts.tex` carries counts rather than
            # experimental parameters — but it is NOT the same claim as "this paper uses
            # no parameters", so do not word it that way.
            r.notes = ('no parameter dependencies declared, and no inline unit-bearing '
                       r'literals in body prose (numbers arriving via \input{tables/} or '
                       'counts.tex are structurally sourced and not counted here)')
    elif unverified:
        # Treat as blocked for submission but acceptable during draft
        r.blockers = [p.replace('param:', '', 1) for p in unverified]
        r.state = 'blocked'
        r.notes = f'{len(unverified)} parameters lack human_verified_date'
    else:
        r.state = 'passed'
        r.notes = 'all dependent parameters human-verified'
    return r


def _eval_computation_correctness(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 4 (P1): ComputationCorrectness — the k_H² failure mode.

    For each Formula this paper GROUNDED_IN, check the Formula's
    incoming VERIFIES edges. If NO test has test_kind ∈ {golden,
    identity, roundtrip}, and it has only bounds-only coverage, block
    the gate.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='ComputationCorrectness', paper=paper_key, priority=1)

    # Formulas this paper depends on: follow CLAIMS→PaperClaim→GROUNDED_IN→Formula
    formula_ids: set[str] = set()
    for claim_edge in idx.outgoing(paper['id'], 'CLAIMS'):
        claim_id = claim_edge['target']
        for ge in idx.outgoing(claim_id, 'GROUNDED_IN'):
            if ge['target'].startswith('formula:'):
                formula_ids.add(ge['target'])

    # Also include formulas listed in the paper's meta['formulas']
    for f_name in paper.get('meta', {}).get('formulas', []):
        formula_ids.add(f'formula:{f_name}')

    bounds_only: list[str] = []
    no_tests: list[str] = []
    strong: list[str] = []
    # ⚠️ Formulas the paper names that are NOT IN THE GRAPH are dropped by the
    # `continue` below. They must be COUNTED, not silently skipped: the evidence
    # line reported `len(formula_ids)` as the number examined while the three
    # buckets summed to fewer, so the gate asserted test coverage of formulas it
    # had never looked at. A self-refuting evidence string ("6 formulas ... 1
    # strong, 0 bounds-only, 0 no tests") is the only thing that made it visible.
    absent: list[str] = []
    for fid in formula_ids:
        if fid not in idx.by_id:
            absent.append(fid)
            continue
        v_edges = [e for e in idx.incoming(fid, 'VERIFIES')]
        if not v_edges:
            no_tests.append(fid)
            continue
        kinds = {e.get('test_kind', 'unknown') for e in v_edges}
        if kinds - {'bounds', 'unknown'} == set():
            bounds_only.append(fid)
        else:
            strong.append(fid)

    # The four buckets now partition `formula_ids` exactly: strong + bounds_only
    # + no_tests + absent == len(formula_ids). If that ever stops holding, the
    # line is lying again.
    assert len(strong) + len(bounds_only) + len(no_tests) + len(absent) == len(formula_ids)
    r.evidence.append(
        f'{len(formula_ids)} formulas grounding paper claims '
        f'({len(strong)} with golden/identity/roundtrip, '
        f'{len(bounds_only)} bounds-only, {len(no_tests)} no tests, '
        f'{len(absent)} NOT IN GRAPH — not examined)'
    )
    if absent:
        r.evidence.append(
            f'⚠️ {len(absent)} named formula(s) absent from the graph, so this '
            f'gate says NOTHING about their test coverage: '
            f'{", ".join(sorted(absent)[:5])}'
            + (' …' if len(absent) > 5 else '')
        )

    # R-06 WARN: surface formulas this paper grounds on whose Lean grounding does
    # NOT resolve to a real theorem (graph verification 'unverified') or is only a
    # definitional record — the honest-label distinction. This is advisory (it does
    # not change the test-coverage blocking semantics above) but makes an
    # unresolved formula mapping visible instead of silently accepted.
    unresolved_grounding = sorted(
        fid.replace('formula:', '', 1)
        for fid in formula_ids
        if fid in idx.by_id and idx.by_id[fid].get('verification') == 'unverified'
    )
    definitional_grounding = sorted(
        fid.replace('formula:', '', 1)
        for fid in formula_ids
        if fid in idx.by_id
        and idx.by_id[fid].get('verification') == 'definitional-record'
    )
    if unresolved_grounding:
        r.evidence.append(
            f'WARN: {len(unresolved_grounding)} grounding formula(s) have no '
            f'resolving Lean theorem (unverified): '
            f'{", ".join(unresolved_grounding[:10])}'
        )
    if definitional_grounding:
        r.evidence.append(
            f'NOTE: {len(definitional_grounding)} grounding formula(s) are '
            f'definitional records (not independent derivations): '
            f'{", ".join(definitional_grounding[:10])}'
        )
    if bounds_only or no_tests:
        r.blockers = (
            [f'bounds-only: {b.replace("formula:","",1)}' for b in bounds_only] +
            [f'no tests: {b.replace("formula:","",1)}' for b in no_tests]
        )
        r.state = 'blocked'
        r.notes = (f'{len(bounds_only)} formulas bounds-only + '
                   f'{len(no_tests)} formulas untested')
    elif not formula_ids:
        r.state = 'open'
        r.notes = 'no grounded formulas — nothing to verify'
    else:
        r.state = 'passed'
        r.notes = f'all {len(formula_ids)} grounded formulas have substantive tests'
    return r


def _eval_lean_proof_substance(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 5 (P1): LeanProofSubstance.

    Fail if any Lean theorem this paper cites (via VERIFIED_BY reverse
    lookup from its grounding Formulas) also has a PlaceholderMarker node.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='LeanProofSubstance', paper=paper_key, priority=1)

    # Lean theorems cited by this paper — two sources:
    # (a) Formulas GROUNDED_IN paper claims → VERIFIED_BY theorems
    # (b) Theorem names mentioned directly in paper .tex via \texttt
    theorem_ids: set[str] = set()
    for claim_edge in idx.outgoing(paper['id'], 'CLAIMS'):
        claim_id = claim_edge['target']
        for ge in idx.outgoing(claim_id, 'GROUNDED_IN'):
            formula_id = ge['target']
            for ve in idx.outgoing(formula_id, 'VERIFIED_BY'):
                if ve['target'].startswith('lean:'):
                    theorem_ids.add(ve['target'])

    # Placeholder set by short-name
    placeholder_labels = {n['name']
                          for n in idx.by_type.get('PlaceholderMarker', [])}

    # Theorems cited by short name in prose.
    #
    # ⚠️ Reuse the shared extractor — do NOT re-implement this. Bundle drafts write Lean
    # references in several verbatim forms (`\texttt{}`, preamble aliases such as D8/D9's
    # `\lean{}` and D11/D12's `\thm{}`/`\mthm{}`, and `\verb`), and a `\texttt`-only regex
    # reaches a small fraction of them. `_extract_prose_lean_candidates` discovers the
    # forms structurally and applies the project's Lean-identifier candidate filter, so
    # this gate and `prose_theorem_reference_coverage` cannot drift apart.
    from validation.checks.prose_lean_refs import _extract_prose_lean_candidates
    tex = idx.paper_tex(paper_key)
    if tex is None:
        return _unreadable_draft(r)
    referenced_short_names = {tok.rsplit('.', 1)[-1]
                              for tok, _offset in _extract_prose_lean_candidates(tex)}

    # Which cited theorems resolve to a placeholder?
    flagged = []
    for short_name in referenced_short_names:
        if short_name in placeholder_labels:
            flagged.append(short_name)
    for tid in theorem_ids:
        short = tid.rsplit('.', 1)[-1]
        if short in placeholder_labels:
            flagged.append(short)

    flagged = sorted(set(flagged))
    r.evidence.append(
        f'{len(theorem_ids)} theorems cited via formulas; '
        f'{len(referenced_short_names)} via \\texttt; '
        f'{len(flagged)} overlap with PlaceholderMarkers'
    )
    if flagged:
        r.blockers = [f'placeholder cited: {n}' for n in flagged]
        r.state = 'blocked'
        r.notes = f'{len(flagged)} cited theorems are placeholders (rfl / Equiv.refl / trivial)'
    else:
        r.state = 'passed'
        r.notes = 'no placeholder theorems cited'
    return r


def _eval_assumption_disclosure(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 6 (P1): AssumptionDisclosure.

    For every Hypothesis a cited theorem ASSUMES, the hypothesis key
    should appear in the paper .tex. Soft heuristic — matches by key
    substring.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='AssumptionDisclosure', paper=paper_key, priority=1)

    # Collect hypotheses that paper-cited theorems assume
    # (follow same path as gate 5)
    assumed_hyp_ids: set[str] = set()
    for claim_edge in idx.outgoing(paper['id'], 'CLAIMS'):
        for ge in idx.outgoing(claim_edge['target'], 'GROUNDED_IN'):
            for ve in idx.outgoing(ge['target'], 'VERIFIED_BY'):
                for ae in idx.outgoing(ve['target'], 'ASSUMES'):
                    if ae['target'].startswith('hyp:'):
                        assumed_hyp_ids.add(ae['target'])

    _tex_raw = idx.paper_tex(paper_key)
    if _tex_raw is None:
        return _unreadable_draft(r)
    tex = _tex_raw.lower()
    undisclosed: list[str] = []
    disclosed: list[str] = []
    for hid in assumed_hyp_ids:
        hyp_node = idx.by_id.get(hid)
        if not hyp_node:
            continue
        key = hid.replace('hyp:', '', 1).lower()
        human_name = (hyp_node.get('name', '') or '').lower()
        found = key in tex or (human_name and human_name[:30] in tex)
        if found:
            disclosed.append(key)
        else:
            undisclosed.append(key)

    r.evidence.append(
        f'{len(assumed_hyp_ids)} hypotheses assumed by cited theorems; '
        f'{len(disclosed)} referenced in paper, {len(undisclosed)} undisclosed'
    )
    if undisclosed:
        r.blockers = [f'undisclosed hypothesis: {k}' for k in undisclosed]
        r.state = 'blocked'
        r.notes = f'{len(undisclosed)} hypothesis dependencies not named in paper'
    elif not assumed_hyp_ids:
        # ⚠️ VACUOUS PASS — and measured 2026-08-10 to be vacuous for **every** paper
        # in the corpus, so this gate contributes no evidence at all today.
        #
        # It is a genuine pass, not a measurement failure: the 4-hop walk
        # (CLAIMS -> GROUNDED_IN -> VERIFIED_BY -> ASSUMES) RUNS and lands on an
        # empty set, so `measured` stays True per THE ONE POLICY (empty population
        # reached != population unreachable). What was wrong is that "passed" read
        # as "disclosure was verified" when nothing was checked.
        #
        # The structural cause, measured: the walk reaches 122 theorem nodes; 66
        # lean nodes carry an ASSUMES edge; the two sets are DISJOINT (intersection
        # 0). The hypothesis-bearing theorems are simply not cited by any paper's
        # claim chain. That is a real wiring signal, not noise — if a future wave
        # cites one, this gate starts doing work, and if it never does, the gate
        # should be retired rather than left as decorative green.
        r.state = 'passed'
        r.notes = ('VACUOUS: no cited theorem assumes any hypothesis, so nothing was '
                   'checked — this pass is not evidence of disclosure')
        r.evidence.append(
            'vacuous pass: the CLAIMS->GROUNDED_IN->VERIFIED_BY->ASSUMES walk reached '
            'no hyp: node for this paper. Corpus-wide this holds for every paper '
            '(measured 2026-08-10), because the theorems that carry ASSUMES edges are '
            'disjoint from those any paper cites.')
    else:
        r.state = 'passed'
        r.notes = 'all hypothesis dependencies disclosed in paper'
    return r


def _eval_narrative_grounding(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 7 (P1): NarrativeGrounding.

    Every ProseClaim for this paper that's tagged `interesting` should
    have a SUPPORTS edge to a formal artifact. Fail for each unsupported
    interesting claim.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='NarrativeGrounding', paper=paper_key, priority=1)

    prose_claims = [n for n in idx.by_type.get('ProseClaim', [])
                    if n.get('meta', {}).get('paper') == paper_key]
    interesting = [n for n in prose_claims if n.get('meta', {}).get('interesting')]
    unsupported: list[str] = []
    for pc in interesting:
        supports = idx.outgoing(pc['id'], 'SUPPORTS')
        if not supports:
            tags = pc.get('meta', {}).get('tags', [])
            tag_str = '/'.join(tags) or 'untagged'
            unsupported.append(f'[{tag_str}] {pc["label"]}')

    r.evidence.append(
        f'{len(prose_claims)} abstract sentences; {len(interesting)} flagged interesting; '
        f'{len(interesting) - len(unsupported)} have SUPPORTS edges'
    )
    if unsupported:
        r.blockers = unsupported
        r.state = 'blocked'
        r.notes = f'{len(unsupported)} "interesting" prose claims lack formal support'
    elif not interesting:
        # ⚠️ CORROBORATE (2026-08-05, PR-review pass 2) — same shape as
        # ParameterProvenance above. `prose_claims` are GRAPH nodes filtered by
        # `meta.paper`, so zero of them means either "the abstract makes no
        # interesting claims" or "the abstract was never extracted". A paper whose
        # prose was never ingested passed NarrativeGrounding cleanly.
        #
        # A draft with an abstract but NO ProseClaim nodes at all is an extraction
        # gap: the gate verified nothing. `open`, so the reviewer sees it.
        tex = idx.paper_tex(paper_key)
        if tex is None:
            return _unreadable_draft(r)
        has_abstract = '\\begin{abstract}' in tex
        if has_abstract and not prose_claims:
            r.state = 'open'
            r.notes = ('NOT ESTABLISHED — the draft has an abstract but NO ProseClaim '
                       'nodes exist for it, so no narrative claim was examined. Either '
                       'the abstract makes no interesting claims (clean) or prose '
                       'extraction did not run for this paper (nothing was checked).')
        else:
            r.state = 'passed'
            r.notes = ('no interesting prose claims flagged'
                       + ('' if prose_claims else ' (and the draft has no abstract block)'))
    else:
        r.state = 'passed'
        r.notes = 'all interesting claims have SUPPORTS edges'
    return r


def _eval_production_run_health(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 8 (P1): ProductionRunHealth.

    For every ProductionRun with PRODUCES→this paper's claim, status
    must be 'success'. Also: if paper prose contains "Monte Carlo
    evidence" or similar, require at least one successful run linked.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='ProductionRunHealth', paper=paper_key, priority=1)

    # Find production runs linked to this paper's claims
    relevant_runs: list[dict] = []
    paper_node_ids = {paper['id']}
    for claim_edge in idx.outgoing(paper['id'], 'CLAIMS'):
        paper_node_ids.add(claim_edge['target'])
    for run in idx.by_type.get('ProductionRun', []):
        produces = idx.outgoing(run['id'], 'PRODUCES')
        if any(e['target'] in paper_node_ids for e in produces):
            relevant_runs.append(run)

    failed = [r_ for r_ in relevant_runs
              if r_.get('meta', {}).get('status') not in ('success', None)]

    # Detect "MC evidence" claim without backing success
    tex = idx.paper_tex(paper_key)
    if tex is None:
        return _unreadable_draft(r)
    mc_claim = bool(re.search(r'\b(Monte\s+Carlo\s+evidence|MC\s+evidence)\b', tex, re.IGNORECASE))
    success_runs = [r_ for r_ in relevant_runs
                    if r_.get('meta', {}).get('status') == 'success']

    r.evidence.append(f'{len(relevant_runs)} production runs linked, '
                      f'{len(success_runs)} successful, {len(failed)} failed')
    if failed:
        r.blockers = [f'failed run: {r_.get("name","?")} ({r_.get("meta",{}).get("status")})'
                      for r_ in failed]
        r.state = 'blocked'
        r.notes = f'{len(failed)} failed/unknown ProductionRuns linked to paper'
    elif mc_claim and not success_runs:
        r.state = 'blocked'
        r.notes = ('paper prose claims "Monte Carlo evidence" but no '
                   'successful ProductionRun is linked')
        r.blockers = ['MC evidence claim without successful run']
    else:
        r.state = 'passed'
        r.notes = ('no MC claim and no failed runs' if not relevant_runs
                   else 'all linked runs successful')
    return r


def _eval_numerical_freshness(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 9 (P2): NumericalFreshness.

    Fails if any of:
      - a REPORTS edge to CountMetric has stale=True
      - the paper has inline unit-bearing numerical literals outside of
        \\input{tables/...} blocks (proxy: count inline literals in the
        paper .tex)
      - autogen tables/*.tex files for this paper are stale relative to
        their spec / source mtimes (proxy: check if newer tables.py
        newer than matching tables/*.tex)

    Renamed from `CountFreshness` (Phase 5v, tables.py framework): the
    same anti-drift principle applies to all numerical content, not
    just count metrics. Evaluation considers both count-level and
    table-level freshness.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='NumericalFreshness', paper=paper_key, priority=2)

    # --- 1. REPORTS→CountMetric drift (count-literal layer) ---
    reports = idx.outgoing(paper['id'], 'REPORTS')
    stale_reports = [e for e in reports if e.get('stale')]

    # --- 2. Inline numerical literals outside \input{tables/...} ---
    # ⚠️ ONE OWNER (2026-08-04, audit finding QI-02). This block used to carry its
    # own byte-identical copy of the pattern AND of the two-step strip that
    # `validation/checks/papers_prose.py` uses for the `numerical_literals` check.
    # Both feed a per-paper verdict, and `validate.py --check
    # readiness_verdicts_agree` exists to assert those verdicts agree — so tuning
    # one copy would have made the two subsystems disagree by construction, in the
    # blind spot of the check written to detect disagreement. Verified identical
    # (pattern string and flags) before merging, so this is behaviour-preserving.
    tex = idx.paper_tex(paper_key)
    if tex is None:
        return _unreadable_draft(r)
    inline_literals = 0
    if tex:
        _, _lit_matches = find_inline_numerical_literals(tex)
        inline_literals = len(_lit_matches)

    # --- 3. Autogen table staleness (table-level freshness) ---
    tables_dir = PAPERS_DIR / paper_key / 'tables'
    tables_py = PAPERS_DIR / paper_key / 'tables.py'
    stale_tables_count = 0
    if tables_py.exists() and tables_dir.exists():
        spec_mtime = tables_py.stat().st_mtime
        for tex_file in tables_dir.glob('*.tex'):
            if tex_file.stat().st_mtime < spec_mtime:
                stale_tables_count += 1

    r.evidence.append(
        f'{len(reports)} REPORTS edges ({len(stale_reports)} stale); '
        f'{inline_literals} inline numerical literals in body; '
        f'{stale_tables_count} stale tables/*.tex files'
    )

    blockers: list[str] = []
    if stale_reports:
        blockers.extend(
            f'{e["target"].replace("count:","",1)}: paper={e.get("paper_value")} '
            f'vs canonical={e.get("canonical_value")} (Δ={e.get("delta_pct")}%)'
            for e in stale_reports[:6]
        )
    if stale_tables_count:
        blockers.append(f'{stale_tables_count} autogen tables/*.tex are stale vs tables.py spec')
    if inline_literals:
        blockers.append(f'{inline_literals} inline unit-bearing literals in body — move to \\input{{tables/*.tex}}')

    if blockers:
        r.blockers = blockers
        r.state = 'needs-recheck'
        parts = []
        if stale_reports:
            parts.append(f'{len(stale_reports)} stale count literal(s)')
        if inline_literals:
            parts.append(f'{inline_literals} inline numerical literal(s)')
        if stale_tables_count:
            parts.append(f'{stale_tables_count} stale autogen table(s)')
        r.notes = '; '.join(parts)
    elif not reports and not inline_literals:
        r.state = 'passed'
        r.notes = ('no numerical literals (uses \\input{counts.tex} + \\input{tables/*.tex})'
                   if tables_py.exists() else
                   'no numerical literals detected')
    else:
        r.state = 'passed'
        r.notes = 'all numerical content current'
    return r


def _eval_first_claim_verification(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 10 (P2): FirstClaimVerification.

    Every ProseClaim tagged `first-claim` should have a SUPPORTS edge to
    a verification ledger entry (FirstClaimLedger node — not yet
    extracted; treat as WARN for now).
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='FirstClaimVerification', paper=paper_key, priority=2)

    prose_claims = [n for n in idx.by_type.get('ProseClaim', [])
                    if n.get('meta', {}).get('paper') == paper_key]
    first_claims = [n for n in prose_claims
                    if 'first-claim' in n.get('meta', {}).get('tags', [])]
    r.evidence.append(f'{len(first_claims)} "first-in-proof-assistant" claims')
    if first_claims:
        r.state = 'needs-recheck'
        r.notes = ('first-claim verification ledger not yet in place — '
                   f'{len(first_claims)} claims need manual verification')
        r.blockers = [pc['label'] for pc in first_claims]
    else:
        r.state = 'passed'
        r.notes = 'no first-in-proof-assistant claims in abstract'
    return r


# A ReviewFinding at or above this severity is submission-blocking, not advisory.
BLOCKING_SEVERITIES = frozenset({'critical', 'blocker', 'major'})


def _eval_fix_propagation(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 11: FixPropagation — severity-aware.

    Every ReviewFinding FLAGS this paper should have status='fixed'.

    Severity determines gate impact (corrected 2026-07-31, D12 Stage-13 round-6
    BLOCKER 8.1). Before that fix this gate was hardwired P2 and could only ever
    emit `needs-recheck`, so a bundle carrying unclosed Stage-13 BLOCKERs still
    rendered as "all P1 passed" in `readiness_submission_gate` — the gate
    reported the *absence of a red P1 gate*, not the absence of blockers, and no
    other evaluator reads FLAGS at all. Now an open finding whose severity is in
    `BLOCKING_SEVERITIES` escalates the result to a **blocked P1** gate, which is
    what both `paper_aggregate_state` and the submission gate key off. Open
    findings below that bar keep the old advisory P2 `needs-recheck`.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='FixPropagation', paper=paper_key, priority=2)

    flagged = idx.incoming(paper['id'], 'FLAGS')
    open_findings = []
    fixed_findings = []
    accepted_findings = []
    for e in flagged:
        finding = idx.by_id.get(e['source'])
        if not finding:
            continue
        status = finding.get('meta', {}).get('status', 'open')
        if status == 'fixed':
            fixed_findings.append(finding)
        elif status == 'accepted':
            # `accepted` is a RECORDED DECISION to accept a finding, not an unclosed
            # one, and `bundle_readiness.py` has always used the narrower
            # `status == "open"`. The `!= 'fixed'` partition predates the severity
            # escalation below, but the escalation is what made it load-bearing: it
            # turned all 122 project-wide `accepted` findings into submission blockers.
            # Concrete false RED it produced: E2 blocked on FixPropagation on the
            # strength of one accepted major, while the heatmap correctly read E2 as
            # YELLOW with blocker_count=0. Counted and named in the evidence line so it
            # never disappears silently. (Self-audit 2026-07-31.)
            accepted_findings.append(finding)
        else:
            open_findings.append(finding)

    blocking = [f for f in open_findings
                if str(f.get('meta', {}).get('severity', '')).lower()
                in BLOCKING_SEVERITIES]

    r.evidence.append(f'{len(flagged)} findings flag this paper '
                      f'({len(fixed_findings)} fixed, {len(accepted_findings)} accepted, '
                      f'{len(open_findings)} open, '
                      f'{len(blocking)} of them submission-blocking)')
    def _refs(findings: list[dict]) -> list[dict]:
        """Keep the finding's IDENTITY beside its prose (ADR-012 D15 S1).

        ⚠️ This function exists because the two lines it replaces read
        `[f'{f.get("label","?")[:60]}' for f in ...]` — holding the entire ReviewFinding
        (id, severity, lane, target, status) and keeping sixty characters of label. That
        is the whole reason a gate cell is a dead end: the id is destroyed HERE, before
        `GateResult`, before the node payload, before the dashboard. Nothing downstream
        could recover it, which is why S1 is an evaluator change and not a render fix.
        """
        out = []
        for f in findings:
            m = f.get('meta') or {}
            out.append({
                'id': str(f.get('id', '')),
                'label': str(f.get('label', '?'))[:60],
                'severity': str(m.get('severity', '')),
                # `unclassified` is the honest default: `lane` is forward-only, and an
                # absent lane must never read as a routed one.
                'lane': str(m.get('lane') or 'unclassified'),
                'status': str(m.get('status', 'open')),
                'target': str(m.get('target') or ''),
            })
        return out

    # ── Accepted AT BLOCKING SEVERITY (D12 rounds 8/9/10 finding 8.5) ────────────────
    # `accepted` is partitioned out above, so these never reach `blocking` and never
    # change `state` — correct, since an accepted finding is a recorded decision, not
    # unclosed work. But they were then invisible EVERYWHERE: the `passed` branch below
    # says "all review findings fixed" over a bundle that may carry accepted criticals,
    # and `accepted` became the cheapest closure in the system precisely because it
    # removes a finding from the gate's blocking set. Disclosure, not blocking — the
    # state is untouched and only the notes and a dedicated ref list are added.
    accepted_blocking = [f for f in accepted_findings
                         if str((f.get('meta') or {}).get('severity', '')).lower()
                         in BLOCKING_SEVERITIES]
    r.accepted_blockers = _refs(accepted_blocking)
    _acc = (f'; {len(accepted_blocking)} accepted at blocking severity'
            if accepted_blocking else '')

    if blocking:
        # ⚠️ THE CAP MOVED, and that is not incidental. This was `blocking[:10]` HERE, so
        # `len(self.blockers)` in the payload counted the truncated list — meaning a
        # `blockers_total` computed there would have reported 10 for a paper carrying 44 and
        # called itself a disclosure. A cap can only be disclosed by a layer that can still
        # see what it cut. The evaluator now assigns everything; `to_node_payload` bounds
        # the payload and states both figures; the dashboard bounds the DISPLAY.
        r.blocker_refs = _refs(blocking)
        r.blockers = [x['label'] for x in r.blocker_refs]
        r.state = 'blocked'
        r.priority = 1
        r.notes = (f'{len(blocking)} open review findings at severity '
                   f'{"/".join(sorted(BLOCKING_SEVERITIES))} '
                   f'({len(open_findings)} open in total){_acc}')
    elif open_findings:
        r.blocker_refs = _refs(open_findings)
        r.blockers = [x['label'] for x in r.blocker_refs]
        r.state = 'needs-recheck'
        r.notes = (f'{len(open_findings)} review findings still open '
                   f'(all advisory){_acc}')
    else:
        r.state = 'passed'
        # ⚠️ "all review findings fixed" was FALSE for any bundle carrying an accepted
        # blocker — they are closed, but not fixed, and the distinction is the whole
        # point of the `accepted` status. This branch is where 8.5 bites hardest: a
        # green gate over a recorded decision to ship a known critical.
        r.notes = ('no review findings' if not flagged
                   else ('all review findings fixed' if not accepted_blocking
                         else f'0 open{_acc[2:]}'))
    return r


# ═══════════════════════════════════════════════════════════════════════
# Registry — gate definitions in execution order (P1 before P2)
# ═══════════════════════════════════════════════════════════════════════

GATES: list[tuple[str, int, Callable[[dict, GraphIndex], GateResult]]] = [
    ('CitationIntegrity',      1, _eval_citation_integrity),
    ('CrossPaperConsistency',  1, _eval_cross_paper_consistency),
    ('ParameterProvenance',    1, _eval_parameter_provenance),
    ('ComputationCorrectness', 1, _eval_computation_correctness),
    ('LeanProofSubstance',     1, _eval_lean_proof_substance),
    ('AssumptionDisclosure',   1, _eval_assumption_disclosure),
    ('NarrativeGrounding',     1, _eval_narrative_grounding),
    ('ProductionRunHealth',    1, _eval_production_run_health),
    ('NumericalFreshness',     2, _eval_numerical_freshness),
    ('FirstClaimVerification', 2, _eval_first_claim_verification),
    ('FixPropagation',         2, _eval_fix_propagation),
]


def evaluate_all_gates(graph: dict) -> list[GateResult]:
    """Run all 11 gates for all Paper nodes in the graph."""
    idx = GraphIndex(graph)
    now = datetime.now(timezone.utc).isoformat(timespec='seconds')
    results: list[GateResult] = []
    for paper in idx.papers():
        for gate_name, prio, evaluator in GATES:
            try:
                r = evaluator(paper, idx)
            except Exception as exc:
                # BLOCKED, not `open` (2026-08-04). `paper_aggregate_state` maps
                # `open` to YELLOW and only `blocked` to RED, so an evaluator that
                # CRASHED used to render as a mild advisory — the gate reported
                # "not evaluated" in a shape a reader takes as "nothing serious".
                # That is the QA_QI_INFRASTRUCTURE_MAP §7 pattern (absence of
                # measurement rendered as success) living in the readiness layer.
                # An evaluator that cannot run has not cleared its paper.
                #
                # Measured before the change: 0 evaluator exceptions across
                # 704 evaluations (64 papers x 11 gates), so this is a no-op on
                # the current tree and pure future-proofing — the failure it
                # guards against is a NEW evaluator bug, which is exactly when a
                # silent downgrade would do the most damage.
                paper_key = paper['id'].replace('paper:', '', 1)
                r = GateResult(gate=gate_name, paper=paper_key, priority=prio,
                               state='blocked',
                               blockers=[f'evaluator raised {type(exc).__name__}'],
                               notes=f'evaluator error (UNVERIFIED, not passing): {exc}')
            r.last_evaluated = now
            results.append(r)
    return results


def paper_unmeasured_gates(results: list[GateResult], paper_key: str) -> list[str]:
    """Gate names whose evaluator COULD NOT MEASURE, for this paper.

    ⚠️ **`GateResult.measured` was write-only until this existed**, and that is
    the defect the field was added to fix, left live at the exact function named
    as its victim. `paper_aggregate_state` keys on `state` alone and maps both
    "measured, outstanding" and "read nothing" to YELLOW, so a paper whose draft
    could not be opened rendered identically to one with real blockers. Adding a
    fourth aggregate value is not the fix — `state` is a contract — so the
    distinction is surfaced BESIDE the colour, which is the convention
    `bundle_readiness.py` already uses one layer up.

    Callers that render a paper's state should render this too; an empty list
    means every gate for this paper actually ran.
    """
    return sorted(r.gate for r in results
                  if r.paper == paper_key and not r.measured)


def paper_aggregate_state(results: list[GateResult], paper_key: str) -> str:
    """Return 'red' / 'yellow' / 'green' for a paper's overall state.

    ⚠️ This deliberately does NOT consult `measured`. A colour is a three-value
    contract read by `check_readiness_submission_gate` and by the heatmap, and a
    fourth value would break both. Ask `paper_unmeasured_gates` alongside it —
    a YELLOW with a non-empty unmeasured list is a different fact from a YELLOW
    with an empty one, and only the caller can render that.
    """
    paper_results = [r for r in results if r.paper == paper_key]
    # Any blocked gate is red, whatever its priority — `check_readiness_submission_gate`
    # has always classified a blocked P2 gate as red, and the two verdicts must agree
    # (enforced by validate.py --check readiness_verdicts_agree).
    if any(r.state == 'blocked' for r in paper_results):
        return 'red'
    if any(r.state in ('blocked', 'needs-recheck', 'open') for r in paper_results):
        return 'yellow'
    return 'green'
