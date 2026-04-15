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
from collections import defaultdict
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Literal

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
                'evidence': self.evidence[:50],
                'blockers': self.blockers[:50],
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

    def paper_tex(self, paper_key: str) -> str:
        """Return paper_draft.tex contents (or empty string if not readable)."""
        tex_path = PAPERS_DIR / paper_key / "paper_draft.tex"
        try:
            return tex_path.read_text()
        except (OSError, UnicodeDecodeError):
            return ''


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
    import re
    paper_key = paper['meta'].get('topic') or paper['name'] or ''
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='CitationIntegrity', paper=paper_key, priority=1)

    tex = idx.paper_tex(paper_key)
    if not tex:
        r.state = 'open'
        r.notes = 'paper_draft.tex not readable'
        return r

    bibkeys = set(re.findall(r'\\bibitem\{([^}]+)\}', tex))
    if not bibkeys:
        r.state = 'passed'
        r.notes = 'no bibitems (paper has no bibliography block)'
        return r

    # CITATION_REGISTRY entries via PrimarySource nodes (id = 'source:{key}')
    registered_keys = {n['id'].replace('source:', '', 1)
                       for n in idx.by_type.get('PrimarySource', [])}

    missing = sorted(bibkeys - registered_keys)
    r.evidence.append(f'{len(bibkeys)} bibitems, {len(bibkeys) - len(missing)} registered')
    if missing:
        r.blockers = [f'unregistered bibkey: {k}' for k in missing[:20]]
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
        r.blockers = [f'{e["target"]}: {e.get("conflict_detail","")}' for e in contradicts_out[:10]]
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
        r.state = 'passed'
        r.notes = 'no parameter dependencies declared'
    elif unverified:
        # Treat as blocked for submission but acceptable during draft
        r.blockers = [p.replace('param:', '', 1) for p in unverified[:20]]
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
    for fid in formula_ids:
        if fid not in idx.by_id:
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

    r.evidence.append(
        f'{len(formula_ids)} formulas grounding paper claims '
        f'({len(strong)} with golden/identity/roundtrip, '
        f'{len(bounds_only)} bounds-only, {len(no_tests)} no tests)'
    )
    if bounds_only or no_tests:
        r.blockers = (
            [f'bounds-only: {b.replace("formula:","",1)}' for b in bounds_only[:10]] +
            [f'no tests: {b.replace("formula:","",1)}' for b in no_tests[:10]]
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
    import re
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

    # Theorems cited by short name in prose
    tex = idx.paper_tex(paper_key)
    referenced_short_names = set(
        re.findall(r'\\texttt\{([A-Za-z_][A-Za-z0-9_]*)\}', tex)
    )

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
        r.blockers = [f'placeholder cited: {n}' for n in flagged[:20]]
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

    tex = idx.paper_tex(paper_key).lower()
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
        r.blockers = [f'undisclosed hypothesis: {k}' for k in undisclosed[:10]]
        r.state = 'blocked'
        r.notes = f'{len(undisclosed)} hypothesis dependencies not named in paper'
    elif not assumed_hyp_ids:
        r.state = 'passed'
        r.notes = 'no hypothesis dependencies'
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
        r.blockers = unsupported[:10]
        r.state = 'blocked'
        r.notes = f'{len(unsupported)} "interesting" prose claims lack formal support'
    elif not interesting:
        r.state = 'passed'
        r.notes = 'no interesting prose claims flagged'
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
    import re
    mc_claim = bool(re.search(r'\b(Monte\s+Carlo\s+evidence|MC\s+evidence)\b', tex, re.IGNORECASE))
    success_runs = [r_ for r_ in relevant_runs
                    if r_.get('meta', {}).get('status') == 'success']

    r.evidence.append(f'{len(relevant_runs)} production runs linked, '
                      f'{len(success_runs)} successful, {len(failed)} failed')
    if failed:
        r.blockers = [f'failed run: {r_.get("name","?")} ({r_.get("meta",{}).get("status")})'
                      for r_ in failed[:10]]
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
    import re as _re
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='NumericalFreshness', paper=paper_key, priority=2)

    # --- 1. REPORTS→CountMetric drift (count-literal layer) ---
    reports = idx.outgoing(paper['id'], 'REPORTS')
    stale_reports = [e for e in reports if e.get('stale')]

    # --- 2. Inline numerical literals outside \input{tables/...} ---
    tex = idx.paper_tex(paper_key)
    inline_literals = 0
    if tex:
        stripped = _re.sub(r'\\input\{tables/[^}]+\}', '', tex)
        stripped = _re.sub(r'\\caption\{[^}]*\}', '', stripped, flags=_re.DOTALL)
        lit_re = _re.compile(
            r'(?<!\\)\b(\d+\.\d+|\d+(?:\.\d+)?e[+-]?\d+)\s*(~?)\\?(?:'
            r'(?:mu|\\mu)\s*m\b|nK\b|mK\b|\\mathrm\{[a-zA-Z]+\}|'
            r's\^?(?:-|\{-|\^{-)1\}?|mm/s\b|\\mu m\b|\\times\s*10\^'
            r')',
            _re.IGNORECASE,
        )
        inline_literals = len(lit_re.findall(stripped))

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
        r.blockers = blockers[:10]
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
        r.blockers = [pc['label'] for pc in first_claims[:10]]
    else:
        r.state = 'passed'
        r.notes = 'no first-in-proof-assistant claims in abstract'
    return r


def _eval_fix_propagation(paper: dict, idx: GraphIndex) -> GateResult:
    """Gate 11 (P2): FixPropagation.

    Every ReviewFinding FLAGS this paper should have status='fixed'.
    """
    paper_key = paper['id'].replace('paper:', '', 1)
    r = GateResult(gate='FixPropagation', paper=paper_key, priority=2)

    flagged = idx.incoming(paper['id'], 'FLAGS')
    open_findings = []
    fixed_findings = []
    for e in flagged:
        finding = idx.by_id.get(e['source'])
        if not finding:
            continue
        status = finding.get('meta', {}).get('status', 'open')
        if status == 'fixed':
            fixed_findings.append(finding)
        else:
            open_findings.append(finding)

    r.evidence.append(f'{len(flagged)} findings flag this paper '
                      f'({len(fixed_findings)} fixed, {len(open_findings)} open)')
    if open_findings:
        r.blockers = [f'{f.get("label","?")[:60]}' for f in open_findings[:10]]
        r.state = 'needs-recheck'
        r.notes = f'{len(open_findings)} review findings still open'
    else:
        r.state = 'passed'
        r.notes = ('no review findings' if not flagged
                   else 'all review findings fixed')
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
                paper_key = paper['id'].replace('paper:', '', 1)
                r = GateResult(gate=gate_name, paper=paper_key, priority=prio,
                               state='open',
                               notes=f'evaluator error: {exc}')
            r.last_evaluated = now
            results.append(r)
    return results


def paper_aggregate_state(results: list[GateResult], paper_key: str) -> str:
    """Return 'red' / 'yellow' / 'green' for a paper's overall state."""
    paper_results = [r for r in results if r.paper == paper_key]
    if any(r.priority == 1 and r.state == 'blocked' for r in paper_results):
        return 'red'
    if any(r.state in ('blocked', 'needs-recheck', 'open') for r in paper_results):
        return 'yellow'
    return 'green'
