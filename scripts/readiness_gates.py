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
    # ⚠️ A dead first assignment was removed here 2026-08-04 (audit QI-05):
    # `paper_key = paper['meta'].get('topic') or paper['name'] or ''` was computed
    # and then overwritten on the very next line by the `paper['id']` form. Every
    # other evaluator uses only the `paper['id']` form, which is the correct one —
    # `meta.topic` is a description, not a key.
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
                       'literals in body prose (numbers arriving via \input{tables/} or '
                       'counts.tex are structurally sourced and not counted here)')
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
        # ⚠️ CORROBORATE (2026-08-05, PR-review pass 2) — same shape as
        # ParameterProvenance above. `prose_claims` are GRAPH nodes filtered by
        # `meta.paper`, so zero of them means either "the abstract makes no
        # interesting claims" or "the abstract was never extracted". A paper whose
        # prose was never ingested passed NarrativeGrounding cleanly.
        #
        # A draft with an abstract but NO ProseClaim nodes at all is an extraction
        # gap: the gate verified nothing. `open`, so the reviewer sees it.
        tex = idx.paper_tex(paper_key)
        has_abstract = bool(tex) and '\\begin{abstract}' in tex
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
    if blocking:
        r.blockers = [f'{f.get("label","?")[:60]}' for f in blocking[:10]]
        r.state = 'blocked'
        r.priority = 1
        r.notes = (f'{len(blocking)} open review findings at severity '
                   f'{"/".join(sorted(BLOCKING_SEVERITIES))} '
                   f'({len(open_findings)} open in total)')
    elif open_findings:
        r.blockers = [f'{f.get("label","?")[:60]}' for f in open_findings[:10]]
        r.state = 'needs-recheck'
        r.notes = f'{len(open_findings)} review findings still open (all advisory)'
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


def paper_aggregate_state(results: list[GateResult], paper_key: str) -> str:
    """Return 'red' / 'yellow' / 'green' for a paper's overall state."""
    paper_results = [r for r in results if r.paper == paper_key]
    # Any blocked gate is red, whatever its priority — `check_readiness_submission_gate`
    # has always classified a blocked P2 gate as red, and the two verdicts must agree
    # (enforced by validate.py --check readiness_verdicts_agree).
    if any(r.state == 'blocked' for r in paper_results):
        return 'red'
    if any(r.state in ('blocked', 'needs-recheck', 'open') for r in paper_results):
        return 'yellow'
    return 'green'
