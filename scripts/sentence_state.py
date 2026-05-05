#!/usr/bin/env python3
"""
sentence_state.py — sole writer for sentence-level verification state (Phase 5v Wave 10b)
==========================================================================================

Sole path for mutating `papers/<paper>/prose_state.json` and
`papers/<paper>/audit_log.jsonl`. LLMs, dashboard backend, and ad-hoc scripts
all call this CLI. No free-form JSON edits.

Architecture
------------
Three artifact files per paper:

  papers/<paper>/claims_review.json  — agent's output (read-only for this CLI)
  papers/<paper>/prose_state.json    — human ratification state (CLI-owned)
  papers/<paper>/audit_log.jsonl     — append-only event stream (CLI-owned)

PG+AGE mirrors all three; JSON is canonical at rest.

Write safety
------------
- Every mutating operation:
  1. Acquires fcntl.flock() on `prose_state.json.lock` (blocking).
  2. Validates schema of current claims_review.json.
  3. Appends one AuditEvent JSONL to audit_log.jsonl (atomic O_APPEND).
  4. Computes new prose_state.json; writes to `.tmp`; renames atomically.
  5. Releases lock.
- If any step fails, partial state is NOT corrupting: audit_log append is
  idempotent per-event (grep dedup), prose_state.json.tmp is orphaned (safe
  to ignore / sweep).

Subcommands
-----------
  mark <sentence_id> <state> [--notes "..."] [--actor <id>]
  ingest_agent_run <claims_review.json> [--dry-run]
  reconcile [--paper <id>]
  supersede <prior_finding_id> --reason "..." [--actor <id>]
  tombstone-sweep [--paper <id>]
  validate <claims_review.json>
  normalize-quote "<quote text>"

See `docs/agents/claims_reviewer.md` and
`temporary/working-docs/{claims_reviewer_v2_design,sentence_kg_schema_delta}.md`
for the full design spec.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
import re
import shutil
import sys
import tempfile
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# ────────────────────────────────────────────────────────────────────────────
# Paths
# ────────────────────────────────────────────────────────────────────────────

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
PAPERS_ROOT = PROJECT_ROOT / "papers"


def paper_dir(paper: str) -> Path:
    d = PAPERS_ROOT / paper
    if not d.is_dir():
        raise SystemExit(f"sentence_state: no such paper directory: {d}")
    return d


def claims_review_path(paper: str) -> Path:
    return paper_dir(paper) / "claims_review.json"


def prose_state_path(paper: str) -> Path:
    return paper_dir(paper) / "prose_state.json"


def audit_log_path(paper: str) -> Path:
    return paper_dir(paper) / "audit_log.jsonl"


def lock_path(paper: str) -> Path:
    return paper_dir(paper) / "prose_state.json.lock"


# ────────────────────────────────────────────────────────────────────────────
# Quote normalization + content-hash IDs (claims_reviewer_v2_design §2.3)
# ────────────────────────────────────────────────────────────────────────────

_LATEX_KEEP_ARG = re.compile(r'\\(?:texttt|emph|textbf|mathrm|text|textit|textsc)\{([^{}]*)\}')
_LATEX_DROP_ARG = re.compile(r'\\(?:cite|ref|label|footnote|autoref|eqref|nocite)\{[^{}]*\}')
_WS = re.compile(r'\s+')
# Trailing bibliographic brackets: numeric [1, 2], author-year [Author 2024],
# combined [Author1, Author2 2024]. Stop before ] so we don't eat brackets in
# content (e.g. "the array [1,2,3] is the answer." — that's mid-sentence).
# Pattern matches bracketed content with letters or digits at end-of-string only.
_TRAILING_BRACKETS = re.compile(
    r'\s*\[[A-Za-z0-9 ,;.&\'-]+\]\s*\.?\s*$'
)


def normalize_quote(quote: str) -> str:
    """Normalize a quote per design §2.3.

    Steps: lowercase → strip latex (keep-arg / drop-arg) → unicode normalize
    punctuation → whitespace-collapse → strip trailing bibliographic brackets.
    """
    q = quote.lower()
    # Step 2a: strip latex commands keeping arg (iterate — nested arguments)
    prev = None
    while prev != q:
        prev = q
        q = _LATEX_KEEP_ARG.sub(lambda m: m.group(1), q)
    # Step 2b: strip latex commands dropping arg entirely
    q = _LATEX_DROP_ARG.sub('', q)
    # Step 3: unicode-normalize punctuation
    q = q.replace('“', '"').replace('”', '"')       # curly dq → straight
    q = q.replace('‘', "'").replace('’', "'")       # curly sq → straight
    q = q.replace('—', '--').replace('–', '-')      # em/en dash
    q = q.replace('…', '...')                              # ellipsis
    q = q.replace(' ', ' ')                                # nbsp → space
    # Step 4: whitespace collapse
    q = _WS.sub(' ', q).strip()
    # Step 5: strip trailing bibliographic brackets
    q = _TRAILING_BRACKETS.sub('', q).strip()
    return q


def sha8(normalized: str) -> str:
    return hashlib.sha256(normalized.encode('utf-8')).hexdigest()[:8]


def slugify(heading: str) -> str:
    """Slugify a section heading for use in sentence IDs (stable under reorder)."""
    s = heading.lower()
    s = unicodedata.normalize('NFKD', s)
    s = re.sub(r"[^a-z0-9\s-]", '', s)
    s = re.sub(r'\s+', '-', s).strip('-')
    return s or 'unnamed'


def compute_sentence_id(paper: str, section_heading: str, quote: str) -> tuple[str, str, str]:
    """Return (sentence_id, quote_normalized, sha8_hash)."""
    section_slug = slugify(section_heading)
    norm = normalize_quote(quote)
    h = sha8(norm)
    sid = f"sentence:{paper}:{section_slug}:{h}"
    return sid, norm, h


# ────────────────────────────────────────────────────────────────────────────
# Schema validation (claims_reviewer_v2_design §2.1/§2.2)
# ────────────────────────────────────────────────────────────────────────────

_VALID_VERDICTS = {'PASS', 'FAIL', 'WARN', 'INFO', 'UNGROUNDED', 'TRANSITION'}
_VALID_TYPES = {
    'numeric', 'theorem-ref', 'citation', 'parameter', 'formal-claim',
    'qualitative', 'methodology', 'transition', 'metaclaim',
}
_VALID_FINDING_CLASSES = {'IA', 'TP', 'SD', 'TN', 'HD'}
_VALID_LINK_KINDS = {
    'formula', 'theorem', 'axiom', 'parameter',
    'citation', 'hypothesis', 'aristotle', 'production_run',
}
_VALID_HUMAN_STATES = {
    None, 'human_verified', 'human_interpretive',
    'human_needs_fix', 'human_needs_recheck',
}
_REPRO_STATUSES = {'superseded', 'candidate_for_supersession'}


# Per-sentence required fields (Wave 10a smoke-test follow-up: enforce strictly)
_SENTENCE_REQUIRED = {
    'id', 'section', 'tex_line_start', 'tex_line_end',
    'quote', 'type', 'finding_classes', 'agent_verdict',
    'agent_run_id', 'tombstone',
}
# Optional fields the schema knows about (warnings on unknown fields beyond these)
_SENTENCE_OPTIONAL = {
    'raw_id_parts', 'section_ordinal', 'quote_normalized',
    'chain_proposed', 'delta_pct', 'agent_notes',
    'gates_invoked', 'rewrite_of', 'meta',
    # Phase 6i Wave 7 bundle-aware schema additions
    'bundle_destination', 'bundle_section_hint', 'lift_action',
}
_SENTENCE_KNOWN = _SENTENCE_REQUIRED | _SENTENCE_OPTIONAL


# Phase 6i Wave 7 — bundle-aware schema additions
# Bundle target enum per docs/PAPER_STRATEGY.md (1 flagship + 5 deep + 3 PRL +
# 2 infrastructure + 2 experimental). A sentence can carry a single bundle
# target (the common case for Lift-section) or a list of targets (for
# Lift-letter, Lift-companion, Lift-flagship — the splash + the deep paper, etc.).
_VALID_BUNDLE_TARGETS = {
    'F',                                # Tier 0 flagship review
    'D1', 'D2', 'D3', 'D4', 'D5',       # Tier 1 deep papers
    'L1', 'L2', 'L3',                   # Tier 2 PRL splashes
    'I1', 'I2', 'I3',                   # Tier 3 infrastructure (I3 added Phase 6n.4 / Phase 6o.ζ — Verified Stochastic Calculus for Mathlib4)
    'E1', 'E2',                         # Tier 4 experimental letters
}
# Lift-action enum per docs/PAPER_DRAFT_MAPPING.md conventions table.
_VALID_LIFT_ACTIONS = {
    'Lift-section',     # content lifts as §section of one bundle
    'Lift-letter',      # PRL splash + deep paper §section (two bundles)
    'Lift-companion',   # 2-3pp experimental letter paired with deep paper
    'Lift-flagship',    # summarized in flagship + fully covered in deep
    'Retain-in-place',  # ships as-is on existing path (rare)
    'Retire',           # tombstoned; consolidated_into_bundle
}


def validate_claims_review(data: dict) -> list[str]:
    """Validate a claims_review.json dict against v2 schema. Return list of errors."""
    errors: list[str] = []

    # Top-level required fields
    required = {
        'paper', 'review_date', 'reviewer_version',
        'reviewer_run_id', 'sentences', 'summary',
    }
    missing = required - set(data.keys())
    if missing:
        errors.append(f"top-level missing required fields: {sorted(missing)}")

    if data.get('reviewer_version') and not data['reviewer_version'].startswith('claims-reviewer-v2'):
        errors.append(
            f"reviewer_version must start with 'claims-reviewer-v2' "
            f"(got {data.get('reviewer_version')!r})"
        )

    # reviewer_model canonical format check (Wave 10a smoke-test follow-up):
    # accept hyphenated lowercase model IDs like 'claude-opus-4-7-1m',
    # 'claude-sonnet-4-6'; reject bracket / slash / mixed-case forms.
    rmodel = data.get('reviewer_model')
    if rmodel and not re.match(r'^[a-z0-9]+(?:-[a-z0-9]+)*$', rmodel):
        errors.append(
            f"reviewer_model not in canonical hyphenated lowercase form: "
            f"{rmodel!r} (e.g., 'claude-opus-4-7-1m', 'claude-sonnet-4-6')"
        )

    # sentences[]
    sentences = data.get('sentences')
    if not isinstance(sentences, list):
        errors.append("'sentences' must be a list")
        return errors  # can't continue

    seen_ids: set[str] = set()
    for i, s in enumerate(sentences):
        if not isinstance(s, dict):
            errors.append(f"sentences[{i}] is not an object")
            continue

        # Per-sentence required-field check (Wave 10a smoke-test follow-up)
        s_missing = _SENTENCE_REQUIRED - set(s.keys())
        if s_missing:
            errors.append(
                f"sentences[{i}] missing required fields: {sorted(s_missing)}"
            )
        # Unknown fields = warnings (likely typos like gates_invoke_list)
        s_unknown = set(s.keys()) - _SENTENCE_KNOWN
        if s_unknown:
            errors.append(
                f"sentences[{i}] has unknown fields (likely typo): {sorted(s_unknown)}"
            )

        sid = s.get('id')
        if not sid or not isinstance(sid, str) or not sid.startswith('sentence:'):
            errors.append(f"sentences[{i}].id missing or malformed: {sid!r}")
        elif sid.count(':') != 3:
            errors.append(
                f"sentences[{i}].id wrong shape (expected sentence:<paper>:<section_slug>:<sha8>): {sid!r}"
            )
        elif sid in seen_ids:
            errors.append(f"sentences[{i}].id duplicate: {sid}")
        else:
            seen_ids.add(sid)

        stype = s.get('type')
        if stype not in _VALID_TYPES:
            errors.append(f"sentences[{i}].type invalid: {stype!r}")

        verdict = s.get('agent_verdict')
        if verdict not in _VALID_VERDICTS:
            errors.append(f"sentences[{i}].agent_verdict invalid: {verdict!r}")

        # tex_line_start / tex_line_end must be integers and start ≤ end
        tls = s.get('tex_line_start')
        tle = s.get('tex_line_end')
        if tls is not None and not isinstance(tls, int):
            errors.append(f"sentences[{i}].tex_line_start must be int, got {type(tls).__name__}")
        if tle is not None and not isinstance(tle, int):
            errors.append(f"sentences[{i}].tex_line_end must be int, got {type(tle).__name__}")
        if isinstance(tls, int) and isinstance(tle, int) and tls > tle:
            errors.append(
                f"sentences[{i}].tex_line_start ({tls}) must be <= tex_line_end ({tle})"
            )

        fcs = s.get('finding_classes', [])
        if not isinstance(fcs, list):
            errors.append(f"sentences[{i}].finding_classes must be a list")
        else:
            for c in fcs:
                if c not in _VALID_FINDING_CLASSES:
                    errors.append(f"sentences[{i}].finding_classes has invalid class: {c!r}")

        chain = s.get('chain_proposed') or {}
        if chain:
            comp = chain.get('completeness')
            if comp not in (None, 'full', 'partial', 'none'):
                errors.append(
                    f"sentences[{i}].chain_proposed.completeness invalid: {comp!r}"
                )
        for j, link in enumerate(chain.get('links', []) or []):
            if link.get('kind') not in _VALID_LINK_KINDS:
                errors.append(f"sentences[{i}].chain_proposed.links[{j}].kind invalid: {link.get('kind')!r}")
            if not link.get('target'):
                errors.append(f"sentences[{i}].chain_proposed.links[{j}].target missing")

        ts = s.get('tombstone')
        if ts is not None and not isinstance(ts, bool):
            errors.append(f"sentences[{i}].tombstone must be bool, got {type(ts).__name__}")

        # Phase 6i Wave 7 bundle-aware schema (optional fields)
        bd = s.get('bundle_destination')
        if bd is not None:
            if isinstance(bd, str):
                if bd not in _VALID_BUNDLE_TARGETS:
                    errors.append(
                        f"sentences[{i}].bundle_destination invalid: {bd!r} "
                        f"(must be one of {sorted(_VALID_BUNDLE_TARGETS)})"
                    )
            elif isinstance(bd, list):
                for j, t in enumerate(bd):
                    if t not in _VALID_BUNDLE_TARGETS:
                        errors.append(
                            f"sentences[{i}].bundle_destination[{j}] invalid: {t!r}"
                        )
                if len(set(bd)) != len(bd):
                    errors.append(
                        f"sentences[{i}].bundle_destination has duplicates"
                    )
            else:
                errors.append(
                    f"sentences[{i}].bundle_destination must be str or list, "
                    f"got {type(bd).__name__}"
                )

        la = s.get('lift_action')
        if la is not None and la not in _VALID_LIFT_ACTIONS:
            errors.append(
                f"sentences[{i}].lift_action invalid: {la!r} "
                f"(must be one of {sorted(_VALID_LIFT_ACTIONS)})"
            )

        bsh = s.get('bundle_section_hint')
        if bsh is not None and not isinstance(bsh, str):
            errors.append(
                f"sentences[{i}].bundle_section_hint must be str, "
                f"got {type(bsh).__name__}"
            )

    # non_reproducing_prior_findings[] (optional)
    nrpf = data.get('non_reproducing_prior_findings', [])
    if not isinstance(nrpf, list):
        errors.append("'non_reproducing_prior_findings' must be a list")
    else:
        for i, f in enumerate(nrpf):
            st = f.get('status')
            if st not in _REPRO_STATUSES:
                errors.append(f"non_reproducing_prior_findings[{i}].status invalid: {st!r}")
            if f.get('auto_closed') is True and not f.get('deterministic_recheck'):
                errors.append(
                    f"non_reproducing_prior_findings[{i}] auto_closed but no deterministic_recheck"
                )
            if st == 'superseded' and f.get('auto_closed') is not True:
                errors.append(
                    f"non_reproducing_prior_findings[{i}] status=superseded but auto_closed not true "
                    "(use candidate_for_supersession for non-mechanical cases)"
                )

    return errors


# ────────────────────────────────────────────────────────────────────────────
# prose_state.json helpers
# ────────────────────────────────────────────────────────────────────────────

def _load_prose_state(paper: str) -> dict:
    p = prose_state_path(paper)
    if p.exists():
        with open(p) as f:
            return json.load(f)
    return {
        'paper': paper,
        'schema_version': 'v2',
        'sentences': {},
    }


def _atomic_write_prose_state(paper: str, state: dict) -> None:
    """Write prose_state.json atomically (tmp + rename)."""
    p = prose_state_path(paper)
    fd, tmp_path = tempfile.mkstemp(
        dir=str(p.parent), prefix='.prose_state.', suffix='.tmp'
    )
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(state, f, indent=2, sort_keys=True)
        os.replace(tmp_path, p)
    except Exception:
        if os.path.exists(tmp_path):
            os.unlink(tmp_path)
        raise


def _append_audit_event(paper: str, event: dict) -> None:
    """Append one JSONL event to audit_log.jsonl (atomic O_APPEND on POSIX)."""
    line = json.dumps(event, sort_keys=True) + '\n'
    with open(audit_log_path(paper), 'a', encoding='utf-8') as f:
        f.write(line)
        f.flush()
        os.fsync(f.fileno())


# ────────────────────────────────────────────────────────────────────────────
# Lock context manager
# ────────────────────────────────────────────────────────────────────────────

class _Lock:
    def __init__(self, paper: str):
        self.paper = paper
        self.fd: int | None = None

    def __enter__(self) -> '_Lock':
        # Create lock file if missing
        lp = lock_path(self.paper)
        lp.parent.mkdir(parents=True, exist_ok=True)
        self.fd = os.open(str(lp), os.O_CREAT | os.O_RDWR, 0o644)
        fcntl.flock(self.fd, fcntl.LOCK_EX)
        return self

    def __exit__(self, *exc) -> None:
        if self.fd is not None:
            fcntl.flock(self.fd, fcntl.LOCK_UN)
            os.close(self.fd)
            self.fd = None


# ────────────────────────────────────────────────────────────────────────────
# Event constructors
# ────────────────────────────────────────────────────────────────────────────

def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z')


def _default_actor() -> str:
    user = os.environ.get('USER') or os.environ.get('USERNAME') or 'unknown'
    return f'user:{user}'


def _make_audit_event(
    *,
    paper: str,
    target_id: str,
    target_type: str,
    action: str,
    prior_state: Any,
    new_state: Any,
    actor: str,
    notes: str | None = None,
    chain_state_snapshot: Any = None,
    propagated_from: str | None = None,
    related_finding_id: str | None = None,
) -> dict:
    ts = _now_iso()
    return {
        'id': f'audit:{ts}:{target_id}:{action}',
        'type': 'AuditEvent',
        'label': f'{action} {new_state}',
        'verification': 'verified',
        'meta': {
            'timestamp': ts,
            'actor': actor,
            'target_id': target_id,
            'target_type': target_type,
            'action': action,
            'prior_state': prior_state,
            'new_state': new_state,
            'notes': notes,
            'chain_state_snapshot': chain_state_snapshot,
            'propagated_from': propagated_from,
            'related_finding_id': related_finding_id,
        },
    }


_VALID_ACTIONS = {
    'verify', 'mark_interpretive', 'mark_needs_fix', 'mark_needs_recheck',
    'supersede_confirm', 'reject_supersession_candidate',
    'tombstone', 'rewrite_of_confirm',
    'propagate_from_cluster', 're_audit',
}

_STATE_TO_ACTION = {
    'verified': 'verify',
    'interpretive': 'mark_interpretive',
    'needs_fix': 'mark_needs_fix',
    'needs_recheck': 'mark_needs_recheck',
}

_STATE_TO_HUMAN = {
    'verified': 'human_verified',
    'interpretive': 'human_interpretive',
    'needs_fix': 'human_needs_fix',
    'needs_recheck': 'human_needs_recheck',
}


def _paper_from_sentence_id(sentence_id: str) -> str:
    # sentence:<paper>:<section_slug>:<sha8>
    parts = sentence_id.split(':')
    if len(parts) < 4 or parts[0] != 'sentence':
        raise SystemExit(
            f"sentence_state: malformed sentence_id: {sentence_id!r} "
            "(expected sentence:<paper>:<section_slug>:<sha8>)"
        )
    return parts[1]


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: mark
# ────────────────────────────────────────────────────────────────────────────

def cmd_mark(args: argparse.Namespace) -> int:
    sentence_id = args.sentence_id
    state_short = args.state

    if state_short not in _STATE_TO_HUMAN:
        print(
            f"sentence_state: invalid state {state_short!r}; "
            f"expected one of {sorted(_STATE_TO_HUMAN)}",
            file=sys.stderr,
        )
        return 1

    paper = _paper_from_sentence_id(sentence_id)
    actor = args.actor or _default_actor()
    new_human_state = _STATE_TO_HUMAN[state_short]
    action = _STATE_TO_ACTION[state_short]

    with _Lock(paper):
        # Validate that claims_review.json has this sentence_id
        cr_path = claims_review_path(paper)
        if not cr_path.exists():
            print(
                f"sentence_state: {cr_path} does not exist; "
                "run claims-reviewer first to populate it",
                file=sys.stderr,
            )
            return 1
        with open(cr_path) as f:
            cr = json.load(f)
        sentence_ids = {s['id'] for s in cr.get('sentences', [])}
        if sentence_id not in sentence_ids:
            print(
                f"sentence_state: sentence_id {sentence_id!r} not found in "
                f"{cr_path}; refusing to write orphan state",
                file=sys.stderr,
            )
            return 1

        state = _load_prose_state(paper)
        prior = state['sentences'].get(sentence_id, {}).get('human_state')

        # Append audit event FIRST (append-only; idempotent on retry)
        event = _make_audit_event(
            paper=paper,
            target_id=sentence_id,
            target_type='Sentence',
            action=action,
            prior_state=prior,
            new_state=new_human_state,
            actor=actor,
            notes=args.notes,
        )
        _append_audit_event(paper, event)

        # Update prose_state.json
        state['sentences'][sentence_id] = {
            'human_state': new_human_state,
            'human_ratified_at': event['meta']['timestamp'],
            'human_ratified_by': actor,
            'human_notes': args.notes or '',
        }
        _atomic_write_prose_state(paper, state)

    print(json.dumps({'ok': True, 'event_id': event['id']}))
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: validate
# ────────────────────────────────────────────────────────────────────────────

def cmd_validate(args: argparse.Namespace) -> int:
    path = Path(args.path).resolve()
    if not path.exists():
        print(f"sentence_state: {path} does not exist", file=sys.stderr)
        return 1
    with open(path) as f:
        data = json.load(f)
    errors = validate_claims_review(data)
    if errors:
        print(f"sentence_state: {len(errors)} validation error(s):", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 2
    print(json.dumps({
        'ok': True,
        'path': str(path),
        'sentences': len(data.get('sentences', [])),
        'reviewer_version': data.get('reviewer_version'),
    }))
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: normalize-quote
# ────────────────────────────────────────────────────────────────────────────

def cmd_normalize_quote(args: argparse.Namespace) -> int:
    quote = args.quote
    norm = normalize_quote(quote)
    h = sha8(norm)
    if args.json:
        print(json.dumps({'quote_normalized': norm, 'sha8': h}))
    else:
        # Two lines: hash then normalized (matches agent prompt's bash helper)
        print(h)
        print(norm)
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: ingest_agent_run
# ────────────────────────────────────────────────────────────────────────────

def cmd_ingest_agent_run(args: argparse.Namespace) -> int:
    """Validate a new claims_review.json and produce a diff report vs prior.

    Does NOT mutate prose_state.json (that's a separate reconcile step for
    candidate-for-supersession entries). Does emit an AuditEvent recording
    the agent run ingest.
    """
    path = Path(args.path).resolve()
    if not path.exists():
        print(f"sentence_state: {path} does not exist", file=sys.stderr)
        return 1
    with open(path) as f:
        data = json.load(f)

    errors = validate_claims_review(data)
    if errors:
        print(f"sentence_state: schema validation failed for {path}:", file=sys.stderr)
        for e in errors:
            print(f"  - {e}", file=sys.stderr)
        return 2

    paper = data['paper']
    current_ids = {s['id'] for s in data['sentences']}

    # Compute tombstones (present in prior prose_state, absent from current agent run)
    prose_state = _load_prose_state(paper)
    prior_ids = set(prose_state.get('sentences', {}).keys())
    tombstoned = sorted(prior_ids - current_ids)

    # Near-match heuristic for rewrite_of candidates (Levenshtein on normalized quotes)
    current_norms = {
        s['id']: s.get('meta', {}).get('quote_normalized')
                 or s.get('quote_normalized')
                 or normalize_quote(s.get('quote', ''))
        for s in data['sentences']
    }
    rewrite_candidates: list[dict] = []
    prior_norms = prose_state.get('tombstoned_quotes', {})
    for t_id in tombstoned:
        t_norm = prior_norms.get(t_id)
        if not t_norm:
            continue
        for c_id, c_norm in current_norms.items():
            if c_norm and _levenshtein_ratio(t_norm, c_norm) >= 0.7:
                rewrite_candidates.append({
                    'tombstoned_id': t_id,
                    'candidate_rewrite_id': c_id,
                    'similarity': _levenshtein_ratio(t_norm, c_norm),
                })

    # Summarize reconciliation
    nrpf = data.get('non_reproducing_prior_findings', [])
    auto_closed = sum(1 for f in nrpf if f.get('auto_closed') is True)
    candidates = sum(1 for f in nrpf if f.get('status') == 'candidate_for_supersession')

    report = {
        'ok': True,
        'paper': paper,
        'reviewer_version': data.get('reviewer_version'),
        'sentences_in_run': len(current_ids),
        'tombstoned_sentences': tombstoned,
        'tombstoned_count': len(tombstoned),
        'rewrite_candidates': rewrite_candidates,
        'non_reproducing_auto_closed': auto_closed,
        'non_reproducing_candidates_for_supersession': candidates,
    }

    if args.dry_run:
        print(json.dumps(report, indent=2))
        return 0

    actor = (data.get('reviewer_run_id')
             or f"agent:{data.get('reviewer_version','unknown')}:{_now_iso()}")

    with _Lock(paper):
        # Log the ingest event
        event = _make_audit_event(
            paper=paper,
            target_id=f"paper:{paper}",
            target_type='Paper',
            action='re_audit',
            prior_state={'sentences_count': len(prior_ids)},
            new_state={'sentences_count': len(current_ids)},
            actor=actor,
            notes=f"claims-reviewer-v2 ingest: {len(current_ids)} sentences, "
                  f"{len(tombstoned)} tombstoned, "
                  f"{auto_closed} auto-closed, {candidates} candidates",
        )
        _append_audit_event(paper, event)

        # Emit tombstone AuditEvents
        for t_id in tombstoned:
            prior_state = prose_state['sentences'].get(t_id, {}).get('human_state')
            t_event = _make_audit_event(
                paper=paper,
                target_id=t_id,
                target_type='Sentence',
                action='tombstone',
                prior_state=prior_state,
                new_state='tombstoned',
                actor=actor,
                notes='Sentence disappeared from paper prose (sentence_id not in new agent run)',
            )
            _append_audit_event(paper, t_event)
            # Preserve prior state in prose_state as tombstoned
            if t_id in prose_state['sentences']:
                prose_state['sentences'][t_id]['tombstoned_at'] = event['meta']['timestamp']

        # Persist normalized quotes for future rewrite-of heuristic
        prose_state.setdefault('tombstoned_quotes', {})
        # Record tombstoned ones' normalized text so future ingests can match
        # Note: this requires prior claims_review.json to have quote_normalized;
        # we snapshot best-effort here
        _atomic_write_prose_state(paper, prose_state)

    print(json.dumps(report, indent=2))
    return 0


def _levenshtein_ratio(a: str, b: str) -> float:
    """Approximate Levenshtein similarity on short strings (simple DP)."""
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    n, m = len(a), len(b)
    if max(n, m) > 500:  # cap to avoid pathological cases
        return 0.0
    prev = list(range(m + 1))
    for i in range(1, n + 1):
        curr = [i] + [0] * m
        for j in range(1, m + 1):
            cost = 0 if a[i - 1] == b[j - 1] else 1
            curr[j] = min(
                curr[j - 1] + 1,
                prev[j] + 1,
                prev[j - 1] + cost,
            )
        prev = curr
    dist = prev[m]
    return 1.0 - dist / max(n, m)


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: supersede
# ────────────────────────────────────────────────────────────────────────────

def cmd_supersede(args: argparse.Namespace) -> int:
    """Human confirms a prior finding is superseded (non-interactive path)."""
    prior_id = args.prior_finding_id
    reason = args.reason
    actor = args.actor or _default_actor()

    # The prior_finding_id format depends on the graph extractor; we accept
    # either a ReviewFinding node id OR a sentence_id (for sentence-level).
    # Paper derivation: if sentence:, parse paper; else look up via the
    # finding's source paper (requires --paper arg).
    if prior_id.startswith('sentence:'):
        paper = _paper_from_sentence_id(prior_id)
    elif args.paper:
        paper = args.paper
    else:
        print(
            "sentence_state: supersede requires either a sentence_id starting "
            "with 'sentence:' or an explicit --paper",
            file=sys.stderr,
        )
        return 1

    with _Lock(paper):
        event = _make_audit_event(
            paper=paper,
            target_id=prior_id,
            target_type='ReviewFinding',
            action='supersede_confirm',
            prior_state='open',
            new_state='superseded',
            actor=actor,
            notes=reason,
            related_finding_id=prior_id,
        )
        _append_audit_event(paper, event)

    print(json.dumps({'ok': True, 'event_id': event['id']}))
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: tombstone-sweep (standalone; usually auto-run by ingest_agent_run)
# ────────────────────────────────────────────────────────────────────────────

def cmd_tombstone_sweep(args: argparse.Namespace) -> int:
    paper = args.paper
    cr_path = claims_review_path(paper)
    if not cr_path.exists():
        print(f"sentence_state: no claims_review.json at {cr_path}", file=sys.stderr)
        return 1
    with open(cr_path) as f:
        cr = json.load(f)
    current_ids = {s['id'] for s in cr.get('sentences', [])}
    state = _load_prose_state(paper)
    prior_ids = set(state.get('sentences', {}).keys())
    tombstoned = sorted(prior_ids - current_ids)
    print(json.dumps({
        'paper': paper,
        'tombstoned_sentences': tombstoned,
        'tombstoned_count': len(tombstoned),
    }, indent=2))
    return 0


# ────────────────────────────────────────────────────────────────────────────
# Subcommand: reconcile (interactive-ish — shows candidates)
# ────────────────────────────────────────────────────────────────────────────

def cmd_rebuild_prose_state(args: argparse.Namespace) -> int:
    """Replay audit_log.jsonl into prose_state.json.

    Recovery path for ``cmd_mark`` partial-failure scenarios: if
    ``_append_audit_event`` succeeded but ``_atomic_write_prose_state``
    failed, the audit log carries an event whose effect didn't land in
    prose_state. Per design doc §9, the audit log is replay-canonical;
    this command makes the recovery path executable.

    Modes:
      --check   compare rebuilt state to current; print diff; exit 1 if drift
      --write   atomically replace prose_state.json with the rebuilt state
      (default: --check)

    Replay rules:
      - Events with ``meta.target_type == 'Sentence'`` and an action in
        {verify, mark_interpretive, mark_needs_fix, mark_needs_recheck}
        set the human_state to the canonical mapping.
      - Events with action == 'tombstone' clear the sentence (entry kept
        for audit, but ``human_state`` set to None and ``tombstoned_at``
        carried).
      - Events with action == 'supersede_confirm' or ``re_audit`` are
        informational; they don't mutate human_state.
      - Other events are skipped (no-op for prose_state purposes).
      - Order: events processed in timestamp order (file order).
    """
    paper = args.paper
    al_path = audit_log_path(paper)
    if not al_path.exists():
        print(json.dumps({
            'paper': paper, 'audit_events': 0, 'rebuilt_sentences': 0,
            'note': 'no audit_log.jsonl — nothing to replay',
        }, indent=2))
        return 0

    # Load all events in file order
    events: list[dict] = []
    with open(al_path, 'r', encoding='utf-8') as f:
        for raw in f:
            line = raw.strip()
            if not line:
                continue
            try:
                events.append(json.loads(line))
            except json.JSONDecodeError as exc:
                print(f"sentence_state rebuild: skipping malformed line: {exc}",
                      file=sys.stderr)
    # Sort by timestamp (defensive — file order should already match,
    # but if events from concurrent processes interleave on a non-POSIX
    # FS, timestamps win).
    events.sort(key=lambda e: (e.get('meta') or {}).get('timestamp', ''))

    # Inverse of _STATE_TO_HUMAN: derive the human_state from action
    _ACTION_TO_HUMAN = {
        'verify': 'human_verified',
        'mark_interpretive': 'human_interpretive',
        'mark_needs_fix': 'human_needs_fix',
        'mark_needs_recheck': 'human_needs_recheck',
    }
    rebuilt: dict[str, dict] = {}
    for ev in events:
        meta = ev.get('meta') or {}
        if meta.get('target_type') != 'Sentence':
            continue
        sid = meta.get('target_id')
        if not sid:
            continue
        action = meta.get('action')
        if action in _ACTION_TO_HUMAN:
            rebuilt[sid] = {
                'human_state': _ACTION_TO_HUMAN[action],
                'human_ratified_at': meta.get('timestamp'),
                'human_ratified_by': meta.get('actor'),
                'human_notes': meta.get('notes') or '',
            }
        elif action == 'tombstone':
            rebuilt[sid] = {
                'human_state': None,
                'tombstoned_at': meta.get('timestamp'),
                'tombstoned_by': meta.get('actor'),
            }
        # else: re_audit / supersede_confirm / etc. don't mutate.

    rebuilt_state = {
        'paper': paper,
        'schema_version': 'v2',
        'sentences': rebuilt,
    }

    # Compare to current
    current = _load_prose_state(paper)
    cur_sentences = current.get('sentences') or {}
    drift_added = sorted(set(rebuilt) - set(cur_sentences))
    drift_removed = sorted(set(cur_sentences) - set(rebuilt))
    drift_changed = sorted(
        sid for sid in (set(rebuilt) & set(cur_sentences))
        if rebuilt[sid] != cur_sentences[sid]
    )
    has_drift = bool(drift_added or drift_removed or drift_changed)

    summary = {
        'paper': paper,
        'audit_events': len(events),
        'rebuilt_sentences': len(rebuilt),
        'current_sentences': len(cur_sentences),
        'drift': {
            'added': drift_added,
            'removed': drift_removed,
            'changed': drift_changed,
        },
        'has_drift': has_drift,
    }
    print(json.dumps(summary, indent=2))

    if args.write:
        if not has_drift:
            return 0
        with _Lock(paper):
            _atomic_write_prose_state(paper, rebuilt_state)
        print(f"sentence_state: wrote rebuilt prose_state.json ({len(rebuilt)} sentences)",
              file=sys.stderr)
        return 0
    # --check mode: drift = nonzero exit
    return 1 if has_drift else 0


def cmd_reconcile(args: argparse.Namespace) -> int:
    paper = args.paper
    cr_path = claims_review_path(paper)
    if not cr_path.exists():
        print(f"sentence_state: no claims_review.json at {cr_path}", file=sys.stderr)
        return 1
    with open(cr_path) as f:
        cr = json.load(f)
    nrpf = cr.get('non_reproducing_prior_findings', [])
    candidates = [f for f in nrpf if f.get('status') == 'candidate_for_supersession']
    print(json.dumps({
        'paper': paper,
        'candidate_count': len(candidates),
        'candidates': candidates,
        'hint': (
            "To confirm supersession on each: "
            "`scripts/sentence_state.py supersede <prior_finding_id> "
            "--reason '...' --paper " + paper + "`"
        ),
    }, indent=2))
    return 0


# ────────────────────────────────────────────────────────────────────────────
# CLI entry
# ────────────────────────────────────────────────────────────────────────────

def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog='sentence_state.py',
        description='Sole writer for sentence-level verification state (Phase 5v Wave 10b)',
    )
    sub = p.add_subparsers(dest='subcommand', required=True)

    # mark
    pm = sub.add_parser('mark', help='Mark a sentence with a human verification state')
    pm.add_argument('sentence_id', help='sentence:<paper>:<section>:<sha8>')
    pm.add_argument('state', help='verified|interpretive|needs_fix|needs_recheck')
    pm.add_argument('--notes', default=None)
    pm.add_argument('--actor', default=None, help='user:<id> or agent:<name>:<ts>')
    pm.set_defaults(func=cmd_mark)

    # validate
    pv = sub.add_parser('validate', help='Schema-check a claims_review.json')
    pv.add_argument('path')
    pv.set_defaults(func=cmd_validate)

    # normalize-quote
    pn = sub.add_parser('normalize-quote', help='Normalize a quote + compute sha8')
    pn.add_argument('quote')
    pn.add_argument('--json', action='store_true', help='Emit JSON instead of two-line format')
    pn.set_defaults(func=cmd_normalize_quote)

    # ingest_agent_run
    pi = sub.add_parser('ingest_agent_run',
                         help='Validate + diff a new claims_review.json against prior prose_state')
    pi.add_argument('path', help='Path to claims_review.json')
    pi.add_argument('--dry-run', action='store_true')
    pi.set_defaults(func=cmd_ingest_agent_run)

    # supersede
    ps = sub.add_parser('supersede', help='Human-confirm a prior finding is superseded')
    ps.add_argument('prior_finding_id')
    ps.add_argument('--reason', required=True)
    ps.add_argument('--actor', default=None)
    ps.add_argument('--paper', default=None,
                     help='Required if prior_finding_id is not a sentence:')
    ps.set_defaults(func=cmd_supersede)

    # tombstone-sweep
    pt = sub.add_parser('tombstone-sweep', help='List tombstoned sentences for a paper')
    pt.add_argument('--paper', required=True)
    pt.set_defaults(func=cmd_tombstone_sweep)

    # reconcile
    pr = sub.add_parser('reconcile', help='List candidate-for-supersession entries')
    pr.add_argument('--paper', required=True)
    pr.set_defaults(func=cmd_reconcile)

    # rebuild_prose_state — Wave 10 strengthening (replay-canonical recovery)
    pb = sub.add_parser(
        'rebuild_prose_state',
        help='Replay audit_log.jsonl into prose_state.json '
             '(--check for diff, --write to apply)',
    )
    pb.add_argument('--paper', required=True)
    grp = pb.add_mutually_exclusive_group()
    grp.add_argument('--check', dest='write', action='store_false',
                     default=False,
                     help='Compare rebuilt to current; exit 1 on drift (default)')
    grp.add_argument('--write', dest='write', action='store_true',
                     help='Atomically replace prose_state.json with rebuilt state')
    pb.set_defaults(func=cmd_rebuild_prose_state)

    return p


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == '__main__':
    sys.exit(main())
