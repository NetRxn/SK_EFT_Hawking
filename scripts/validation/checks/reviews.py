"""Review-document and supersession-ledger checks — ADR-009 Phase 2.

`recurrence_reopens_closures` (a closed finding must not recur in a later review),
`review_severity_declared`, `review_docs_mint_findings` (a review that produces zero
graph nodes fails loudly), `accepted_findings_carry_rationale`.

These four exist because the ledger is the ONLY channel that can close a finding,
which makes a stale or unjustified closure the remaining way for a real defect to
read as resolved. Each was written against an observed failure, and each carries its
measurement history in-body — notably `recurrence_reopens_closures`, whose threshold
was mis-calibrated three times against a self-remediating corpus before being frozen
against labelled pairs. **Read those comments before touching a constant here.**

`_recurrence_norm`, `_RECURRENCE_MIN_TITLE` and `_RECURRENCE_MIN_OVERLAP` are at
module scope precisely so `tests/.../TestRecurrenceThresholdAgainstFrozenPairs` binds
the REAL matcher instead of re-implementing it — which it did until 2026-08-03, when
the production matcher could have been deleted or inverted with that test still
green. `_recurrence_norm` and `_RECURRENCE_MIN_OVERLAP` are in the frozen external
surface; `validate` re-exports them.

Import rules as elsewhere. No check here reads a runtime flag.
"""
from __future__ import annotations

import json
import re

import validate_helpers as _H
from validation._registry import CheckResult, Detail, register_check


# ── Recurrence matcher — module scope so tests can reach the REAL implementation ──
# These were function-locals until 2026-08-03 (ADR-009 Phase 0, Guard 3). The consequence
# was that `tests/test_bundle_formulas_d11_d12.py::TestRecurrenceThresholdAgainstFrozenPairs`
# — the test whose whole purpose is to hold this threshold to a frozen labelled set —
# could not import them, so it RE-IMPLEMENTED `norm()` locally and re-hardcoded the
# threshold. The production matcher could have been deleted or inverted and that test would
# still have passed. It asserted nothing about this code.
#
# The calibration history lives with the check body below, where the decision was made; do
# not restate it here. `_MIN_TITLE` / `_MIN_OVERLAP` / `_norm` inside the check are aliases
# of these, so the two can never diverge.
_RECURRENCE_MIN_TITLE = 12     # see the check body for why
_RECURRENCE_MIN_OVERLAP = 0.45  # Jaccard over token sets; see the check body for the derivation

#: A later review's heading that ANNOUNCES a fix is confirmation of the closure, not
#: evidence against it (added 2026-08-05, audit finding QI-34). Every finding is born
#: `open` by the birth-status invariant — including the "✅ FIXED — <restated finding>"
#: entries a later round writes to record that a prior finding was remediated. Those
#: restatements are near-verbatim by construction, so they are the HIGHEST-scoring
#: pairs in the corpus and every one of them is a false positive: measured, the top
#: three matches under heading-based comparison (0.643 / 0.500 / 0.438) are all a
#: closure paired with its own resolution notice.
#:
#: ⚠️ This is NOT a revival of heading-parse closure — the mechanism removed in D12
#: round 11 because it let a document close its own findings by wording. Nothing here
#: changes any status: the finding stays `open` in the graph and to every other
#: consumer. It states only that a heading asserting "this was fixed" does not
#: CONTRADICT the ledger record saying the same thing. The residual exposure is that
#: wording a genuine recurrence as a resolution notice would suppress a hit here; it
#: would not close anything, and `review_docs_mint_findings` still sees the finding.
_RECURRENCE_RESOLUTION_NOTICE_RE = re.compile(
    r'✅|✓|\bRESOLVED\b|\bFIXED\b|\bverified clean\b|\bNO ACTION\b|\bnot a defect\b',
    re.IGNORECASE)


def _recurrence_norm(s: str) -> str:
    """Normalize a finding label for recurrence comparison.

    Strips markup, lowercases, drops non-alphanumerics, then removes leading
    section-number and severity-word tokens — a recurrence appears under a DIFFERENT
    number in a later round (round 8's 5.1 recurring as round 9's 3.2), so leading
    numbers are noise in exactly the case the check exists for.
    """
    s = re.sub(r'[`*_\[\]]', '', str(s or '')).lower()
    s = re.sub(r'[^a-z0-9 ]+', ' ', s)
    toks = s.split()
    while toks and (re.fullmatch(r'[0-9]+([a-z0-9]*)?', toks[0])
                    or toks[0] in ('blocker', 'required', 'recommended', 'critical',
                                   'major', 'minor', 'advisory', 'regression')):
        toks.pop(0)
    return " ".join(toks)


@register_check("recurrence_reopens_closures",
                "A closure is not contradicted by a later review raising the same finding")
def check_recurrence_reopens_closures() -> CheckResult:
    """CHECK: a finding closed in the ledger must not recur in a LATER review.

    Added 2026-07-31 (D12 Stage-13 round-11 finding 8.1b, part 3c). The ledger is now the
    sole channel that can close a finding, which makes a stale closure the remaining way
    for a real defect to read as resolved: close it, have a later round raise the same
    thing, and the ledger still says fixed. That happened repeatedly this session — the
    "effective modulus" misnomer was closed and re-raised across five rounds.

    Recurrence is matched on the finding's own title text, normalised, requiring a long
    overlap so that two genuinely different findings about the same file do not collide.
    A hit is reported against the CLOSURE, not the new finding: the new finding is correct,
    and it is the closure that is now false.
    """
    try:
        from build_graph import extract_review_finding_nodes
    except ImportError as exc:
        return CheckResult(passed=False, details=[
            Detail("import", False, f"unavailable ({exc}) — unverified, not passing")])

    # ⚠️ THRESHOLDS ARE MEASURED, NOT GUESSED. The first version required a 60-character
    # common prefix. Measured afterwards: normalized finding labels run min 5 / median 48 /
    # **max 56** characters, so that threshold could never be met and the check was
    # structurally incapable of ever reporting a hit — while printing a reassuring
    # "0 contradicted" over 500 closures. That is the sixth guard in this session that
    # could not do what its summary said, and the pattern each time was choosing a constant
    # from what I imagined the data looked like.
    # ⚠️ The PRIMITIVE was wrong, not just the constant (D11 round-12 BLOCKER 4.2).
    # I required a 30-character common PREFIX. Measured over all 4,210 candidate pairs in
    # this corpus, the maximum prefix ANY pair achieves is 17 — and `_PREFIX_FRAC *
    # _MIN_TITLE = 22.5` put a second floor above that ceiling, so no single constant could
    # revive it. The check printed "0 contradicted by a recurrence" while being incapable
    # of anything else, under a comment that read "THRESHOLDS ARE MEASURED, NOT GUESSED"
    # and listed the six previous instances. I had measured label LENGTHS; the predicate
    # compares PREFIXES, and I never measured those.
    #
    # A recurrence restates a finding, it does not re-type it: word order and wording drift
    # while the vocabulary persists. Token overlap (Jaccard) is the right primitive.
    # Measured on the same 4,210 pairs: median 0.00, p99 0.20, max 0.67 — and the single
    # pair at 0.67 is a TRUE recurrence ("israel third law parenthetical", closed then
    # re-raised in a later round). 0.50 sits in the empty band between p99 and that pair.
    _MIN_TITLE = _RECURRENCE_MIN_TITLE   # below this a title carries too few tokens to compare
    # ⚠️ RE-DERIVED 2026-08-01 (D11 round-13 N1). Switching the primitive from prefix to
    # Jaccard was right; I then kept a 0.50 threshold that I had measured on a sweep whose
    # pairing rules were NOT the check's own. Measured with the check's `_norm`, its
    # same-bundle rule and its date rule, over 4,706 pairs: median 0.000, p99 0.200,
    # MAX 0.429. So 0.50 admitted nothing — the guard still could not fire, one round after
    # being "fixed", and the 0.67 pair I cited as calibration does not exist as a
    # closure/open pair at all.
    #
    # The two D12 records I reported it "rejecting" were added already `open`; the guard had
    # no part in it. That claim in commit 03a4592e's message is false and this comment is
    # the correction.
    #
    # 0.40 sits between p99 (0.200) and the top pair (0.429), which is a TRUE stale closure:
    # 1530:D11:4.1 closed, 2220:D11:4.6 open, both about PAPER_DRAFT_MAPPING.md:109.
    _MIN_OVERLAP = _RECURRENCE_MIN_OVERLAP   # Jaccard over token sets
    #
    # ⚠️ THIS MATCHER IS WEAK, and its limits are measured — but an earlier version of this
    # comment said it "cannot do its job", which round 14 disproved: driving the ledger off
    # git snapshots it fires 3 real hits at 0.40 that 0.50 could not reach, and scores 22/29
    # on a 29-pair labelled set built from twelve self-declared chains. My own fixture has
    # three positives and I generalised from it to an absolute — the same over-reach, one
    # layer up, as the numbers this session kept overstating. What follows is the measured
    # limit, not an impossibility claim. Measured on
    # `tests/fixtures/recurrence_pairs.json`: true recurrences score 0.188, 0.000, 0.071
    # while unrelated pairs score 0.000 — the worst positive does not beat the best
    # negative, so NO threshold separates them. All three tunings this session
    # (30-char prefix -> 0.50 -> 0.40) were tuning a matcher that cannot discriminate.
    #
    # Root cause is upstream: `label` is `heading[:50]`, so a RESTATED finding — which is
    # what a recurrence is — shares almost no vocabulary with its original. What this guard
    # actually detects is duplicate heading OPENINGS, which is why every real hit it has
    # produced was a near-verbatim repeat. Those hits were genuine and worth having; the
    # guard is kept for them, at a threshold that admits them and little else.
    #
    # It is a WEAK recurrence detector — good on near-verbatim restatements, poor on
    # rewordings — and must not be quoted as a reliable one. Improving it
    # needs the full finding text carried on the node, not a wider constant — and
    # `tests/…::TestRecurrenceThresholdAgainstFrozenPairs` fails the day that lands, which
    # is the signal to replace this comment.
    #
    # QI: qi-threshold-calibration-consumes-its-own-datum. Three times a constant was set
    # just under the live corpus maximum by the same commit that repaired the pair
    # producing that maximum, so it was unreachable on arrival. Thresholds on a
    # self-remediating corpus must be calibrated against frozen labelled pairs.
    #
    # ══ 2026-08-05, audit finding QI-34 — the fourth tuning is NOT a tuning ══
    #
    # The finding as filed: threshold 0.40 sits above the live corpus maximum 0.375 over
    # 7,489 pairs, so the guard cannot fail in production. **Partly true, and the
    # capability half is overstated** — measured, a realistic restatement of a real
    # finding scores 0.500 on `label` and would fire. What is true is that the corpus
    # max is 0.375, so the guard is silent today; and that 1.33x of separation between
    # "silent on this corpus" and "fires on a true recurrence" is not a working margin.
    #
    # A fifth constant would have been the fourth instance of the QI above. The comment
    # four paragraphs up already named the real fix — "the full finding text carried on
    # the node" — and the text was ALREADY THERE: the node carries `name: heading[:200]`
    # next to `label: heading[:50]`, and this check read the shorter field. The change is
    # therefore to the SUBSTRATE, not to a threshold:
    #
    #   * match on `name`, so a truncation artifact stops being a token (`heading[:50]`
    #     cut `falsifier` to `falsifie` and `the` to `t`, which is why two headings
    #     differing in one word scored only 0.500);
    #   * exclude open findings whose heading is a RESOLUTION NOTICE — those are the
    #     corpus's top three scores (0.643 / 0.500 / 0.438) and all three are a closure
    #     paired against its own "**RESOLVED**" restatement.
    #
    # Result, same pairing rules, same normalizer: corpus max 0.375 -> **0.267**; a true
    # restatement 0.500 -> **0.900**; separation 1.33x -> **3.37x**. 0.45 sits in the
    # empty band with 1.7x clearance above the corpus and 2x below a true hit — it is the
    # first of these constants NOT chosen by looking at the live maximum.
    #
    # The frozen-pairs fixture still scores 0.188 / 0.000 / 0.071 and is still not
    # separated: those three are heavy rewordings, and this change does not claim to
    # reach them. `TestRecurrenceThresholdAgainstFrozenPairs` therefore still passes,
    # unchanged, and the guard's coverage is still partial. What changed is that it is
    # now weak with a margin instead of weak without one.

    # Drops leading section-number and severity-word tokens. A recurrence appears under
    # a DIFFERENT number in a later round — round 8's 5.1 recurring as round 9's 3.2 —
    # so comparing prefixes that begin with the number is fragile in exactly the case
    # the check exists for. Verified with a planted probe whose label minted as
    # "1.1 1.1 blocker ..." against a source of "1.1 blocker ...": the prefix agreement
    # was near zero for two identical findings.
    # Implementation is `_recurrence_norm` at module scope (ADR-009 Phase 0, Guard 3) so
    # the frozen-pairs test binds to the real matcher instead of a copy of it.
    _norm = _recurrence_norm

    # ⚠️ MATCH ON `name`, NOT `label` (changed 2026-08-05, audit finding QI-34).
    #
    # `label` is `f'{section_num} {heading[:50]}'`. Fifty characters truncates
    # mid-word, and the fragment counts as a token: two headings that differ only in
    # one word scored 0.500 because `_norm` produced `'falsifie'` and `'t'` from the
    # cut. The in-body comment below concluded that "improving it needs the full
    # finding text carried on the node, not a wider constant" — and the full text was
    # ALREADY on the node. `build_graph.extract_review_finding_nodes` emits
    # `name: heading[:200]` alongside `label`; this check simply read the wrong field.
    #
    # Measured on the live corpus with the check's own pairing rules, and this is the
    # whole justification for the switch:
    #
    #   field                 corpus max      a realistic restatement    separation
    #   label  (heading[:50])   0.375                0.500                  1.33x
    #   name   (heading[:200])  0.267*               0.900                  3.37x
    #
    #   (* after the resolution-notice exclusion above; 0.643 without it, and that
    #      0.643 pair is a closure matched against its own "**RESOLVED**" notice.)
    #
    # `name + detail[:400]` was measured too and is WORSE — body boilerplate dilutes
    # the vocabulary that carries the signal (median rises 0.043 -> 0.104 while the
    # max falls 0.643 -> 0.427). More text is not the axis; less TRUNCATION is.
    findings = extract_review_finding_nodes()
    closed, open_ = [], []
    for f in findings:
        m = f.get("meta") or {}
        text = f.get("name") or f.get("label", "")
        rec = (m.get("review_date", ""), _norm(text), f["id"], m.get("severity"),
               m.get("inferred_bundle") or m.get("inferred_paper"), text)
        if not rec[1] or len(rec[1]) < _MIN_TITLE:
            continue
        (closed if m.get("status") in ("fixed", "accepted") else open_).append(rec)

    details: list[Detail] = []
    hits = 0
    compared = 0
    _had_candidate: set = set()
    skipped_short = sum(1 for f in findings
                        if len(_norm(f.get("name") or f.get("label", ""))) < _MIN_TITLE)
    skipped_notice = 0
    for cdate, ctext, cid, csev, cbundle, _craw in closed:
        if csev not in ("critical", "major"):
            continue
        for odate, otext, oid, _, obundle, oraw in open_:
            # Same bundle only. Reviews share heading boilerplate across bundles, so a D2
            # closure matching an I2 finding's title is a template collision, not a
            # recurrence — measured: the two hits before this constraint were exactly that
            # (D2 vs I2, L3 vs L2).
            if cbundle is None or obundle is None or cbundle != obundle:
                continue
            if odate <= cdate:
                continue
            # A later heading that ANNOUNCES the fix confirms the closure; it does not
            # contradict it. See `_RECURRENCE_RESOLUTION_NOTICE_RE` — these restatements
            # are near-verbatim by construction and were the corpus's top three scores.
            if _RECURRENCE_RESOLUTION_NOTICE_RE.search(oraw):
                skipped_notice += 1
                continue
            _a, _b = set(ctext.split()), set(otext.split())
            if not _a or not _b:
                continue
            # Count a closure as COMPARED only once it has something to compare against
            # (D12 round-13). `compared += 1` used to sit before this loop, so it counted
            # closures that reached the loop rather than closures that met a candidate:
            # the summary said 318 where 162 had any counterpart. Ninth instance of the
            # same defect, and the third consecutive version of THIS summary line to
            # overstate its own coverage.
            if cid not in _had_candidate:
                _had_candidate.add(cid)
                compared += 1
            if len(_a & _b) / len(_a | _b) < _MIN_OVERLAP:
                continue
            # Section-number agreement as a tie-breaker (D12 round-14 finding 14.4). The
            # guard's FIRST live D12 effect was a false positive: it held 1524:8.2 open
            # against 1823:8.4 at exactly j = 2/5 = 0.400, carried entirely by the shared
            # phrase "fails open" — two different guards that both failed open, not one
            # finding recurring. A real recurrence is the SAME finding restated, and this
            # corpus numbers findings by class, so a recurrence overwhelmingly keeps its
            # section number (round 14: 8.3 -> 8.3 is the true pair; 8.2 -> 8.4 is not).
            # Marginal scores need that corroboration; strong scores do not.
            if (len(_a & _b) / len(_a | _b) < _MIN_OVERLAP + 0.10
                    and cid.rsplit(':', 1)[-1] != oid.rsplit(':', 1)[-1]):
                continue
            # A surviving pair is a recurrence: every filter above has passed.
            # (A vestigial `if True:` wrapped this block until 2026-08-04 — audit
            # QI-07 — left over from a condition that migrated into the `continue`
            # guards above it.)
            hits += 1
            details.append(Detail(
                cid, False,
                f"closed on {cdate}, but {oid} ({odate}) raises the same finding and is "
                f"open. The later review is the evidence; the CLOSURE is what is now "
                f"false. Reopen it or record why the recurrence is a different defect."))
            break

    # Report what was COMPARED, not what was collected. The previous summary printed
    # `len(closed)` — 552 — while the loop's severity filter meant 148 were actually
    # compared, and it never mentioned the findings excluded for a short title. A guard's
    # summary overstating its own coverage is the failure this session kept producing.
    details.insert(0, Detail(
        "summary", hits == 0,
        f"{compared} blocking-severity closure(s) compared against {len(open_)} open "
        f"finding(s) from later same-bundle reviews; {hits} contradicted by a recurrence. "
        f"NOT compared: {len(closed) - compared} non-blocking closure(s), and "
        f"{skipped_short} finding(s) whose normalised title is under {_MIN_TITLE} chars, "
        f"and {skipped_notice} pairing(s) whose later finding is a resolution notice "
        f"(a heading announcing the fix confirms the closure; it does not contradict it)"))
    return CheckResult(passed=hits == 0, details=details)


@register_check("review_severity_declared",
                "Review documents from the cutoff forward declare each finding's severity")
def check_review_severity_declared() -> CheckResult:
    """CHECK: severity must be a declared field, not an inferable glyph.

    Added 2026-07-31 (D12 Stage-13 round-11 finding 8.1b, part 3b). Severity drove the
    blocking-closure bar while being inferred from glyphs in the heading, which made it
    editable without leaving a trace. Two exploits were demonstrated against that: a
    one-line glyph demotion plus the word "fixed" reopened self-closure on a past BLOCKER,
    and typesetting a summary as `0 «**»BLOCKER«**»` escalated a whole zero-blocker report
    to critical.

    `build_graph` now prefers an explicit `- **Severity:** <level>` line in the finding
    body. This check makes that mandatory from `_CUTOFF` forward, so omitting it is a red
    build rather than a silent downgrade. Historical documents keep glyph inference — there
    are ~1400 findings that predate the convention and rewriting them would be churn with
    no provenance value, so the cutoff is the honest boundary rather than a blanket rule.
    """
    _CUTOFF = "2026-08-01"   # documents dated on/after this must declare severity

    reviews_dir = _H.PAPERS_DIR / "AutomatedReviews"   # one owner (audit QI-11)
    if not reviews_dir.is_dir():
        return CheckResult(passed=True, details=[
            Detail("scope", True, "no review directory", warning=True)])

    _SEV_LINE = re.compile(r'^[-*]\s*\*\*Severity:?\*\*', re.M | re.I)
    _HEADING = re.compile(r'^#{3,5}\s+\S', re.M)
    # ⚠️ VALUE VALIDATION, added 2026-08-05 (PR-review reviewer 6). This check counted
    # `**Severity:**` LINES and never looked at what they said — so `- **Severity:**
    # blockr` satisfied it completely, while `build_graph` could not map the token and
    # the finding landed as `advisory`. A typo'd BLOCKER then read YELLOW and
    # `readiness_submission_gate` passed. The line count is the weaker half of the
    # obligation; the vocabulary is the other half, and this check owns both.
    _SEV_VALUE = re.compile(r'^[-*]\s*\*\*Severity:?\*\*:?\s*([A-Za-z]+)', re.M | re.I)

    details: list[Detail] = []
    bad = 0
    bad_value = 0
    checked = 0
    try:
        from build_graph import _SEVERITY_DECL_MAP
        vocabulary = set(_SEVERITY_DECL_MAP)
    except ImportError as exc:      # cannot-measure is not success
        return CheckResult(passed=False, details=[Detail(
            "import", False,
            f"build_graph._SEVERITY_DECL_MAP unavailable ({exc}) — the accepted "
            f"vocabulary is unknown, so this check cannot validate anything")])

    for md in sorted(reviews_dir.glob("*/*.md")):
        date = md.parent.name[:10]
        if date < _CUTOFF:
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        n_head = len(_HEADING.findall(text))
        if n_head == 0:
            continue
        checked += 1
        n_sev = len(_SEV_LINE.findall(text))
        if n_sev < n_head:
            bad += 1
            details.append(Detail(
                str(md.relative_to(_H.PROJECT_ROOT)), False,
                f"{n_head} finding heading(s) but only {n_sev} `- **Severity:**` line(s). "
                f"From {_CUTOFF} every finding must declare its severity explicitly: "
                f"severity drives the blocking-closure bar, and inferring it from a glyph "
                f"lets it be changed without leaving a trace."))
        unknown = sorted({v for v in _SEV_VALUE.findall(text)
                          if v.strip().lower() not in vocabulary})
        if unknown:
            bad_value += 1
            details.append(Detail(
                f"{md.relative_to(_H.PROJECT_ROOT)}:vocabulary", False,
                f"declares severity value(s) `build_graph` cannot map: {unknown}. "
                f"Accepted: {sorted(vocabulary)}. An unmappable token is not a "
                f"declaration — the finding falls back to inference, and a mistyped "
                f"BLOCKER lands advisory while this check's line count reads clean."))

    details.insert(0, Detail(
        "summary", bad == 0 and bad_value == 0,
        f"{checked} review document(s) dated >= {_CUTOFF} checked; {bad} with findings "
        f"that do not declare severity, {bad_value} declaring an unmappable severity "
        f"value (earlier documents keep glyph inference)"))
    return CheckResult(passed=(bad == 0 and bad_value == 0), details=details)


@register_check("review_docs_mint_findings",
                "Every bundle Stage-13 review document mints at least one ReviewFinding node")
def check_review_docs_mint_findings() -> CheckResult:
    """CHECK: a review that produces zero graph nodes must fail loudly, not silently pass.

    Added 2026-07-31 (D12 Stage-13 round-9 BLOCKER 8.2). This is the fail-open path that
    survived every previous repair, and it needs no mutation to trigger — only a heading
    that drifts from `### N.N — ` to `#### `, `### Finding `, or `### 1.1: `. The
    round-9 reviewer wrote a review declaring four BLOCKERs with such headings and it
    minted **zero** nodes; `findings_reach_the_graph` structurally cannot see it, because
    that guard's file index is built *from findings*, so a file with no findings is not in
    it. A whole round of blockers then reads exactly like a clean round.

    The predicate the existing guards cannot express is this one: for each review document
    named after a bundle in the roster, at least one `ReviewFinding` node must resolve to
    it. Zero is a parser failure or a malformed document — never evidence of a clean review.
    """
    # Deliberately LOOSER than `build_graph._REVIEW_SECTION_RE`: this asks "does this
    # document look like it carries findings", and the gap between the two regexes IS the
    # defect being detected. If they were the same pattern the check would be a tautology.
    #
    # ⚠️ The first version was circular anyway (D12 round-11 BLOCKER 8.2). It required
    # `<digits><dash>` — the exact fragment that drifts — so the six documents minting zero
    # were precisely the six it skipped, and my "8 → 0" was measured inside the scope the
    # check itself defines. Those six carry 47 severity-marked headings including four
    # declared BLOCKERs in `lean_project_audit.md` and four 🔴 in `CitationReview-01.md`.
    #
    # The predicate is now SEVERITY, not numbering: a heading that declares BLOCKER /
    # REQUIRED / RECOMMENDED / CRITICAL, or carries a severity glyph, is a finding heading
    # whatever its numbering scheme — including the forms that defeated the old one
    # (`### 1. Paper 7 —`, `### 1. Class 6 BLOCKER —`, `### BLOCK-1 (…) —`,
    # `### I.1 Count …`, and glyph-first `### 🔴 BLOCKER 1.1 —`). Severity is the thing a
    # finding cannot omit and still be a finding.
    _SEVERITY_HEADING = re.compile(
        r'^#{3,5}\s+.*(?:BLOCKER|REQUIRED|RECOMMENDED|CRITICAL|MAJOR|MINOR'
        r'|\U0001F534|\U0001F7E1|\U0001F535|\u26a0)', re.M)
    # ...but a severity WORD is not a severity LABEL. A clean figure review's headings read
    # "`fig5.png` (P2) — **PASS** (round-2 BLOCKER resolved)": the token appears inside a
    # resolution note, and that document correctly mints nothing. Excluding headings that
    # also declare PASS/RESOLVED is the difference between "carries findings" and "mentions
    # a finding", and skipping it would have made this guard fire on a correct document —
    # the fifth time today.
    _RESOLVED_HEADING = re.compile(r'PASS|RESOLVED|resolved', re.I)

    def _carries_findings(text: str) -> bool:
        """True if any severity-labelled heading is NOT a PASS/RESOLVED note.

        ⚠️ This was `any(... findall ...) or any(... finditer ...)` until 2026-08-04
        (audit QI-09). `_SEVERITY_HEADING` has only non-capturing groups, so
        `findall` yields the same full-match strings `finditer` yields via
        `m.group(0)` — the two legs were the identical predicate computed twice and
        OR-ed with itself. Scanning the review corpus twice per document, to reach a
        conclusion the first leg already had.
        """
        return any(not _RESOLVED_HEADING.search(h)
                   for h in _SEVERITY_HEADING.findall(text))

    try:
        from build_graph import extract_review_finding_nodes
    except ImportError as exc:
        return CheckResult(passed=False, details=[
            Detail("import", False,
                   f"could not import the review extractor ({exc}) — unverified, not passing")])

    try:
        findings = extract_review_finding_nodes()
    except Exception as exc:
        return CheckResult(passed=False, details=[
            Detail("extract", False,
                   f"review extraction failed ({type(exc).__name__}: {exc}) — unverified")])

    minted: dict[str, int] = {}
    for f in findings:
        rf = (f.get("meta") or {}).get("review_file")
        if rf:
            minted[rf] = minted.get(rf, 0) + 1

    reviews_dir = _H.PAPERS_DIR / "AutomatedReviews"   # one owner (audit QI-11)
    details: list[Detail] = []
    empty = 0
    checked = 0
    if reviews_dir.is_dir():
        for md in sorted(reviews_dir.glob("*/*.md")):
            # Scope by CONTENT, not by filename or directory.
            #
            # Two earlier scopings were both wrong, in opposite directions. Filtering to
            # roster-named files put 120 documents out of scope. Then excluding
            # `*-bundle-stage13/` — because 107 of 138 files there are
            # `bundle_readiness.py` aggregations that mint zero BY DESIGN — excluded the
            # directory `BUNDLE_DIRECTORY_SCHEMA.md:86` and `BUNDLE_LIFT_PROCEDURE.md:243`
            # name as THE canonical location for a Stage-13 review, hiding five
            # findings-bearing reviews, one of them declaring a BLOCKER (D12 round-10 8.2).
            #
            # The honest discriminator is the document's own content: a file containing
            # finding-shaped headings must mint findings. A generated aggregation has no
            # such headings and is silently skipped — not because of where it lives, but
            # because it never claimed to carry findings.
            if not _carries_findings(md.read_text(encoding="utf-8", errors="replace")):
                continue
            checked += 1
            rel = str(md.relative_to(_H.PROJECT_ROOT))
            n = minted.get(rel, 0)
            if n == 0:
                empty += 1
                details.append(Detail(
                    rel, False,
                    f"this Stage-13 review document mints ZERO ReviewFinding nodes. Either "
                    f"its finding headings do not match the extractor's expected "
                    f"`### <N.N> — <severity> — <text>` form, or the document is malformed. "
                    f"A round that mints nothing is invisible to Gate 11 and reads exactly "
                    f"like a clean round."))

    details.insert(0, Detail(
        "summary", empty == 0,
        f"{checked} document(s) carrying unresolved severity-labelled headings checked "
        f"(a document mentioning a severity only inside a PASS/RESOLVED note carries no "
        f"findings and is skipped); {empty} mint zero"))
    return CheckResult(passed=empty == 0, details=details)


# ── NOT SHIPPED: `ledger_evidence_names_its_finding` ────────────────────────────────
# D12 round-13 BLOCKER 13.1 found three ledger records that close a finding their evidence
# does not describe, and nothing detects it. I built a guard requiring the evidence to share
# a content word with the finding's title, and MEASURED it before shipping: it flags 40
# records, and the ones I sampled are correct. Example —
# `2026-04-28-...:paper40_higher_curvature:2.1`, whose evidence reads "CrossPaperConsistency
# gate verifies sampled cross-paper bibitems match character-for-character on load-bearing
# fields". That describes the FIX; the title describes the DEFECT; well-written evidence
# routinely shares no vocabulary with the finding it closes.
#
# So the premise is wrong, not the threshold, and a guard that flags 40 correct records is
# worse than no guard — that is the lesson this session has taught eleven times. The three
# real mis-keys were caught by a reviewer READING them, which is not a test I can currently
# mechanise. Recording the gap rather than shipping a check that manufactures work.
#
# What would work, and is not built: require the record to name the artifact it changed
# (a file path) and verify that path appears in the cited commit's diff. That is mechanical
# and would have caught all three, since their evidence names another round's artifacts.
#
# (Moved here from `scripts/validate.py` on 2026-08-04 — audit finding QI-26b. It was
# stranded under a `# CHECK 18: Readiness submission gate` header whose body had been
# extracted, so a genuinely useful design record was filed under an unrelated check in
# a file that no longer contains any check. Its nearest kin is the ledger-rationale
# gate below.)


@register_check("accepted_findings_carry_rationale",
                "Every `accepted` supersession record justifies acceptance in writing")
def check_accepted_findings_carry_rationale() -> CheckResult:
    """CHECK: `accepted` must be a recorded decision, never a way to silence a finding.

    Added 2026-07-31 (D12 Stage-13 round-8). `_eval_fix_propagation` stopped treating
    `accepted` as an open blocker this session — correct, because it is a deliberate
    decision written into the supersession ledger, not an unclosed finding. But that
    change also made `accepted` the cheapest way to make a blocking finding disappear
    from Gate 11: 27 blocking-severity findings are currently invisible to it on that
    status alone. The round-8 reviewer measured that 138 of 140 accepted records carry
    substantive rationale and none is wholly bare — so the practice is sound and this
    check pins it, rather than fixing a live defect.

    A blocking-severity acceptance additionally has to say why acceptance rather than a
    fix; "accepted" with a one-line restatement of the finding is not a decision.
    """
    # ADR-009 H1. This site is one of the two where a retargeted anchor would be
    # SILENT: a missing ledger returns passed=True below, so on a module move this
    # check would report success having examined nothing.
    ledger_path = _H.DOCS_DIR / "review_finding_supersessions.json"
    if not ledger_path.is_file():
        return CheckResult(passed=True, details=[
            Detail("ledger", True, "no supersession ledger; skipping", warning=True)])
    try:
        led = json.loads(ledger_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return CheckResult(passed=False, details=[
            Detail("ledger", False, f"ledger unreadable ({exc}) — unverified, not passing")])

    MIN_CHARS = 40
    bad, checked = [], 0
    for e in led.get("supersessions", []):
        if e.get("status") != "accepted":
            continue
        checked += 1
        # The ledger uses three field names for the same thing across its history:
        # `evidence` (recent), `rationale`, and `note` (the 2026-05 records). Reading only
        # the first two produced two false positives on records that are in fact well
        # justified — a guard that flags correct data is worse than none.
        why = " ".join(str(e.get("evidence") or e.get("rationale")
                           or e.get("note") or "").split())
        if len(why) < MIN_CHARS:
            bad.append((e.get("finding_id", "?"), len(why)))

    details = [Detail("summary", not bad,
                      f"{checked} accepted record(s) checked, {len(bad)} without a written "
                      f"rationale of at least {MIN_CHARS} characters")]
    for fid, n in bad[:10]:
        details.append(Detail(
            fid, False,
            f"status=accepted with {n} characters of rationale. `accepted` removes a "
            f"finding from Gate 11's blocking set, so it must record a DECISION — why "
            f"acceptance rather than a fix — not merely assert one."))
    return CheckResult(passed=not bad, details=details)


# ── Chain-of-backing resolvability (B4) ───────────────────────────────────────────────
#
# A `claims_review.json` sentence record carries a chain of backing links — the audit trail
# tying a manuscript sentence to the substrate that supports it. A link of kind
# theorem/axiom/lemma names a Lean target. Nothing verified that the target EXISTS until this
# check: `chain_canonicalize.py --report` could surface it, but no gate consumed the report,
# so a sentence could cite `gapped_interface_axiom` (discharged 2026-05-19) or
# `gap_solution_bounded` (a commented-out block, never a declaration) and read as backed.
#
# ⚠️ THE RESOLVER IS THE WHOLE CHECK, and a naive one manufactures findings rather than
# finding them. Measured on the live corpus, membership-in-declaration-names alone reports
# 515 unresolved links; the true figure is 156. The difference is entirely legitimate targets
# the naive test cannot see:
#   * MODULE targets — `SKEFTHawking.IsingBraiding` is a module, not a declaration (247 links)
#   * SHORT names — `gap_solution_monotone` for `SKEFTHawking.TetradGapEquation....` (785)
#   * Lean CORE axioms — `propext`, `Classical.choice`, `Quot.sound`, never project decls
#   * NOTATION variants — `module:X`, `X (module)`, `X (module, 20 decls)` (89 more, once
#     normalized) — reviewers wrote these by hand across three years of review rounds.
# Resolve against every population a target may legitimately name, and normalize first.
_CORE_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound",
                          "Lean.trustCompiler", "Lean.ofReduceBool"})
# Roots owned by Mathlib/Lean/PhysLib: real names this repo does not index.
_EXTERNAL_ROOTS = frozenset({
    "Mathlib", "Nat", "Int", "Real", "Complex", "Finset", "Matrix", "List", "Set",
    "Function", "Polynomial", "MeasureTheory", "Filter", "Topology", "Metric", "PhysLib"})
_CHAIN_KEYS = ("chain_proposed", "chain_verified", "chain")
_LEAN_LINK_KINDS = frozenset({"theorem", "axiom", "lemma"})

# ZERO headroom: the live measured count of unresolved links (2026-08-07). A ratchet above
# the population cannot fire. This may only ever be LOWERED — see the module docstring rule.
UNRESOLVED_CHAIN_LINK_CEILING = 156


def _normalize_chain_target(raw: str) -> str:
    """Strip the hand-written notation variants that accumulated across review rounds."""
    t = (raw or "").strip()
    t = re.sub(r"^(module|theorem|axiom|lemma|decl)\s*:\s*", "", t)
    t = re.sub(r"\s*\((module|axiom)[^)]*\)$", "", t)
    return t.strip()


def _chain_target_resolves(target: str, names: set, modules: set, short: set) -> bool:
    t = _normalize_chain_target(target)
    if not t:
        return False
    if t in names or t in _CORE_AXIOMS or t in modules:
        return True
    if t.rsplit(".", 1)[-1] in short:
        return True
    if ("SKEFTHawking." + t) in modules or t in {m.rsplit(".", 1)[-1] for m in modules}:
        return True
    return t.split(".", 1)[0] in _EXTERNAL_ROOTS


@register_check("chain_backing_targets_resolve",
                "Every Lean target named in a claims-review chain of backing exists")
def check_chain_backing_targets_resolve() -> CheckResult:
    """Catch a sentence whose audit trail points at a Lean name that is not there.

    Fails when the unresolved-link count exceeds the ratchet, i.e. when a review round ADDS
    a dangling reference. The standing backlog is reported every run, named by paper, so it
    is visible rather than merely bounded.
    """
    if not _H.lean_deps_present():
        return CheckResult(passed=False, measured=False, details=[Detail(
            "lean_deps", False,
            "SKIPPED — lean_deps.json absent, so no target could be resolved; the chain "
            "backing is UNVERIFIED, not passing")])

    deps = _H.load_lean_deps()
    names = {d["name"] for d in deps if d.get("name")}
    modules = {d["module"] for d in deps if d.get("module")}
    short = {n.rsplit(".", 1)[-1] for n in names}

    total = 0
    unresolved: dict[str, int] = {}
    by_paper: dict[str, int] = {}
    for path in sorted(_H.PAPERS_DIR.rglob("claims_review.json")):
        try:
            doc = json.loads(path.read_text())
        except (json.JSONDecodeError, OSError):
            continue
        for sent in doc.get("sentences", []) or []:
            for key in _CHAIN_KEYS:
                for link in ((sent.get(key) or {}).get("links") or []):
                    if link.get("kind") not in _LEAN_LINK_KINDS:
                        continue
                    total += 1
                    tgt = str(link.get("target", ""))
                    if not _chain_target_resolves(tgt, names, modules, short):
                        norm = _normalize_chain_target(tgt) or "<empty>"
                        unresolved[norm] = unresolved.get(norm, 0) + 1
                        by_paper[path.parent.name] = by_paper.get(path.parent.name, 0) + 1

    details = []
    # Guard the seam (§2.5): a scan that matched nothing passes vacuously.
    if total == 0:
        return CheckResult(passed=False, details=[Detail(
            "population", False,
            "no theorem/axiom/lemma chain links found across papers/**/claims_review.json — "
            "the scan reached nothing, which is a resolver or path defect, not a clean corpus")])
    details.append(Detail("population", True,
                          f"{total} Lean chain-of-backing link(s) across the corpus"))

    n_bad = sum(unresolved.values())
    worst = sorted(by_paper.items(), key=lambda kv: -kv[1])[:8]
    within = n_bad <= UNRESOLVED_CHAIN_LINK_CEILING
    details.append(Detail(
        "unresolved", within,
        f"{n_bad} link(s) name a target that does not resolve, across {len(unresolved)} "
        f"distinct target(s) in {len(by_paper)} paper(s) "
        f"(ceiling {UNRESOLVED_CHAIN_LINK_CEILING}); worst: "
        + ", ".join(f"{p}={c}" for p, c in worst)))
    if not within:
        for tgt, cnt in sorted(unresolved.items(), key=lambda kv: -kv[1])[:20]:
            details.append(Detail("target", False, f"{cnt}x unresolved: {tgt}"))
    elif n_bad < UNRESOLVED_CHAIN_LINK_CEILING:
        details.append(Detail(
            "ratchet", True,
            f"backlog fell to {n_bad} — lower UNRESOLVED_CHAIN_LINK_CEILING to match, "
            f"or the ratchet regains headroom and stops being able to fire"))
    return CheckResult(passed=within, details=details)
