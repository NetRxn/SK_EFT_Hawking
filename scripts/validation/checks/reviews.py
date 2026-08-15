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

#: Severities at which a finding blocks submission. Mirrors
#: `readiness_gates.BLOCKING_SEVERITIES`; imported lazily there to keep this module's
#: import graph flat, and asserted equal by `tests/test_d5_reviews.py` so the two cannot
#: drift into disagreeing about what "blocking" means.
_BLOCKING_SEVERITIES = frozenset({'critical', 'blocker', 'major'})

#: Blocking-severity `accepted` records with no `accepted_by`. **MAY ONLY FALL.**
#: Measured 2026-08-15 by the leg below, on the live ledger: 32.
#:
#: ⚠️ A SIBLING MEASUREMENT SAID 31, AND THE DIFFERENCE IS THE POINT. Counting
#: `ReviewFinding` nodes whose `meta.status == 'accepted'` gives 31 (12 critical, 19
#: major); counting last-wins LEDGER records whose finding resolves to a blocking
#: severity gives 32. Both are correct about their own population — a record can name a
#: finding whose node carries a different resolved status. A ceiling must be measured by
#: the predicate that ENFORCES it, or the first honest run trips a ratchet nobody moved.
#: See `check_accepted_findings_carry_rationale` for why this is a ratchet rather than a
#: hard gate, and why bulk-stamping a name to clear it is prohibited.
ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING = 32

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
        # ⚠️ THE ZERO IS NOT EVIDENCE OF ABSENCE, and the summary now says so (D12
        # round-13 13.3). This matcher compares `label` (`heading[:50]`) by token overlap,
        # so it is good on near-verbatim restatements and poor on rewordings — and a
        # recurrence IS a restatement. Measured on the frozen labelled pairs, the worst
        # true positive does not beat the best negative, so no threshold separates them:
        # three tunings of the constant were tuning a matcher that cannot discriminate.
        # A reader who takes `0 contradicted` as "no stale closures exist" is reading a
        # capability the check does not have, which is this project's own defect class
        # pointed at its own instrument.
        f"finding(s) from later same-bundle reviews; {hits} contradicted by a recurrence "
        f"(⚠️ WEAK detector: near-verbatim restatements only — token overlap on a 50-char "
        f"heading cannot see a reworded recurrence, so {hits} is a floor, not a count). "
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
        # ⚠️ This site is IN `CANNOT_MEASURE_PASS_BASELINE` — the project's own frozen
        # list of PASS-without-measuring branches — and reported `measured=True`
        # anyway. 27 of the 28 baselined sites carried the flag; this was the one
        # that did not, and none of the scanner's keywords matches "no review
        # directory". A site listed in today's baseline was today's hole.
        return CheckResult(passed=True, measured=False, details=[
            Detail("scope", True, "no review directory", warning=True,
                   measured=False)])

    _SEV_LINE = re.compile(r'^[-*]\s*\*\*Severity:?\*\*', re.M | re.I)
    _HEADING = re.compile(r'^#{3,5}\s+\S', re.M)
    # ⚠️ VALUE VALIDATION, added 2026-08-05 (PR-review reviewer 6). This check counted
    # `**Severity:**` LINES and never looked at what they said — so `- **Severity:**
    # blockr` satisfied it completely, while `build_graph` could not map the token and
    # the finding landed as `advisory`. A typo'd BLOCKER then read YELLOW and
    # `readiness_submission_gate` passed. The line count is the weaker half of the
    # obligation; the vocabulary is the other half, and this check owns both.
    _SEV_VALUE = re.compile(r'^[-*]\s*\*\*Severity:?\*\*:?\s*([A-Za-z]+)', re.M | re.I)
    # ⚠️ SAME SHAPE, SAME WALK (ADR-012 D1/D2). A lane routes the finding to a worker; a
    # lane `build_graph` cannot map routes NOWHERE, which is an unroutable finding rather
    # than a cosmetic typo. This deliberately reuses the per-document walk below instead of
    # adding a second one, and reads values with `findall` — `_parse_lane` uses `.search`,
    # so applying it to whole-document text would validate one lane per FILE.
    #
    # ⚠️ CAPTURES THE WHOLE VALUE, not a leading `[A-Za-z]+` run. Capturing only the run
    # meant the validator and the extractor read DIFFERENT values off the same line:
    # `- **Lane:** lean/substrate` validated as `lean` and PASSED, while `_parse_lane`
    # emitted `lean/substrate` — unmappable, so the finding routed nowhere. Two mechanisms
    # disagreeing about one line is the defect the `re.I` note in `build_graph` records for
    # case; this was the same disagreement about the value grammar. The shape mirrors
    # `_parse_finding_field`, and the normalisation below mirrors `_parse_lane` exactly.
    _LANE_VALUE = re.compile(r'^\s*[-*]\s*\*\*Lane:?\*\*:?\s*(.+?)\s*$', re.M | re.I)

    details: list[Detail] = []
    bad = 0
    bad_value = 0
    bad_lane = 0
    checked = 0
    try:
        from build_graph import (_SEVERITY_DECL_MAP, _LANE_DECL_MAP,
                                 _RELEASE_SCHEMES as _RELEASE_SCHEME_NAMES)
        vocabulary = set(_SEVERITY_DECL_MAP)
        lane_vocabulary = set(_LANE_DECL_MAP) | {'unclassified'}
    except ImportError as exc:      # cannot-measure is not success
        return CheckResult(passed=False, details=[Detail(
            "import", False,
            f"build_graph declaration maps unavailable ({exc}) — the accepted "
            f"vocabulary is unknown, so this check cannot validate anything")])

    # ⚠️ A DIRECTORY NAME IS NOT A DATE, and treating it as one made the cutoff an
    # OPT-OUT. `date < _CUTOFF` is a string compare against `parent.name[:10]`, so a
    # review filed in a directory whose name does not begin with an ISO date silently
    # skipped every requirement below — the reviewer chose whether to be checked by
    # choosing a folder name. Unparseable provenance is now a FAILURE, not a skip:
    # the check cannot know whether such a document is in scope, and a check that
    # cannot know must not answer "fine". (D12 round-11 8.4, 2026-07-31.)
    _ISO_DATE = re.compile(r'^\d{4}-\d{2}-\d{2}$')
    bad_scope = 0
    for md in sorted(reviews_dir.glob("*/*.md")):
        date = md.parent.name[:10]
        if not _ISO_DATE.match(date):
            bad_scope += 1
            details.append(Detail(
                f"{md.relative_to(_H.PROJECT_ROOT)}:scope", False,
                f"review directory {md.parent.name!r} does not begin with an ISO date, so "
                f"whether it falls on/after the {_CUTOFF} cutoff is undecidable. This used "
                f"to skip the document silently, which made the cutoff opt-out: a reviewer "
                f"evaded every requirement below by naming the folder."))
            continue
        if date < _CUTOFF:
            continue
        text = md.read_text(encoding="utf-8", errors="replace")
        heads = list(_HEADING.finditer(text))
        if not heads:
            continue
        checked += 1
        # ⚠️ PER-FINDING, NOT PER-DOCUMENT COUNTS. This compared `len(severity lines)` to
        # `len(headings)` and passed whenever the totals reached parity — so one finding
        # carrying two `- **Severity:**` lines paid for a neighbour carrying none, and the
        # document read compliant while a finding's severity fell back to glyph inference.
        # Severity drives the blocking-closure bar, so that is exactly the finding whose
        # severity must not be inferable. Totals are not an association; the section is.
        missing = []
        for i, h in enumerate(heads):
            end = heads[i + 1].start() if i + 1 < len(heads) else len(text)
            section = text[h.start():end]
            if not _SEV_LINE.search(section):
                # `_HEADING` matches only up to the first non-space character, so
                # `h.group(0)` is `### 1` — useless for naming the finding. Take the
                # heading LINE: a failure that cannot say which finding is missing its
                # declaration sends the reader back to re-derive it by hand.
                missing.append(section.split("\n", 1)[0].strip()[:70])
        if missing:
            bad += 1
            details.append(Detail(
                str(md.relative_to(_H.PROJECT_ROOT)), False,
                f"{len(missing)} of {len(heads)} finding(s) declare no `- **Severity:**` "
                f"line in their own section: {missing}. From {_CUTOFF} every finding must "
                f"declare its severity explicitly: severity drives the blocking-closure "
                f"bar, and inferring it from a glyph lets it be changed without leaving a "
                f"trace."))
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

        unknown_lanes = sorted({v.strip().strip('`').lower()
                                for v in _LANE_VALUE.findall(text)
                                if v.strip().strip('`').lower() not in lane_vocabulary})
        if unknown_lanes:
            bad_lane += 1
            details.append(Detail(
                f"{md.relative_to(_H.PROJECT_ROOT)}:lane", False,
                f"declares lane value(s) `build_graph` cannot map: {unknown_lanes}. "
                f"Accepted: {sorted(lane_vocabulary)}. A lane that does not map routes "
                f"the finding nowhere — no worker, no gate set, no fan-out key — so it is "
                f"an unroutable finding, not a typo. `lane` is forward-only: OMITTING it "
                f"reads `unclassified` and is fine; declaring a token that means nothing "
                f"is not."))

    # ── A `Blocked-by:` that resolves to nothing (ADR-012 D10) ───────────────────────
    # ⚠️ THIS LEG REPLACES A RAISE. `_blocked_by_edges` used to raise on an unresolvable
    # entry, which propagated out of both edge-assembly sites and so out of
    # `build_graph_json()` — one hand-typed id in reviewer markdown would have taken down
    # `knowledge_graph.json`, the atlas, `graph_integrity`, gate extraction and the
    # dashboard together, including the checks that would diagnose it. The values come from
    # LLM reviewers typing ids by hand, the same population that produced the dangling
    # ledger records, so that first typo was a matter of time.
    #
    # Detection is unchanged in strength and bounded in blast radius. **Zero, not a
    # ratcheted baseline**: unlike the ledger's historical debt, this population starts
    # empty and every entry is new, so there is nothing to ratchet down from.
    bad_dep = 0
    try:
        from build_graph import blocked_by_unresolved, extract_review_finding_nodes
        unresolved = blocked_by_unresolved(extract_review_finding_nodes())
    except Exception as exc:
        bad_dep = 1
        details.append(Detail(
            "blocked_by_resolves", False, measured=False,
            message=f"could not evaluate `Blocked-by:` resolution ({exc}) — the guard did "
                    f"not run, so its silence is not evidence"))
    else:
        for fid, toks in sorted(unresolved.items()):
            bad_dep += 1
            details.append(Detail(
                f"{fid}:blocked_by", False,
                f"blocked_by {toks} resolves to nothing — not a minted finding, and not a "
                f"known release scheme with a value ({', '.join(_RELEASE_SCHEME_NAMES)}). "
                f"A token nothing can satisfy makes the finding read WAITING when it is "
                f"STUCK, and it reaches no worker either way."))
        if not unresolved:
            details.append(Detail(
                "blocked_by_resolves", True,
                "every declared `Blocked-by:` names a minted finding or a valued release "
                "scheme"))

    _ok = (bad == 0 and bad_value == 0 and bad_lane == 0 and bad_dep == 0
           and bad_scope == 0)
    details.insert(0, Detail(
        "summary", _ok,
        f"{checked} review document(s) dated >= {_CUTOFF} checked; {bad} with findings "
        f"that do not declare severity, {bad_value} declaring an unmappable severity "
        f"value, {bad_lane} declaring an unmappable lane, {bad_dep} unresolvable "
        f"`Blocked-by:` entr(ies) corpus-wide, {bad_scope} document(s) whose directory "
        f"name is not an ISO date so their scope is undecidable (earlier documents keep "
        f"glyph inference; `lane` is forward-only and its absence is not a failure)"))
    return CheckResult(passed=_ok, details=details)


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
            # `*-bundle-stage13/` — because most files there are `bundle_readiness.py`
            # aggregations that mint zero BY DESIGN — excluded the directory
            # `BUNDLE_DIRECTORY_SCHEMA.md:86` and `BUNDLE_LIFT_PROCEDURE.md:243` name as
            # THE canonical location for a Stage-13 review, hiding the findings-bearing
            # reviews among them, one of them declaring a BLOCKER (D12 round-10 8.2).
            #
            # ⚠️ The census that used to sit here ("107 of 138") is DELETED rather than
            # corrected. Re-measured at its own stated date and at three plausible
            # denominators, it reproduces at NONE — the directory went 131 → 152 → 173 →
            # 194 and never passed through 138. A number nobody can reproduce is worse
            # than no number, and the argument ("most of them are generated aggregations")
            # never needed one.
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


#: `- **Verify:** …` as the review-document contract writes it.
_VERIFY_LINE = re.compile(r'^[ \t]*[-*]\s*\*\*Verify:?\*\*:?[ \t]*(.*)$', re.M)
#: The whole remainder must be ONE backtick-delimited command and nothing else.
_VERIFY_ONE_COMMAND = re.compile(r'^`([^`]+)`$')


@register_check("review_verify_is_one_command",
                "Every `Verify:` line is a single runnable command and nothing else")
def check_review_verify_is_one_command() -> CheckResult:
    """CHECK: rule 4 of the review-document marker contract, which was enforced nowhere.

    Added 2026-08-15 (`2026-08-15-verify-contract-unenforced`). The contract has four
    rules. `validate_review_doc.py` delegates severity declaration and finding minting to
    registered checks, so rules 1–3 bind; rule 4 was stated in that validator's docstring
    and in `close_finding.py`'s, and checked by neither.

    ⚠️ **The consumer is literal.** `close_finding.py` reads the `Verify:` line, takes it
    as ONE command, and runs it under `shell=True`. Explanatory prose trailing the command
    is therefore not commentary — it is argv. A finding whose Verify line cannot run is a
    finding whose closure cannot be verified, and `close_finding` refuses a closure whose
    `--verify` differs from the declared command, so such a finding is STRANDED: it can be
    neither verified nor closed except by amending the document.

    ⚠️ **This pins a practice; it does not repair a live defect.** Measured 2026-08-15:
    129 `Verify:` lines corpus-wide, **0** violating. That is why the bar is a hard zero
    rather than a ratchet — there is no historical debt to ratchet down from, so any
    violation is new, and a ceiling above zero would only make room for one.
    """
    reviews_dir = _H.PAPERS_DIR / "AutomatedReviews"
    if not reviews_dir.is_dir():
        # Cannot-measure is not success (ADR-009 H1): the PASS stays, but it stops
        # counting as evidence toward the coverage floor.
        return CheckResult(passed=True, measured=False, details=[
            Detail("scope", True, "no review directory", warning=True, measured=False)])

    bad: list[tuple[str, str]] = []
    checked = 0
    for md in sorted(reviews_dir.glob("*/*.md")):
        text = md.read_text(encoding="utf-8", errors="replace")
        for m in _VERIFY_LINE.finditer(text):
            checked += 1
            rest = m.group(1).strip()
            if not _VERIFY_ONE_COMMAND.match(rest):
                bad.append((str(md.relative_to(_H.PROJECT_ROOT)), rest[:120]))

    details = [Detail(
        "summary", not bad and checked > 0,
        f"{checked} `Verify:` line(s) checked, {len(bad)} carrying anything other than a "
        f"single backticked command"
        + ("" if checked else
           " — NONE FOUND, so this check asserted nothing this run; the corpus had 129 "
           "on 2026-08-15, so zero means the walk or the pattern broke, not that the "
           "documents changed"))]
    for path, rest in bad[:10]:
        details.append(Detail(
            path, False,
            f"`Verify:` is not a single command: {rest!r}. `close_finding.py` runs this "
            f"line verbatim under a shell, so trailing prose is argv, not commentary — "
            f"the finding can then be neither verified nor closed. Put the explanation on "
            f"the following line as `*What it asserts:* …`."))
    # ⚠️ `checked > 0` is part of the verdict, not decoration. Every other leg here is a
    # zero-violation assertion, which an empty walk satisfies perfectly.
    return CheckResult(passed=not bad and checked > 0, details=details)


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
    #
    # ⚠️ The comment above described the hazard for weeks and the code did nothing
    # about it. `measured=False` is what closes it: the PASS stays (an absent
    # ledger is not a failure) but it stops counting as evidence toward the `--ci`
    # coverage floor, and `_memo` refuses to cache it. Found 2026-08-09 by WIDENING
    # `test_cannot_measure_baseline`'s keyword list to include "skipping" — the
    # scanner had been unable to see this site, so nothing contradicted the comment.
    ledger_path = _H.DOCS_DIR / "review_finding_supersessions.json"
    if not ledger_path.is_file():
        return CheckResult(passed=True, measured=False, details=[
            Detail("ledger", True, "no supersession ledger; skipping",
                   warning=True, measured=False)])
    try:
        led = json.loads(ledger_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        return CheckResult(passed=False, measured=False, details=[
            Detail("ledger", False, f"ledger unreadable ({exc}) — unverified, not passing",
                   measured=False)])

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

    # ── WHO accepted it (D12 rounds 8/9/10 finding 8.5, second half) ─────────────────
    # The rationale floor above enforces that a decision was WRITTEN. It says nothing
    # about who made it. For a blocking-severity finding — a critical or major that a
    # bundle will ship carrying — an unattributed decision is not a decision anyone can
    # be asked about later.
    #
    # ⚠️ A RATCHET, NOT A HARD GATE, and deliberately. Measured 2026-08-15: 31 records
    # are accepted at blocking severity (12 critical, 19 major) and NONE carries
    # `accepted_by`. Turning this red immediately would block every bundle on historical
    # debt. The ceiling may only fall.
    #
    # ⚠️ DO NOT CLEAR THIS BY BACK-FILLING `accepted_by` IN BULK. Stamping a name onto 31
    # decisions nobody re-made reproduces exactly the defect
    # `2026-08-15-textbook-exemption-rewards-absent-metadata` describes one layer over —
    # a field satisfied by paperwork rather than by the thing it attests. Each one comes
    # down by being re-decided or fixed.
    bad_owner: list[str] = []
    owner_measured = True
    try:
        from build_graph import extract_review_finding_nodes
        sev = {n["id"]: str((n.get("meta") or {}).get("severity", "")).lower()
               for n in extract_review_finding_nodes()}
    except Exception as exc:
        owner_measured = False
        details.append(Detail(
            "accepted_by", False, measured=False,
            message=f"could not load finding severities ({type(exc).__name__}: {exc}) — "
                    f"the attribution floor did NOT run, so its silence is not evidence"))
    else:
        last: dict[str, dict] = {}
        for e in led.get("supersessions", []):
            last[e.get("finding_id")] = e          # last-wins, as the reader
        for fid, e in last.items():
            if e.get("status") != "accepted":
                continue
            if sev.get(fid, "") not in _BLOCKING_SEVERITIES:
                continue
            if not str(e.get("accepted_by") or "").strip():
                bad_owner.append(fid)

    # ⚠️ The check fails only ABOVE the ceiling. Headroom — a ceiling left standing above
    # a corpus that has improved — is asserted by
    # `tests/test_d5_reviews.py::TestAcceptedByRatchet::test_the_ceiling_carries_no_headroom`
    # against the PRODUCTION ledger, matching `TestChainOfBackingResolves` in the same
    # file. It cannot live here: every fixture in that suite builds a small synthetic
    # ledger whose ids resolve to no severity, so a below-ceiling failure would fire on
    # every one of them and the ratchet would be measuring the fixtures.
    over = owner_measured and len(bad_owner) > ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING
    details.append(Detail(
        "accepted_by", not over,
        f"{len(bad_owner)} blocking-severity `accepted` record(s) carry no `accepted_by` "
        f"(ceiling {ACCEPTED_BLOCKING_UNATTRIBUTED_CEILING}, may only fall)"
        + (f" — ABOVE the ceiling: {sorted(bad_owner)[:5]}" if over else "")))

    return CheckResult(passed=not bad and not over,
                       measured=owner_measured, details=details)


# ── Chain-of-backing resolvability ────────────────────────────────────────────────────
#
# A `claims_review.json` sentence carries a chain of backing links tying a manuscript sentence
# to the substrate. A link of kind theorem/axiom/lemma names a Lean target, and nothing GATED on
# those targets existing — `chain_canonicalize.py --report` measured them and no check consumed
# the report.
#
# ⚠️ THIS CHECK OWNS NO RESOLVER. `chain_canonicalize.canonicalize_link` is the project's single
# resolver for chain links; this check builds its `GraphIndex`, iterates its `_iter_links`, and
# counts what it returns. An earlier draft of this check carried its own normalizer and
# membership test — a second resolver beside a working one, which is the
# hand-maintained-list-parallel-to-a-registry failure the suite exists to catch. It also
# disagreed: 156 unresolvable against the real resolver's 121, because the local version could
# not resolve module refs, short names or constant aliases. **Do not reintroduce a local
# resolver. If resolution is wrong, fix `chain_canonicalize` and both consumers improve.**
#
# ⚠️ THE CEILING IS A KNOWN UPPER BOUND. `canonicalize_link` skips ambiguous short names
# (`zero` → 12 candidates, `A` → 9, `F` → 8) and counts them `theorem-absent`, so some fraction
# of the population is a name-resolution artifact rather than a missing theorem. The 2026-08-01
# audit records this caveat against the same figure. The ratchet is therefore a
# **do-not-grow** guard, not a defect count: shrinking it means either fixing a citation or
# disambiguating a name, and both are improvements.

#: Zero-headroom ratchet: unresolvable theorem/axiom/lemma chain links, measured 2026-08-07
#: with `canonicalize_link`. Matches `chain_canonicalize.py --report`'s independent figure.
#: May only be LOWERED.
#: 2026-08-11: 121 -> 109. I1's Stage-10 re-review replaced its `claims_review.json`,
#: and the rewritten records resolve twelve links the previous pass left dangling.
#: Repayment, not a predicate change.
UNRESOLVED_CHAIN_LINK_CEILING = 109

_LEAN_LINK_KINDS = frozenset({"theorem", "axiom", "lemma"})


@register_check("chain_backing_targets_resolve",
                "Every Lean target named in a claims-review chain of backing exists")
def check_chain_backing_targets_resolve() -> CheckResult:
    """Gate the resolver that `chain_canonicalize --report` already runs but never blocks on.

    Fails when the unresolvable count exceeds the ratchet — i.e. when a review round ADDS a
    dangling reference. The standing population is reported by paper every run.
    """
    try:
        import chain_canonicalize as _cc
    except ImportError as exc:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "resolver", False,
            f"SKIPPED — chain_canonicalize unimportable ({exc}); the chain backing is "
            f"UNVERIFIED, not passing")])

    try:
        idx = _cc.GraphIndex()
    except Exception as exc:  # graph build is the check's only heavy dependency
        return CheckResult(passed=False, measured=False, details=[Detail(
            "graph", False,
            f"SKIPPED — could not build the graph index ({exc}); UNVERIFIED, not passing")])

    total = 0
    unresolvable: dict[str, int] = {}
    by_paper: dict[str, int] = {}
    for paper, _sid, kind, target in _cc._iter_links():
        if kind not in _LEAN_LINK_KINDS:
            continue
        total += 1
        if _cc.canonicalize_link(kind, target, idx).status == _cc.UNRESOLVABLE:
            unresolvable[target] = unresolvable.get(target, 0) + 1
            by_paper[paper] = by_paper.get(paper, 0) + 1

    # Guard the seam: a scan that matched nothing passes vacuously.
    if total == 0:
        return CheckResult(passed=False, details=[Detail(
            "population", False,
            "no theorem/axiom/lemma chain links found across papers/**/claims_review.json — "
            "the scan reached nothing, which is a path or iterator defect, not a clean corpus")])

    details = [Detail("population", True,
                      f"{total} Lean chain-of-backing link(s), resolved by "
                      f"chain_canonicalize.canonicalize_link")]
    n_bad = sum(unresolvable.values())
    within = n_bad <= UNRESOLVED_CHAIN_LINK_CEILING
    worst = sorted(by_paper.items(), key=lambda kv: -kv[1])[:8]
    details.append(Detail(
        "unresolvable", within,
        f"{n_bad} link(s) unresolvable, across {len(unresolvable)} distinct target(s) in "
        f"{len(by_paper)} paper(s) (ceiling {UNRESOLVED_CHAIN_LINK_CEILING}); worst: "
        + ", ".join(f"{p}={c}" for p, c in worst)))
    if not within:
        for tgt, cnt in sorted(unresolvable.items(), key=lambda kv: -kv[1])[:20]:
            details.append(Detail("target", False, f"{cnt}x unresolvable: {tgt}"))
    elif n_bad < UNRESOLVED_CHAIN_LINK_CEILING:
        details.append(Detail(
            "ratchet", True,
            f"population fell to {n_bad} — lower UNRESOLVED_CHAIN_LINK_CEILING to match, "
            f"or the ratchet regains headroom and stops being able to fire"))
    return CheckResult(passed=within, details=details)

#: Ledger records whose `finding_id` matches no minted node. **A RATCHET: may only shrink.**
#:
#: Baseline re-measured 2026-08-01 (D11 Stage-13 round-13 finding 2220:4.5). It was pinned
#: at 67 against a population of 66, i.e. it carried one slot of headroom in the one guard
#: whose whole purpose is catching a NEWLY filed closure that names nothing. Three such
#: records were filed while it was effectively inert.
#:
#: Its justifying comment was also wrong about the population it described. Measured: of the
#: 66, 53 used annotated IDs and 13 did not — the comment claimed all 67 were annotated. 67
#: was the count of ledger ids MENTIONING stage9/stage10, a different population that
#: happened to be one larger.
#:
#: 2026-08-12: 66 -> 59. Seven records whose keys carried suffixes no minted id has
#: (`:3.1-residual`, `:5.1-5.3`) were re-keyed; two more were SKIPPED because their
#: corrected key already carried a record and `_load_supersession_ledger` is last-wins, so
#: re-keying onto an occupied id would have made one of the pair silently do nothing. 59 is
#: the skip-rule number; 57 is the blind one.
LEDGER_DANGLING_BASELINE = 59


@register_check("ledger_ids_resolve",
                "Supersession records name findings that exist (ratcheted)")
def check_ledger_ids_resolve() -> CheckResult:
    """CHECK: a closure that names no finding closes nothing, silently.

    Findings raised in rounds whose review document was never written to disk were filed
    under an EARLIER review's IDs. That both collides with live findings (a still-open
    finding rendered `fixed`) and mints dangling IDs naming no node. Neither is detectable
    from the ledger alone.

    ⚠️ PROMOTED 2026-08-12 out of `check_graph_integrity`, where it lived as a `Detail` leg,
    and the leg was DELETED in the same commit. It is not new: an earlier draft of ADR-012
    proposed BUILDING it at a ceiling of 247 — the aggregate over three id schemes — which
    would have been a second mechanism beside a working one AND weaker, because one ratchet
    over 190 permanently-inert legacy records plus the live ones lets deleting a legacy
    record silently buy headroom for a real dangler.

    ⚠️ A CLAIM MADE HERE WAS WRONG, retracted 2026-08-01. A reviewer wrote that this guard
    "does not run" and filed it as a twelfth defect, on the strength of a mutation test that
    planted a dangling record and saw no `ledger_ids_resolve` detail. The test was invoking
    `check_bundle_registry_consistency` — a different check entirely, so of course it emitted
    nothing. Diagnosing by running the wrong function is the same class of mistake as
    measuring the wrong quantity.

    ⚠️ Scoped to the `review:<date-dir>:<name>:<section>` scheme, which is the one
    `extract_review_finding_nodes` mints nodes for. Legacy Stage-9/10 records use an
    unrelated `bundle-stage10:...` scheme and were never graph nodes, so flagging them would
    be noise, not signal.

    ⚠️ An ABSENT ledger FAILS here, unlike in `accepted_findings_carry_rationale`, and the
    asymmetry is deliberate rather than an inconsistency. That check asks whether the
    acceptances present are justified — no ledger means no acceptances, which is genuinely
    fine. This one asks whether the closure channel still points at real findings, and a
    vanished channel is at least as severe as a corrupt one. A malformed ledger was already
    red while a missing one printed ✓, so the single guard whose subject had disappeared was
    the one reporting success.
    """
    ledger_path = _H.DOCS_DIR / "review_finding_supersessions.json"
    if not ledger_path.is_file():
        return CheckResult(passed=False, measured=False, details=[
            Detail("ledger", False, measured=False,
                   message=f"no supersession ledger at {ledger_path} — UNVERIFIED, not "
                           f"passing. It is the ONLY channel that can close a finding, so "
                           f"its absence means no closure can be checked, not that every "
                           f"closure is sound")])
    try:
        entries = json.loads(ledger_path.read_text(encoding="utf-8")).get(
            "supersessions", [])
    except (OSError, json.JSONDecodeError) as exc:
        return CheckResult(passed=False, measured=False, details=[Detail(
            "ledger", False, measured=False,
            message=f"unreadable supersession ledger ({exc}) — UNVERIFIED, not passing")])

    try:
        # ⚠️ From the extractor, NOT `build_graph_json()`. The leg's original `_known` came
        # from a full graph build ~70 lines above it in its old host; re-running that here
        # would add a whole graph build to every validate.py run. This is 0.25 s.
        from build_graph import extract_review_finding_nodes
        known = {n["id"] for n in extract_review_finding_nodes()}
    except Exception as exc:
        # FAIL, not warn. This handler once returned passed=True, so ANY exception made the
        # guard silently absent — exactly the state a mutation test found it in. A guard that
        # cannot run must say so loudly; its silence is not evidence.
        return CheckResult(passed=False, measured=False, details=[Detail(
            "ledger_ids_resolve", False, measured=False,
            message=f"ledger integrity scan FAILED TO RUN ({type(exc).__name__}: {exc}) — "
                    f"the dangling-closure guard did not execute")])

    dangling = sorted({e["finding_id"] for e in entries
                       if e.get("finding_id", "").startswith("review:")
                       and e["finding_id"] not in known})
    # ⚠️ A record with NO `finding_id` at all closes nothing and names nothing, so the
    # `.get(..., "")` above skips it — invisible to the one guard whose subject is records
    # that close nothing. Count it separately: it is a different defect from a wrong key,
    # and zero is the only acceptable number.
    keyless = [i for i, e in enumerate(entries) if not str(e.get("finding_id") or "").strip()]
    details = []
    if keyless:
        details.append(Detail(
            "keyless", False,
            f"{len(keyless)} supersession record(s) carry no `finding_id` (index "
            f"{', '.join(str(i) for i in keyless[:4])}). Such a record closes nothing and "
            f"is invisible to the dangling scan, which keys on the field it lacks."))
    if len(dangling) > LEDGER_DANGLING_BASELINE:
        details.append(Detail(
            "ratchet", False,
            f"{len(dangling)} supersession finding_id(s) name no ReviewFinding node, above "
            f"the pinned baseline of {LEDGER_DANGLING_BASELINE} — a closure filed against a "
            f"nonexistent finding closes nothing: {', '.join(dangling[:4])}. Re-key it or "
            f"remove it; never raise the baseline."))
        return CheckResult(passed=False, details=details)
    details.append(Detail(
        "ratchet", True,
        f"{len(dangling)} of {len(entries)} supersession record(s) name no live finding "
        f"(pre-existing annotated-ID debt, baseline {LEDGER_DANGLING_BASELINE}); no growth",
        warning=bool(dangling)))
    return CheckResult(passed=not keyless, details=details)
