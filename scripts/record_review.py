#!/usr/bin/env python3
"""Record a reviewer-stage verdict on a bundle — the writer transition 2 never had.

Why this exists
---------------
`END_TO_END_MAP.md` §8 documents the bundle promotion path as a five-transition state
machine, and one transition had no actor:

    | 2 | `"pending"` -> `"green"` on any of the three stages | ⛔ nothing |

No code path in the repository wrote `"green"` to any `stage*_status`. The only writers
were creation (which sets `"pending"`) and append (which demotes `green` -> `"pending"`).
**Every green in the corpus was therefore a hand edit**, and the reviewer agents that
would earn one had no write path to the field they gate on. The transition was never
specified, so it was never built.

That is not a cosmetic gap. It is why bundle status could not be read as evidence of
review, and it is upstream of two measured failures: five bundles holding a Stage-13
verdict with a prerequisite stage never run, and the portfolio's only GREEN bundle (D9)
having no `claims_review.json` at all.

What this refuses to do
-----------------------
The sanctioned path enforces at WRITE time what `bundle_reviewer_stage_ordering`
enforces at VALIDATE time. Both exist deliberately: this one gives the author immediate
feedback at the point of action, the check catches hand edits, which remain possible and
are not forbidden — only unsupervised.

  * **Stage 13 green requires Stages 9 and 10 green** (`BUNDLE_LIFT_PROCEDURE.md:9`).
  * **A Stage-13 verdict requires `--kind`.** A targeted attribution sweep and a full
    fresh-context adversarial pass are not the same evidence, and until now the metadata
    could not tell them apart: any document referenced by `stage13_review_doc` satisfied
    the readiness formula's unreviewed-guard identically. That is how a bundle whose
    Stage 10 never ran reached GREEN.
  * **`--doc` must exist on disk.** A verdict citing a review document that is not there
    is the paper-side analogue of a chain-of-backing link naming a theorem that does not
    exist.

Usage
-----
    uv run python scripts/record_review.py --bundle D6 --stage 9  --verdict green \\
        --doc papers/D6/figures/figure_review_report.json
    uv run python scripts/record_review.py --bundle D6 --stage 13 --verdict green \\
        --kind full-adversarial \\
        --doc papers/AutomatedReviews/2026-08-08-bundle-stage13/D6.md

Exit code is non-zero if the write was refused.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from bundle_json import write_bundle_json  # noqa: E402

REPO = Path(__file__).resolve().parent.parent
PAPERS = REPO / "papers"

#: Verdicts a reviewer may record. Deliberately NOT the full on-disk status set:
#: `pending`, `pending-redo`, `skeleton` and `not_started` describe a stage that has
#: not produced a verdict, and are set by the lifecycle scripts, not by a reviewer.
VERDICTS = ("green", "yellow", "red")

#: What KIND of Stage-13 evidence a document is. The distinction is load-bearing:
#: `bundle_readiness.py`'s `review_recorded` treats any referenced document as a
#: review, so without this field a 16-anchor attribution sweep counts exactly as a
#: full adversarial pass (audit 2026-08-01, PROMOTION-PATH-AND-SIGNAL.md).
KINDS = ("full-adversarial", "attribution-sweep", "section-scoped", "figure-only")

#: Only a full fresh-context pass earns a Stage-13 green.
KINDS_SUFFICIENT_FOR_GREEN = frozenset({"full-adversarial"})


def _meta_path(bundle: str) -> Path:
    return PAPERS / bundle / "bundle_metadata.json"


#: `review_date: <ISO8601>` in a review document's own front matter — the reviewer's
#: statement of WHEN it reviewed, which is the fact `last_stage{N}_review` is asking for.
_REVIEW_DATE_RE = re.compile(
    r"^review_date:\s*(\d{4}-\d{2}-\d{2}(?:[T ][0-9:]{5,8}Z?)?)\s*$", re.MULTILINE)


def _declared_review_date(path: Path) -> str | None:
    """The review date a document declares about itself, or `None` if it declares none."""
    try:
        head = path.read_text(errors="replace")[:1200]
    except OSError:
        return None
    m = _REVIEW_DATE_RE.search(head)
    return m.group(1) if m else None


def record(bundle: str, stage: int, verdict: str, doc: str | None,
           kind: str | None) -> tuple[bool, str]:
    """Returns `(written, message)`. Refuses rather than raising."""
    mp = _meta_path(bundle)
    if not mp.is_file():
        return False, f"no bundle_metadata.json for {bundle} at {mp}"
    try:
        md = json.loads(mp.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        return False, f"{mp} is unreadable ({exc})"

    # ⚠️ TWO guards, and the second is the one that was missing. `--doc` is optional
    # at the parser, so `doc is None` skipped the existence check ENTIRELY: a
    # Stage-13 GREEN could be recorded citing NO document at all. Nothing
    # downstream caught it — `bundle_readiness.py` derives `review_recorded` from
    # the DATE (always written) and the KIND (always written), and no validate.py
    # check reads `stage13_review_doc`, so the bundle rendered GREEN.
    if doc is not None and not (REPO / doc).exists():
        return False, (f"--doc {doc} does not exist. A verdict citing a review document "
                       f"that is not on disk records nothing a later reader can check.")

    if stage == 13 and doc is None:
        return False, ("--doc is REQUIRED for --stage 13. A Stage-13 verdict is a claim "
                       "that an adversarial review happened; without a document on disk "
                       "it is unfalsifiable, and the green it produces is indistinguishable "
                       "from one backed by a real review.")

    if stage == 13:
        if kind is None:
            return False, ("--kind is required for a Stage-13 verdict "
                           f"({', '.join(KINDS)}). Without it the metadata cannot tell a "
                           f"targeted sweep from a full adversarial pass, which is how a "
                           f"bundle whose Stage 10 never ran reached GREEN.")
        if verdict == "green" and kind not in KINDS_SUFFICIENT_FOR_GREEN:
            return False, (f"kind={kind!r} does not earn a Stage-13 green; only "
                           f"{'/'.join(sorted(KINDS_SUFFICIENT_FOR_GREEN))} does. "
                           f"Record the verdict this evidence supports, or run the full pass.")
        if verdict == "green":
            missing = [f"stage{n}={md.get(f'stage{n}_status') or 'absent'}"
                       for n in (9, 10)
                       if str(md.get(f"stage{n}_status") or "").strip().lower() != "green"]
            if missing:
                return False, (
                    f"refusing: Stage 13 may not be recorded green while "
                    f"{', '.join(missing)} (BUNDLE_LIFT_PROCEDURE.md:9). Run the "
                    f"prerequisite stage — do not edit stage13_status.")

    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    # ⚠️ THE REVIEW'S DATE, NOT THE RECORDING'S (2026-08-15). `last_stage{N}_review` answers
    # "when was this reviewed", and stamping `now` answered "when was this typed" — so a
    # review recorded late reported as fresh, and the drift runs ONE WAY only, always toward
    # looking newer. Measured: L1's 2026-08-14 full-adversarial pass recorded as 2026-08-15.
    # That matters because the staleness rule (WAVE_EXECUTION_PIPELINE Stage 13) compares
    # edit dates against this field, so an inflated value suppresses a re-review obligation
    # the corpus has actually earned.
    #
    # The document declares `review_date` in its own front matter; prefer it, and fall back
    # to `now` only when it declares nothing — recording the recording is still better than
    # recording nothing, provided it is not passed off as the review's own date.
    reviewed_at, date_src = now, "recording time (document declared no review_date)"
    if doc is not None:
        declared = _declared_review_date(REPO / doc)
        if declared:
            reviewed_at, date_src = declared, f"declared by {doc}"
    md[f"stage{stage}_status"] = verdict
    md[f"last_stage{stage}_review"] = reviewed_at
    md[f"last_stage{stage}_review_recorded_at"] = now
    if stage == 13:
        md["stage13_review_kind"] = kind
        # UNCONDITIONAL write. This was guarded by `if doc is not None`, so a
        # Stage-13 write without `--doc` left the PREVIOUS document path in place
        # while flipping `stage13_review_kind` — the metadata then asserted that an
        # old targeted sweep WAS the full adversarial pass, the exact conflation
        # `KINDS` exists to prevent. `doc` is now required above, so this always
        # overwrites with the document this verdict actually cites.
        md["stage13_review_doc"] = doc

    # ensure_ascii=False: these blobs carry `§`/`—` in their apex `claims` strings and
    # the default rewrites every one as `\uXXXX` (TODO-D25).
    write_bundle_json(mp, md)
    suffix = f", kind={kind}" if stage == 13 else ""
    return True, (f"{bundle}: stage{stage}_status = {verdict}{suffix} — reviewed "
                  f"{reviewed_at} ({date_src}); recorded {now}")


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bundle", required=True)
    ap.add_argument("--stage", required=True, type=int, choices=(9, 10, 13))
    ap.add_argument("--verdict", required=True, choices=VERDICTS)
    ap.add_argument("--doc", help="path (repo-relative) to the review artifact")
    ap.add_argument("--kind", choices=KINDS,
                    help="Stage-13 evidence kind; required when --stage 13")
    args = ap.parse_args(argv)

    ok, msg = record(args.bundle, args.stage, args.verdict, args.doc, args.kind)
    print(("✓ " if ok else "✗ REFUSED — ") + msg)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
