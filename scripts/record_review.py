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
import sys
from datetime import datetime, timezone
from pathlib import Path

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

    if doc is not None and not (REPO / doc).exists():
        return False, (f"--doc {doc} does not exist. A verdict citing a review document "
                       f"that is not on disk records nothing a later reader can check.")

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
    md[f"stage{stage}_status"] = verdict
    md[f"last_stage{stage}_review"] = now
    if stage == 13:
        md["stage13_review_kind"] = kind
        if doc is not None:
            md["stage13_review_doc"] = doc

    # ensure_ascii=False: these blobs carry `§`/`—` in their apex `claims` strings and
    # the default rewrites every one as `\uXXXX` (TODO-D25).
    mp.write_text(json.dumps(md, indent=2, ensure_ascii=False) + "\n")
    suffix = f", kind={kind}" if stage == 13 else ""
    return True, f"{bundle}: stage{stage}_status = {verdict}{suffix} (recorded {now})"


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
