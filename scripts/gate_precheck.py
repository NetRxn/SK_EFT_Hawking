#!/usr/bin/env python3
"""L4 — cheap deterministic prechecks BEFORE an expensive LLM reviewer stage,
so Opus tokens/wall-time never burn on stale/failing state (spec 12 L4).

  gate_precheck.py s9   -> figures fresh + structural (before figure-reviewer)
  gate_precheck.py s10  -> paper_provenance + tables_fresh + placeholder/citation (before claims-reviewer)
  gate_precheck.py s13  -> validate.py green over Stages 1-12, INCLUDING the LaTeX
                           compile (before adversarial)
  gate_precheck.py submission
                        -> the Paper Submission Gate: everything s13 runs, PLUS the
                           six --strict legs. Run before arXiv/journal submission.

Exit 0 = prereqs pass (safe to dispatch the reviewer); nonzero = do NOT dispatch.
Stdlib only; delegates to the existing checks.
"""
from __future__ import annotations
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
STAGE_CHECKS = {
    # s9 (before the figure-reviewer): the READ-ONLY `viz_consistency` check (review C2 + the
    # plan's sanctioned fallback). We deliberately do NOT call `review_figures.py --check`
    # here: although it does not regenerate PNGs, it REWRITES the TRACKED
    # figures/structural_checks.json with a fresh timestamp on every run — so a precheck
    # (which must be side-effect-free + repeatable, runnable on every gate) would dirty the
    # working tree each time. `validate.py --check viz_consistency` validates the figure/viz
    # layer without any write.
    "s9":  ["viz_consistency"],
    "s10": ["paper_provenance", "tables_fresh", "placeholder_not_cited",
            "citation_primary_sources_present"],
    "s13": ["__full__"],  # validate.py full green over 1-12 (with --force-latex; see below)

    # ── The Paper Submission Gate (added 2026-08-05) ──────────────────────────────
    # `WAVE_EXECUTION_PIPELINE.md` Invariant #12 calls `--strict` *"mandatory at the
    # Paper Submission Gate"*, and :72 spells the gate as a `--strict` invocation — but
    # NOTHING called it. Six checks carry a strict-only leg (`parameter_provenance`,
    # `provenance_doi_in_registry`, `bibitem_title_primary_source`,
    # `theorem_name_embedded_citations`, `axiom_closure_allowlist`,
    # `bundle_source_freshness`), so an invariant declared mandatory ran nowhere.
    #
    # WHY ITS OWN STAGE, not folded into s13. The strict legs gate SUBMISSION, not wave
    # close, and the distinction is real: `bundle_source_freshness` WARNs whenever a
    # source paper moved after the last lift, which is the NORMAL state of an
    # in-progress bundle. Promoting that to a hard fail at every wave close would make
    # the gate fire on correct work — and a gate that fires on correct work gets
    # switched off. ADR-009 §Deferred item 6 reached the same split by measurement:
    # `--strict` is a correctly-designed submission-time mode, and what was missing was
    # a caller, not a change of default.
    "submission": ["__strict__"],
}


def _run(args: list[str]) -> int:
    return subprocess.run(["uv", "run", "python"] + args, cwd=str(ROOT)).returncode


def main(argv=None) -> int:
    argv = argv or sys.argv[1:]
    if not argv or argv[0] not in STAGE_CHECKS:
        print(f"usage: gate_precheck.py {{{'|'.join(STAGE_CHECKS)}}}"); return 2
    stage = argv[0]
    rc = 0
    # --no-archive: a precheck runs repeatedly (before every reviewer dispatch), so it must be
    # side-effect-free — without this validate.py archives a timestamped report under
    # docs/validation/reports/ on EVERY run. The canonical archived validate run is a separate
    # concern (the official wave-gate validate / /sync), not this cheap pre-dispatch guard.
    for chk in STAGE_CHECKS[stage]:
        if chk == "__full__":
            # --force-latex is NOT optional here (added 2026-08-05). Without it
            # `paper_latex_compiles` returns PASS with detail "SKIPPED (slow)", so
            # "full green over Stages 1-12" was achievable with a draft that does not
            # compile — and D3 does not, with 2 fatal errors, today. The "slow" premise
            # is also stale: measured 16.8s for all bundle drafts, against an
            # adversarial-review dispatch this gate exists to protect.
            rc |= _run(["scripts/validate.py", "--force-latex", "--no-archive"])
        elif chk == "__strict__":
            rc |= _run(["scripts/validate.py", "--strict", "--force-latex",
                        "--no-archive"])
        else:
            # A real validate.py check (incl. s9's read-only viz_consistency). Post-Task-2.5 an
            # unknown name returns rc2 -> propagates as FAIL here (never a silent pass). NOTE: we
            # do NOT shell to `review_figures.py --check` for s9 — it rewrites the tracked
            # figures/structural_checks.json (timestamp) every run, which a repeatable precheck
            # must not do (review C2); viz_consistency validates the figure/viz layer read-only.
            rc |= _run(["scripts/validate.py", "--check", chk, "--no-archive"])
    print(f"gate_precheck {stage}: {'PASS' if rc == 0 else 'FAIL — do not dispatch the reviewer'}")
    return rc


if __name__ == "__main__":
    sys.exit(main())
