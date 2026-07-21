#!/usr/bin/env python3
"""Codex dossier pipeline — keep GPT-provider output OUT of the orchestrator's context.

The point of running a second provider is that its reasoning happens in *its* context, not
ours. A raw `codex exec` transcript is 1-2 MB; reading one would overflow the orchestrator and
destroy the benefit. This script is the seam: it extracts the run's **final deliverable** plus
its run metadata mechanically, so the orchestrator reads ~30 KB instead of ~2 MB and never
touches the transcript.

Three ops:

  harvest <raw.md> --slug <name> [--phase Phase5qH] [--question "..."]
      Extract metadata + final deliverable -> docs/dev-loops/<phase>/codex-dossiers/codex_<slug>.md
      and upsert its row in CODEX_INDEX.md. Idempotent.

  index [--phase Phase5qH]
      Rebuild CODEX_INDEX.md from the dossiers on disk (preserves the human-authored
      VERDICT / FINDINGS FOR DISPATCH / PROMOTED fields — those are the orchestrator's).

  check [--phase Phase5qH] [--scratchpad DIR]
      Warn about (a) dossiers over the read budget, (b) raw transcripts sitting UNHARVESTED
      in an ephemeral scratchpad — the failure that lost 9 dossiers before 2026-07-21.

Protocol (why the layers exist):
  raw transcript (ephemeral, scratchpad)  -- never read by the orchestrator
    -> codex_<slug>.md      (durable, ~30 KB)      -- the orchestrator reads THIS
    -> CODEX_INDEX.md       (the codex notebook)   -- one row per run + dispatch-ready findings
    -> canonical LAB_NOTEBOOK / INDEX              -- ONLY what the orchestrator promotes
"""

from __future__ import annotations

import argparse
import datetime
import pathlib
import re
import sys

# A dossier over this is a smell: the deliverable should be a report, not a transcript.
DOSSIER_BUDGET_BYTES = 120_000
REPO = pathlib.Path(__file__).resolve().parent.parent
TURN = re.compile(r"^(?:codex|user|thinking|exec|tokens used)\s*$", re.M)


def dossier_dir(phase: str) -> pathlib.Path:
    return REPO / "docs" / "dev-loops" / phase / "codex-dossiers"


def split_transcript(raw: str) -> tuple[str, str]:
    """(run metadata, final deliverable). Never returns the whole transcript.

    Codex CLI marks turns with bare lines (`codex`, `user`, `exec`, `thinking`) and closes with
    a `tokens used` footer. The deliverable is the text after the LAST bare `codex` marker, up
    to that footer. Falls back to the tail if the markers are absent (format drift).
    """
    parts = raw.split("--------", 2)
    meta = parts[1].strip() if len(parts) >= 2 else "(run metadata not parsed)"

    marks = [(m.start(), m.end(), m.group().strip()) for m in TURN.finditer(raw)]
    codex_marks = [m for m in marks if m[2] == "codex"]
    if not codex_marks:
        return meta, raw[-60_000:].strip()

    start = codex_marks[-1][1]
    footer = [m for m in marks if m[2] == "tokens used" and m[0] > start]
    end = footer[0][0] if footer else len(raw)
    return meta, raw[start:end].strip()


def harvest(raw_path: pathlib.Path, slug: str, phase: str, question: str | None) -> pathlib.Path:
    raw = raw_path.read_text(errors="replace")
    meta, deliverable = split_transcript(raw)
    out_dir = dossier_dir(phase)
    out_dir.mkdir(parents=True, exist_ok=True)
    out = out_dir / f"codex_{slug}.md"
    today = datetime.date.today().isoformat()

    out.write_text(
        f"# codex_{slug}\n\n"
        f"> **Codex dossier — the run's FINAL DELIVERABLE only.** Harvested {today} by "
        f"`scripts/codex_dossier.py`.\n"
        f"> The raw transcript ({len(raw):,} bytes) is ephemeral and is deliberately NOT in the "
        f"repo: reading it\n"
        f"> would overflow the orchestrator and defeat the point of using a second provider.\n"
        f"> Source: `{raw_path.name}`.\n\n"
        f"**Question asked:** {question or '(record it in CODEX_INDEX.md)'}\n\n"
        f"## Run metadata\n\n```\n{meta}\n```\n\n"
        f"## Deliverable\n\n{deliverable}\n"
    )
    print(f"harvested {slug}: {len(raw):>10,} raw -> {out.stat().st_size:>8,} dossier  ({out})")
    if out.stat().st_size > DOSSIER_BUDGET_BYTES:
        print(f"  ⚠ dossier > {DOSSIER_BUDGET_BYTES // 1000} KB — the extraction may have caught "
              f"transcript, not just the deliverable. Inspect the turn markers.")
    return out


INDEX_HEADER = """# Codex dossier index — the codex-specific lab notebook

> **This is the codex layer, not the canonical notebook.** Codex runs land here first. The
> orchestrator decides what gets **promoted** into `LAB_NOTEBOOK.md` / the canonical
> `LAB_NOTEBOOK_INDEX.md` — nothing flows automatically. Raw transcripts are never read or
> committed; `scripts/codex_dossier.py harvest` extracts the deliverable mechanically.
>
> **Per run, the orchestrator fills in three fields by hand** (the script never overwrites them):
> - **VERDICT** — one line: what the run concluded, and whether it was lead-verified.
> - **FINDINGS FOR DISPATCH** — paste-ready facts for worker briefs (exact identifiers, file:line,
>   traced dead ends). This is the reason the dossier exists: it should shorten the next brief.
> - **PROMOTED** — `no`, or where it went (SETTLED_FORKS / KERNEL_NOGO_REGISTRY / notebook FRONTIER).
>
> ⚠ **A codex claim is UNVERIFIED until the lead checks it in the Lean.** Dossiers are advisory;
> they have been wrong (see the `codex_212_collarpair_design` route-defect note). Mark verified
> claims explicitly before they enter a worker brief.

| date | dossier | verdict | promoted |
|---|---|---|---|
"""


def rebuild_index(phase: str) -> pathlib.Path:
    d = dossier_dir(phase)
    idx = d / "CODEX_INDEX.md"
    existing = idx.read_text() if idx.exists() else ""
    # Preserve any hand-authored per-run block (everything after the table).
    tail = existing.split("<!-- PER-RUN NOTES -->", 1)[1] if "<!-- PER-RUN NOTES -->" in existing else ""

    rows = []
    for f in sorted(d.glob("codex_*.md")):
        if f.name == "CODEX_INDEX.md":
            continue
        head = f.read_text(errors="replace")[:2000]
        m = re.search(r"Harvested (\d{4}-\d{2}-\d{2})", head)
        date = m.group(1) if m else "?"
        prior = re.search(rf"\|\s*{re.escape(f.stem)}\s*\|([^|]*)\|([^|]*)\|", existing)
        verdict = prior.group(1).strip() if prior else "_(orchestrator: fill in)_"
        promoted = prior.group(2).strip() if prior else "no"
        rows.append(f"| {date} | [`{f.stem}`]({f.name}) | {verdict} | {promoted} |")

    idx.write_text(INDEX_HEADER + "\n".join(rows) + "\n\n<!-- PER-RUN NOTES -->" + (tail or "\n"))
    print(f"index: {len(rows)} dossiers -> {idx}")
    return idx


def check(phase: str, scratchpad: str | None) -> int:
    warns = 0
    d = dossier_dir(phase)
    for f in sorted(d.glob("codex_*.md")):
        if f.name != "CODEX_INDEX.md" and f.stat().st_size > DOSSIER_BUDGET_BYTES:
            print(f"  ⚠ {f.name} is {f.stat().st_size // 1000} KB "
                  f"(> {DOSSIER_BUDGET_BYTES // 1000} KB) — likely transcript, not deliverable.")
            warns += 1
    if scratchpad:
        sp = pathlib.Path(scratchpad)
        harvested = {f.stem for f in d.glob("codex_*.md")}
        for raw in sorted(sp.glob("codex_*.md")):
            if raw.stem not in harvested:
                print(f"  ⚠ UNHARVESTED: {raw.name} ({raw.stat().st_size // 1000} KB) sits in an "
                      f"EPHEMERAL scratchpad and is not in {d.name}/ — harvest it or it is lost.")
                warns += 1
    print("[codex check] clean" if not warns else f"[codex check] {warns} warning(s)")
    return warns


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="op", required=True)
    ap.add_argument("--phase", default="Phase5qH")

    h = sub.add_parser("harvest"); h.add_argument("raw"); h.add_argument("--slug", required=True)
    h.add_argument("--question", default=None); h.add_argument("--phase", default="Phase5qH")
    i = sub.add_parser("index"); i.add_argument("--phase", default="Phase5qH")
    c = sub.add_parser("check"); c.add_argument("--phase", default="Phase5qH")
    c.add_argument("--scratchpad", default=None)

    a = ap.parse_args()
    if a.op == "harvest":
        harvest(pathlib.Path(a.raw), a.slug, a.phase, a.question); rebuild_index(a.phase); return 0
    if a.op == "index":
        rebuild_index(a.phase); return 0
    return 1 if check(a.phase, a.scratchpad) else 0


if __name__ == "__main__":
    sys.exit(main())
