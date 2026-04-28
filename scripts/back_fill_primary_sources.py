#!/usr/bin/env python3
"""Cache a primary-source artifact for every external bibkey.

For each (bibkey, phase) pair this script ensures a file exists at:

    Lit-Search/<phase>/primary-sources/<bibkey>.{pdf,abstract.txt,json}

Sources walked in order (best-tier-wins):
    1. arXiv PDF                 (when arxiv id is set)
    2. arXiv abstract (Atom API) (when arxiv id is set, fallback)
    3. Crossref abstract (JATS)  (when DOI is set)
    4. Crossref metadata JSON    (when DOI is set, last resort)

Inputs:
    - CITATION_REGISTRY (canonical)
    - docs/missing_bibkey_stubs.json (ephemeral; produced by
      extract_missing_bibkeys.py for cited-but-unregistered bibkeys)

Phase routing: `used_in[0]` paper path → src.core.citations.paper_phase().
Bibkeys cited only in src/ or docs/ fall back to Phase-1-and-Background.

Sidecar state at docs/primary_sources_state.json records each fetch verdict
so the script is resumable. The Stage-5 promotion script consumes the
sidecar to write `primary_source_path` fields back into citations.py.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from collections import Counter, defaultdict
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable, Optional

PROJECT_ROOT = Path(__file__).resolve().parent.parent.parent
SK_ROOT = Path(__file__).resolve().parent.parent
LIT_SEARCH = PROJECT_ROOT / "Lit-Search"
STUBS_PATH = SK_ROOT / "docs" / "missing_bibkey_stubs.json"
SIDECAR_PATH = SK_ROOT / "docs" / "primary_sources_state.json"
FALLBACK_PHASE = "Phase-1-and-Background"

sys.path.insert(0, str(SK_ROOT))
from src.core.citations import CITATION_REGISTRY, paper_phase, bibkey_phase  # noqa: E402


# ────────────────────────────────────────────────────────────────────────
# Conventions
# ────────────────────────────────────────────────────────────────────────

TIER_EXTENSIONS = [
    ("pdf",          "arxiv-pdf"),
    ("abstract.txt", "abstract"),
    ("json",         "crossref-json"),
]

PHASE_6A_LEGACY_ALIASES = {
    "balbinot":   "Balbinot2025",
    "jk0205174":  "JacobsonKoike2002",
    "jv9801308":  "JacobsonVolovik1998",
    "v0301043":   "Volovik2003BraneBH",
}

USER_AGENT = (
    "SK-EFT-Hawking-PrimarySource-Cache/1.0 "
    "(+https://github.com/anthropics/claude-code; jgroehm@gmail.com)"
)
ARXIV_PDF_URL  = "https://arxiv.org/pdf/{id}"
ARXIV_ABS_URL  = "http://export.arxiv.org/api/query?id_list={id}"
CROSSREF_URL   = "https://api.crossref.org/works/{doi}"


# ────────────────────────────────────────────────────────────────────────
# Unified entry view (registry + stubs)
# ────────────────────────────────────────────────────────────────────────

@dataclass
class Entry:
    """A bibkey with the minimum data needed by the fetcher."""
    bibkey: str
    phase: str
    fallback: bool                  # True if phase came from src/-only fallback
    arxiv: Optional[str]
    doi: Optional[str]
    inprep: bool
    source: str                     # "registry" or "stub"
    used_in: list[str] = field(default_factory=list)
    cited_in: list[str] = field(default_factory=list)


def _resolve_phase_for_stub(cited_in: list[str]) -> tuple[str, bool]:
    """Stubs only carry `cited_in` paper-keys. First match wins."""
    for paper_key in cited_in:
        ph = paper_phase(f"papers/{paper_key}/paper_draft.tex")
        if ph is not None:
            return ph, False
    return FALLBACK_PHASE, True


def load_entries(include_stubs: bool = True) -> list[Entry]:
    entries: list[Entry] = []

    # Registry-resident entries
    for bibkey, e in CITATION_REGISTRY.items():
        if e.get("inprep"):
            continue
        canonical = bibkey_phase(e)
        fallback = canonical is None
        phase = canonical or FALLBACK_PHASE
        entries.append(Entry(
            bibkey=bibkey,
            phase=phase,
            fallback=fallback,
            arxiv=e.get("arxiv") or None,
            doi=e.get("doi") or None,
            inprep=False,
            source="registry",
            used_in=list(e.get("used_in") or []),
        ))

    if include_stubs and STUBS_PATH.is_file():
        payload = json.loads(STUBS_PATH.read_text(encoding="utf-8"))
        for stub in payload.get("stubs", []):
            # Skip stubs already promoted into CITATION_REGISTRY (Stage 5).
            if stub["bibkey"] in CITATION_REGISTRY:
                continue
            phase, fallback = _resolve_phase_for_stub(stub.get("cited_in", []))
            entries.append(Entry(
                bibkey=stub["bibkey"],
                phase=phase,
                fallback=fallback,
                arxiv=stub.get("arxiv") or None,
                doi=stub.get("doi") or None,
                inprep=False,
                source="stub",
                cited_in=stub.get("cited_in", []),
            ))

    return entries


# ────────────────────────────────────────────────────────────────────────
# Sidecar state
# ────────────────────────────────────────────────────────────────────────

@dataclass
class FetchRecord:
    bibkey: str
    phase: str
    tier_achieved: Optional[str]    # e.g. "arxiv-pdf"; None on full failure
    primary_source_path: Optional[str]  # relative path from PROJECT_ROOT
    verdict: str                    # "success" | "no-source" | "fetch-failed"
    fetched_at: str
    size_bytes: int = 0
    url_used: Optional[str] = None
    note: Optional[str] = None


class Sidecar:
    """Append-only-ish state file: bibkey → most-recent FetchRecord."""

    def __init__(self, path: Path = SIDECAR_PATH) -> None:
        self.path = path
        self.records: dict[str, FetchRecord] = {}
        if path.is_file():
            payload = json.loads(path.read_text(encoding="utf-8"))
            for k, v in payload.get("entries", {}).items():
                self.records[k] = FetchRecord(**v)

    def get(self, bibkey: str) -> Optional[FetchRecord]:
        return self.records.get(bibkey)

    def put(self, rec: FetchRecord) -> None:
        self.records[rec.bibkey] = rec
        self._flush()

    def _flush(self) -> None:
        payload = {
            "_schema_version": 1,
            "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
            "entries": {k: asdict(v) for k, v in sorted(self.records.items())},
        }
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


# ────────────────────────────────────────────────────────────────────────
# Status discovery (used for --report)
# ────────────────────────────────────────────────────────────────────────

@dataclass
class BibkeyStatus:
    entry: Entry
    target_dir: Path
    on_disk: list[Path] = field(default_factory=list)
    best_tier: Optional[str] = None
    legacy_marker: bool = False

    @property
    def needs_fetch(self) -> bool:
        return self.best_tier is None


def discover_status(entry: Entry) -> BibkeyStatus:
    target_dir = LIT_SEARCH / entry.phase / "primary-sources"
    on_disk: list[Path] = []
    best_tier: Optional[str] = None
    if target_dir.is_dir():
        for ext, tier_name in TIER_EXTENSIONS:
            candidate = target_dir / f"{entry.bibkey}.{ext}"
            if candidate.is_file() and candidate.stat().st_size > 0:
                on_disk.append(candidate)
                if best_tier is None:
                    best_tier = tier_name

    legacy_marker = False
    for alias, mapped in PHASE_6A_LEGACY_ALIASES.items():
        if mapped == entry.bibkey:
            if (LIT_SEARCH / "Phase-6a" / "primary-sources" / alias).is_dir():
                legacy_marker = True
                break

    return BibkeyStatus(entry, target_dir, on_disk, best_tier, legacy_marker)


# ────────────────────────────────────────────────────────────────────────
# Fetchers
# ────────────────────────────────────────────────────────────────────────

class FetchError(Exception):
    pass


def _strip_jats(jats: str) -> str:
    """Remove JATS/HTML tags and decode entities."""
    import html
    txt = re.sub(r"<[^>]+>", " ", jats)
    txt = html.unescape(txt)
    return re.sub(r"\s+", " ", txt).strip()


def fetch_arxiv_pdf(arxiv_id: str, dest: Path, client) -> int:
    """Download arXiv PDF to dest. Returns bytes written."""
    url = ARXIV_PDF_URL.format(id=arxiv_id)
    r = client.get(url, follow_redirects=True, timeout=60.0)
    if r.status_code != 200:
        raise FetchError(f"arXiv PDF fetch HTTP {r.status_code}: {url}")
    if not r.content.startswith(b"%PDF"):
        raise FetchError(f"arXiv PDF fetch: response is not a PDF (head={r.content[:8]!r})")
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(r.content)
    return len(r.content)


def fetch_arxiv_abstract(arxiv_id: str, dest: Path, client) -> int:
    """Fetch abstract via the arXiv Atom API; write plaintext to dest."""
    url = ARXIV_ABS_URL.format(id=arxiv_id)
    r = client.get(url, timeout=30.0)
    if r.status_code != 200:
        raise FetchError(f"arXiv abstract fetch HTTP {r.status_code}: {url}")
    body = r.text
    # Atom: <entry><summary>...</summary>...
    m = re.search(r"<summary[^>]*>(.*?)</summary>", body, re.DOTALL)
    if not m:
        raise FetchError("arXiv abstract: no <summary> tag")
    title_m = re.search(r"<entry>.*?<title[^>]*>(.*?)</title>", body, re.DOTALL)
    authors = re.findall(r"<author>\s*<name>(.*?)</name>", body, re.DOTALL)
    abstract = _strip_jats(m.group(1))
    title = _strip_jats(title_m.group(1)) if title_m else "(title not in feed)"
    header = f"Title:   {title}\nAuthors: {', '.join(authors)}\nSource:  arXiv {arxiv_id}\n\n"
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(header + abstract + "\n", encoding="utf-8")
    return dest.stat().st_size


def fetch_crossref(doi: str, dest_json: Path, dest_abstract: Optional[Path], client) -> tuple[str, int]:
    """Fetch Crossref metadata JSON + (if available) the abstract.

    Writes metadata to dest_json. If the response carries an `abstract`
    field, also writes plaintext to dest_abstract (when supplied) and
    returns ("abstract", size). Otherwise returns ("crossref-json", size).
    """
    url = CROSSREF_URL.format(doi=doi)
    r = client.get(url, timeout=30.0)
    if r.status_code != 200:
        raise FetchError(f"Crossref fetch HTTP {r.status_code}: {url}")
    payload = r.json()
    dest_json.parent.mkdir(parents=True, exist_ok=True)
    dest_json.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    abstract_jats = payload.get("message", {}).get("abstract")
    if abstract_jats and dest_abstract is not None:
        text = _strip_jats(abstract_jats)
        if len(text) > 80:  # otherwise it's likely a JATS empty stub
            dest_abstract.write_text(text + "\n", encoding="utf-8")
            return "abstract", dest_abstract.stat().st_size
    return "crossref-json", dest_json.stat().st_size


# ────────────────────────────────────────────────────────────────────────
# Fetch driver
# ────────────────────────────────────────────────────────────────────────

def fetch_one(entry: Entry, client, sleep_s: float = 1.0) -> FetchRecord:
    """Walk the tier ladder for one bibkey. Returns a FetchRecord."""
    target_dir = LIT_SEARCH / entry.phase / "primary-sources"
    target_dir.mkdir(parents=True, exist_ok=True)

    pdf_path      = target_dir / f"{entry.bibkey}.pdf"
    abs_path      = target_dir / f"{entry.bibkey}.abstract.txt"
    json_path     = target_dir / f"{entry.bibkey}.json"
    rel = lambda p: str(p.relative_to(PROJECT_ROOT))
    now = lambda: datetime.now(timezone.utc).isoformat(timespec="seconds")

    # Tier 1: arXiv PDF
    if entry.arxiv:
        try:
            size = fetch_arxiv_pdf(entry.arxiv, pdf_path, client)
            time.sleep(sleep_s)
            return FetchRecord(
                bibkey=entry.bibkey, phase=entry.phase,
                tier_achieved="arxiv-pdf",
                primary_source_path=rel(pdf_path),
                verdict="success", fetched_at=now(),
                size_bytes=size, url_used=ARXIV_PDF_URL.format(id=entry.arxiv),
            )
        except FetchError as exc:
            note_arxiv_pdf = str(exc)
            time.sleep(sleep_s)
        else:
            note_arxiv_pdf = None
    else:
        note_arxiv_pdf = "no arxiv id"

    # Tier 2: arXiv abstract (lightweight; only if PDF tier failed)
    if entry.arxiv:
        try:
            size = fetch_arxiv_abstract(entry.arxiv, abs_path, client)
            time.sleep(sleep_s)
            return FetchRecord(
                bibkey=entry.bibkey, phase=entry.phase,
                tier_achieved="abstract",
                primary_source_path=rel(abs_path),
                verdict="success", fetched_at=now(),
                size_bytes=size, url_used=ARXIV_ABS_URL.format(id=entry.arxiv),
                note=f"arXiv PDF failed: {note_arxiv_pdf}",
            )
        except FetchError as exc:
            time.sleep(sleep_s)
            note_arxiv_pdf = f"arxiv-pdf: {note_arxiv_pdf}; arxiv-abs: {exc}"

    # Tier 3+4: Crossref (abstract preferred, then metadata-only)
    if entry.doi:
        try:
            tier, size = fetch_crossref(entry.doi, json_path, abs_path, client)
            time.sleep(sleep_s)
            chosen = abs_path if tier == "abstract" else json_path
            return FetchRecord(
                bibkey=entry.bibkey, phase=entry.phase,
                tier_achieved=tier,
                primary_source_path=rel(chosen),
                verdict="success", fetched_at=now(),
                size_bytes=size, url_used=CROSSREF_URL.format(doi=entry.doi),
                note=note_arxiv_pdf,
            )
        except FetchError as exc:
            time.sleep(sleep_s)
            return FetchRecord(
                bibkey=entry.bibkey, phase=entry.phase,
                tier_achieved=None, primary_source_path=None,
                verdict="fetch-failed", fetched_at=now(),
                note=f"crossref: {exc}; arxiv: {note_arxiv_pdf}",
            )

    return FetchRecord(
        bibkey=entry.bibkey, phase=entry.phase,
        tier_achieved=None, primary_source_path=None,
        verdict="no-source", fetched_at=now(),
        note=f"no arxiv id and no doi; manual fill required ({note_arxiv_pdf})",
    )


def find_on_disk(entry: Entry) -> tuple[Optional[str], Optional[Path]]:
    """If a cache file already exists for `entry`, return (tier_name, path).
    Otherwise return (None, None)."""
    target_dir = LIT_SEARCH / entry.phase / "primary-sources"
    if not target_dir.is_dir():
        return None, None
    for ext, tier_name in TIER_EXTENSIONS:
        p = target_dir / f"{entry.bibkey}.{ext}"
        if p.is_file() and p.stat().st_size > 0:
            return tier_name, p
    return None, None


def run_fetch(
    entries: list[Entry],
    sidecar: Sidecar,
    *,
    force: bool = False,
    limit: Optional[int] = None,
    sleep_s: float = 1.0,
) -> dict[str, int]:
    import httpx
    client = httpx.Client(headers={"User-Agent": USER_AGENT}, http2=False)
    counts: Counter[str] = Counter()
    n_processed = 0
    now = lambda: datetime.now(timezone.utc).isoformat(timespec="seconds")
    try:
        for entry in entries:
            existing = sidecar.get(entry.bibkey)
            if existing and existing.verdict == "success" and not force:
                if existing.primary_source_path:
                    p = PROJECT_ROOT / existing.primary_source_path
                    if p.is_file() and p.stat().st_size > 0:
                        counts["skipped-cached"] += 1
                        continue

            # Pre-existing on-disk file with no sidecar record? Record it.
            if not force:
                tier_name, on_disk = find_on_disk(entry)
                if tier_name is not None:
                    sidecar.put(FetchRecord(
                        bibkey=entry.bibkey, phase=entry.phase,
                        tier_achieved=tier_name,
                        primary_source_path=str(on_disk.relative_to(PROJECT_ROOT)),
                        verdict="success", fetched_at=now(),
                        size_bytes=on_disk.stat().st_size,
                        url_used=None,
                        note="pre-existing on disk; recorded without re-fetch",
                    ))
                    counts["pre-existing"] += 1
                    continue

            rec = fetch_one(entry, client, sleep_s=sleep_s)
            sidecar.put(rec)
            counts[rec.verdict] += 1
            n_processed += 1
            print(
                f"  [{n_processed:3d}] {entry.bibkey:40s} {entry.phase:24s} "
                f"→ {rec.verdict:13s} {rec.tier_achieved or '-'}",
                file=sys.stderr,
            )
            if limit is not None and n_processed >= limit:
                break
    finally:
        client.close()
    return dict(counts)


# ────────────────────────────────────────────────────────────────────────
# Reporting
# ────────────────────────────────────────────────────────────────────────

def render_report(rows: Iterable[BibkeyStatus]) -> str:
    rows = list(rows)
    by_phase: dict[str, list[BibkeyStatus]] = defaultdict(list)
    for st in rows:
        by_phase[st.entry.phase].append(st)

    lines: list[str] = []
    lines.append("# Primary-Sources Cache — Backfill Report")
    lines.append("")
    lines.append(f"External bibkeys (registry + stubs): {len(rows)}")
    cached = sum(1 for st in rows if st.best_tier)
    pct = 100 * cached / max(1, len(rows))
    lines.append(f"Already cached (any tier): {cached} ({pct:.1f}%)")
    legacy = sum(1 for st in rows if st.legacy_marker)
    lines.append(f"Phase-6a legacy aliases needing migration: {legacy}")
    lines.append("")
    lines.append("## Per-phase tier distribution")
    lines.append("")
    lines.append(
        "| Phase | Total | Cached | arxiv-pdf | abstract | crossref-json "
        "| Needs fetch | Has arXiv | Has DOI | Stubs |"
    )
    lines.append(
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|"
    )
    for phase in sorted(by_phase):
        items = by_phase[phase]
        tier_counts = Counter(st.best_tier for st in items if st.best_tier)
        cached_n = sum(1 for st in items if st.best_tier)
        needs_n = sum(1 for st in items if st.needs_fetch)
        with_arxiv = sum(1 for st in items if st.entry.arxiv)
        with_doi = sum(1 for st in items if st.entry.doi)
        n_stubs = sum(1 for st in items if st.entry.source == "stub")
        lines.append(
            f"| {phase} | {len(items)} | {cached_n} | "
            f"{tier_counts.get('arxiv-pdf', 0)} | "
            f"{tier_counts.get('abstract', 0)} | "
            f"{tier_counts.get('crossref-json', 0)} | "
            f"{needs_n} | {with_arxiv} | {with_doi} | {n_stubs} |"
        )
    lines.append("")
    lines.append("## Fetchability projection (entries needing fetch)")
    lines.append("")
    lines.append("| Phase | arXiv-reachable | Crossref-only | Manual-fill |")
    lines.append("|---|---:|---:|---:|")
    for phase in sorted(by_phase):
        items = [st for st in by_phase[phase] if st.needs_fetch]
        a = sum(1 for st in items if st.entry.arxiv)
        d = sum(1 for st in items if not st.entry.arxiv and st.entry.doi)
        m = sum(1 for st in items if not st.entry.arxiv and not st.entry.doi)
        lines.append(f"| {phase} | {a} | {d} | {m} |")
    lines.append("")

    manual_items = [
        st for st in rows
        if st.needs_fetch and not st.entry.arxiv and not st.entry.doi
    ]
    if manual_items:
        lines.append("## Manual-fill backlog (no arXiv, no DOI)")
        lines.append("")
        for st in sorted(manual_items, key=lambda x: (x.entry.phase, x.entry.bibkey)):
            src_tag = " [stub]" if st.entry.source == "stub" else ""
            lines.append(f"- **{st.entry.bibkey}** [{st.entry.phase}]{src_tag}")
        lines.append("")

    if any(st.legacy_marker for st in rows):
        lines.append("## Phase-6a legacy migration")
        lines.append("")
        for st in rows:
            if st.legacy_marker:
                alias = next(a for a, b in PHASE_6A_LEGACY_ALIASES.items() if b == st.entry.bibkey)
                lines.append(f"- `Phase-6a/primary-sources/{alias}/` → `{st.entry.bibkey}.{{pdf,abstract.txt,json}}`")
        lines.append("")

    return "\n".join(lines)


# ────────────────────────────────────────────────────────────────────────
# CLI
# ────────────────────────────────────────────────────────────────────────

def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument("--report",  action="store_true", help="Aggregate per-phase summary; no I/O.")
    mode.add_argument("--dry-run", action="store_true", help="Per-bibkey dry-run lines; no I/O.")
    mode.add_argument("--fetch",   action="store_true", help="Actually fetch missing primary sources.")
    p.add_argument("--phase",  help="Limit to one phase (e.g. '6e' or 'Phase-6e').")
    p.add_argument("--bibkey", help="Limit to one bibkey (debugging).")
    p.add_argument("--no-stubs", action="store_true", help="Exclude missing-bibkey stubs.")
    p.add_argument("--limit",  type=int, help="Process at most N entries this run.")
    p.add_argument("--force",  action="store_true", help="Re-fetch even if sidecar says success.")
    p.add_argument("--sleep",  type=float, default=1.0, help="Inter-request sleep, seconds (default 1.0).")
    p.add_argument("--out",    type=Path, help="Write report to file (default stdout).")
    args = p.parse_args(argv)

    entries = load_entries(include_stubs=not args.no_stubs)

    if args.phase:
        phase_arg = args.phase if args.phase.startswith("Phase-") else f"Phase-{args.phase}"
        entries = [e for e in entries if e.phase == phase_arg]
        if not entries:
            print(f"warning: no bibkeys routed to {phase_arg}", file=sys.stderr)
    if args.bibkey:
        entries = [e for e in entries if e.bibkey == args.bibkey]
        if not entries:
            print(f"error: bibkey '{args.bibkey}' not in registry or stubs (or is inprep)", file=sys.stderr)
            return 1

    if args.report or args.dry_run:
        rows = [discover_status(e) for e in entries]
        out = render_report(rows)
        if args.out:
            args.out.write_text(out, encoding="utf-8")
            print(f"wrote {args.out}", file=sys.stderr)
        else:
            print(out)
        return 0

    # --fetch
    sidecar = Sidecar()
    print(f"fetching up to {args.limit or len(entries)} of {len(entries)} entries", file=sys.stderr)
    counts = run_fetch(
        entries, sidecar,
        force=args.force, limit=args.limit, sleep_s=args.sleep,
    )
    print(file=sys.stderr)
    print(f"summary: {counts}", file=sys.stderr)
    print(f"sidecar: {sidecar.path.relative_to(PROJECT_ROOT)}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
