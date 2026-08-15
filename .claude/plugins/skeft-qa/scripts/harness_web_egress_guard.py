#!/usr/bin/env python3
"""
Web-egress guard — PreToolUse(WebSearch|WebFetch) dev-harness SECURITY control.

Two jobs, on EVERY WebSearch/WebFetch call in the repo (main loop or any subagent):
  1. DENY if the query/URL contains a denylisted local/private identifier.
  2. DENY a WebFetch to a non-whitelisted domain.

Unlike the question-guard this is UNCONDITIONAL (not gated on a /goal marker) and
FAILS CLOSED: any internal error => deny. The launcher in hooks.json adds a second
fail-closed layer (a printf-deny fallback if this script cannot even start).

Denylist = committed research_egress_denylist.sample.txt (baseline, always)
         UNION untracked research_egress_denylist.txt (operator literals, if installed).
Both live in this script's directory; the local file is gitignored so it may hold
literals (incl. firewall terms) without ever being committed.

Stdlib only. Owning document: docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md §1.5 (the
enforcement layer — whitelist forms, how to add an entry, and the three places that name
scholarly domains of which only this one enforces). What a claim may rest on once a fetch
lands: docs/adrs/ADR-014-source-acquisition-and-citation-fidelity.md.

⚠️ This docstring cited `docs/dev-loops/RESEARCH_LADDER_AND_WEB_EGRESS.md` as its "full spec"
from the day it shipped until 2026-08-15. That file never existed, so the only description of
this fail-closed control was its own source; and a later reader, trusting the path, created the
phantom rather than asking which document already owned the surface — producing a second
description beside QA_QI_INFRASTRUCTURE_MAP §1.5, which had owned it all along. A dangling
reference invents a home if you let it.
"""
from __future__ import annotations

import json
import os
import posixpath
import re
import sys
from urllib.parse import urlparse

_HERE = os.path.dirname(os.path.abspath(__file__))
_SAMPLE = os.path.join(_HERE, "research_egress_denylist.sample.txt")
_LOCAL = os.path.join(_HERE, "research_egress_denylist.txt")

# Whitelisted WebFetch destinations (registrable hostnames). A host passes iff it equals
# an entry or is a subdomain of one (endswith "." + entry) — so export.arxiv.org passes
# but arxiv.org.evil.com / notarxiv.org do not. WebSearch is a search engine: not domain-gated.
_WHITELIST = (
    "arxiv.org", "export.arxiv.org", "doi.org", "link.aps.org", "journals.aps.org",
    "iopscience.iop.org", "projecteuclid.org", "stacks.math.columbia.edu",
    "leanprover-community.github.io", "leanprover.github.io", "oeis.org", "pdg.lbl.gov",
    # Official Lean docs: the reference manual, release notes and toolchain pages for
    # the language this substrate is written in.
    "lean-lang.org",
    "en.wikipedia.org", "ncatlab.org", "encyclopediaofmath.org",
    "mathoverflow.net", "math.stackexchange.com",
    # Project tooling/infrastructure (NOT scholarly primaries), user-authorized 2026-06-29:
    #  - Aristotle theorem prover's dashboard/API docs (we submit to it as part of the
    #    Stage-4 Lean pipeline; its docs are operational reference).
    #  - anthropic.com + claude.com + claude.ai, all subdomains: Anthropic engineering blog
    #    (www.anthropic.com) + API docs (docs.anthropic.com) + the Claude Code product docs
    #    (code.claude.com) + the Claude web app / shared artifacts (claude.ai). This repo's
    #    autonomous-dev harness IS Claude Code, so these are operational reference.
    #    claude.ai added on operator request 2026-07-04 (fetch shared artifacts/conversations).
    "aristotle.harmonic.fun", "harmonic.fun", "anthropic.com", "claude.com", "claude.ai",
    # KT-LMS §5 primary-text mirrors — Kirby–Taylor "Pin structures on low-dimensional
    # manifolds" (LMS-151, 1990) — academic paper archives, user-authorized 2026-07-04 for
    # the Phase 5q.H full-strength ABK-completeness fetch (the surgery proof is off-arXiv).
    "math.berkeley.edu", "webhomes.maths.ed.ac.uk",
    # Patent & trademark public records (prior-art, FTO, clearance verification) +
    # nature.com scholarly primary + Semantic Scholar meta, user-authorized 2026-07-10:
    "patents.google.com", "patentscope.wipo.int", "uspto.gov",
    "worldwide.espacenet.com", "nature.com", "semanticscholar.org",
    # Isabelle Archive of Formal Proofs — a curated, refereed formalization archive and a
    # primary prior-art source for novelty claims. User-authorized 2026-08-01 for the D12
    # blocking prior-art gate (AFP `Error_Function`, `Probability`, `Kraus Maps`,
    # `Concentration Inequalities`, `Projective Measurements`, `Isabelle Marries Dirac`).
    "isa-afp.org",
    # Source-acquisition targets (ADR-014). Each entry is here for a P0 row of
    # docs/SOURCE_ACQUISITION_REGISTER.md — a source a bundle's CLAIM depends on that we do
    # not hold in full text. Named so a later reader can retire an entry once its target is
    # acquired, rather than inheriting an unexplained grant. User-authorized 2026-08-15:
    #  - NASA ADS + NTRS: Mather 1982 (Appl. Opt. 21, 1125). NASA-authored, so the scanned
    #    full text may be reachable free; the abstract we hold cannot settle the PSD-vs-
    #    amplitude convention that D12 §3.2 turns on.
    #  - NIST public-access: Irwin & Hilton 2005 (NIST authors) — the attributed source of
    #    D12's diffuse-conduction closed form, currently held only as a resolved DOI record.
    #  - Springer: JHEP (Sen 2013, open access) and the Cryogenic Particle Detection volume.
    #  - Optica: the Mather landing record.
    #  - ScienceDirect: Theoret. Comput. Sci. 560 (2014), the open republication of BB84.
    "adsabs.harvard.edu", "ntrs.nasa.gov", "nvlpubs.nist.gov",
    "link.springer.com", "opg.optica.org", "sciencedirect.com",
    # Datastar — the hypermedia framework the provenance dashboard is built on
    # (docs/architecture/DASHBOARD.md, docs/references/Datastar_Dashboard_Reference.md).
    # Operational reference, not a scholarly primary. User-authorized 2026-08-15.
    #
    # ⚠️ This domain sat in `.claude/settings.local.json` as `WebFetch(domain:data-star.dev)`
    # and was NEVER reachable: permissions.allow cannot grant egress, only this list can, and
    # this list did not carry it. Verified 2026-08-15 by fetching it and being denied. Anyone
    # building dashboard work against "best Datastar practice" was doing so without ever
    # having read the source. A grant in the wrong file is indistinguishable from no grant.
    "data-star.dev",
    # ── Publisher hosts our OWN citation corpus resolves to (user-authorized 2026-08-15) ──
    # DERIVED, not guessed: every DOI prefix present in CITATION_REGISTRY was mapped to its
    # registrant's article host, and the ones missing here are listed below. This matters
    # because `doi.org` alone is not enough — a DOI resolves by CROSS-HOST REDIRECT, and
    # WebFetch returns cross-host redirects rather than following them, so the destination
    # must be reachable in its own right. Whitelisting doi.org while omitting the publisher
    # buys the redirect and not the paper.
    #
    # Re-derive after adding citations:
    #   uv run python -c "from src.core.citations import CITATION_REGISTRY as C; import re,collections;
    #   print(collections.Counter(re.match(r'(10\.\d{4,5})/',v.get('doi') or '').group(1)
    #   for v in C.values() if re.match(r'(10\.\d{4,5})/', v.get('doi') or '')))"
    #
    # All are scholarly publishers serving editorially-controlled content — unlike a code
    # host, a bare entry here is not a grant over arbitrary user-supplied material.
    "dl.acm.org",                    # 10.1145 — ACM
    "worldscientific.com",           # 10.1142 — World Scientific
    "pubs.aip.org",                  # 10.1063 — AIP
    "science.org",                   # 10.1126 — AAAS
    "royalsocietypublishing.org",    # 10.1098 — Royal Society
    "annualreviews.org",             # 10.1146 — Annual Reviews
    "academic.oup.com",              # 10.1093, 10.1143 — Oxford (incl. Prog. Theor. Phys.)
    "mdpi.com",                      # 10.3390 — MDPI
    "intlpress.com",                 # 10.4310 — International Press (ATMP)
    "cambridge.org",                 # 10.1017 — Cambridge
    "scipost.org",                   # 10.21468 — SciPost
    "onlinelibrary.wiley.com",       # 10.1002, 10.1112 — Wiley / LMS
    "journals.uchicago.edu", "press.uchicago.edu",   # 10.1086, 10.7208 — U. Chicago
    "edpsciences.org",               # 10.1051 — EDP Sciences
    "tandfonline.com",               # 10.1080 — Taylor & Francis
    "ieeexplore.ieee.org",           # 10.1109 — IEEE
    "ems.press",                     # 10.4171 — EMS Press
    "msp.org",                       # 10.2140 — Mathematical Sciences Publishers
    "pos.sissa.it",                  # 10.22323 — Proceedings of Science
    "centre-mersenne.org",           # 10.5802 — Centre Mersenne
    "emis.de",                       # 10.3842 — SIGMA
    "digital-library.theiet.org",    # 10.1049 — IET
    # Already reachable via entries above, recorded so the mapping is not re-derived:
    #   10.48550 -> arxiv.org · 10.1134, 10.1023, 10.1140, 10.12942 -> link.springer.com
    #   10.3847, 10.1070 -> iopscience.iop.org
    # STILL UNMAPPED (1 entry): 10.26421 — registrant not identified; if a fetch of it is
    # ever denied, identify the host and add it here rather than widening anything.
    # Python stdlib reference — the language this substrate is written in (added 2026-08-15)
    "docs.python.org",
    # package metadata and released versions; dependency-declaration checks (added 2026-08-15)
    "pypi.org",
    # hosts the documentation for a large share of our Python dependencies (added 2026-08-15)
    "readthedocs.io",
    # uv and ruff — uv is this project's package manager and lockfile authority (added 2026-08-15)
    "docs.astral.sh",
    # NumPy — core numerics beneath formulas.py and the WKB/ADW solvers (added 2026-08-15)
    "numpy.org",
    # SciPy — integrators and optimizers in the same layer (added 2026-08-15)
    "scipy.org",
    # Plotly — the project's MANDATED figure library (matplotlib is prohibited) (added 2026-08-15)
    "plotly.com",
    # pytest — the harness both test suites run under (added 2026-08-15)
    "docs.pytest.org",
    # Quart and Flask — the provenance dashboard's web layer (added 2026-08-15)
    "palletsprojects.com",
    # Playwright — the real-chromium tests that guard page JS (added 2026-08-15)
    "playwright.dev",
    # Rust language reference — the RHMC crate (added 2026-08-15)
    "doc.rust-lang.org",
    # Rust crate API docs for the RHMC dependency set (added 2026-08-15)
    "docs.rs",
    # Rust crate metadata and released versions (added 2026-08-15)
    "crates.io",
    # PyO3 — the Rust/Python bridge the RHMC crate is built on (added 2026-08-15)
    "pyo3.rs",
    # PostgreSQL — the shared provenance graph database (added 2026-08-15)
    "postgresql.org",
    # Docker — the sk_eft_graph container the database runs in (added 2026-08-15)
    "docs.docker.com",
    # Cloudflare Workers and Access — the website deployment path (added 2026-08-15)
    "developers.cloudflare.com",
    # OpenAI API reference — a provider this workspace evaluates against (added 2026-08-15)
    "platform.openai.com",
    # OpenAI model and pricing documentation (added 2026-08-15)
    "openai.com",
)

# Path-scoped destinations: (host, path_prefix). A URL passes iff its host matches the
# entry (exactly or as a subdomain) AND its NORMALIZED path equals the prefix or extends
# it at a "/" boundary. This exists so single code-hosting repositories can be reached
# WITHOUT whitelisting the whole host — github.com carries arbitrary user-controlled
# content, so a bare host entry would be a far broader grant than intended.
#
# User-authorized 2026-08-01: theorem-prover ecosystem repositories, for prior-art and
# novelty verification. Absence-of-formalization is a claim this project makes in print;
# it must be checkable against the actual sources. Add repos here one at a time — never
# widen this to a bare "github.com" entry in _WHITELIST.
_PATH_WHITELIST = (
    # D12 blocking prior-art gate (the highest prior-art risk in that bundle):
    ("github.com", "/RemyDegenne/testing-lower-bounds"),
    ("raw.githubusercontent.com", "/RemyDegenne/testing-lower-bounds"),
    # Coq `infotheo` — the other half of the same D12 gate:
    ("github.com", "/affeldt-aist/infotheo"),
    ("raw.githubusercontent.com", "/affeldt-aist/infotheo"),
    # Standing prover-ecosystem prior-art sources:
    ("github.com", "/leanprover-community/mathlib4"),
    ("raw.githubusercontent.com", "/leanprover-community/mathlib4"),
    ("github.com", "/leanprover/lean4"),
    ("raw.githubusercontent.com", "/leanprover/lean4"),
    ("github.com", "/math-comp/math-comp"),
    ("raw.githubusercontent.com", "/math-comp/math-comp"),
    ("github.com", "/agda/agda-stdlib"),
    ("raw.githubusercontent.com", "/agda/agda-stdlib"),
    ("github.com", "/HOL-Theorem-Prover/HOL"),
    ("raw.githubusercontent.com", "/HOL-Theorem-Prover/HOL"),
)

_HEADER = re.compile(r"^#\s*-+\s*(.+?)\s*-+\s*$")


def _load_patterns():
    """(compiled_regex, category) from sample (always) UNION local (if present).

    A `# --- label ---` line sets the category. Active rows: a `/regex/` line, or a
    bare case-insensitive literal. Blank lines and other `#` lines are inert, so the
    sample's commented placeholders stay off until copied into the local file.

    ⚠️ **RAISES rather than skipping, and that is the security property.** This
    module's contract is "any internal error => deny", and two handlers here used
    to break it in the direction that ALLOWS:

      * a malformed `/regex/` row was dropped with `except re.error: continue`,
        so ONE TYPO removed that identifier from the guard permanently and printed
        nothing. Measured: a local file holding `/johnroehm(/` and `SECRETPROJ`
        loaded only `SECRETPROJ`, and a WebSearch for `/Users/johnroehm/secret`
        was ALLOWED while the operator saw a working guard.
      * `except FileNotFoundError: continue` is correct for `_LOCAL`, which is
        untracked and legitimately absent. It was applied to `_SAMPLE` too — the
        COMMITTED baseline — so the always-on denylist could vanish silently.
        Measured: renaming the sample dropped the pattern count 11 -> 7, no signal.

    Exceptions raised here propagate through `evaluate` to `main`, which denies.
    """
    out = []
    for path in (_SAMPLE, _LOCAL):
        try:
            with open(path, encoding="utf-8") as fh:
                lines = fh.readlines()
        except FileNotFoundError:
            if path == _LOCAL:
                continue  # untracked; the operator may not have installed one
            raise RuntimeError(
                f"denylist baseline missing: {path}. It is committed and must be "
                f"present; its absence is a broken install, not an empty denylist.")
        category = "denylisted identifier"
        for lineno, raw in enumerate(lines, 1):
            line = raw.strip()
            if not line:
                continue
            if line.startswith("#"):
                m = _HEADER.match(line)
                if m:
                    category = m.group(1)
                continue
            if len(line) >= 2 and line.startswith("/") and line.endswith("/"):
                try:
                    out.append((re.compile(line[1:-1], re.IGNORECASE), category))
                except re.error as exc:
                    raise RuntimeError(
                        f"denylist {path}:{lineno} is not a valid regex ({exc}); "
                        f"the row it was meant to block is UNGUARDED") from exc
            else:
                out.append((re.compile(re.escape(line), re.IGNORECASE), category))
    if not out:
        raise RuntimeError(
            "denylist loaded ZERO patterns — an empty guard cannot deny anything")
    return out


def _host_matches(host: str, entry: str) -> bool:
    """Exact host, or a subdomain of it — never a suffix-confusable lookalike."""
    return host == entry or host.endswith("." + entry)


def _host_allowed(host: str) -> bool:
    host = (host or "").lower()
    return any(_host_matches(host, d) for d in _WHITELIST)


def _path_allowed(host: str, path: str) -> bool:
    """True iff (host, path) matches a _PATH_WHITELIST entry.

    The path is normalized first, so `/owner/repo/../../elsewhere` cannot walk out of an
    allowed prefix. Matching is casefolded: a case variant of an allowed repo path resolves
    to the same repository, and denying on case alone would produce exactly the kind of
    spurious "policy block" this guard must not manufacture.
    """
    host = (host or "").lower()
    norm = posixpath.normpath(path or "/")
    if not norm.startswith("/"):
        norm = "/" + norm
    norm = norm.casefold()
    for entry_host, prefix in _PATH_WHITELIST:
        if not _host_matches(host, entry_host):
            continue
        pref = prefix.casefold()
        if norm == pref or norm.startswith(pref + "/"):
            return True
    return False


def evaluate(ev: dict):
    """Return a deny-reason string, or None to allow.

    Pure apart from reading the denylist files. Anything it raises propagates to
    main(), which fails closed.
    """
    tool = ev.get("tool_name", "")
    if tool not in ("WebSearch", "WebFetch"):
        return None
    tool_input = ev.get("tool_input") or {}
    text = json.dumps(tool_input, ensure_ascii=False)
    for rx, category in _load_patterns():
        if rx.search(text):
            return (
                f"[web-egress] blocked: this {tool} query/URL matches a denylisted "
                f"'{category}'. Strip local paths / private identifiers from the request "
                f"and retry. (dev-harness web-egress guard)"
            )
    if tool == "WebFetch":
        parsed = urlparse(tool_input.get("url", ""))
        host = parsed.hostname or ""
        if not _host_allowed(host) and not _path_allowed(host, parsed.path):
            return (
                f"[web-egress] WebFetch to non-whitelisted domain "
                f"'{host or tool_input.get('url', '')}'. Only scholarly primaries / greylist "
                f"are allowed (see docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md §1.5). "
                f"Do NOT reason from a remembered whitelist: if a fetch returns content it "
                f"was sanctioned. To request a domain, name the SOURCE you need it for."
            )
    return None


def _deny(reason: str) -> None:
    print(json.dumps({"hookSpecificOutput": {
        "hookEventName": "PreToolUse",
        "permissionDecision": "deny",
        "permissionDecisionReason": reason,
    }}))


def main() -> int:
    try:
        ev = json.loads(sys.stdin.read() or "{}")
        reason = evaluate(ev)
    except Exception as exc:
        # Name the cause. A bare "internal error" gave the operator no way to tell
        # a malformed denylist row from a transient fault, and the row stays
        # unguarded until someone notices.
        _deny(f"[web-egress] guard internal error; failing closed: {exc}")
        return 0
    if reason is not None:
        _deny(reason)
    return 0


if __name__ == "__main__":
    sys.exit(main())
