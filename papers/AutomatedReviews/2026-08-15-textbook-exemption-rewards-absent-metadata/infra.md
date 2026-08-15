---
paper: infra
bundle: infra
bundle_target: infra
tier: 2
reviewer: lead
model: claude-opus-5
review_date: 2026-08-15T04:30:00Z
readiness_gates_version: 1
kind: targeted-infra
---

# The textbook exemption fires on absent metadata, so the emptier an entry the more exempt it is

## Summary

**1 MAJOR.** `citation_primary_sources_present` asks whether a cited reference is backed by a
primary source we hold. Its textbook exemption is keyed on
`primary_source_path is None and doi is None and arxiv is None` — a **proxy** for "canonical
pre-DOI textbook" that is satisfied by *any* entry whose metadata was never filled in.

The incentive is inverted: **an entry earns exemption by being empty.** A 2024 arXiv preprint
with a blank title and no identifiers is exempt; the same preprint with its arXiv id recorded is
not.

Measured at HEAD 2026-08-15: of 150 textbook-exempt bibkeys, **85 are dated 2000 or later**.
Four are named in `I1`'s open findings and are plainly not textbooks: `physlean` (2024, title
`''`), `alphaproof` (2024, title `''`), `compcert` (2009, title `'Comm.\ ACM'` — a venue in the
title field), `sel4` (2009, title `'Proc.\ ACM SOSP'`).

⚠️ **This makes the check's own green partly hollow, and I reported that green earlier today.**
After fixing `check_undefined_citations` I ran `citation_primary_sources_present` and reported
"381 cached / 0 need cache" as a clean pass. It is a pass, but 150 of the corpus's references
were never asked the question, and 85 of those are modern.

---

### 1.1 — 🔴 MAJOR — Exemption is granted by missing metadata rather than by reference class

- **Severity:** major
- **Lane:** `infra`
- **Verify:** `cd "$REPO" && uv run python -c "import sys; sys.path.insert(0,'.'); from src.core.citations import CITATION_REGISTRY as C; bad=[k for k,v in C.items() if v.get('primary_source_path') is None and v.get('doi') is None and v.get('arxiv') is None and (v.get('year') or 0)>=2000 and not str(v.get('notes','')).lower().count('textbook')]; assert not bad, f'{len(bad)} post-2000 refs exempted by absent metadata: {sorted(bad)[:8]}'"`
  *What it asserts:* that no modern reference is textbook-exempt without an explicit textbook rationale in `notes`. Exits 1 at HEAD.
- **Gate:** CitationIntegrity
- **Location:** `scripts/validation/checks/citations.py` — the textbook-exemption branch in `check_citation_primary_sources_present`
- **Observed:** The branch's own comment says "canonical textbook references … **verified via secondary academic citations per `notes`**", but the predicate never reads `notes`. Nothing distinguishes a deliberately-exempted textbook from an entry nobody finished.
- **Evidence:** Measured 2026-08-15 over `CITATION_REGISTRY` (663 entries):
  - 150 bibkeys currently textbook-exempt; **85 have `year >= 2000`**.
  - `physlean` — 2024, `title: ''`, no doi/arXiv/path. The real record (`TooBySmithHepLean`, arXiv:2405.08863) exists in the registry and is *not* the one I1 cites.
  - `alphaproof` — 2024, `title: ''`, all identifiers `None`; its only cache record is `verdict: fetch_failed`.
  - `compcert` / `sel4` — 2009, with the venue stored in the `title` field.
  - The check passes cleanly at HEAD: `381 cached / 12 inprep-exempt / 150 textbook-exempt / 0 need cache / 0 missing-from-registry`.
- **Expected:** Exemption is a **declared** property, not an inferred one. A reference is exempt because someone recorded that it is a pre-DOI textbook, not because its fields are blank.
- **Fix:** Require an explicit marker — either a `textbook: True` field or a `notes` string the
  predicate actually reads — and treat "no identifiers AND no marker" as **needs cache**, which is
  the honest state. ⚠️ **Measure before shipping:** this will move some or all of the 85 into the
  failing population, so the change needs a triage pass and probably a declared ratchet rather
  than an immediate hard gate. Do not close the gap by back-filling `textbook: True` onto
  everything currently exempt — that reproduces the defect with extra steps.
- **Related:** the same class as `2026-08-15-verify-contract-unenforced` and the `\bibitem`-as-proxy
  defect retired in `d39d2ffb` — a check asserting a stand-in for its own purpose. This one is the
  most consequential of the three because the stand-in is *satisfied by neglect*.
- **Cache:** N/A.
