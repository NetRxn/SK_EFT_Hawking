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
- **Verify:** `cd "$REPO" && uv run python -c "import sys, copy; sys.path.insert(0,\".\"); sys.path.insert(0,\"scripts\"); from src.core import citations as C; from validation.checks import citations as ck; s=lambda r: [d for d in r.details if d.name==\"summary\"][0].message; d={k:v for k,v in C.CITATION_REGISTRY.items() if v.get(\"citation_class\")}; assert len(d)>=50, \"fewer than 50 declared citation_class entries\"; assert all(v[\"citation_class\"] in ck._EXEMPT_CITATION_CLASSES and len(str(v.get(\"exempt_reason\") or \"\").strip())>=25 for v in d.values()), \"a declared class is unknown or carries no pathway\"; b=copy.deepcopy(C.CITATION_REGISTRY); p=copy.deepcopy(b); p[\"Gilkey1995\"][\"doi\"]=\"10.9999/verify-probe\"; C.CITATION_REGISTRY=p; r=ck.check_citation_primary_sources_present(); assert r.passed and \" 0 need cache \" in s(r), \"a DECLARED textbook lost its exemption to an identifier -- exemption is keyed on absent metadata again\"; q=copy.deepcopy(b); q[\"KobayashiNomizu1963\"].pop(\"citation_class\"); q[\"KobayashiNomizu1963\"].pop(\"exempt_reason\"); C.CITATION_REGISTRY=q; assert not ck.check_citation_primary_sources_present().passed, \"an entry with no metadata and no declaration is STILL exempt -- absence still buys the exemption\"; print(\"OK\")"`
  *What it asserts:* three things the ORIGINAL Verify could not. **The original was keyed on
  the defect's own proxy** — it asked whether `notes` contains the word "textbook", which is the
  same class of stand-in as the predicate it was filed against, and it would have been satisfied
  by writing "textbook" into 74 auto-generated stubs. **Amended 2026-08-15** when the fix landed;
  the fix moved what the measurement was scoped by, which voids a Verify keyed on the old shape.
  The replacement asserts (a) the declared vocabulary is populated and every declaration carries a
  pathway; (b) **the incentive** — a DECLARED textbook given a DOI keeps its exemption, where the
  old predicate revoked it and demanded a cache; (c) **absence buys nothing** — stripping the
  declaration off a real entry turns the check RED. Legs (b) and (c) both exit 1 under the old
  predicate, verified by restoring it; a Verify both predicates pass would not distinguish fixed
  from unfixed. Exits 0 at `9cd6dd72`, 1 before it.
- **Gate:** CitationIntegrity
- **Location:** `scripts/validation/checks/citations.py` — the textbook-exemption branch in `check_citation_primary_sources_present`
- **Observed:** The branch's own comment says "canonical textbook references … **verified via secondary academic citations per `notes`**", but the predicate never reads `notes`. Nothing distinguishes a deliberately-exempted textbook from an entry nobody finished.
- **Evidence:** Measured 2026-08-15 over `CITATION_REGISTRY` (663 entries):
  - 150 bibkeys currently textbook-exempt; **85 have `year >= 2000`**.
  - `physlean` — 2024, `title: ''`, no doi/arXiv/path. The real record (`TooBySmithHepLean`, arXiv:2405.08863) exists in the registry and is *not* the one I1 cites.
  - `alphaproof` — 2024, `title: ''`, all identifiers `None`; its only cache record is `verdict: fetch_failed`.
  - `compcert` / `sel4` — 2009, with the venue stored in the `title` field.
  - The check passes cleanly at HEAD: `381 cached / 12 inprep-exempt / 150 textbook-exempt / 0 need cache / 0 missing-from-registry`.
- **RE-MEASURED at remediation time, same day — the figures above had already drifted, which is
  why a filed number is re-derived rather than quoted.** `129` textbook-exempt, `51` of them
  post-2000, over `544` cited bibkeys. The severity is better stated by a different cut than
  `year >= 2000`, which is a proxy in its own right:
  - **74 of the 129** carry the literal `notes` string `"Auto-generated stub from \bibitem block
    in …"` — nobody ever said what these references are. That, not the year, is the population.
  - **51 of the 129** carry a human-authored rationale naming a genuine non-cacheable class:
    textbook 24 · pre-arXiv 22 · software (Mathlib/Lean attribution) 5. These are the real
    exemptions and they were migrated.
  - **4 of the 129** are under-populated, not exempt: `isabelleCBO`, `leanQI2025` and `survey2021`
    each record an arXiv id **in prose** with `arxiv: None`; `Sola2023`'s note is the open TODO
    `"User verify DOI + arXiv"`. These are the perverse incentive caught in the act.
  - **0 of the 129 hold a cache on disk.** This is the constraint that decided the design:
    revoking the exemption drops every revoked entry straight into the blocking bucket, so the
    honest repair could not be "demand a cache".
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
