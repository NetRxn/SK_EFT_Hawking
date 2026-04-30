---
paper: paper44_riemannian_connection
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-30T13:36:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper44_riemannian_connection

## Summary

Eight findings. Six BLOCKER, one REQUIRED, one RECOMMENDED. Gates affected:
CitationIntegrity (registry-absence on six paper-level bibkeys; no cached
primary sources for textbooks Klingenberg1995 / KobayashiNomizu1963 nor for
`MassotRothgangMacbeth2025` / `Gouezel2025` / `Gouezel2024LieBracket`),
CountFreshness (abstract literal "forty-four substantive theorems" disagrees
with the ground-truth `^theorem|^lemma` count of forty-five across the seven
modules after marker exclusion), NarrativeGrounding (three "first
formalization in any proof assistant" claims with non-exhaustive prior-art
search), CrossPaperConsistency (count-literal drift inside paper44 itself
between abstract and §10.2 strengthening-cuts subsection — abstract says 44,
§10.2 still says "thirty-three substantive theorems across five modules"
which is the W7+W8 S1-3 count and was not updated for sessions 4+5).
**This paper is not submission-ready** — registry absences are gate-1 hard
blockers and the stale §10.2 count is a self-contradiction in the same
artifact.

## Findings

### 1.1 — 🔴 BLOCKER — bibkey `MassotRothgangMacbeth2025` absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `papers/paper44_riemannian_connection/paper_draft.tex:1224`
  (bibitem) and intro/L99, L679, L1213 in-text cites
- **Observed:** `\bibitem{MassotRothgangMacbeth2025}` cites
  "Mathlib4 covariant derivatives library, Mathlib4 commit 8850ed93,
  April 2026, Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.{Basic,Torsion}"
  but the bibkey is not present in `src/core/citations.py` `CITATION_REGISTRY`.
- **Evidence:** `grep -nE "'MassotRothgangMacbeth2025'" src/core/citations.py`
  returns empty; `grep` of `docs/citation_verifications.jsonl` returns empty.
- **Expected:** Either an explicit registry entry (with `inprep: True` if
  treated as upstream-Mathlib-source, or with primary_source_path pointing
  at a cached upstream-Mathlib-commit metadata JSON) OR a textbook-class
  exemption record per Pipeline Invariant #11 / CHECK 19 (textbook
  exemption is for primary_source_path/doi/arxiv all None — but the bibitem
  must still be in the registry).
- **Fix:** Add `'MassotRothgangMacbeth2025'` to CITATION_REGISTRY with
  authors / title / a stable Mathlib-commit URL or arXiv ID. Cache an
  upstream metadata snapshot at e.g.
  `Lit-Search/Phase-6f/primary-sources/MassotRothgangMacbeth2025.json`.
- **Cache:** fresh-fetch (skipped — registry-absent, no fetch protocol applies)

### 1.2 — 🔴 BLOCKER — bibkey `Gouezel2025` absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:1230` bibitem, L209/L1215 cites
- **Observed:** Cites Gouëzel "Riemannian vector bundles in Mathlib4,
  Mathlib4 commit 8850ed93, March 2026" — bibkey not in registry.
- **Evidence:** Registry grep empty.
- **Expected:** Registry entry + cache.
- **Fix:** Mirror the fix for 1.1.
- **Cache:** fresh-fetch (skipped — registry-absent)

### 1.3 — 🔴 BLOCKER — bibkey `Gouezel2024LieBracket` absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:1282` bibitem, L620 cite
- **Observed:** Cites Gouëzel "Lie brackets of vector fields on manifolds
  in Mathlib4, 2024–2026" — bibkey not in registry.
- **Evidence:** Registry grep empty.
- **Expected:** Registry entry + cache; load-bearing for the cyclic-Jacobi
  derivation in §9 and the W8-S3 wave-headlines in §8.
- **Fix:** Add registry entry pointing at the Mathlib
  `Geometry/Manifold/VectorField/LieBracket.lean` upstream file at
  commit 8850ed93.
- **Cache:** fresh-fetch (skipped — registry-absent)

### 1.4 — 🔴 BLOCKER — bibkeys `KobayashiNomizu1963` and `Klingenberg1995` absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:1264, 1276` bibitems; KobayashiNomizu1963
  cites at L283, L298, L946; Klingenberg1995 cite at L594.
- **Observed:** Both classical-textbook bibitems are present in
  the bibliography but neither key appears in CITATION_REGISTRY.
- **Evidence:** `grep -nE "'(KobayashiNomizu1963|Klingenberg1995)'"
  src/core/citations.py` returns empty; no entries in
  `Lit-Search/**/primary-sources/`. By contrast `Wald1984` IS in the
  registry (line 2607) with `primary_source_path` and DOI — so paper44
  is inconsistent with how it treats the same class of textbook source.
- **Expected:** Both must be in the registry. Pipeline Invariant #11's
  textbook-exemption (added in Phase 6i Wave 6) only exempts
  `primary_source_path/doi/arxiv` from being non-None — it does not
  exempt the bibkey from registry presence.
- **Fix:** Add both with `inprep: False`, ISBN, publisher; for
  KobayashiNomizu1963 add the Wiley-Interscience ISBN; mirror the
  `Wald1984` registry entry shape (DOI for U.~Chicago Press electronic
  edition); for Klingenberg add the de~Gruyter Studies in Mathematics
  vol.~1 ISBN.
- **Cache:** fresh-fetch (skipped — registry-absent)

### 1.5 — 🔴 BLOCKER — bibkeys `Roehm2026Wave6f`, `Roehm2026Wave6g`, `Roehm2026Pipeline` absent from CITATION_REGISTRY

- **Gate:** CitationIntegrity
- **Location:** `paper_draft.tex:1237, 1244, 1251` bibitems; cites at
  L118 (6f, 6g) and L1069 (Pipeline).
- **Observed:** All three are project-internal "in preparation" companion
  papers, but absent from CITATION_REGISTRY.
- **Evidence:** Registry grep returns
  `Roehm2026Wave1/Wave4/Wave5/LinearizedEFE` — Wave6f/Wave6g/Pipeline
  are missing. Comparator: `Roehm2026Wave1` is in the registry at
  line 2427 with `inprep: True`.
- **Expected:** Three new entries with `inprep: True`,
  `primary_source_path: None`, `doi: None`, `arxiv: None` — the standard
  in-prep self-cite shape per the schema docstring at the top of
  `citations.py`.
- **Fix:** Mechanical add of three registry entries.
- **Cache:** N/A (in-prep self-cite)

### 4.1 — 🔴 BLOCKER — abstract count "forty-four substantive theorems" contradicts §10.2 "thirty-three substantive theorems across five modules"

- **Gate:** CrossPaperConsistency (intra-paper) / CountFreshness
- **Location:** `paper_draft.tex:136` (abstract) vs `paper_draft.tex:1124-1126`
  (§10.2 strengthening-cuts subsection)
- **Observed:** Abstract: "the library ships forty-four substantive
  theorems across seven modules". §10.2: "After the cuts the library
  ships **thirty-three substantive theorems across five modules**".
  These cannot both be true.
- **Evidence:** §10.2 is the W7+W8 Sessions 1-3 closure paragraph and was
  the correct count at that snapshot; abstract was updated for W8 sessions
  4+5 but §10.2 was not. Ground-truth count from
  `grep -cE "^theorem |^lemma " lean/SKEFTHawking/{LorentzianMetric,
  RiemannianConnection,RiemannCoordinate,RiemannDifferentialBianchi,
  BundleRiemannAux,BundleRiemann,LeviCivita}.lean` minus the seven
  `True := trivial` markers gives **45** (5+6+8+8+7+7+4), not 44 nor 33.
- **Expected:** Both numbers reconciled to the ground-truth 45 (or 44 if
  the paper deliberately excludes the `IsLeviCivita` structure or one
  `_apply`/section pair).
- **Fix:** Recount programmatically and update both the abstract and §10.2.
  The §10.2 paragraph as written is now stale — it claims a five-module /
  thirty-three-theorem state that no longer matches the seven-module
  shipped library.
- **Cache:** N/A

### 5.1 — 🔴 BLOCKER — three independent "first formalization in any proof assistant" claims without an exhaustive prior-art search

- **Gate:** NarrativeGrounding (first-claim sub-class)
- **Location:** `paper_draft.tex:85` ("To our knowledge no proof assistant
  has previously formalized any of these"); L186 ("first
  signature-distinguishing falsifier we are aware of in any proof
  assistant"); L766-768 ("To our knowledge no proof assistant has
  previously formalised cyclic Jacobi for the manifold Lie bracket");
  L951-953 ("To our knowledge no proof assistant has previously
  formalised bundle-level Levi-Civita uniqueness via the substantive
  Koszul-bilinear-form derivation"); L1157-1164 (Coq/Isabelle/HOL Light
  comparison paragraph).
- **Observed:** Five distinct first-claim statements. The
  Coq/Isabelle/HOL-Light/HOL4/Mizar/Agda comparison paragraph (L1157-1164)
  is anecdotal — it asserts "HOL Light's geometric-algebra library
  provides Riemannian inner-product spaces but no Christoffel/connection.
  Isabelle's AFP has nothing in this space. Coq's MathComp has neither
  Riemannian nor Lorentzian metric infrastructure. PhysLean ports physics
  formulas but has no curvature library." but cites no AFP entry IDs, no
  Mathcomp-Analysis search, no HOL Light Multivariate index lookup, no
  Mizar MML search, no Agda standard-library + agda-categories search.
- **Evidence:** WebSearch on "Lean Mathlib Levi-Civita Christoffel
  formalization Koszul" / "Coq mathcomp Riemannian geometry Christoffel
  formalization" / "Isabelle AFP differential geometry connection
  curvature formalization" returned no positive prior-art matches but
  also did not exhaustively cover Mizar / HOL4 / Agda / Lean3-archive /
  Coq-PhysLean predecessors / Coq-MathComp-Analysis / mathlib-archive.
- **Expected:** Either (a) per the agent spec, "REQUIRED if you don't find
  anything but haven't searched exhaustively" — five first-claims need
  an explicit per-system search log, or (b) downgrade prose to "first
  formalization in Lean we are aware of" (narrower claim) at all five
  sites.
- **Fix:** Run a per-system search (Mizar MML, HOL4 examples/, AFP entries
  catalogued under "Mathematics/Geometry", Agda's agda-categories +
  agda-unimath). Document findings in a `qi-firstclaimverification`
  cluster file; ship the search log alongside the paper. If any prior
  art found, downgrade the claim. The paper has TWO falsifiable
  claims (cyclic-Jacobi for `mlieBracket`, bundle-level Levi-Civita
  uniqueness via Koszul-bilinear-form) plus a third (Riemannian-vs-
  Lorentzian signature falsifier) plus the broad "any of these"
  abstract claim — each needs documentation.
- **Severity rationale:** BLOCKER (not REQUIRED) because **five** first-claims
  shipped together raises the qi-firstclaimverification ceiling above
  what the per-system anecdotal paragraph can support; per the agent
  spec a single un-verified first-claim is REQUIRED, but the
  multiplicative effect across five claims plus the existence of a
  one-paragraph dismissal of every other proof assistant pushes this
  to BLOCKER.

### 7.1 — 🟡 REQUIRED — count-literal "forty-four substantive theorems across seven modules" disagrees with ground-truth count

- **Gate:** CountFreshness
- **Location:** `paper_draft.tex:135-138` (abstract)
- **Observed:** "library ships forty-four substantive theorems across
  seven modules"
- **Evidence:** Computed `grep -cE "^theorem |^lemma "` minus `True :=
  trivial` markers across the seven new modules:
  LorentzianMetric=5, RiemannianConnection=6, RiemannCoordinate=8,
  RiemannDifferentialBianchi=8, BundleRiemannAux=7, BundleRiemann=7,
  LeviCivita=4. Total = **45**. The paper says 44 (off by one).
- **Expected:** Either 45, or, if the paper excludes one structural
  declaration (e.g., the `IsLeviCivita` structure on
  `LeviCivita.lean:214` is a `structure`, not a theorem), document the
  exclusion convention explicitly.
- **Fix:** Count via `scripts/validate.py --check counts_fresh` if it
  covers the 6f/8 modules, or recount manually and update the abstract
  literal. Also rewrite §10.2 (see Finding 4.1).
- **Severity rationale:** Off-by-one on a single literal is REQUIRED-tier
  per agent spec class 7. It compounds with Finding 4.1 (which is
  intra-paper and gets BLOCKER severity).

### 6.1 — 🔵 RECOMMENDED — undisclosed `(2 : 𝕜) ≠ 0` hypothesis on `leviCivita_unique_of_isLeviCivita` in §10.4 prose

- **Gate:** AssumptionDisclosure
- **Location:** `paper_draft.tex:935-944` (composition uniqueness theorem)
- **Observed:** §10.4 prose acknowledges the `(2 : 𝕜) ≠ 0` hypothesis
  ("two connections satisfying the same Koszul identity differ by an
  element annihilated by 2, which is 0 iff char(𝕜) ≠ 2"). However,
  the abstract (L77-85 enumerating the LeviCivita.lean deliverable) and
  the discussion of follow-up work (§13) do NOT mention this
  characteristic-2 restriction. A reader who scans abstract + §13 will
  miss the restriction.
- **Evidence:** Lean source at `lean/SKEFTHawking/LeviCivita.lean:366`
  carries `mul_left_cancel₀` discharge requiring `(2 : 𝕜) ≠ 0`; this is
  load-bearing.
- **Expected:** Either a parenthetical "(over a base field of
  characteristic ≠ 2)" in the abstract enumeration of the LeviCivita.lean
  deliverable, or a one-sentence acknowledgement in the discussion
  section.
- **Fix:** Add "over a base field of characteristic ≠ 2" to the abstract
  bullet describing the Koszul-bilinear-form derivation in LeviCivita.
- **Severity rationale:** Standard mathematical practice in
  pseudo-Riemannian geometry is to assume char≠2 implicitly, so RECOMMENDED
  rather than REQUIRED. Not a submission blocker.

## QI Candidate (optional)

**qi-bibkey-registry-absence-on-publication-day**: paper44 was shipped
2026-04-30 with **eight load-bearing bibkeys absent from
CITATION_REGISTRY** (`MassotRothgangMacbeth2025`, `Gouezel2025`,
`Gouezel2024LieBracket`, `KobayashiNomizu1963`, `Klingenberg1995`,
`Roehm2026Wave6f`, `Roehm2026Wave6g`, `Roehm2026Pipeline`). Phase 6i
Wave 1 closed `qi-citationintegrity` via the Primary-Sources Cache
Rollout, but the gating mechanism evidently did not fire on paper44 —
either Stage 13 was not invoked at ship time, or the registry-absence
check (`scripts/extract_missing_bibkeys.py` per Wave-1 memory) was
not re-run after the paper draft landed. This is not a per-paper
finding; it is a pipeline gap (Stage 13 reflexive check should be
gated on registry-completeness for every bibkey appearing in the
target draft, not only on already-cached ones). Recommend:
`scripts/validate.py --check bibkey_registry_complete` that walks
every `\bibitem{key}` in every `papers/paper*_*/paper_draft.tex` and
fails if `key not in CITATION_REGISTRY`.
