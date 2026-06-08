---
paper: paper10_modular_generation
reviewer: adversarial-reviewer
model: claude-opus-4-8
review_date: 2026-06-08T23:14:39Z
readiness_gates_version: 1
invocation: re-review (post-remediation of 2026-06-08-2242 report)
---

# Adversarial Review (re-run) — paper10_modular_generation

## Summary

Re-review after author remediation of the 2026-06-08-2242 report (8 findings: 4 BLOCKER,
3 REQUIRED, 1 RECOMMENDED). **All 8 prior findings are RESOLVED; zero regressions; no new
issues.** The paper now frames `16 ∣ σ` as the unconditional kernel-pure theorem
`SmoothSpinManifold4.rokhlin`, cites `sixteen_convergence_unconditional`, correctly states that
`ChangeOfRings.lean` *documents but does not machine-prove* the Hom-tensor adjunction (attributed
to Weibel Thm 2.6.1, now in CITATION_REGISTRY as a textbook-exempt entry), scopes the `A(1)` Ext
computation as independent corroboration rather than the live mechanism, replaced all stale count
literals with `\input`-ed `counts.tex` macros (11039/853/0), dropped the "well-motivated physics
axiom" clause, and pins toolchain v4.29.1 / Mathlib 5e932f97. The cross-paper contradiction with
D2 is gone — both papers now describe `16 ∣ σ` identically. **New finding counts: 0 BLOCKER,
0 REQUIRED, 0 RECOMMENDED.**

## Disposition of prior findings

### 5.1 — Paper framed `16 ∣ σ` as undischarged hypothesis / external input — **RESOLVED**

- The "16 Convergence" section is rewritten. `paper_draft.tex:226-244` now states "The signature
  half of this convergence is now an unconditional formally-verified theorem," describes
  `SmoothSpinManifold4` + the single topological factor `2 ∣ σ/8`, and proves
  `SmoothSpinManifold4.rokhlin : 16 ∣ σ` "as a kernel-pure theorem (standard axioms only; no
  global Rokhlin hypothesis, no new axiom)." Verified against
  `lean/SKEFTHawking/SpinRokhlinInterface.lean:73-77` — exact match to source docstring.
- The Conclusions/`16∣σ` framing at `:280-287` matches: "a proved kernel-pure theorem
  (`SmoothSpinManifold4.rokhlin`), not an assumed hypothesis and not an axiom."
- The prior "three standard textbook topology results (ko cohomology, ASS convergence, ABP
  splitting)" sentence is gone; the abandoned `Ω^Spin_4 ≅ ℤ` route is now explicitly disavowed
  at `:349-352` ("deliberately not used … would be circular").
- The residual `8 ∣ σ` (van der Blij) and `2 ∣ σ/8` (topological factor) framing at `:236-240`
  matches the source: `RokhlinHMRankFour.lean:599 eight_dvd_latticeSig`,
  `:604 sixteen_dvd_latticeSig`, `:595 hasIsotropicVector` all exist and are substantive
  (Chevalley–Warning / Hensel / Hilbert-reciprocity bodies); modules carry no `sorry`/`axiom`/
  `native_decide` (grep clean).

### 5.2 — `ChangeOfRings.lean` placeholder cited as establishing the isomorphism — **RESOLVED** (special-attention item)

- Independently re-read `lean/SKEFTHawking/ChangeOfRings.lean`: unchanged, still five tautology
  declarations (`hom_tensor_adjunction_dim : rank = rank := rfl`,
  `change_of_rings_ext_dim … := h_ext`, `h2_discharged : True := trivial`,
  `remaining_hypotheses : 4-1=3`, `generation_constraint_status : 7+3=10`). The module does NOT
  machine-prove the adjunction — confirmed.
- The paper's prose now matches that reality. `paper_draft.tex:343-348`: "The change-of-rings step
  uses the Hom-tensor adjunction … a standard algebra fact (Weibel, Thm.~2.6.1~\cite{Weibel1994})
  that reduces the full Adams spectral sequence computation to the finite $A(1)$ computation;
  `ChangeOfRings.lean` documents this isomorphism but does not itself supply a machine-checked
  proof of it." This is an accurate, non-overclaiming statement. The prior assertion
  ("establishes the change-of-rings isomorphism as pure algebra") is gone.
- `Weibel1994` resolves in `src/core/citations.py:5089-5104` CITATION_REGISTRY with
  `doi=None, arxiv=None, primary_source_path=None` (textbook exemption), `used_in` includes
  paper10, notes document the textbook-exemption basis and the Thm 2.6.1 citation. The `\bibitem`
  at `:426-428` matches.

### 5.3 — Abstract overstated Ext computation as closing the "why 16" question — **RESOLVED**

- Abstract `:40-42`: the Ext computation now "corroborates the algebraic 'why 16'" as an
  "independent machine-checked Ext computation," after explicitly stating `16∣σ` is "itself an
  unconditional kernel-pure theorem ($8∣σ$ via van der Blij plus the single topological factor
  $2∣σ/8$)." Conclusion `:328-354` ("Independent corroboration") states the unconditional
  derivation "does *not* route through the Adams spectral sequence," the Ext groups are an
  "independent algebraic artifact, not the mechanism behind the live $16∣σ$ result." Correctly
  decoupled.

### 5.4 — "well-motivated physics axiom" clause contradicting zero-axiom claim — **RESOLVED**

- Intro `:80-81` now reads: "Every numerical coefficient is derived from the formalization; the
  generation constraint chain introduces no axioms." The "or enters as a well-motivated physics
  axiom" clause is deleted (grep confirms no remaining instance).

### 6.1 — Cited conditional `sixteen_convergence_full`, hid unconditional companion — **RESOLVED**

- `paper_draft.tex:241-248` now leads with `sixteen_convergence_unconditional`
  (`SpinRokhlinInterface.lean`) as the "headline statement," and correctly characterizes
  `sixteen_convergence_full` (`RokhlinBridge.lean`) as "the older … enumeration over an abstract
  free-integer manifold type that still carries $16∣σ$ as an explicit hypothesis by design; we
  cite the unconditional form for the substantive claim." Verified against
  `SpinRokhlinInterface.lean:82-88` — the unconditional theorem proves the `∀ M, 16 ∣ M.sig`
  conjunct via `fun M => M.rokhlin`.

### 2.1 — Cross-paper contradiction with D2 — **RESOLVED**

- `papers/D2/paper_draft.tex:329-354` ("From assumed hypothesis to a wired theorem") describes
  the identical construct as paper10: `SmoothSpinManifold4.rokhlin : 16 ∣ σ` "a kernel-pure
  theorem (standard axioms only; no global Rokhlin hypothesis, no new axiom)" and
  `sixteen_convergence_unconditional` "reruns the four-16 enumeration with the $16∣σ$ conjunct now
  a theorem rather than an assumed input." Both papers now agree with each other and the codebase.

### 9.1 — Stale count literals — **RESOLVED**

- `paper_draft.tex:7` `\input{../../docs/counts.tex}`. Counts at `:33-34` (abstract) and
  `:310-311` (conclusion) use `\totaltheorems{}` / `\leanmodules{}` / `\axiomcount{}` macros.
  `docs/counts.tex` defines `\totaltheorems{11039}`, `\leanmodules{853}`, `\axiomcount{0}`. The
  hardcoded "2237+/170/1 axiom" literals are gone; "1 axiom" replaced by "0 project-local axioms"
  via macro.

## Class re-scan (current draft)

- **Class 1 (CitationIntegrity):** PASS. New bibkey `Weibel1994` present in CITATION_REGISTRY
  (textbook-exempt, correctly so). 12 bibkeys total; prior 5 arXiv refs verified `match` in the
  2242 run and unchanged (same arXiv IDs in `\bibitem`s). No `wrong_target`/registry-absence
  issues. (Project-wide `citation_primary_sources_present` failure for
  `ChungHajdusekVanMeter2025QNetSimXval` belongs to paper D6 — not attributed here.)
- **Class 2 (CrossPaperConsistency):** PASS — see 2.1. D2 ↔ paper10 Rokhlin framing now identical;
  shared bibkeys (Wang2024 2312.14928, GarciaEtxebarria2019 1808.00009) consistent.
- **Class 3 (LeanProofSubstance):** PASS. Re-read `ChangeOfRings.lean` (placeholder, no longer
  cited as a proof — see 5.2). All other cited theorems substantive: `eight_dvd_latticeSig`,
  `sixteen_dvd_latticeSig`, `hasIsotropicVector` (RokhlinHMRankFour.lean), `SmoothSpinManifold4.rokhlin`,
  `sixteen_convergence_unconditional` (SpinRokhlinInterface.lean), all non-trivial, zero `sorry`/
  `axiom`/`native_decide` in those modules. `A1Ext.ext_dim_n` (`decide`) / `A1Resolution`
  (`native_decide` finite checks) legitimate.
- **Class 4 (ComputationCorrectness):** N/A — formal-Lean + textbook physics only.
- **Class 5 (NarrativeGrounding):** PASS — 5.1/5.2/5.3/5.4 all resolved.
- **Class 6 (AssumptionDisclosure):** PASS — 6.1 resolved; unconditional theorem cited as headline,
  conditional form's explicit hypothesis disclosed.
- **Class 7 (NumericalFreshness):** PASS — 9.1 resolved; macro-driven counts.
- **Class 8 (ProductionRunHealth):** PASS — both figures (`fig73_*`, `fig75_*`) on disk; no
  Monte-Carlo / production-run dependency claimed.

## New issues

None.

## Stage-13 gate

**GREEN.** All prior BLOCKER (4) and REQUIRED (3) and RECOMMENDED (1) findings resolved; no
regressions; no new findings.
