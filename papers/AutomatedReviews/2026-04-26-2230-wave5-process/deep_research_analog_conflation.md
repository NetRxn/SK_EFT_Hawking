---
paper: process
reviewer: wave5-deep-research-conflation-audit
model: claude-opus-4-7
review_date: 2026-04-26T22:30:00Z
readiness_gates_version: 1
---

# Wave 5 process audit — deep research conflated two analog systems and shipped the wrong primary-source anchor

## Summary

The Phase 6a Track C Wave 5 deep-research return
(`Lit-Search/Phase-6a/6a-BCH four-laws regime partition for emergent-gravity
ADW black holes — a Wave 5 literature survey.md`) cited Jacobson–Koike 2002
Eq. (13) as the structural anchor for the ADW-extremality regime "BHs cool
toward extremality" claim, supplying the functional form
`T_H(M) = T_H,0·(1 − (M/M_c)²)`. Wave 5 shipped end-to-end with this
framework: a Lean module (`BHThermodynamicsFourLaws.lean` — 18 thms,
`H_RegimePartition.slope_sign_below: M < M_c → 0 < slope`), a Python
subpackage, paper27, a figure, 51 tests, and 26 new citations.

Stage 9 figure review caught a slope-sign annotation contradicting the
plotted curve. Tracing back to primary sources revealed:

1. **Jacobson–Koike 2002 (cond-mat/0205174) Eq. (13)** verbatim:
   `T_H(v) = T_H(0)·(1 − v²/c_⊥²)` where `v` is the moving-domain-wall
   soliton velocity in `³He-A`. `dT_H/dv < 0` monotonically on
   `(0, c_⊥)`. Evaporation slows the wall (`v ↓`), so `T_H ↑`
   ("**heats** as evaporates" — same direction as Schwarzschild).

2. **Jacobson–Volovik 1998 (cond-mat/9801308) §VIII** prose claim
   "cools as it evaporates and approaches an extremal black hole" is
   **inconsistent with the same paper's own equations** — back-reaction
   slows the soliton, the formula gives `T_H ↑`, but the prose says
   cooling. Loose / wrong prose, not a real cooling result.

3. **The actual project anchor** `src/wkb/backreaction.py` (which the
   Wave 5 deep research did not reference, but the Phase 6a roadmap
   cited as a prerequisite) implements `κ(t) ~ κ_0 · exp(-t/τ_cool)`
   for **BEC-acoustic black holes**, citing **Balbinot, Fagnocchi,
   Fabbri, Procopio (gr-qc/0405098 = PRD 71, 064019, 2005)**. This is
   a structurally **different** analog system from JK 2002.

4. **Balbinot 2005 §"The fate of the acoustic black hole"** verbatim:
   "the emission temperature of the sonic black hole decreases in
   time. Unlike Schwarzschild black holes, the sonic black hole gets
   cooler as it evaporates." `t ~ 1/T³` asymptotically. Evaporation
   reaches `T → 0` in **infinite** time (analog of near-extremal
   Reissner–Nordström). And critically: "**other analog models like
   a thin film of ³He-A with a moving domain wall [Jacobson] seem to
   show a non-vanishing end-temperature of the evaporation
   process**" — Balbinot **explicitly contrasts** BEC-acoustic
   (cools) with `³He-A` moving-wall (does NOT cool).

So the Wave 5 deep research **conflated** the two analog systems,
attributing the cooling-toward-extremality behavior to JK 2002 (which
does not have it — see Balbinot's own contrast statement) instead of
Balbinot 2005 (which has it explicitly). The Lean module imported the
wrong functional form (`T_H_schottky`) on the wrong primary-source
basis. The shipped `H_RegimePartition.slope_sign_below: M < M_c → 0 <
slope` is **internally inconsistent with the Schottky form** in the
same module (which gives `dT/dM < 0` everywhere on `(0, M_c)`).

This was caught only because Stage 9 reviewer flagged the figure
annotation; without that flag the inconsistency would have shipped to
external review. The error survived Stages 1–12 of the pipeline (Lean
build clean, validate.py 22/22, 51 tests pass, paper compile clean) —
no automated check could detect a primary-source-misattribution +
within-module-inconsistency conjunction.

## QI Candidate

This is a **process-level** failure mode not currently surfaced in
`docs/QI_REGISTER.md`. Recommend new QI item:

**id:** `qi-deep-research-analog-conflation`
**Gate affected:** AssumptionDisclosure / CitationIntegrity (cross-cuts
both — the cited primary source does not support the claim, and the
underlying assumption (which analog system the wave applies to) is
undisclosed).
**Severity:** critical (allowed a correctness violation to ship
end-to-end through the pipeline).
**Pattern summary:** Deep research returns sometimes cite multiple
analog/parallel physical systems (e.g., `³He-A` moving wall vs
BEC-acoustic vs lattice spin-models), and may attribute a behavior or
functional form to the wrong system. The pipeline has no automated
check that the primary-source citation actually supports the claim
the wave makes; primary-source PDF verification is currently human-
or LLM-discretionary.
**Mitigations to consider:**
1. **Pre-integration verification step.** Before integrating a deep
   research return into a wave plan, fetch (TeX or PDF) every
   load-bearing primary source it cites, locate the relevant equation
   verbatim, confirm functional form, sign, and context match the
   wave's planned usage. Save TeX/PDF to
   `Lit-Search/Phase-{N}/primary-sources/`. Document mismatches
   inline in the wave plan.
2. **Cross-check against existing project anchors.** Wave 5 had an
   existing project-side computation
   (`src/wkb/backreaction.py` citing Balbinot 2005); the deep
   research did not reference it. Pipeline could enforce: when a
   wave's roadmap entry lists a Python module as a prerequisite,
   the wave plan must cite that module's primary-source attributions.
3. **Within-module consistency check.** A Prop bundle
   (`H_RegimePartition.slope_sign_below: M < M_c → 0 < slope`)
   asserting a sign that contradicts the same module's explicit
   functional form (`T_H_schottky = T_H,0·(1−(M/M_c)²)` whose
   derivative is negative on the same domain) is mechanically
   detectable. Could be a `validate.py` check via SymPy
   differentiation of named functional forms in the module + Prop
   sign-claim cross-check.

## Findings

### 1.1 — 🔴 BLOCKER — Wrong primary-source anchor in Wave 5 deep research (CitationIntegrity + AssumptionDisclosure cross-class)

- **Gate:** CitationIntegrity / AssumptionDisclosure
- **Location:** `Lit-Search/Phase-6a/6a-BCH four-laws regime partition for emergent-gravity ADW black holes — a Wave 5 literature survey.md` §3, §6, §7; `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean` lines 299–414; `papers/paper27_bh_thermodynamics_four_laws/paper_draft.tex` (entire regime-partition section); `src/bh_thermodynamics/schottky_saturation.py`; `src/core/visualizations.py:8485`.
- **Observed:** Deep research §3 lists "Rank 1 — M/M_c, the analog mass to a critical/extremal mass" with Jacobson & Koike (cond-mat/0205174) as the explicit primary anchor for "**T_H(v) = T_H(0)(1 − v²/c_⊥²)**" + "the analog BH **cools** toward analog-extremality". Verbatim TeX-source verification of cond-mat/0205174 (saved at `Lit-Search/Phase-6a/primary-sources/jk0205174/bhbu.tex`, equation `\label{E:TH}` at line 597) confirms the formula but contradicts the cooling claim: §5 `dE/dt = -bv^n` (line 659) gives evaporation = velocity decrease, hence `T_H ↑`. Verbatim verification of cond-mat/9801308 (Jacobson-Volovik 1998 §VIII at `Lit-Search/Phase-6a/primary-sources/jv9801308/EventHorIn3He13Unix.tex` line 707-713) shows the same prose-vs-math discrepancy. Verbatim verification of gr-qc/0405098 (Balbinot 2005 at `Lit-Search/Phase-6a/primary-sources/balbinot/acusticpap.tex` Eq. Tsonic) shows the cooling-toward-extremality functional form **does** exist for the **BEC-acoustic** system (`T(t) = (ℏc/2π)·κ·[1 − (563/720π)·ε·κ³·c·A_0·t]` decreasing in time, asymptotic extremality `t ~ 1/T³`), and Balbinot **explicitly** contrasts BEC-acoustic with `³He-A` moving wall as having the opposite behavior. Wave 5's anchor citation is the wrong analog system.
- **Severity:** critical
- **Status:** open (remediation in progress: Wave 5 full rewrite around Balbinot 2005 — see `temporary/working-docs/wave5_rewrite_plan.md`)

### 1.2 — 🔴 BLOCKER — Within-module sign inconsistency (LeanProofSubstance / structural)

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHThermodynamicsFourLaws.lean:299` (`T_H_schottky T_H0 M M_c := T_H0 * (1 - (M/M_c)^2)`) vs line 413 (`slope_sign_below: b.M < M_c p → 0 < slope`).
- **Observed:** The shipped `T_H_schottky` is monotonically **decreasing** in M on `(0, M_c)` (`dT/dM = -2 T_H,0 M / M_c² < 0`). The shipped `H_RegimePartition.slope_sign_below` asserts `slope > 0` on the same domain `M < M_c`. Both ship under the same module-level docstring claiming the slope statement is "rooted in Jacobson-Koike Eq. (13)". The Lean theorem and the Lean function are mutually inconsistent at the only published functional form they could share.
- **Severity:** critical
- **Status:** open (remediation: full rewrite per 1.1)

### 1.3 — 🟡 REQUIRED — Pipeline gap: no automated check for primary-source-vs-claim consistency

- **Gate:** ProcessHealth (new)
- **Location:** `scripts/validate.py` — current 22 checks; no check verifies that a load-bearing primary-source citation actually supports the claim attributed to it. CHECK 14 (`paper_provenance`) verifies numerical claims trace to computations within 0.5%, but does not verify primary-source claim attribution.
- **Observed:** This wave's failure shipped past every internal check. Stage 13 adversarial-reviewer would have caught it (the slope-sign-vs-formula inconsistency is exactly the kind of thing it audits) but Stage 13 was not yet run on paper27. Stages 1–12 are blind to this class.
- **Severity:** major (as a process gap; not paper-local)
- **Status:** open

## Recommendations

1. **Adopt the verified-PDF pre-integration step** as a soft pipeline rule for every load-bearing deep-research integration: every cited primary source in the deep-research return that grounds a load-bearing claim must be fetched (TeX preferred, PDF fallback), the relevant equation/text quoted verbatim into the wave-plan working doc, and saved alongside the deep-research return at `Lit-Search/Phase-{N}/primary-sources/`. Make this concrete by writing it into `WAVE_EXECUTION_PIPELINE.md` Stage 1's "Deep Research Reconciliation Protocol" section.
2. **Cross-check existing project anchors.** When a roadmap wave's prerequisites include an existing Python module, the deep-research return MUST audit that module's primary-source attributions (and the wave plan MUST inherit them) before introducing new analog systems.
3. **Add `validate.py` check** for within-Lean-module sign consistency: when a Prop bundle asserts a sign-of-derivative claim about a named function, mechanically differentiate the function (SymPy) and check the asserted sign matches over the asserted domain. Tractable for any closed-form `T_H_*` def.
4. **Run Stage 13 adversarial-reviewer on every newly-shipped wave before declaring "ship end-to-end"** — currently policy is user-triggered. Recommend at least automated invocation on first-time wave shipments.
