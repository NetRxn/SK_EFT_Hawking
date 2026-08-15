# Bundle L3 — Change Log

_Initial bookkeeping created 2026-05-01T04:18:23Z by `scripts/bundle_source_manifest.py`. Append history accumulates as `scripts/bundle_append.py` invocations land._

## 2026-05-01 — Lift-letter from `paper27_bh_thermodynamics_four_laws` (§1)

- Source title: BCH four laws by regime
- Lift action: Lift-letter
- Insertion point: §1
- Stage-13 redo required: yes
- Notes: Initial lift: paper27 → L3 PRL splash (BCH four-laws regime partition + sign-flip of dT_H/dt; Phase 6a W5; ships first wave with L1)

## 2026-05-06 — Lift-section from `_phase6n_W2a_lean_only` (§3)

- Source title: Glorioso-Liu axiomatic skeleton
- Lift action: Lift-section
- Insertion point: §3
- Stage-13 redo required: yes
- Notes: D.2 absorption: Phase 6n W2a Glorioso-Liu axiomatic skeleton (Glorioso_Liu_local_second_law cross-ref upgrade only; no prose change)

## 2026-08-15 — Full Stage-10 redraft (manuscript replaced, not edited)

- Lift action: Redraft (no new source registered; substrate unchanged)
- Stage-13 redo required: yes
- Sections: the manuscript was re-outlined from the charter rather than
  carried forward. New spine: Introduction / The critical mass / One
  substrate, both branches / The two branches and the criterion / What
  would refute this / Discussion. The former standalone "Four laws by
  regime" section was compressed to a scope paragraph inside the criterion
  section, after a read-through found it advanced the argument by zero
  steps while occupying a fifth of a four-page Letter.
- Substantive changes:
  - `M_c` is now presented via the identity `G_N^emerg · M_c = 1/Lambda_UV`
    (exact, verified symbolically and numerically against
    `src/bh_thermodynamics/regime_classifier.py::M_c_default`), replacing
    the prior "project-original dimensional ansatz, no derivation" framing.
    The residual free choice (the order-unity coefficient) is stated.
  - The cooling branch is re-attributed. Balbinot et al. compute a sonic
    hole at constant sound speed and explicitly defer the Bose--Einstein
    condensate; the prior "BEC-acoustic" framing was a misattribution.
  - Jacobson--Volovik 1998 is moved from the heating contrast case to the
    cooling branch, matching that paper's Eq. (5.7) and its own Discussion.
    The thin-film Jacobson--Koike texture remains the heating contrast.
    One superfluid hosting both branches is now the motivating argument.
  - The second-law slot is described as a recorded hypothesis on a supplied
    entropy-current divergence, not as a derivation; the "without invoking
    pointwise NEC" attribution to Glorioso--Liu is dropped as vacuous.
  - The zeroth- and third-law absence is stated as a present-tense fact.
  - Abstract rewritten to 594 characters for the PRL limit (prior: ~1900).
  - Reall 2024 dropped from the reference list with the third-law detour;
    Sakharov 1968, Adler 1982, Visser 2002 and Finazzi--Liberati--Sindoni
    2012 added.
- Compile: 4 pages, 0 TeX errors, 0 unresolved references, 2679 words plus
  one figure against a 3750 word-equivalent ceiling.
- Findings filed: `papers/AutomatedReviews/2026-08-15-l3-stage10-redraft/L3.md`
  (2 blocker, 5 required, 8 recommended). The two blockers are the
  primary-source misreadings above; both propagate beyond L3.
