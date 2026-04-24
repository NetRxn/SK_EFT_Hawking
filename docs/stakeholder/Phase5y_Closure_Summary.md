# Phase 5y Closure Summary

**Date:** 2026-04-23
**Status:** CLOSED — no further deep-research rounds, no papers, no
Phase-5y scope continuation.

---

## One-paragraph summary

Phase 5y attempted to formalize and evaluate the Volovik-family
emergent-vacuum frameworks (q-theory, vestigial gravity) as candidates
for the DESI DR2 preferred dark-energy parameter region. After **six
rounds of deep research** (Rounds 3, 4a, 4b, 5 on q-theory realizations;
Rounds H1, H4 on reframe alternatives), the phase returned **five
NO-GO verdicts** plus one original closed-form derivation. The NO-GOs
are structural — grounded in a Gibbs-Duhem obstruction theorem that
applies realization-independently — so **the phase closes terminally**.
The substantive harvest is now formalized in Lean: ~109 new theorems
across 7 new modules + 3 extensions, a classification table, and an
architectural-scoping document. No papers, no community engagement
track, no revival of H3 inflation-era q-dynamics.

---

## What 5y attempted

**Goal.** Determine whether Klinkhamer-Volovik q-theory — a Volovik-school
framework for emergent cosmological constant via self-tuning composite
scalar `q` — can produce the DESI DR2 preferred `(w₀, w_a) ≈ (−0.73, −1.05)`
dark-energy dynamics without 10⁻¹²¹ fine-tuning.

**Sub-goals.** Evaluate four q-theory realizations (4-form, 2-brane,
fermionic-crystal, unimodular); evaluate reframe alternatives
(H1 second-sound graviton; H4 vestigial-gravity effective fluid EOS).

---

## What 5y found

**Round 3 (q-theory → DESI).** NO-GO. Using Volovik's own
explicit vacuum→matter energy-transfer rate (arXiv:2411.01892 Eq. 32),
the model yields `(w₀, w_a) ≈ (−0.685, −2×10⁻¹²¹)` at `T_dS = H/π` and
similar at `T_dS = H/(2π)`. The predicted `w_a` is ~120 orders of
magnitude below the DESI region.

**Round 4a (δq Klein-Gordon extension).** NO-GO. Klein-Gordon mass
`m_δq² = 1/(χ₀ q₀²) ∼ M_Pl²` at natural scales; the suppression
`(H₀/M_Pl)² ∼ 10⁻¹²¹` is the cosmological-constant fine-tuning
rediscovered.

**Round 4b (3-form aether literature sweep).** No new mechanism; the
3-form-aether literature does not provide a route evading the Round 4a
obstruction.

**Round 5 (fermionic-crystal).** NO-GO + strengthened Gibbs-Duhem
theorem. The elasticity-tetrad q-theory (Klinkhamer-Volovik 2019,
arXiv:1812.07046) has q = (1/4) e^μ_a E^a_μ as an algebraic composite,
producing numerically the same `m_δq² ∼ M_Pl²` as the 4-form
realization. The obstruction is realization-independent.

**Round H1 (Kronecker-anomaly second-sound graviton).** NO-GO with
PARTIAL footnote. The mode is not a derived propagating DOF; its decay
channel reduces to q-theory, inheriting the same Planck-scale mass.

**Round H4 (vestigial-gravity EOS).** NO-GO for DESI, PARTIAL for
framework. The derivation produces the first closed-form
`w_vest(τ) = (1 − τ²)/(5τ² − 1)` plus `c_s²(τ) = −(1 − τ²)/(3 − 5τ²)`,
but the natural branch is phantom-today (wrong sign vs. DESI) and
`c_s²(0) = −1/3 < 0` produces catastrophic gradient instability.

---

## What remains valuable

**Formal harvest (Lean).**

- `GibbsDuhemTheorem.lean` — first machine-checked emergent-vacuum
  obstruction theorem. 16 theorems. Lorentz-invariance + Gibbs-Duhem
  equilibrium → `w_vac = −1` identically.
- `QTheoryNoGoTheorem.lean` — instance-of-theorem across all four
  tested KV realizations. 12 theorems. Quantitative `m_δq² ∼ M_Pl²`
  under natural scales.
- `DarkEnergyObstructionPrinciple.lean` — four-factor orthogonality
  principle (H4 EQ.137-138). 8 theorems. Decomposes DESI-reachability
  into Gibbs-Duhem + `c_s² ≥ 0` + `T_c` attractor + MICROSCOPE.
- `DESIComparison.lean` — DESI DR2 preferred region encoded + `w_vac = −1`
  shown to sit outside. 8 theorems.
- `CondensedMatterAnalog.lean` + `VestigialMapping.lean` — Fernandes-Fu
  charge-4e template + H4 §3 dictionary. 18 theorems.
- `VestigialEOS.lean` — H4 closed-form derivation of `w_vest, c_s², ζ_vest`.
  20 theorems. Phantom-today + gradient-instability + DESI-incompatibility
  theorems.
- Extensions to `VestigialGravity.lean` (+7 thms: Z4 symmetry, WEP-violation
  structural lemma), `VestigialSusceptibility.lean` (+8 thms: Kubo + RPA + FDT),
  `TetradGapEquation.lean` (+4 thms: BCS-like T_c, natural-scale obstruction).
- `ClassificationTableDark.lean` — 8 theorems, dark-sector viability
  columns with Gibbs-Duhem / orthogonality flags across the 6 tested
  mechanisms.

**Total Lean harvest:** 109 new theorems, 7 new modules, 3 extensions.
Zero sorry maintained.

**Architectural harvest.**
- `docs/ARCHITECTURE_SCOPE.md` — first explicit predictive-scope
  document for the three-layer architecture. Layer 3 scoped to SM+GR
  sector under tested mechanisms; dark sector out-of-scope under
  Volovik-family obstruction.
- `temporary/working-docs/phase5y_classification_table_dark.md` —
  human-readable classification table.
- Cross-phase integration memos for 5x, 5u, 5d, 5w (companion files).

---

## What 5y does NOT claim

- q-theory is falsified as a vacuum-stability framework (it is not —
  only the late-time dark-energy application is closed; equilibrium
  and inflation-era applications remain open).
- Vestigial gravity is ruled out as a concept (the H4 PARTIAL verdict
  preserves the mathematical framework).
- No emergent dark energy is possible (obstruction is specific to
  Volovik-family mechanisms; entropic/thermodynamic-GR approaches are
  outside the tested scope).
- The three-layer architecture is falsified (only the dark-sector
  predictive claim is scoped out; Layer-3 SM+GR claims are unaffected).

---

## What comes next

**Nothing in 5y.** The phase is closed. Forward motion belongs to:

- **Phase 5u** (polariton Hawking, Tier A) — Paris LKB collaboration
  preparation, unaffected by 5y
- **Phase 5d** (RHMC ADW fermion-bootstrap) — orthogonal physics,
  continues on its own timeline
- **Phase 5w** (graphene Dirac fluid) — orthogonal physics, continues
- **Phase 5x** (dark matter) — does NOT inherit 5y's NO-GO; different
  mechanisms, different obstruction landscape

**If** dark-sector physics reopens later — via unexpected experimental
data, new theoretical hook, or collaborator interest — it would be
scoped as a fresh phase (6y or later), not a 5y revival. The Phase 5y
closure is terminal by design.

---

## Reusable methodology

Phase 5y demonstrated a GO/NO-GO methodology reusable for future
high-leverage program bets:

1. **Write strongest sorry stubs first.** Aristotle-first discipline
   (per `feedback_aristotle_first.md`).
2. **Execute deep-research rounds sequentially.** Six rounds completed;
   each grounded in published source material.
3. **Land structural NO-GO where mathematically appropriate.** Five
   NO-GOs in Phase 5y = structural obstruction.
4. **Harvest formally, not rhetorically.** Lean modules + architectural
   scope, not papers or community outreach.
5. **Close terminally.** No re-scoping, no "trailing round" H3 revival.
   Move on.

This pattern is now part of the program's operational vocabulary.

---

## References

- **Roadmap:** `docs/roadmaps/Phase5y_Roadmap.md` (terminal rev. 2026-04-24)
- **Deep research:** `Lit-Search/Phase-5y/` (6 complete rounds)
- **Formal output:** 7 new Lean modules in `lean/SKEFTHawking/` + 3 extensions
- **Architecture:** `docs/ARCHITECTURE_SCOPE.md`
- **Classification:** `temporary/working-docs/phase5y_classification_table_dark.md`

---

*Terminal closure artifact. Phase 5y executed 2026-04 through 2026-04-23.*
