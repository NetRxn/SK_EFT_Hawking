# P25 finite-tolerance mathematical propagation proposal

Scratch-only author package for ROOT intake. Target source is `papers/paper25_gravitational_waves/paper_draft.tex` in `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/.publication-l1-checkpoint-20261103`, packet HEAD `3c56f0c6d6c0785f2b9958ec9c136d8dd293a3d8`. No tracked edits, notebook writes, Git mutations, Lean calls, slots, builds, scientific pipeline runs, physical attribution work, or compile were performed.

## Deliverables

- `paper_draft.tex`: complete proposed P25 TeX, SHA256 `4731b7629188131385fb309ecdd58f65fbc30bf8062d73785a5af1479ef1ab20`.
- `paper_draft.patch`: exact unified original-to-proposed patch, with repository-relative target path.
- `edits.json`: every before/after replacement and original line number.
- `statement_provenance.json`: actual extracted types for every GravitationalWaves declaration named in the original P25 manuscript and represented in the supplied actual-declaration evidence. Names/types are copied from the supplied extractor receipt, not inferred from grep or comments.
- `controls.py`, `controls.log`, `math_controls.json`: scratch-only assertions, original RED/proposed PASS evidence, and exact high-precision interval arithmetic. These are intake evidence, not a new gate or harness.
- `propose.py`: exact scratch transformation recipe, guarded by the source SHA256.

The tracked source SHA256 remains `75a84e6136717a2db4158f9b35c51b9026563a1869b48c3243a01abcbbf27048`, checked after proposal and controls.

## Direct sources and carrier audit

All paths below are relative to the checkpoint unless explicitly absolute. The author packet was read first at `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/l1-source-math-propagation-author-r1-20261105.json`. The complete contributing P25 TeX, current L1 TeX, the supplied `papers/AutomatedReviews/2026-11-05-l1-current-claims/r1/lean_actual_declarations.json`, and actual definitions/statements/proofs in `lean/SKEFTHawking/GravitationalWaves.lean` were consulted. Paper-authoring SKILL.md and its mandatory prohibited-patterns.md and dispatch-brief.md were read in the primary checkout. Workspace CLAUDE.md, owning AGENTS.md/CLAUDE.md, and pipeline orientation were also consulted.

The load-bearing carriers are real numbers and predicates over them. In actual Lean source:

- Lines 123, 138: `c_GW (χ_vest c : ℝ) : ℝ := c * Real.sqrt χ_vest`; `c_GW_deviation (χ_vest : ℝ) : ℝ := Real.sqrt χ_vest - 1`.
- Lines 185–188: `tolGW170817 : ℝ := 3e-15`; `LigoSatisfied (δ : ℝ) : Prop := |δ| ≤ tolGW170817`.
- Lines 201–204: for nonnegative real susceptibility, compatibility iff `(1-tolGW170817)^2 ≤ χ_vest ∧ χ_vest ≤ (1+tolGW170817)^2`.
- Lines 151–152: for `c ≠ 0`, `(c_GW χ_vest c - c) / c = c_GW_deviation χ_vest`.
- Lines 256 and 276: concrete failures at the two natural endpoints; lines 429–452: endpoint-only existential exclusion and the nonzero-c relative-deviation form. They do not quantify over microscopic actions, mode dynamics, or matter couplings.
- Lines 368–385: exact width `4 * tolGW170817`, natural range width `99 / 10`.
- Lines 472–475: `H_VestigialModeIsGraviton (χ_vest : ℝ) : Prop := 0 < χ_vest ∧ LigoSatisfied (c_GW_deviation χ_vest) ∧ |c_GW_deviation χ_vest| < 1 / 2`.
- Lines 509 onward: `¬ H_VestigialModeIsGraviton (1 / 4)`; the proof uses the third conjunct to contradict `|-1/2| < 1/2`. The actual theorem asserts bundle failure, not conjunct independence or exclusive failure.

The supplied declaration receipt confirms these actual types. This package neither searches for missing Lean statements nor claims any Lean declaration or physical derivation is absent. `statement_provenance.json` contains the full actual extracted types, including all preserved named theorems used elsewhere in P25.

## Edit-by-edit provenance

Original P25 line positions for each replacement are recorded exactly in `edits.json`. Current L1 references below refer to the read checkpoint text, not an independent new scientific source.

| Replacement keys in edits.json | Current L1 provenance | Actual mathematical basis |
| --- | --- | --- |
| abstract-finite-window; theorem-A-interpretation; discussion-finite-tolerance; conclusion-finite-window; conclusion-finite-interval | L1 258–261 distinguishes exact zero from finite tolerance; 339–350 expands endpoints and rejects exact-unity/generic-UV inference | Actual `c_GW_match_iff_chi_close_to_one` and `c_GW_deviation_zero_iff_chi_one`; algebraic midpoint `1+τ²`, half-width `2τ`. These midpoint formulas are algebraic consequences, not a newly claimed Lean theorem. |
| abstract-endpoint-ratios; caption-finite-window-endpoints | L1 225–235 gives different lower/upper endpoint ratios; 266–285 caption retains a finite unresolved interval | Actual `natural_lower_violates_ligo`, `natural_upper_violates_ligo`; numerical controls give `2.2792407799…e14` and `7.2075922006…e14`. Figure path unchanged. |
| abstract-quarter; bundle-introduction; bundle-redundancy; falsifier-header; quarter-both-fail; conclusion-quarter | L1 286–320 explicitly preserves the recorded Prop, notes P2⇒P3′ and describes both failures at the quarter point | Actual Prop above; `τ=3e-15 < 1/2`; at χ=1/4, deviation=-1/2 fails both `|δ|≤τ` and `|δ|<1/2`, while positivity holds. |
| abstract-interval-prior; intro-width-prior; bundle-width-probability | L1 109–114 and 317–320 separate relative width from probability, with a uniform-prior example | Actual width theorem gives `4τ`; uniform density on `[0.1,10]` gives probability `4τ/9.9`. No prior-independent probability follows. |
| intro-conditional-constraint; comparison-endpoints-only; comparison-no-selection | L1 105–114, 321–334 and 425–438 constrain a free susceptibility and preserve the interior interval | Endpoint-only theorem statements, positive compatible interval, free real parameter carrier; no generic UV exclusion or parameter-selection theorem follows. |
| downstream-no-false-dichotomy | L1 145–155 allows a mechanism selecting within the compatible interval or modifying the identification | The finite interval contains χ=1 and other values. The observational cap alone does not require exact unity or dictate a distinct identification when unity is not exact. No new FLRW physical claim was substituted. |
| proof-real-inequalities | L1 237–243 describes the concrete inequalities without claiming a general decision procedure for Lean reals | Read proof terms use sqrt monotonicity and linear arithmetic for these specific inequalities. |

## Original RED evidence and controls actually executed

`python3 /tmp/l1-source-math-author-20261105-r1/controls.py` completed successfully. It intentionally catches original assertion failures before checking the proposal; `controls.log` records seven original RED observations and seven proposal PASS observations. These are scratch checks of the original manuscript's actual false phrases, paired with independent arithmetic/logic controls:

1. Original susceptibility `1 ± 3e-15` is too narrow. With τ=3e-15 and speed ratio `1+0.75τ`, the deviation is within τ, while susceptibility `(1+0.75τ)^2 > 1+τ`. Exact interval center and half-width are `1+τ²` and `2τ`.
2. The same compatible susceptibility is not exactly one, so finite compatibility does not require exact unity.
3. A uniform prior on the adopted range has mass `4τ/9.9 ≈ 1.21212e-15`, whereas a prior concentrated at χ=1 gives mass one. Thus interval width alone supplies no statement for every prior, and the width scales linearly in τ rather than exponentially.
4. `|δ|≤τ` implies `|δ|<1/2`; at χ=1/4, `δ=-1/2` fails both P2 and P3′. It cannot isolate independence of P3′ from the other conjuncts.
5. The lower/upper ratios are about `2.27924e14` and `7.20759e14`, respectively; one common `7e14` factor for both is false.
6. The interval contains χ=1 and lies inside the adopted range. Endpoint failures do not exclude the entire range.
7. Exact-zero compatibility and finite-tolerance compatibility are distinct sets.

Preservation checks actually passed: unchanged source bytes; every original theorem identifier represented by the supplied actual declaration receipt remains present; unchanged `\includegraphics` line; unchanged pytest census line; byte-identical full dispersion section; byte-identical displayed Prop definition. No figures were generated or edited. No new long unbreakable theorem identifier or macro was introduced.

## Proposed acceptance and limits

ROOT should inspect the exact patch, integrate only the owned P25 TeX, propagate the sibling's accepted actual test census, and run the canonical source compile from the authorized checkout. Compile and rendered-page checks remain necessary: this author did not claim zero overfull boxes or layout acceptance without a compile. Existing macros, equation displays, plot path, and physical source paragraphs were preserved where outside this bounded correction. ROOT retains sole notebook and integration ownership.

These assertions establish bounded mathematical propagation, not publication readiness, source attribution acceptance, a microscopic dynamical bridge, or target-runtime/build acceptance. Independent review and the canonical pipeline remain ROOT's acceptance boundary.

## Remaining inherited physical/source/prose issues

These are observed source-text boundaries, not new source findings or a claim that no external derivation exists:

- P25 still attributes the second-sound interpretation to the older Volovik papers; its global “never derived” language and H1 endpoint subsection remain inherited. Actual endpoint theorem types do not establish the absence or impossibility of a dynamical derivation. No new physical source work was authorized, so these passages were neither strengthened nor silently reattributed.
- P25 still calls the RPA resummed response a bubble integral and describes the adopted `[0.1,10]` interval as an induced “half-decade” window. Current L1 has source qualifications and distinguishes a project-adopted window, but this package does not propagate new physical attribution or range-derivation claims.
- The full dispersion section is intentionally unchanged: it still describes Γ_H/c_GW² as a dimensionless coefficient and a leading transport correction, with placeholder-to-LIGO-band interpretation. The later discussion's claim that the placeholder “does not relax the constraint” also remains. Current L1 qualifies normalization/matching and distinguishes endpoint rescue from arbitrarily near-boundary compensation. That unresolved mathematical/physical boundary needs a separately scoped transport intake if ROOT chooses to repair it; this package preserves the assigned transport BUILD rather than silently extending scope.
- Inherited source/process narration, novelty superlatives, em-dashes, and census inconsistencies remain (abstract 32 theorems/lemmas versus conclusion 21; pytest line left unchanged at the assigned boundary). No count has been certified by this author. The new prose introduces no em-dash; a whole-paper house-voice or count cleanup would be a different pass.
- The existing figure is referenced at exactly its original path. Caption correction states finite unresolved extent and differing endpoint factors; correspondence with current rendered callouts remains for canonical visual acceptance.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No substantive contradiction between the brief's mathematical targets and the actual theorem statements or current accepted L1 paragraphs was found. The source Lean comments still contain stronger wording (including a P3′ “independently necessary” sentence) than the actual Prop and theorem types support. The actual declarations and definitions win; this proposal follows them and leaves Lean untouched. The endpoint rescaling theorem actually assumes `c ≠ 0`, which is stronger in domain than P25's physical restriction `c > 0`; retaining the latter does not overstate the theorem. The brief's desired layout preservation is a constraint, not evidence of a compiled outcome: no compile was permitted to this author, so zero-overfull layout remains unverified pending ROOT's canonical compile.
