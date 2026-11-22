# Independent Phase 6EE source-alignment review r1

Verdict: REQUEST ONE PROSE CORRECTION before accepting the full bounded package. Seven targeted repairs are acceptable. C5.4 fixes the original detuning omission but its new physical-angle sentence still omits the nonnegative-amplitude condition required by the cited theorem. C7.1 is acceptable as partial disclosure only. C5.2 and C6.1 remain unchanged and OPEN. No canonical closure, Stage 13, full-tree, build or publication acceptance is established.

## Identity and authority

Candidate: `/private/tmp/skeft-phase6ee-alignment.rdkc68tx/SK_EFT_Hawking`, branch `codex/phase6ee-claim-proof-alignment-20261122`, HEAD/base `83dac57c6936bded796624bd34069e7366f25f03`, dirty four-file candidate identified below. Reviewer wrote only this report. No tests, Lean tools, builds, runtime/slot operations or Git mutations were performed; read-only `git diff` and `git show` supplied comparison evidence.

FIRST ACTION: `python3 scripts/codex_continuity.py check .codex/continuity/phase6ee-source-alignment-review-r1.json` returned fresh=true, changed=[]. Read governing AGENTS.md, CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, ADR-008, ADR-017, CODEX_CONTINUITY.md, assigned roadmap/notebook and original review. ROOT owns closure and merging; the notebook writer remains the lead. The packet is snapshot evidence, not admission or acceptance authority.

Original ID prefix for every C-number below: `review:2026-08-01-0504-internal-adversarial:phase6EE_control:`. For example C2.1 means suffix `2.1`. Original review: `papers/AutomatedReviews/2026-08-01-0504-internal-adversarial/phase6EE_control.md`.

## Actionable residual within changed prose

**R1 / C5.4: add the amplitude sign condition to the new zero-detuning physical-angle statement.** `lean/SKEFTHawking/Control/RotatingWave.lean:704-708` identifies the exponent angle at zero detuning as `(m/2)·Ω·T`, then gives `(T/2)√(Δ²+Ω²m²)` at general detuning. The actual identification theorem `generalRotationAngle_resonance`, lines 766-771, explicitly requires `hΩ : 0 ≤ Ω`. This matters: Ω=-1, b=1, c=0, T=1, Δ=0 gives generalRotationAngle=+1/2 and rwaRotationAngle=-1/2. Their equality is false without the condition. Suggested minimal repair: “the calibration identity at zero detuning, for nonnegative amplitude Ω, is ...”. Preserve the signed `rwaRotationAngle_eq_projected` identity and all proofs. The original C5.4 detuning defect is corrected, but full claim-to-proof alignment of the changed sentence needs this qualifier. This is a static mathematical counterexample, not a Lean run.

## Scoped repairs reviewed

| Original finding | Result | Exact candidate evidence |
|---|---|---|
| C2.1 | ACCEPT | BanachAveraging:76-80 now retains KL·KU; theorem at 106-115 has precisely KL*KU*B*(1+T*(Kp+Kq)). Direct-G comparison also retains factor bounds. Capstone at 215-243 retains the further KUr transfer factor. |
| C4.1 | ACCEPT | RotatingWave:811-815 correctly identifies physical theorem, abstract bridge, scaled antiderivative and parallel integral theorem. Source calls physical→abstract at 1155-1164, abstract→norm_propagator_sub_le at 1079-1083; BanachAveraging:234-243 composes transfer/discrepancy/averaging. The separate conjugated-integral theorem at RotatingWave:823-836 calls norm_integral_mul_mul_le directly. Canonical value_deps_project agrees with all four edges. |
| C4.2 | ACCEPT | DriveCalibration:67-74 retargets to physical theorem and explicitly retains ODE/norm hypotheses. RotatingWave:1136-1148 bounds the actual U(T)-rwaPropagator(T) pair conditionally on those hypotheses. |
| C5.1 | ACCEPT | RotatingWave:667-669 distinguishes all-T validity from the single-time exact resonance value. Statements at 673-678 and 694-700 supply precisely those claims. No propagator-error lower bound is newly claimed by this edit. |
| C5.3 | ACCEPT | RotatingWave:1719-1723 accurately says ω≠0 is weaker than 0<ω, while Ω≠0 and 0≤Ω are incomparable. Negative and zero examples are correct; nonzero Ω is used at 1762 to contradict the zero-remainder assumption. |
| C5.4 | ORIGINAL DETUNING ERROR FIXED; R1 REMAINS | RotatingWave:704-708 now gives the resonance qualifier and general formula. General definition at 752-755 and strict comparison at 773-788 agree. Sign condition discussed above is still needed. |
| C8.1 | ACCEPT | Roadmap:83 separates four ceiling-call/conclusion-bound pairs from the relaxation existential. CompositeReadoutCeilings:524-535 exhibits e0=0,e1=readoutDecayProb and fidelity≥999/1000 without calling relaxation_ceiling. Other four call their ceilings at 581,621,828,851; their conclusions pair a ceiling conclusion with a permissive lower bound on that same expression. Five BITES declarations at 510,557,597,631,648 call their own ceiling theorems. “At least” is correctly weaker than the old source comment’s “exceeds” and matches the actual existential statement. No high-fidelity existence is attributed to the other four conditional bound pairs. |
| C8.2 | ACCEPT | Roadmap:74-83 explicitly dates the census to 83dac57c and counts raw module-attributed entries including generated declarations, rather than independently authored theorems. Independent read of canonical lean_deps.json gives RotatingWave 117, BanachAveraging 8, DriveCalibration 45, CompositeReadoutCeilings 44. |
| C7.1 | ACCEPT PARTIAL DISCLOSURE ONLY; OPEN | DriveCalibration:619-623 says H=id is scalar, eigenspace is all C², establishes satisfiability and actual theorem application only, and explicitly owes classification/non-scalar information separately. Proof at 633-644 sets H=LinearMap.id, lam=1 and calls kramers_degeneracy. No general classification or non-scalar witness is supplied; an informative non-scalar witness cannot be inferred on C². This does not close original C7.1. |

## Preserved obligations and surrounding limitations

C5.2 remains OPEN: RotatingWave:1703 says “not a multiple of identity”, while conjunct 3 at 1732 excludes only `(a:ℂ) • 1`. No theorem strengthening or prose downgrade was made. The owed all-scalars claim has not been waived.

C6.1 remains OPEN: RotatingWave:1025-1029 retains the Hermitian/anti-Hermitian exclusion argument without adding the requested remainder/interaction-Hamiltonian Hermiticity support declarations. No proof obligation has been removed.

Read across surrounding affected assertions and theorem siblings. Existing original recommended C2.2 persists at DriveCalibration:72-73 and RotatingWave:1092-1094: O(Ω/ω) language has no fixed-time qualifier while the bound grows with T. Existing C7.2 persists at DriveCalibration:614-615 (“six” hypotheses versus seven explicit binders at 577-580). These are inherited out-of-scope original findings, not regressions or a reason to claim their closure. The dated 191-declaration historical closeout above the roadmap table remains historical; it is not the current four-module raw entry total (214).

## Exact preservation and counting evidence

Full four-file diff reviewed. The three Lean files differ solely in comments: an independent nested block/line-comment remover, preserving strings and noncomment source, produced byte-for-byte identical remaining text between exact base and candidate in each file. Thus theorem statements, proof terms, imports and executable source text are unchanged, with no accidental noncomment token changes detected. This is source-preservation evidence, not elaboration/build evidence.

Canonical lean_deps.json counts by exact `module` field, without filtering autogen or kind:

| Module | Raw entries | autogen=true | Kinds |
|---|---:|---:|---|
| RotatingWave | 117 | 9 | 17 def, 100 theorem |
| BanachAveraging | 8 | 0 | 8 theorem |
| DriveCalibration | 45 | 2 | 4 def, 41 theorem |
| CompositeReadoutCeilings | 44 | 0 | 2 def, 41 theorem, 1 instance |

The raw table total is 214, including 11 entries marked autogen=true. The raw-entry convention is explicit and correct; the table does not claim all entries are authored theorem declarations.

Candidate bytes / SHA-256:

- docs/roadmaps/Phase6EE_Roadmap.md: 52355 / cdd3ce3a2d95fc0582a59848e06bd70cddf88d62f28a9a790938a0eb02210665
- lean/SKEFTHawking/Control/BanachAveraging.lean: 14489 / 56d44953197aa51047c84f25e93de9090c2d8f9121638131dd134b7c04575113
- lean/SKEFTHawking/Control/DriveCalibration.lean: 38034 / 82087be5817d7ad2c1cd0b20b5fc0663e0ef2024673e9bed966c68bfdb4e92ec
- lean/SKEFTHawking/Control/RotatingWave.lean: 102046 / e8d3c22d805bd3d653cc2968d3ae2806653c57941dadd1a62437370c3aec1b6e

Final continuity check and report hash/byte evidence are returned with this report to the lead. No other review was viewed. No repository files were written.
