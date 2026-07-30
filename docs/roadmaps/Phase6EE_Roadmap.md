# Phase 6EE — Kernel-Verified Two-Level Control & Composite Readout Ceilings

**Status: COMPLETE (2026-07-30).** Capstone phase of the `6E*` series (*verified device-physics metrology*).

> **⚠️ Close-out qualification — read before citing this phase as fully clean.**
>
> Completion criteria 1–4 are met. Criterion 5 as written (*a fresh-context adversarial review
> reports zero BLOCKER findings*) is met: reviews 3, 4, 5 and 6 each completed and each returned
> **zero BLOCKERs**.
>
> The **stricter operator bar — zero BLOCKER *and* zero MAJOR *and* zero IMPORTANT — was NOT
> reached.** Six completed rounds returned, in order, `1/7/6 → 1/3/5 → 0/3/5 → 0/2/5 → 0/2/4 →
> 0/3/5` (B/M/I). BLOCKERs converged after round 2 and stayed at zero; MAJOR/IMPORTANT stayed flat
> at ~2–3 / ~5 while the `Control/` family grew from 99 to 191 declarations, essentially all of it
> review-driven. Round 5's headline fix became round 6's MAJOR. A seventh review was launched and
> **terminated by the operator mid-flight** during an explicit stop-and-reassess, so no seventh
> result exists.
>
> The operator's judgement at close-out was that the loop had become reactive and was generating
> its own tail. That reading is supported by the data above: the remaining findings are concentrated
> in the *meta-layer* (docstrings, the remediation tables below, and the Inventory entries) rather
> than in the verified substrate, and the remediation tables in particular — prose about prose,
> unverifiable by construction — produced roughly six findings of their own across rounds 4–6.
>
> **What is solid:** the Lean substrate. 191/191 kernel-pure, zero project axioms, zero `sorry` /
> `native_decide` / `maxHeartbeats`, build clean at 10,799 jobs with zero `Control/` warnings,
> `validate.py` 50/50. Every reviewer independently re-derived the load-bearing mathematics
> (`interactionHamiltonian_decomp`, the Bloch–Siegert constant, `rwaGenerator_sq`, the Kramers
> algebra, the ceiling compositions) and confirmed all of it.
>
> **What is not:** treat the remediation tables below as a review log, not as verified claims —
> three of their rows were themselves found to misdescribe their own fixes. Git history is the
> reliable record. Residual MINORs are listed per round and were deliberately not chased.

---

## ✅ Shipped declarations (2026-07-30)

`lean/SKEFTHawking/Control/` — 4 modules, all root-imported in `lean/SKEFTHawking.lean`.
**191 extracted declarations** (180 authored + 11 compiler-generated equation lemmas), **191/191
kernel-pure** with axiom closures ⊆ `{propext, Classical.choice, Quot.sound}` and **zero project
axioms** (verified from `lean/lean_deps.json` axiom closures, not spot-checks). Zero `sorry`, zero
`native_decide`, zero `maxHeartbeats`, zero linter warnings. `lake build SKEFTHawking.ExtractDeps`
clean at 10,799 jobs; `validate.py` **50/50 ALL CHECKS PASSED** (2026-07-30).

**Reviewed six times, fresh context each time.** Review 2 found a BLOCKER in code review 1 had
already blessed; review 3 found 3 MAJOR / 5 IMPORTANT (zero BLOCKERs) showing round 2's own fixes
were bridged to their referents by prose; review 4 found 2 MAJOR / 5 IMPORTANT (zero BLOCKERs), by
then almost entirely in the documentation layer — including two rows of the remediation tables
below that misdescribed their own fixes; review 5 found 2 MAJOR / 4 IMPORTANT (zero BLOCKERs), both
MAJORs on round 4's own headline fix; review 6 found 3 MAJOR / 5 IMPORTANT (zero BLOCKERs) —
including that `Kq` was still an exported binder while three artifacts said it was discharged, that
the applied bound admitted `d = 0` (the identity drive again), and that both Inventory artifacts had
gone stale *again* and cited a declaration that had been renamed. Everything BLOCKER/MAJOR/IMPORTANT is remediated
in-session per PD-5 — see the five remediation tables below. The recurring defect class, in every
round, is **a claim bridged to its referent by prose rather than by a declaration** — first in the
Lean (a hypothesis set that excluded the physical instantiation), then in docstrings, and finally
in the remediation tables recording that the class had been closed.

⚠️ **The phase's original QI diagnosis — "no automated gate detects it" — was partly wrong, and
review 6 corrected it.** For the *mechanical* sub-class a gate existed and DID fire:
`validate.py --check lean_docstring_refs_resolve` flagged a dangling `Control/` docstring reference
with the correct replacement name, and was ignored because `Control.` sat outside its
`_DOCSTRING_STRICT_FAMILIES` (advisory, not FAIL). Two structural gaps, both now fixed in
`scripts/validate.py`: `SKEFTHawking.Control.` added to the strict families, and the block regex
widened from `/-- … -/` + `/-! … -/` to include plain `/- … -/` **module headers** — the omission
that hid a load-bearing reference to a nonexistent `combined_floor_add_strictly_sharper` for five
rounds. Widening it immediately caught two further real errors, including a docstring asserting
`kramers_anticommutation` is `eq_neg_of_add_eq_zero_left` when it is a one-line `linarith`.
What remains genuinely ungated is the non-mechanical residue: claims with no identifier to resolve
("a real propagator pair", "the first theorem in the series", "zero linter warnings", "the two
Inventory artifacts now agree").

| Module | Decls | Core content |
|---|---:|---|
| `RotatingWave` | 112 | `interactionPicture_ode` (the frame change GENERATES the dynamics — what forces the `−(ω/2)σ_z`); `interactionHamiltonian_decomp` (the EXACT split `H_I = H_RWA + V`); `driveOp_conjTranspose` + `exists_driveOp_of_isHermitian` (the Hermitian-generality scope claim); `norm_counterRotating_le` + `integral_counterRotating_naive_bound` (the naive Duhamel alternative, shipped so the route justification is checkable); `rwaPropagator_mul_neg` (unitarity) + `rwa_propagator_difference_bound_physical` (the bound AT the exact/co-rotating pair, nondegenerate); `rotFrame_zero`/`_hasDerivAt`/`_ode`/`_unique` (the frame pinned as `exp(i(ωt/2)σ_z)` — uniqueness now a THEOREM via `ODE_solution_unique`, not a docstring claim); `bsAntiderivative` + `_hasDerivAt` + `bsAntiderivative_norm_le` (`‖S t‖ ≤ 2(Ω/ω)·ℓ¹`, uniform in `t`); `integral_counterRotating` (FTC); `rwaGenerator_sq` (general `(Δ²+Ω²m²)/4`) and its resonance corollary; `generalRotationAngle` + `rwaRotationAngle_lt_generalRotationAngle`; `rwa_propagator_difference_bound` (+ `_inhabited`, a degenerate commuting-drive witness) and `rwa_propagator_difference_bound_physical` — **applied** at `diagonal_drive_propagator_bound`, where an `a·1 + d·σ_z` drive at nonzero detuning gives a nonzero generator, a nonzero remainder, a closed-form exact propagator (`diagonalExactPropagator` + `_ode`) and an OBSERVABLE error (the `d` term shifts the accumulated `σ_z` angle), with every constant discharged from `norm_zRotation`/`norm_rwaPropagator_diagonal`; `linftyOpNorm_one_sub_I_sigmaX` + `norm_rwaPropagator_quarter_turn` (`= √2`) refuting `KL = 1`; the closed-form co-rotating propagator `rwaPropagator` pinned by `rwaPropagator_ode` + `rwaPropagator_unique` and read by `rwaPropagator_trace`; validity + exact-value failure witnesses |
| `BanachAveraging` | 8 | `hasDerivAt_mul₃`, `integral_averaging`, `norm_integral_mul_mul_le` (bounds `∫L·G·U` via the ANTIDERIVATIVE of `G`, general factor bounds), `integral_mul_ode` (discrepancy identity), `norm_sub_le_norm_mul_sub_one` (unitarity transfer), `norm_propagator_sub_le` |
| `DriveCalibration` | 36 | `transverseElement`/`longitudinalElement` read off the operator and proved equal to their Pauli forms; transverse + longitudinal + general-detuning **duration** calibration identities; `no_duration_achieves_nonzero_angle_of_zero_element`, `magnitude_calibration_rotates_backwards`; the **phase** calibration layer — `rwaAxisPhasor` bridged to the generator by `transverseElement_rwaGenerator`, the factorisation `rwaAxisPhasor_eq`, `envelope_phase_alignment` (command `φ = χ − arg conj⟨0\|O\|1⟩` to land the axis at azimuth `χ`), its `m = 0` fail condition, and a σ_y quarter-turn mis-pointing witness; `calibrated_duration_transverse_propagator_full` (the WHOLE operator, sign- and axis-sensitive) + `trace_blind_to_rotation_direction` (refuting the trace-only reading); `transverseElement_norm_le` + traceless 11× witness; Kramers (`kramers_inner_eq_zero`, `_partner_eigenvector`, `_degeneracy` with linear independence, `_hypotheses_inhabited`) |
| `CompositeReadoutCeilings` | 35 | `assignmentFidelity` + floor→ceiling format; `add_le_branch_error_of_disjoint` (measure-theoretic disjointness); `combined_floor/ceiling_max`, `combined_floor/ceiling_add`, `combined_ceiling_add_lt_max` + `combined_ceiling_gap_witness` (gap `= 1/200`, derived by instantiating the comparison at the concrete `gapWitnessMeasure` model); **`relaxation_photon_ceiling`** — two NAMED floors on one attributed readout, with `relaxation_dominates_photon_at_separation_99` showing the `max` selects; per-mechanism ceilings for relaxation, relaxation⊕thermal, 6EA, 6EB, 6EC — the last three DERIVED from their upstream floor theorems; a BITES/does-not-BITE witness pair for **all five** ceilings, every BITES half proved *through its own ceiling theorem* (so it concludes about `assignmentFidelity`, not about a detached bound expression) and every does-not-BITE half stated on that ceiling's own bound expression with the operating point as a hypothesis |

### Second-review remediation (2026-07-30)

The second adversarial pass found that several theorems were bridged to the physical objects they
are *named* for by a docstring sentence rather than by a declaration. That is the sharper,
machine-detectable sub-class of this phase's own QI finding, and it is what all four severe items
had in common.

| # | Finding | Fix |
|---|---|---|
| **B1** | `rwa_propagator_difference_bound`'s hypothesis `hSgen` forced `P + Q = counterRotating` (the *Hermitian* remainder) by uniqueness of the derivative. A Schrödinger propagator pair gives `P + Q = −i·V`. So the theorem, while true, **could not be instantiated at `U_exact`/`U_rwa` at all** — the systems it covered were never the physical ones. | Restated `hSgen` on the `−i`-scaled antiderivative (§4.1); `‖−i • S‖ = ‖S‖`, so the Bloch–Siegert constant is untouched. Added `rwa_propagator_difference_bound_inhabited`, exhibiting a propagator pair satisfying every binder (commuting identity-drive at resonance). ⚠️ **That witness is DEGENERATE** — identity drive means `rwaGenerator = 0`, `U_rwa ≡ 1`, and the whole difference is unobservable global phase; the third review caught the docs overstating it. The nondegenerate statement is `rwa_propagator_difference_bound_physical` (MJ-1 below). |
| **M1** | The whole rotation-angle layer was disconnected from any propagator — no matrix exponential existed in the phase, `rwaRotationAngle` was a definition, and `rwaGenerator_sq` was cited by `calibrated_duration_general`'s docstring but called by nothing. | Built §3.5: `rwaRate`, `rwaPropagator`, and **`rwaPropagator_ode`** pinning the closed form by `U' = −i·H·U` (this is where `rwaGenerator_sq` is consumed). `rwaPropagator_trace` reads the angle off the propagator; `calibrated_duration_transverse_propagator` restates the calibration identity *on the propagator*. |
| **M2** | Calibration docstrings said the duration achieves the target angle "exactly", with no RWA caveat — contradicted by the phase's own `integral_counterRotating_witness_resonance`. | Both duration identities now carry the co-rotating-model caveat naming the remainder bound and the resonance witness. |
| **M3** | Nothing composed a *detection-layer* floor with a *device-layer* floor: `combined_floor_max` was generic in abstract reals and never instantiated at a 6EA/6EB/6EC floor. | Added `avgAssignmentError_mono`, `photon_budget_floor_attributed`, and **`relaxation_photon_ceiling`**, plus `relaxation_dominates_photon_at_separation_99` showing the `max` genuinely selects. ⚠️ **This row originally claimed `relaxation_photon_ceiling` was the first two-named-floor composite in the series — that was false**, and the third review caught it: `relaxation_thermal_ceiling` already composed relaxation ⊕ thermal and predates this phase. The correct claim is *first cross-layer* composite. |
| **I1** | `combined_ceiling_gap_witness` was numerals only — it would survive any edit to either composite. | Now **derived by instantiating `combined_ceiling_add_lt_max`** at a concrete two-point measure model (`gapWitnessMeasure`), at operating point `(e0,e1) = (0, 3/100)`. |
| **I2** | `norm_integral_counterRotating_conjugated_le` assumed four facts the module proves, so it carried no `Ω/ω`. | Discharges them from `hω`/`hΩ`; the conclusion now carries the explicit Bloch–Siegert constant. |
| **I3** | `combined_floor_max` is `max_le` under a physics name. | Docstring now says so plainly and points at §3.5, where the content actually lives. |
| **I4** | `longitudinalElement` was an orphan, and the reason it *cannot* have a duration identity was prose only. | `longitudinal_drive_purely_counterRotating` (through `interactionHamiltonian_decomp`) + `longitudinalElement_driveOp_sub` put that reason in the kernel. |
| **N1** | Validity witness concluded `≤ 1/100` while its docstring claimed `2×10⁻³`. | Statement strengthened to `≤ 1/500`, making the docstring — and the "250×" comparison — true. |
| **N4** | `kramers_degeneracy` claimed double degeneracy but never stated linear independence. | Added `linearIndependent_of_inner_eq_zero`; the theorem now carries the independence conjunct. |
| **N3** | `rotFrame`'s docstring said the ODE + `R(0)=1` "pins it uniquely", but no uniqueness theorem existed. | Built `lipschitzWith_const_mul` + **`rotFrame_unique`** (via Mathlib's `ODE_solution_unique`), and the same for the new propagator (`rwaPropagator_unique`). The uniqueness claim is now a theorem, not a softened docstring. |
| **N7** | AC text had the phase-alignment sign backwards. | Corrected in place, with the reason. |

**MINORs left alone, deliberately:** N2 (a trivial longitudinal zero-detuning lemma — superseded by
the substantive `no_duration_achieves_nonzero_longitudinal_angle_of_zero_detuning` shipped alongside
it), N5 (disclosed below rather than fixed), N6 (redundant-but-harmless binders in
`combined_ceiling_add_lt_max`).

### Third-review remediation (2026-07-30)

A third fresh-context pass reported **zero BLOCKERs** but 3 MAJOR / 5 IMPORTANT — largely finding
that the *second* round's fixes were bridged to their physical referents by prose in the same way
the defects they replaced had been. All closed in-session.

| # | Finding | Fix |
|---|---|---|
| **MJ-1** | The B1 inhabitation witness sits where the co-rotating dynamics is EMPTY (identity drive ⇒ `rwaGenerator = 0`, `U_rwa ≡ 1`, difference is pure global phase), while the docs called it "a real propagator pair". No declaration connected the bound to `rwaPropagator` at all. | Built the missing substrate — `rwaGenerator_conjTranspose`, `rwaPropagator_neg_eq_conjTranspose`, `rwaPropagator_mul_neg` (unitarity), `rwaGenerator_comm_rwaPropagator`, `rwaPropagatorInv_hasDerivAt`, `continuous_rwaPropagator` — and shipped **`rwa_propagator_difference_bound_physical`**: for ANY solution of `U' = −i·H_I·U` with `U(0)=1`, the difference from `rwaPropagator` is bounded, with `b`,`c` unconstrained beyond `0 < rate`. Nondegenerate, and no existence theorem needed. |
| **MJ-2** | `calibrated_duration_transverse_propagator` certifies only the TRACE, which is even in `θ` — blind to both the rotation direction (`magnitude_calibration_rotates_backwards`) and the axis (`envelope_phase_alignment`). | **`calibrated_duration_transverse_propagator_full`** pins the whole operator (`sin θ` carries the sign, `rwaGenerator` the axis), and **`trace_blind_to_rotation_direction`** refutes the trace-only reading outright: the time-reverse shares the trace but is a different operator. |
| **MJ-3** | Nothing tied `interactionHamiltonian` to the dynamics of `drivenHamiltonian` — replacing `−(ω/2)σ_z` by `+(ω/2)σ_z` would leave every theorem in the module true. Likewise `driveOp`'s Hermiticity and "loses no generality" were prose. | **`interactionPicture_ode`**: if `U' = −i·H·U` then `(R·U)' = −i·H_I·(R·U)` — the subtraction is now forced by a declaration. Plus `rotFrame_conjTranspose_mul`, `sigmaY_conjTranspose`, `driveOp_conjTranspose`, and **`exists_driveOp_of_isHermitian`** (every Hermitian 2×2 has that form). |
| **IM-1** | `relaxation_dominates_photon_at_separation_99` matched the relaxation floor by the bare numeral `1/4`. | Restated on the ceiling's own expression `t/T₁/(2(1+t/T₁))` at `t = T₁`. |
| **IM-2** | "First theorem in the series composing two named floors" was false. | Corrected in the docstring, this table, and both Inventory files — see the M3 row above. |
| **IM-3** | `SK_EFT_Hawking_Inventory.md` was stale relative to the second-round fixes (still carried the pre-N1 `10⁻²`, omitted the whole M3 deliverable). | Body rewritten. ⚠️ **This row overstated the fix** — the Index was not touched at all and both files kept a stale review-count line plus the very "a real propagator pair" phrasing MJ-1 was filed against. Review 4 caught it (MJ4-1); both artifacts corrected 2026-07-30. |
| **IM-4** | The Duhamel/Grönwall counterfactual — the stated justification for the entire route — appeared in three mutually incompatible forms and was backed by no declaration. | **`norm_counterRotating_le`** and **`integral_counterRotating_naive_bound`** ship the alternative bound (`2Ω·ℓ¹·T`, linear in `T`, no `1/ω`). The contrast is now between two theorems; all three prose sites reworded to match. |
| **IM-5** | The 6EB/6EC does-not-bite witnesses were one arithmetic fact with decorative binders, calling neither ceiling. | Both now CALL their ceiling. ⚠️ The first attempt used `∃ F, fidelity ≤ F ∧ 17/18 ≤ F`, which is **trivially satisfiable** by `F = max(…)` and carries no content — self-caught before review 4 and replaced by a conjunction naming the ceiling's own bound expression in both halves (`f4dc0c51`). This row previously described the discarded existential form. |
| **N3** *(2nd round)* | — | see previous table. |

**Disclosed, not fixed:** the 6EB and 6EC BITES witnesses fire at `matchedBudget = 0`, i.e. a
signal-free readout. That is a real operating point and the witnesses are honest, but it is a
*degenerate* one — no non-degenerate biting point is bracketed for those two ceilings. Recorded here
because the summaries previously said only "a witness pair for all five ceilings".

**Third-review MINORs left:** MN-1 (section numbering in `RotatingWave.lean` is out of order —
cosmetic), MN-2 (`linearIndependent_of_inner_eq_zero` states the pair-independence property rather
than Mathlib's bundled `LinearIndependent`), MN-5 ("Bloch–Siegert scale" names the `Ω/ω` small
parameter, not the second-order shift — flagged as a possible reader trap), MN-6, MN-8.

### Fourth-review remediation (2026-07-30)

Zero BLOCKERs. 2 MAJOR / 5 IMPORTANT — by this round the defect had **migrated out of the Lean and
into the documentation layer**, including into the remediation tables above, which are themselves
claims. All closed.

| # | Finding | Fix |
|---|---|---|
| **MJ4-1** | Both Inventory artifacts were frozen at the pre-third-review state while the IM-3 row above asserted they had been rewritten. The Index still carried the exact "a real propagator pair" phrasing MJ-1 was filed against, and both files said "reviewed by TWO passes" attributing round 3's findings to round 2. | Both rewritten with accurate review history, the degeneracy disclosed, and every round-3 declaration listed. The IM-3 row now records that it overstated its own fix. |
| **MJ4-2** | `relaxation_dominates_photon_at_separation_99`'s docstring claimed it "cannot survive an edit to either mechanism's floor" — but the declaration called no floor or ceiling theorem at all; IM-1 had replaced an un-anchored numeral with an un-anchored *expression* and asserted anchoring in prose. | Restated to **call `relaxation_photon_ceiling`** and conclude about `assignmentFidelity` after the `max` collapse, so an edit to either floor breaks the proof. |
| **IMP-1** | "Zero linter warnings" was false — two warnings, both introduced by the third-round fixes. | Both cleared (`simpa`→`simp`, deprecated `push_neg`→`not_or`); `Control/` builds warning-free. |
| **IMP-2** | The IM-5 row described its fix as the **existential form it was fixed away from**. | Row corrected; it now records that the existential shape was trivially satisfiable and was replaced. |
| **IMP-3** | "Pinning `KL`/`KU` to 1 would make the hypotheses unsatisfiable" — load-bearing, asserted in three places, backed by no declaration (the exact category review 2's BLOCKER lived in). | `linftyOpNorm_one_sub_I_sigmaX`, **`norm_rwaPropagator_quarter_turn`** (`= √2`) and `one_lt_norm_rwaPropagator_quarter_turn` ship it. |
| **IMP-4** | The headline propagator bound had no norm lemma for its own constants. | The quarter-turn lemmas supply a point value. ⚠️ **This row overstated it** — `√2` at one time is not the *uniform* `KL` the bound needs; review 5 caught it (IMP5-3). The uniform bounds now exist for the diagonal family (`norm_rwaPropagator_diagonal`, `norm_diagonalExactPropagator`, both `= 1` for all `t`) and are what `diagonal_drive_propagator_bound` actually uses. |
| **IMP-5** | (a) No in-repo `U` satisfied the physical bound's ODE hypothesis at a *rotating* generator — the phase's own standard, set by B1, was unmet by its own headline fix. (b) The degeneracy caveat landed in the roadmap but not at the declaration site. | (a) a closed-form exact propagator at nonzero detuning with nonzero generator and nonzero remainder. ⚠️ **The three declaration names this row originally gave no longer exist** — review 5 ruled that witness degenerate (identity drive + detuning ⇒ discrepancy still global phase) and it was replaced by `diagonalExactPropagator` / `_ode` / `diagonal_drive_propagator_bound`. Names corrected 2026-07-30 after review 6 (IMP6-3). (b) Caveats added to the §4.2 header and the `_inhabited` docstring, pointing at the nondegenerate statement. |

**Fourth-review MINORs:** fixed MN-1 (redundant `hgen` binder — now *derived* from `0 < rate`),
MN-3 (the third duration identity now carries the co-rotating caveat), MN-9 (duplicate `§3.1`).
⚠️ MN-6a was recorded as fixed **and was not** — the edit never matched and the false "previously
impossible" claim stayed live until review 5 caught it (IMP5-1). Now genuinely removed. Left: MN-2
(`0 < rwaRate` is a `field_simp` artifact in four lemmas — harmless), MN-4, MN-5, MN-7, MN-8.

### Fifth-review remediation (2026-07-30)

Zero BLOCKERs; 2 MAJOR / 4 IMPORTANT, both MAJORs landing on round 4's own headline fix.

| # | Finding | Fix |
|---|---|---|
| **MJ5-1** | `longitudinal_drive_nondegenerate_instantiation` claimed "every precondition of `rwa_propagator_difference_bound_physical` is met" while **calling it nowhere** — and the claim was false on its own binders (`ω ≠ 0` vs the bound's `0 < ω`). The bound had zero call sites. Round 4 reproducing MJ4-2 inside its own remedy. | **`diagonal_drive_propagator_bound`** now *applies* the bound, discharging every constant: `norm_zRotation`, `norm_rwaPropagator_diagonal`, `norm_diagonalExactPropagator` (all `= 1`, uniform in `t`), `Kp` from the generator norm. ⚠️ **`Kq` was NOT discharged** at that point — it remained a free binder with `hQb` exported, while this row said otherwise; review 6 caught it (MJ6-1). Now discharged internally via `norm_interactionHamiltonian_le`. Verified by reverse-dependency: the bound has a consumer. The collecting theorem's docstring no longer claims to apply it. |
| **MJ5-2** | The "nondegenerate" witness was **§4.2's identity drive again** (`driveOp a 0 0 0 = a·1`) with detuning bolted on; its discrepancy was still unobservable global phase; and "longitudinal" was a misnomer since `longitudinalElement (driveOp a 0 0 0) = 0`. | Witness now carries `d ≠ 0`: `driveOp a 0 0 d = a·1 + d·σ_z` is not a multiple of the identity, `V` still commutes with `H_RWA` so the closed form survives (`diagonalExactPropagator` + `_ode`, solving the EXACT equation), but `d` shifts the accumulated `σ_z` angle — so the bounded error is a genuine **relative rotation**, physically observable. |
| **IMP5-1** | MN-6a was recorded as fixed and never applied. | Applied; the claim is gone and the roadmap records the miss. |
| **IMP5-2** | The remainder conjunct was pointwise at `t = 0`, forcing `hφ : cos φ ≠ 0` and excluding ordinary drive phases. | Now function-level (`counterRotating … ≠ 0`), proved by evaluating at `t = −φ/ω`; `hφ` dropped. |
| **IMP5-3** | The IMP-4 row overstated its fix — `√2` at a point is not the *uniform* `KL` the bound needs. | Row corrected; uniform bounds now exist and are used. |
| **IMP5-4** | The roadmap's shipped-declarations table was not updated for round 4. | Updated. |

### Sixth-review remediation (2026-07-30)

Zero BLOCKERs; 3 MAJOR / 5 IMPORTANT.

| # | Finding | Fix |
|---|---|---|
| **MJ6-1** | `Kq` was **not** discharged — a free binder with `hQb` exported — while the docstring, the MJ5-1 row and the shipped table all said it came from `interactionHamiltonian_decomp` + `norm_counterRotating_le`. A caller could pass `Kq = 10⁹` and the "APPLIED" bound is true and useless. | **`norm_interactionHamiltonian_le`** discharges it internally; `Kq` and `hQb` deleted from the binder list. All five constants are now computed. |
| **MJ6-2** | The applied bound carried no `d ≠ 0`, so it admitted the identity drive MJ5-2 rejected (discrepancy = global phase); observability was a docstring bullet with no conjunct; and the nondegeneracy theorem had zero consumers. | `diagonal_drive_propagator_bound` now takes `hobs : sin (Φ_d T) ≠ 0` and **concludes** `d ≠ 0` (`d_ne_zero_of_observable`) together with `zRotation_not_scalar` — the discarded factor is proved not to be a global phase. `diagonalExactPropagator_factor` + `zRotation_add` supply the factorisation. Observability is now a conjunct, not a bullet. |
| **MJ6-3** | Both Inventory artifacts were stale **again** (frozen pre-review-5), cited `longitudinal_drive_nondegenerate_instantiation` which no longer exists, and described the round-4 witness review 5 had ruled degenerate — while the DoD box was ticked. MJ4-1 verbatim, two rounds later. | Both rewritten against the tree. The underlying cause — a point-in-time edit instead of a process — is why the drift guard was strengthened (IMP6-5). |
| **IMP6-1** | IMP-5(b)'s own degeneracy pointers were dangling in two places (the renamed theorem). | Repointed at `diagonal_drive_propagator_bound`. |
| **IMP6-2** | `combined_floor_add_strictly_sharper` does not exist — cited in the module header stating the discipline the module is *gated on*. Invisible because the guard never scanned plain `/- … -/` headers. | Corrected to `combined_ceiling_add_lt_max`; the guard now scans module headers. |
| **IMP6-3** | The IMP-5 row named three declarations, none of which exists. | Corrected, with the reason recorded. |
| **IMP6-4** | "Every binder is discharged" was false for `_physical` too — eight remain. | Reworded to "every *structural* binder", enumerating the constants that stay general and where they are computed. |
| **IMP6-5** | The phase's QI finding said "no automated gate detects it". **False for the mechanical sub-class**: `lean_docstring_refs_resolve` fired on IMP6-1 with the correct fix and was ignored because `Control.` was advisory-only. | `scripts/validate.py`: `SKEFTHawking.Control.` promoted into `_DOCSTRING_STRICT_FAMILIES`, and `_DOCSTRING_BLOCK_RE` widened to include plain `/- … -/` module headers. The widened gate immediately caught two further real errors (a nonexistent `U_exact` reference and a false `eq_neg_of_add_eq_zero_left` citation — the real proof is `linarith`). QI diagnosis corrected in all three docs. |

**Not in scope, still owed:** `MajoranaKramers` renaming (see the series-close list below). The
second review independently confirmed the characterization of those two lemmas.

### Planned → shipped name map

The acceptance boxes below are ticked against **content**, not against the placeholder names the plan
used before the substrate existed. Where a name differs, the shipped one is authoritative:

| Planned name (AC text) | Shipped as |
|---|---|
| `rwaReduction_def` | `rwaGenerator` + `rotFrame` + `interactionHamiltonian`, tied by `interactionHamiltonian_decomp` |
| `rwa_remainder_bound` | `bsAntiderivative_norm_le` (integrated remainder) → `rwa_propagator_difference_bound` (propagator level) |
| `rwa_rotation_angle` | `rwaRotationAngle` + `calibrated_duration_transverse`; `generalRotationAngle` off resonance |
| `projectedDriveElement_def` | `projectedDriveElement`, `transverseElement`, `longitudinalElement` (+ their `_driveOp` identities) |
| `envelope_phase_alignment` | shipped under this name |
| `matrixElement_suppression` | `transverseElement_norm_le` + `transverseElement_strictly_suppressed` |
| `kramers_degeneracy` | shipped under this name |
| `relaxation_thermal_ceiling`, `photon_budget_ceiling`, `filtered_readout_ceiling`, `detector_chain_ceiling`, `combined_ceiling_max` | shipped under these names |

## Open UNKNOWNs — resolutions

- **UNKNOWN-1 (RWA remainder route): RESOLVED — none of the three planned routes.** The in-repo BCH
  corpus does NOT instantiate: `bch_order_2_cubic_thm` bounds a *static* group commutator, whereas
  the RWA remainder compares a **time-ordered** propagator of a time-*dependent* generator; and BCH
  is cubic in one small `δ` bounding both arguments while the remainder is *first order* in `Ω/ω`
  with non-co-small arguments. PhysLib `Resolvent` fails for the first reason too. the naive Duhamel route
  yields only `2Ω·ℓ¹·T` — true, but **not** Bloch–Siegert scale, and shipping it would have been a
  silent de-scope. That contrast is no longer a counterfactual: `norm_counterRotating_le` and
  `integral_counterRotating_naive_bound` ship the alternative bound, so both sides are theorems. The route taken is the **near-identity (Bloch–Siegert) frame
  transformation**: `counterRotating` is a trigonometric polynomial with a CLOSED-FORM
  antiderivative bounded uniformly in `t`, which is where the `1/ω` comes from.
- **UNKNOWN-2 (Kramers formulation): RESOLVED — built from first principles.** Mathlib's
  antiunitary machinery was not used; `Θ` is carried as a plain map with `⟪Θx,Θy⟫ = ⟪y,x⟫`,
  `Θ² = -1` and conjugate-homogeneity as explicit hypotheses, which is weaker than requiring a
  bundled `LinearIsometryEquiv` and suffices for the whole argument (the orthogonality lemma needs
  no linearity at all). The pre-arm guardrail directing reuse of `MajoranaKramers`'
  `Θ`-algebra was **retracted** — see below.
- **UNKNOWN-3 (channel-theoretic independence): RESOLVED — measure-theoretic, not channel-theoretic.**
  The additive composite rests on `Disjoint A B` for measurable error events inside the branch
  error event, which is the honest formalisation of "the mechanisms contribute separately". A
  channel-composition route was not needed.

## `6E*` series-close summary

The series set out to make device-physics metrology claims machine-checkable end to end. Shipped
across 6EA–6EE: detection floors (6EA), filtered-readout/matched-filter floors (6EB), detector-chain
bolometric floors (6EC), material-parameter band substrate (6ED), and — here — the **control** layer
(RWA with an explicit remainder, projected-drive calibration, Kramers protection) and the
**composite-ceiling** layer that assembles every mechanism floor into a single end-to-end fidelity
ceiling. The series' organising fact is that every mechanism floor lower-bounds the *same* quantity,
`avgAssignmentError`, which is what lets them compose at all.

**Carried forward, not silently dropped:**
- The Bloch–Siegert scale is earned at the integrated-remainder and propagator levels; no theorem
  asserts the co-rotating reduction as an equality anywhere in the phase.
- `MajoranaKramers` needs honest renaming or real substrate — its `kramers_anticommutation` is
  `eq_neg_of_add_eq_zero_left` on two reals and its `kramers_pfaffian_definite_sign` is `mul_nonneg`
  under a self-admitted placeholder hypothesis, while both docstrings claim matrix/Pfaffian content.
  Out of 6EE scope; flagged, and this phase now supplies the genuine Kramers substrate they could be
  re-pointed at.
- Neither those lemmas nor the pre-remediation 6EE defects appeared in any disclosure registry, so
  the **name/docstring ↔ statement mismatch class was invisible to the automated gates as then
  configured** (the rename-drift guard treated `Control/` as advisory and never scanned module
  headers — both fixed 2026-07-30; see the header note).
  That is the phase's QI-level finding and is the one worth acting on project-wide.

---

## Original plan (retained for provenance)

Consumes 6EA (detection floors), 6EB (filtered-readout floors), 6EC (detector floors), and the existing readout-metrology corpus; 6ED feeds material-parameter seams optionally. See `Phase6EA_Roadmap.md` for the series framing.

**Thesis.** The repo already owns strong single-mechanism readout floors: `readoutDecayProb_eq_cohGamma` with its enclosure suite (relaxation), `ThermalAssignmentFloor` (thermal excitation), `avgAssignmentError_rational_floor` (their composition), the generalized-amplitude-damping channel, and the T1⊕T2 gate-fidelity family. Two layers are missing to make this a complete, state-of-the-art verified-metrology stack: (1) the *control* layer — rotating-wave reduction with an explicit error bound, projected-drive Rabi calibration algebra, and the Kramers-degeneracy protection statement, which turn "a qubit was driven" into kernel-checked rotation claims; and (2) the *composite-ceiling* layer — theorems assembling relaxation + thermal + photon-budget (6EA) + filtered-noise (6EB) + detector (6EC) floors into single end-to-end assignment-fidelity ceilings, each mechanism's hypothesis explicit, each ceiling falsifiable by `norm_num`. Together they finish the arc the `6E*` series exists for: any claimed readout performance can be screened against a machine-checked ceiling assembled from its own stated budget.

Clean whitespace: no prover has a kernel-checked RWA error bound, projected-drive calibration algebra, or an end-to-end multi-mechanism readout-fidelity ceiling.

> **⚠️ GUARDRAIL — ceilings compose under explicit independence/attribution hypotheses.** Error mechanisms do not add for free. Every composite ceiling states its attribution model (which mechanism claims which branch, what independence or worst-case-max is assumed) as explicit hypotheses. A composite that silently double-counts (conservative) is acceptable only when flagged; one that silently under-counts (fail-open) is a defect of the highest order for this phase.

> **⚠️ GUARDRAIL — RWA bounds are bounds, not the RWA.** The rotating-wave *approximation* is folklore; the deliverable is the *inequality*: the exact evolution differs from the co-rotating reduction by an explicitly bounded remainder (Bloch–Siegert scale `Ω/ω`). No theorem may assert the reduction as an equality, and every calibration statement inherits the remainder bound.

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK.** *(Compaction / sub-agent backstop.)*
> 1. **Bootstrap reads, in order:** workspace `../../CLAUDE.md` + `SK_EFT_Hawking/CLAUDE.md` → `docs/WAVE_EXECUTION_PIPELINE.md` → `SK_EFT_Hawking_Inventory_Index.md` → `Phase6EA_Roadmap.md` (series head) → `lean/SKEFTHawking/QuantumNetwork/ReadoutRelaxationBound.lean` + `ThermalAssignmentFloor.lean` + `lean/SKEFTHawking/DampedTwoLevel.lean` (the corpus this phase extends — read the sources directly). *(Path corrected 2026-07-30 by pre-arm plan-currency check: there is no `OpenSystems/` directory; `DampedTwoLevel` and `LindbladSemigroup` sit directly under `SKEFTHawking/`.)*
> 2. **Read this roadmap end-to-end**; Bricks are exact (verified 2026-07-27).
> 3. **Dev loop is MCP-first** (`lean-lsp-mcp`), per the 6EA instructions.
> 4. **Pipeline disciplines (hard gates):** (a) **bundle target D12** (authorized 2026-07-27; Invariant #14 applies — bundle-aware content from inception; scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`); (b) preemptive-strengthening + post-wave audit — this phase is the series' highest tautology risk (composition theorems degenerate into restated hypotheses if the ceiling isn't strictly sharper than its inputs; audit for that specifically); (c) kernel-purity, zero sorry, no new axioms without sign-off (#15); (d) no `maxHeartbeats` (#10).
> 5. **This phase:** matrix exponential bounds go through Mathlib's `NormedSpace.exp` and operator-norm Duhamel-type estimates (UNKNOWN-1); everything numeric follows `NumericalBounds` enclosures.

**Standing invariants:** kernel-pure; no new axioms (#15); no `native_decide`; no `maxHeartbeats` (#10); preemptive-strengthening; never push. **Two-layer honesty:** the control/ceiling mathematics is Lean-verified; drive-Hamiltonian and mechanism-attribution identifications are consumer-side hypotheses. Wave sizing ≈ one `/goal`.

**Substrate (verified 2026-07-27).**
- **Reuse:** `SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound` (`readoutDecayProb_eq_cohGamma`, `readoutDecayProb_enclosure`, `avgAssignmentError_rational_floor`) — the existing composition capstone this phase generalizes; `ThermalAssignmentFloor` (`thermalExcitedPop`, `half_one_sub_tanh`); `SKEFTHawking.DampedTwoLevel` + `SKEFTHawking.LindbladSemigroup` (**note: no `OpenSystems.` namespace segment** — corrected 2026-07-30); `QuantumNetwork.GeneralizedAmpDamp` (thermal T1 channel) + `CoherenceFidelity` (T1⊕T2 fidelity closed forms) + `NamedChannels`; 6EA/6EB/6EC outputs per their roadmaps — **all four 6E predecessors are now COMPLETE** (6ED closed 2026-07-30), so every floor this phase composes is available.
- **Absent → build:** RWA remainder bound; projected-drive/Rabi calibration algebra; Kramers-degeneracy statement; the multi-mechanism composite ceilings. *(Re-verified 2026-07-30: `rotatingWave`/`Rabi` are genuinely absent.)*

> **⚠️ GUARDRAIL — Kramers must be BUILT FROM SCRATCH. The prior guardrail's premise was false; it is retracted.** *(Retracted 2026-07-30 after reading `MajoranaKramers.lean` in source rather than by name.)*
>
> The earlier instruction read "reuse its `Θ`-algebra rather than rebuilding it". **There is no `Θ`-algebra in `MajoranaKramers` to reuse.** Verified directly in source:
> - `kramers_anticommutation (j2_a a_j2 : ℝ) (h : j2_a + a_j2 = 0) : j2_a = -a_j2 := by linarith` — two REALS. The docstring claims `{J₂, A} = 0` for the fermion matrix; the statement is `eq_neg_of_add_eq_zero_left` on ℝ. No matrix, no `J₂`, no anticommutator.
> - `kramers_pfaffian_definite_sign (pf1 pf2 : ℝ) (h_kramers : ∀ (a : ℝ), a = a) …  : pf1 * pf2 ≥ 0 := by positivity` — the Kramers hypothesis is a **self-admitted placeholder** (`-- Kramers condition placeholder`, vacuously true); the docstring claims the Wei et al. PRL 116 Pfaffian-sign theorem; the statement is `mul_nonneg`.
>
> **Calibration of the finding.** These theorems are *true* and are NOT "vacuous statements" in the detector's sense — `validate.py --check vacuous_statement_audit` PASSES and does not flag them, correctly, because they are genuine real-arithmetic implications. The defect is a **name/docstring ↔ statement mismatch**: the names and docstrings assert matrix/Pfaffian/antiunitary content the statements do not contain. Neither appears in `VACUOUS_STATEMENT_BASELINE` or any other disclosure registry, so the debt is currently invisible to every gate.
>
> **Consequence for this phase:** the Wave-2 Kramers statement is genuinely new substrate and must be built from first principles — an antiunitary `Θ` with `Θ² = -1` and a real degeneracy conclusion. Nothing may be cited as "reused" from `MajoranaKramers`.
>
> **Owed elsewhere (out of 6EE scope, flagged not fixed):** `MajoranaKramers` needs either honest renaming/disclosure or real substrate. Building genuine Kramers here creates the substrate those lemmas could later be re-pointed at.
- **Mathlib/PhysLib:** `NormedSpace.exp` for matrix exponentials; PhysLib `QuantumInfo.Finite.Qubit` (qubit-specific helpers, consumed already via bridge modules).

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology* (**authorized 2026-07-27**; `PAPER_STRATEGY.md` §2.2; this phase supplies layers (iv) control and (v) composite ceilings). Scaffolding at first content-lift per `BUNDLE_LIFT_PROCEDURE`.

---

## Wave 1 — Rotating-wave reduction with explicit remainder

**Goal.** For the driven two-level Hamiltonian `H(t) = (ω₀/2)σ_z + Ω·cos(ωt+φ)·O_drive`, the co-rotating reduction at resonance with an operator-norm remainder bound of Bloch–Siegert scale. Verdict: reachable-with-care — a Duhamel/averaging estimate on 2×2 matrices; the spike is picking the estimate route (UNKNOWN-1) before freezing constants.

**Why.** Every control claim in any two-level platform routes through the RWA; the explicit inequality version is the series' most broadly citable control theorem.

**Bricks.** Mathlib `NormedSpace.exp`; `DampedTwoLevel` (ODE-verification pattern); PhysLib `Qubit`.
**Additional in-repo bricks (added 2026-07-29, post-v4.32-bump substrate re-scan).** The project
already owns a 37-declaration matrix-exponential corpus that this Bricks list predates and that
UNKNOWN-1 should cost out before spiking either route from scratch:
`MatrixBCHCubicMathlibPR` (4 decls — order-2/cubic Baker–Campbell–Hausdorff; BCH is the direct tool
for bounding `exp(A)·exp(B)` against `exp(A+B)`, which is the RWA remainder's exact shape),
`MatrixExpLocalHomeomorphMathlibPR` (14), `FKLW/GenericSUdMatrixMercatorLog` (19 — concrete-radius
matrix log). All three are kernel-pure and Mathlib-PR-packaged. A second candidate route is PhysLib
`Mathematics/Resolvent.lean` (new at pin `c4843367`): `norm_resolvent_le` (‖resolvent z t‖ ≤ |z.im|⁻¹),
`contDiff_resolvent`, `iteratedDeriv_resolvent`, `norm_iteratedDeriv_resolvent_le`,
`hasTemperateGrowth_resolvent` — a resolvent-estimate path to the same bound.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Control/RotatingWave.lean` builds 0-sorry, kernel-pure, with:
- [x] `rwaReduction_def` — the co-rotating effective Hamiltonian in the interaction picture (definition, convention-explicit);
- [x] `rwa_remainder_bound : ‖U_exact(T) − U_rwa(T)‖ ≤ C·(Ω/ω)·(1 + Ω·T)`-shape inequality with explicit `C` (exact shape frozen after the UNKNOWN-1 spike; the deliverable is ANY honest explicit-constant bound of Bloch–Siegert scale, not the optimal one);
- [x] `rwa_rotation_angle : θ = (m/2)·Ω·T` for the co-rotating propagator with projected drive element `m = |⟨0|O_drive|1⟩|` — the calibration identity at the RWA level;
- [x] `norm_num` witnesses: a parameter point where the remainder bound is small (validity) and one where it is order-unity (honest failure);
- [x] preemptive-strengthening + post-wave audit.

## Wave 2 — Projected-drive calibration algebra & Kramers protection

**Goal.** The calibration layer: signed projected drive elements, duration/phase calibration identities (transverse and longitudinal), matrix-element-suppression algebra, and the Kramers-degeneracy statement for time-reversal-protected doublets. Verdict: reachable — finite-dimensional algebra; the Kramers statement is a clean antiunitary-symmetry theorem (UNKNOWN-2 for its best Mathlib formulation).

**Why.** Calibration identities are where control claims silently break (magnitude-vs-sign, suppressed matrix elements); making them signed, exact theorems closes that class. Kramers degeneracy is the textbook protection statement for any doublet-encoded system.

**Bricks.** Wave 1; `blochPauli` spectral core (`Topological.BlochBundle`, if the doublet statement uses it); PhysLib `Qubit`.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Control/DriveCalibration.lean` builds 0-sorry, kernel-pure, with:
- [x] `projectedDriveElement_def` (signed complex `⟨0|O|1⟩` and longitudinal `(⟨0|O|0⟩−⟨1|O|1⟩)/2`) + `calibrated_duration_transverse : T = 2θ/(m·Ω)` and the longitudinal dual — both SIGNED, with fail-conditions (`m = 0`, sign-inverted target) as explicit hypotheses, not absorbed magnitudes;
- [x] `envelope_phase_alignment` (the phase-calibration identity). ⚠️ **The AC text originally read `achieved axis phase = φ + arg⟨0|O|1⟩`; that sign is wrong.** The shipped identity gives azimuth `= φ − arg⟨0|O|1⟩` (equivalently `φ + arg⟨1|O|0⟩`), because the axis phasor factorises as `(Ω/2)·conj⟨0|O|1⟩·e^{iφ}` (`rwaAxisPhasor_eq`). Corrected 2026-07-30 after adversarial review; the shipped table above was already right.
- [x] `matrixElement_suppression : ‖⟨0|O|1⟩‖ ≤ ‖O‖`-shape bound + a strict-suppression witness (a concrete frame where `m ≪ ‖O‖` — the physics that makes naive `θ = Ω·T` calibration wrong);
- [x] `kramers_degeneracy : time-reversal antiunitary with T² = −1 → every eigenvalue of a T-symmetric Hamiltonian is (at least) doubly degenerate` (finite-dimensional statement; formulation per UNKNOWN-2);
- [x] preemptive-strengthening + post-wave audit.

## Wave 3 — Composite readout ceilings

**Goal.** The capstone: end-to-end assignment-fidelity ceilings assembling relaxation (existing), thermal (existing), photon-budget (6EA), filtered-noise/matched-filter (6EB), and detector (6EC) floors, under explicit attribution hypotheses; each ceiling with `norm_num` non-vacuity witnesses on both sides. Verdict: reachable — the mechanism floors all exist by this point; the work is honest composition (the guardrail's independence/attribution discipline) and sharpness witnesses.

**Why.** This is the theorem family the whole series exists to enable: a single machine-checked inequality per readout class, from stated physical budget to fidelity ceiling.

**Bricks.** `avgAssignmentError_rational_floor` + `readoutDecayProb_enclosure` + `thermalExcitedPop` (existing); 6EA `poisson_avgError_floor` + Gaussian floors; 6EB `error_floor_from_budget`; 6EC `bolometer_error_floor`; `GeneralizedAmpDamp` + `CoherenceFidelity` for the channel-level statements.

**Done (AC / `/goal` condition).**
- [x] `lean/SKEFTHawking/Control/CompositeReadoutCeilings.lean` builds 0-sorry, kernel-pure, with:
- [x] `relaxation_thermal_ceiling` — the existing pairwise composition re-stated in the phase's uniform ceiling format (cite `avgAssignmentError_rational_floor`; no re-proof) as the format anchor;
- [x] `photon_budget_ceiling : F ≤ 1 − (1/2)·(1/4)·exp(−(√N_a−√N_b)²)`-shape ceiling from the 6EA floor, attribution hypotheses explicit;
- [x] `filtered_readout_ceiling` — 6EB budget floor composed to a fidelity ceiling for any admissible-filter threshold readout;
- [x] `detector_chain_ceiling` — the 6EC bolometric floor composed end-to-end (the deepest chain: detector NEP → filter → Gaussian error → fidelity);
- [x] `combined_ceiling_max` — mechanisms combine at least as `F ≤ 1 − max(individual floors)/2`-shape (worst-mechanism form, always sound) plus the strictly-sharper additive form under stated independence hypotheses, with the difference between the two forms itself witnessed;
- [x] per-ceiling `norm_num` witness pairs: a budget point where the ceiling bites (claim above it = refuted) and one where it doesn't (non-triviality both ways);
- [x] root-module import + Inventory/counts refresh; series-close notes recorded in this roadmap.
- [x] preemptive-strengthening + post-wave audit (tautology hunt per the instructions blockquote — mandatory emphasis).

---

## Sequencing & parallelism

Wave 1 → Wave 2 serialize (calibration consumes the RWA identity); Wave 3 consumes everything and closes the series. Wave 1 may start once 6EA Wave 2 exists (it needs nothing from 6EB/6EC); **Wave 3 is the series barrier** — do not start it before 6EB Wave 3 and 6EC Wave 3 ship, or its AC list degrades to the mechanisms available (record the descope explicitly if the operator orders an early close). 6ED is an optional seam (material-parameter instantiations of the ceilings), never a blocker.

## Phase Definition of Done

- [x] `lake build` + ExtractDeps clean; zero sorry; kernel-pure; no new axioms.
- [x] `validate.py` green; Inventory + Index refreshed with the `Control/` family.
- [x] Adversarial statement audit logged — composite-tautology hunt is the priority class.
- [x] Roadmap status updated with dated shipped-declarations list; `6E*` series-close summary recorded here (what shipped across 6EA–6EE, what remains deferred).

## Open UNKNOWNs

- **UNKNOWN-1:** the RWA remainder route — direct Duhamel estimate on the interaction-picture generator (elementary, likely loose constant) vs. first-order averaging lemma (sharper, more machinery). Spike both to statement level before freezing Wave 1's AC constant shape.
  **→ Spike a THIRD route first (added 2026-07-29): in-repo BCH.** `MatrixBCHCubicMathlibPR` already
  proves the cubic BCH remainder for matrices, and the RWA bound is structurally a BCH remainder
  (`‖exp(A)exp(B) − exp(A+B)‖` at Bloch–Siegert scale `Ω/ω`). If it applies, Wave 1 reduces to
  instantiating an existing kernel-pure theorem instead of building a Duhamel or averaging estimate.
  Cost to check: one `lean_hover_info` on the BCH statement + one dimensional-analysis pass against
  the target shape. Do this before either planned spike — if it lands, both are moot; if it doesn't,
  the two original routes stand unchanged and ~15 minutes were spent.
  (PhysLib `Mathematics/Resolvent.lean` is a fourth route — see the Wave-1 Bricks note.)
- **UNKNOWN-2:** Kramers-degeneracy formulation — Mathlib's antiunitary/`LinearIsometryEquiv` conjugate-linear machinery vs. an explicit 2n×2n real-form statement. Check `lean_leansearch`/`lean_loogle` for existing quaternionic-structure results first; do not rebuild what Mathlib has.
- **UNKNOWN-3:** whether the additive combined ceiling's independence hypotheses can be stated channel-theoretically (via `GeneralizedAmpDamp` composition) rather than probabilistically — prefer the channel route if `CoherenceFidelity`'s composition pattern extends; it keeps the phase inside the existing corpus's idiom.
