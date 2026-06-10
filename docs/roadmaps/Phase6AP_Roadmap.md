# Phase 6AP — QuantumNetwork substrate completions (textbook-math origination + diamond AKN bound)

**Status: OPEN 2026-06-10.** Successor to 6AO (closed 2026-06-10). Scope: five small-to-medium
waves completing the QuantumNetwork substrate where textbook/published math is still missing or
only worked-instance-level, plus one documentation-verification wave. Per the going-forward
origination rule: textbook/published math lives HERE (defensive-pub), at full strength, first try.

**Invariants (unchanged):** kernel-pure (`{propext, Classical.choice, Quot.sound}`), zero sorry,
no project-local axioms (#15), no `maxHeartbeats` in proof bodies (#10), preemptive-strengthening
checklist applied to every statement before writing it. Gate-strength discipline per the 6AO
header: no vacuous/definitional-only deliverables; no effort-based deferral.

## W1 — general rational exp-enclosure (NumericalBounds)

- **What:** promote the worked `expNeg046_enclosure` instance to the general Bernoulli bracket
  `expNeg_enclosure : 0 ≤ r → 1 − r ≤ exp(−r) ∧ exp(−r) ≤ 1/(1+r)` — both endpoints rational at
  rational `r`; the load-bearing primitive for rigorous rational enclosures of any decay factor
  `e^{−t/τ}` (fiber loss, memory decoherence) without floating-point `exp`.
- **Gate:** the general lemma, kernel-pure; the existing worked instance remains as the
  operating-point example. ✅ **SHIPPED 2026-06-10.**

## W2 — Kronecker-with-identity operator-norm bound (`KroneckerOpNorm.lean`)

- **What:** `l2_opNorm_kronecker_one_le : ‖A ⊗ₖ (1 : Matrix p p 𝕜)‖ ≤ ‖A‖` (L²-operator norm),
  by column-slice factorization of the Kronecker action + the per-column `Matrix.l2_opNorm_mulVec`
  bound. Textbook fact (ancilla extension does not increase the operator norm); absent from
  Mathlib (verified by search). Mathlib-upstream candidate.
- **Why now:** it is the ancilla-register step every diamond-norm comparison with auxiliary
  system needs — the direct substrate for W3.
- **Gate:** the bound at full generality (`RCLike 𝕜`, arbitrary finite index types), kernel-pure.
- ✅ **SHIPPED 2026-06-10 (`d525c793`):** `KroneckerOpNorm.lean`, linter-clean, kernel-pure.

## W3 — unitary operator-norm → diamond bound (the AKN inequality)

- **What:** the Aharonov–Kitaev–Nisan-style bound: for unitary channels,
  `diamondDist (unitary U) (unitary V) ≤ 2‖U − V‖_op`-class (constant per our ½-diamond
  convention to be fixed at proof time; the SHARP version with optimized global phase is
  documented as the known tightening, not silently claimed). Proof via the add-subtract
  telescope `UρU† − VρV† = (U−V)ρU† + Vρ(U−V)†` under the ancilla extension, Hölder
  (`‖AB‖₁ ≤ ‖A‖_op‖B‖₁`, existing `OpNormHolder`/`TraceNormCauchySchwarz` substrate as
  available), and W2's Kronecker bound.
- **Why now:** converts compiled-gate operator-norm errors (e.g. from
  `FKLW.GenericSU2.cliffordTCompile_correct`) into certified diamond-distance figures — the
  missing link between gate-synthesis correctness and worst-case channel error.
- **Gate:** the bound on a non-trivial unitary pair class with the ancilla register included
  (not the ancilla-free weakening); kernel-pure; a worked instance connecting to an exact
  named-channel distance as cross-check.
- ✅ **SHIPPED 2026-06-10 (`f50e9406`):** `UnitaryDiamond.lean` — `traceNorm_eq_physlib`
  identification importing PhysLib's general trace-norm toolbox (subadditivity + both Hölder
  bounds, now on the project trace norm); `l2_opNorm_le_one_of_unitary`;
  `traceNorm_conj_diff_le` (the telescope for arbitrary CONTRACTIONS — strictly stronger than
  unitary); **`diamondDist_unitaryKraus_le`**: `diamondDist Φ_U Φ_V ≤ ‖U − V‖_op` (½-diamond
  convention; = AKN `‖·‖_◇ ≤ 2‖U−V‖_op`), ancilla via the W2 Kronecker bound. The sharpness
  caveat ships AS A THEOREM: `diamondDist_unitary_smul_phase` (global phase ⇒ same channel at
  zero diamond distance, positive opnorm distance — the gate's cross-check instance; the
  phase-optimized tightening documented, not claimed). Kernel-pure (lean_verify).

## W4 — erasure two-way capacity formula (`ErasureRateBound.lean` or PLOBRateBound extension)

- **What:** `erasureBound p := 1 − p` with range/monotonicity lemmas — the erasure-channel
  two-way capacity FORMULA (Bennett–DiVincenzo–Smolin 1997; also PLOB 2017 §V). Same two-layer
  posture as `plobBound`: the FORMULA + properties are Lean-verified; the channel-converse
  semantics stays literature-cited until the teleportation-stretching machinery exists.
- **Gate:** formula + monotonicity/range, kernel-pure, with the converse-vs-formula layer split
  documented in the module header (mirroring `PLOBRateBound.lean`).
- ✅ **SHIPPED 2026-06-10 (`a3933e49`):** `ErasureRateBound.lean` — formula + endpoints + STRICT
  antitonicity + the cross-formula comparison `erasureBound_le_plobBound` (loss dominates
  erasure at matched parameter; the two formulas provably not interchangeable). Kernel-pure.

## W5 — Ross–Selinger citation-scaffolding verification (documentation)

- **What:** verify the Phase-6AM/6AO RS citation scaffolding (§6 iff-criterion; §7.2 constant)
  verbatim against the primary source `arXiv:1403.2975v3`; the prior DR self-flagged these
  PARTIAL-VIABLE. Update the scaffolding docs/docstrings; record the verification artifact.
  Lean theorem validity is unaffected (kernel-checked); this gates published-bundle RS *claims*.
- **Gate:** per-claim verbatim confirmation or correction, recorded with source extracts.
- ✅ **RESOLVED 2026-06-10 (no duplicate read needed):** the 6AO Track-1 closure had already
  performed the end-to-end primary-source verification (all 40 pp; recorded in
  `Phase6AO_Roadmap.md` §"PRIMARY-SOURCE VERIFICATION COMPLETE", the citation source of truth,
  with numbering errata fixed in-repo — it even caught a mathematically-impossible roadmap item,
  ℤ[√2][i]-ED). Both 6AM-flagged items are covered: §6 iff-criterion = **Appendix C Lemma C.16**
  (solvable ⟺ doubly-positive ∧ †-decomposable); §7.2 = ε-region eq. (14), with the constant
  question resolved by the Hypothesis-8.3 ↔ Selinger-1212.6253-Hyp-29 cross-identification
  (K+12 = ∀SU(2) slope vs K+4 z-rotation slope). W5 closure = the stale PARTIAL-VIABLE flags
  annotated RESOLVED with pointers (6AM roadmap; private-consumer notes follow the same pointer).

## Closure

- `lake build` + `lake build SKEFTHawking.ExtractDeps` clean; `validate.py` green; counts +
  Inventory refreshed; Stage-13-style review of new statements (strengthening checklist).
