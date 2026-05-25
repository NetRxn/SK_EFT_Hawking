# Phase 6u — Post-Compact Handoff (2026-05-25)

## Goal restated

**Complete Phase 6u fully. No de-scoping. No backsliding. No tracked-Prop
deferrals shipped as "done".** Grind through the substantive T-S.2
discharge over as many sessions as it takes. Then CP2 adversarial review +
final strengthening sweep.

The pre-compact session significantly OVER-estimated remaining work as
"intractable / multi-session research effort". A read-only triple-check
of the codebase + Mathlib revealed the actual remainder is **~400-600 LoC
over 1-2 focused sessions**, not 750-1900 LoC over 4-5 sessions.

## Critical findings from the read-only scout (commit `2aacccd`)

### Refutation: "Niven not in Mathlib" was WRONG

Mathlib v4.29.1 already ships:
- `Real.isIntegral_two_mul_cos_rat_mul_pi : ∀ (q : ℚ), IsIntegral ℤ (2 * Real.cos (↑q * Real.pi))`
- `niven : ∀ {θ : ℝ}, (∃ r, θ = ↑r * Real.pi) → (∃ q, Real.cos θ = ↑q) → Real.cos θ ∈ {-1, -1/2, 0, 1/2, 1}`
- `Real.isAlgebraic_cos_rat_mul_pi`, `Complex.isAlgebraic_cos_rat_mul_pi`
- `isIntegral_exp_rat_mul_pi_mul_I`
- File: `lean/.lake/packages/mathlib/Mathlib/NumberTheory/Niven.lean`

### Generic substrate already in project

`lean/SKEFTHawking/FKLW/FibRepInfiniteOrder.lean` ships TWO completely
alphabet-agnostic theorems:

- `matrix_no_pow_eq_one_of_eigenvalue_not_rootOfUnity` (lines 108-143)
- `not_finOrder_of_eigenvalue_not_rootOfUnity` (lines 150-165): for
  `A : Matrix.specialUnitaryGroup (Fin d) ℂ` with non-root-of-unity
  eigenvalue, `¬ IsOfFinOrder A`.
- `complex_exp_not_root_of_unity` (lines 179-208).

Plus `AharonovAradLemma6.one_accPt_of_infinite_closed_subgroup` is generic
(documented in roadmap).

Plus `BinaryTetrahedral.lean` (890 LoC) is project-local SU(2)
finite-subgroup substrate — not mentioned in roadmap.

### Sub-lemma 1 is 95% done

`CliffordTGeneratorCaseAnalysis.lean::T_SU_mat_never_anticommute_ts` has
a fully-fleshed proof body. The only blocker is `Fin 2` representation
friction (numeric literal `0`/`1` vs `⟨0, by decide⟩`) preventing
`linear_combination` from closing. **The fix is mechanical 4-spot rewrite**:

```lean
have h_eq : (2 * α) * X ⟨0, by decide⟩ ⟨0, by decide⟩ = 0 := by
  have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
  have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
  rw [h0eq, h1eq, h_T00, h_T01, h_T10] at h_entry
  linear_combination h_entry
```

Apply analogous pattern to all 4 entry blocks. **Verified to pass via
`lean_multi_attempt` by the scout agent.**

## Current state (end of pre-compact session)

### Shipped + committed (all built clean, kernel-only, zero new axioms):

| File | Commit | LoC | Status |
|---|---|---:|---|
| `GenericSU2GeneratingSet.lean` (W1) | 7ad8e55 | 230 | ✅ |
| `GenericClosureDenseWitness.lean` (W2) | 7ad8e55 | 280 | ✅ |
| `GenericEpsilonNet.lean` (W3) | 7ad8e55 | 145 | ✅ |
| `GenericSolovayKitaevRecursion.lean` (W4a) | 7ad8e55 | 280 | ✅ |
| `GenericSolovayKitaevLengthBound.lean` (W5) | 7ad8e55 | 88 | ✅ |
| `GenericSolovayKitaevQuantitative.lean` (W6) | 7ad8e55 | 150 | ✅ |
| `GenericSolovayKitaevRecursionDischarge.lean` (W4b) | 14eda8a | 1226 | ✅ UNCONDITIONAL |
| `CliffordTGeneratingSet.lean` (T-S.1) | b48c985 | 340 | ✅ |
| `CliffordTClosureDenseWitness.lean` (T-S.2 conditional) | e3e5230 | 180 | ✅ |
| `CliffordTQuantitative.lean` (T-S.3-5) | e3e5230 | 170 | ✅ |
| `CliffordTNonCommuting.lean` (T-S.2 substrate piece) | eaefc3e | 140 | ✅ |

### Work-in-progress (committed but NOT imported by root, so zero-sorry policy preserved):

| File | Commit | LoC | Status |
|---|---|---:|---|
| `CliffordTGeneratorCaseAnalysis.lean` | 2aacccd | 267 | 🟡 4 sorries; sub-lemma 1 near-complete |

### CP1 adversarial review remediation:

Commit 7c9fa29 + 9ffa5f7. 5 of 15 findings addressed (R1, R2 doc, RC3,
RC5, A2). Remaining are low-priority documentation / aesthetic.

### Current conditional reduction:

T-S.5 Clifford+T strict headline is CONDITIONAL ONLY on
`cliffordT_v4_witness_tracked` (a single tracked Prop). All Phase 6u
substrate (Waves 1-6 + 4b + T-S.1, 3, 4, 5) is shipped. The remaining
substantive work is discharging this ONE tracked Prop.

## Action plan for post-compact sessions

### Session 2 (next): Close sub-lemma 1 + start sub-lemma 2

**Mechanical fix to sub-lemma 1** (~30 minutes):

1. Open `lean/SKEFTHawking/FKLW/CliffordTGeneratorCaseAnalysis.lean`.
2. For each of the 4 `h_X??_zero` blocks (currently at lines ~142, 152,
   160, 168), apply the verified pattern:
   ```lean
   have h_eq : ... = 0 := by
     have h0eq : (0 : Fin 2) = ⟨0, by decide⟩ := rfl
     have h1eq : (1 : Fin 2) = ⟨1, by decide⟩ := rfl
     rw [h0eq, h1eq, h_T00, h_T01, h_T10, h_T11] at h_entry
     linear_combination h_entry
   ```
3. Run `lean_diagnostic_messages` to verify zero errors.
4. Final `ext` + `fin_cases` step at the bottom also needs the `Fin 2`
   form unification (or just use `Fin.isValue` simp lemmas).

**Begin sub-lemma 2** (`T_SU_mat_commute_ts_iff_paulI_z`, ~50-80 LoC).
Use `Matrix.diag_eq_of_commute_single : Commute (Matrix.single i j 1) M
→ M i i = M j j` for the centralizer-of-distinct-diagonal characterization.

### Session 3: Finish sub-lemmas 2, 3, 4 + the case-analysis headline

**Sub-lemmas 3 & 4** are ~50 LoC each entry-wise Pauli computations.
Use the same Fin-representation pattern as sub-lemma 1.

**Once all 4 sub-lemmas land**: `exists_cliffordT_generator_not_commute_not_anticommute`
compiles (composition already written, line ~210 of the WIP file).

**Add file to root SKEFTHawking.lean imports** at that point (zero
sorries → ADR-003 compliant in shipped build).

### Session 4-5: Infinite-order proof via FibRepInfiniteOrder substrate

**The path** (revised from scout findings):

1. **Compute eigenvalues of H_SU·T_SU**. Trace = √2·sin(π/8), det = 1.
   Eigenvalues = `(tr ± √(tr²-4))/2`. Since `tr² < 4`, eigenvalues are
   complex conjugates on unit circle: `e^{±iθ}` with `cos(θ) = √2·sin(π/8)/2`.

2. **Prove the eigenvalue is not a root of unity** using Niven:
   - Suppose `e^{iθ}` IS a root of unity. Then `θ = q·π` for some `q ∈ ℚ`.
   - Then `2·cos(θ) = √2·sin(π/8)` would be an algebraic integer
     (by `Real.isIntegral_two_mul_cos_rat_mul_pi`).
   - But `√2·sin(π/8)` is NOT an algebraic integer over ℤ (it's an
     algebraic real with minimal polynomial `2x⁴ - 4x² + 1` —
     non-monic with non-integer roots). Contradiction.
   - Specifically: if `α = √2·sin(π/8)`, then `α² = 2·sin²(π/8)
     = 1 - cos(π/4) = 1 - √2/2`. So `2α² = 2 - √2`, so `√2 = 2 - 2α²`.
     Squaring: `2 = (2 - 2α²)²` → `4α⁴ - 8α² + 2 = 0`. Divide by 2:
     `2α⁴ - 4α² + 1 = 0` (Eisenstein at p=2 → irreducible over ℚ).
     A monic integer polynomial would have `α` as algebraic integer, but
     `2x⁴ - 4x² + 1` has leading coefficient 2, not 1. The minimal poly
     of `α` over ℚ is `2x⁴ - 4x² + 1` divided by leading coefficient
     (i.e., `x⁴ - 2x² + 1/2`), not monic-integer.

3. **Apply `not_finOrder_of_eigenvalue_not_rootOfUnity`** (alphabet-agnostic
   from FibRepInfiniteOrder.lean) to conclude `H_SU·T_SU` has infinite
   order in SU(2).

4. **Lift to `H_of_G cliffordTGeneratingSet` is infinite**: scout's
   Opportunity 2 — check whether `H_Fib_infinite_of_exists_inf_order_mem`
   (FibSU2Density.lean:3142) is structurally generic. If yes, plug in
   directly; if no, write a small generic variant (~20-50 LoC).

5. **Compose**: `one_accPt_of_infinite_closed_subgroup` →
   `vonNeumann_assemble_explicit_X_unconditional` → case-analysis
   sub-lemma 5 (i.e., headline `exists_cliffordT_generator_not_commute_not_anticommute`)
   → bundle into `cliffordT_v4_witness_tracked` discharge.

**Estimated LoC**: ~150-300 (per scout).

### Session 6 (maybe): Compose final unconditional headline + CP2

1. **`cliffordT_v4_witness_discharged`**: substantive theorem proving
   `cliffordT_v4_witness_tracked` unconditionally. Replaces the tracked
   Prop hypothesis in T-S.5's headline → T-S.5 becomes fully unconditional.

2. **CP2 adversarial review** on the now-fully-discharged Track T-S chain.

3. **Final strengthening sweep** on any remaining low-priority CP1
   findings (RC1, RC2, RC4, RC6, RC7, A1, A3, A4, A5, A6).

4. **Update**: `docs/PERMANENT_TRACKED_HYPOTHESES.md` to REMOVE
   `cliffordT_v4_witness_tracked` (no longer permanent). Roadmap close.

## Important workflow reminders for post-compact

1. **Use `lean4` skill** (lean-lsp-mcp + lean_multi_attempt) — the
   pre-compact session showed that LSP-driven iteration is MUCH faster
   than `lake build` rebuilds. Specifically: use `lean_multi_attempt`
   for testing tactic candidates BEFORE writing them to file.

2. **Use `lean_local_search` before remote searches** to find existing
   project substrate.

3. **READ deep-research files directly** (don't delegate to summaries)
   when working on hard proofs.

4. **`Fin 2` representation choice**: pick ONE form (`(0 : Fin 2)` OR
   `⟨0, by decide⟩`) and stick with it throughout a proof. The scout
   verified that bridging via `(0 : Fin 2) = ⟨0, by decide⟩ := rfl`
   works.

5. **WIP files OK with sorries** as long as NOT imported by
   `SKEFTHawking.lean`. The current `CliffordTGeneratorCaseAnalysis.lean`
   is in this state (committed but not in root).

6. **Background agents for parallel substantive work** — Wave 4b's
   1226 LoC was shipped via background agent in ~18 minutes. Consider
   the same pattern for the Niven-infinite-order proof.

7. **Parallel agent on Phase 6r** is active — be careful with commits
   to `lean/lean_deps.json.hash` and `docs/validation/reports/` (leave
   those alone). My new files go in distinct paths under
   `lean/SKEFTHawking/FKLW/`.

## Hard rules (NOT to be relaxed)

- **No new axioms** without explicit user sign-off (Pipeline Invariant #15).
- **No `set_option maxHeartbeats`** in proof bodies (Invariant #10).
- **Zero sorries in the shipped build** (root-imported tree) — ADR-003.
  WIP files OK as long as not imported.
- **Standard kernel only** for headline theorems (`{propext,
  Classical.choice, Quot.sound}`).
- **No de-scoping** of T-S.2 substantive discharge. Tracked Prop
  `cliffordT_v4_witness_tracked` MUST be substantively discharged.
- **Roadmap stays in sync** with progress as commits land.
- **Git discipline**: don't push without explicit user permission.

## Final state summary

- 7 commits this session: 7ad8e55, b48c985, 14eda8a, e3e5230, 7c9fa29,
  9ffa5f7, eaefc3e, 2aacccd.
- Branch: `main`, NOT pushed.
- Build: 8289 jobs clean (last verified at commit eaefc3e).
- Phase 6u substrate: SHIPPED kernel-only.
- T-S.5 Clifford+T headline: CONDITIONAL on 1 tracked Prop.
- T-S.2 substantive discharge: ~400-600 LoC remaining over 1-2 focused
  sessions (per scout-verified revision).
- CP2 adversarial review + final strengthening: post T-S.2 discharge.

Done when: T-S.2 discharged unconditionally + CP2 review passes
cleanly + all strengthening targets closed.
