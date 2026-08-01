---
paper: phase6EE_control
reviewer: adversarial-reviewer
model: claude-opus-5
review_date: 2026-08-01T05:04:55Z
readiness_gates_version: 1
scope: lean/SKEFTHawking/Control/{BanachAveraging,CompositeReadoutCeilings,DriveCalibration,RotatingWave}.lean
head: 40b5a9b4
---

# Adversarial Review — Phase 6EE `Control/` modules (item G, confirmation pass)

## Summary

**This is a discovery pass, not a confirmation pass — report it as such.** 20 findings:
2 BLOCKER, 10 REQUIRED, 8 RECOMMENDED. Every instance the class sweep enumerated and
patched checks out (all seven "Corrected 2026-07-31" notes verified true; both restated
does-not-bite witnesses verified as `refine ⟨<ceiling> …, ?_⟩`; `calibrated_duration_divisor_eq_rate`
verified correct; roadmap lines 93 and 351 verified accurate). But the *class* was not
swept: a satisfiability counterfactual that five docstrings assert and the modules' own
theorems refute (1.1), a factor-of-two in `rwaRate`'s docstring contradicted by the
justification it cites (3.1), and a wrong-target theorem pointer at two sites (4.1/4.2)
all survive untouched, in the same four files, in the same class. Gates affected:
LeanProofSubstance (5), AssumptionDisclosure (6), NarrativeGrounding (7), CountFreshness (9).
Not submission-ready until 1.1 and 3.1 are fixed.

**Files touched (read-only):** the four `Control/` modules; `CLAUDE.md`;
`docs/dev-loops/Phase6EE/class-sweep-log.md`; `docs/roadmaps/Phase6EE_Roadmap.md`;
`lean/SKEFTHawking/MajoranaKramers.lean`; `lean/SKEFTHawking/QuantumNetwork/{ReadoutRelaxationBound,ThermalAssignmentFloor}.lean`;
`lean/SKEFTHawking/Electrothermal/BolometricFloors.lean`; `lean/SKEFTHawking/Detection/GaussianThreshold.lean`;
`lean/lean_deps.json`. No writes outside this review file. No git state changed.

---

## Findings

### 1.1 — 🔴 BLOCKER — "would exclude every rotation whose angle is not a multiple of π/2" is refuted by the same modules' own theorems, and by their flagship applied theorem

- **Severity:** BLOCKER
- **Gate:** NarrativeGrounding / LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/BanachAveraging.lean:94-96`; `Control/RotatingWave.lean:803-806`, `:1154-1157`, `:1221-1222`, `:1250-1252`
- **Observed:** Five docstring sites assert that pinning `KL`, `KU` to `1` makes the averaging
  hypotheses unsatisfiable. The strongest phrasings:
  - `BanachAveraging.lean:94` — "a hypothesis `‖L s‖ ≤ 1` would exclude **every rotation** whose
    angle is not a multiple of `π/2` — i.e. exactly the propagators this machinery exists to bound."
  - `RotatingWave.lean:1154` — "Two docstrings assert that pinning `KL`, `KU` to `1` would make the
    hypotheses **unsatisfiable for every rotation**."
  - `RotatingWave.lean:1221` — "pinning the factor bounds to `1` would have made the averaging
    hypotheses unsatisfiable for **the very propagators the module exists to bound**."
- **Evidence:** `RotatingWave.lean:1509` proves `norm_zRotation (θ : ℝ) : ‖zRotation θ‖ = 1` — and
  `zRotation` is documented at `:1423` as "A `σ_z` rotation by angle `θ`, i.e. `exp(−i·θ·σ_z)`".
  So at θ = π/3 there is a rotation, whose angle is not a multiple of π/2, with `ℓ^∞` operator
  norm exactly 1 — not excluded by `‖L s‖ ≤ 1`. `RotatingWave.lean:1551` lifts this to the
  propagator: `norm_rwaPropagator_diagonal : ‖rwaPropagator ω₀ ω Ω φ 0 0 t‖ = 1`.
  Decisively, the module's own capstone instantiation `diagonal_drive_propagator_bound`
  (`:1661`) calls `rwa_propagator_difference_bound_physical ω₀ ω Ω φ a 0 0 d T 1 1 1 …` —
  i.e. **KL = KU = KUr = 1** — and succeeds. The hypothesis set the prose calls unsatisfiable
  is the one the file's headline applied theorem lives in.
  What §4.1d actually proves is narrower: `one_lt_norm_rwaPropagator_transverse`
  (`:1253`) is quantified over `rwaPropagator ω ω Ω 0 1 0 t` only — resonance, φ = 0, b = 1,
  c = 0 — i.e. the transverse σ_x family, not "every rotation".
- **Expected:** Prose scoped to what is proved: pinning the factor bounds to `1` excludes the
  **transverse** co-rotating propagators `exp(−iθσ_x)` at angles that are not multiples of π/2.
  Not "every rotation", not "the very propagators the module exists to bound" (the diagonal
  ones are exactly such propagators and have norm 1).
- **Fix:** At all five sites replace the universal with the transverse-family scope, and add one
  clause noting that σ_z rotations are `ℓ^∞`-isometric (`norm_zRotation`) so the exclusion is
  family-specific. Do not weaken `KL`/`KU` generality — the generality is still justified by the
  transverse family; only the counterfactual is overstated.
- **Cache:** n/a (source-verified, lines read in full)

### 1.2 — 🔵 RECOMMENDED — `rwa_propagator_difference_bound_physical`'s transverse scope note is honest but leaves inhabitation at b ≠ 0 ambiguous

- **Severity:** RECOMMENDED
- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:1108-1117`
- **Observed:** The SCOPE paragraph is accurate: the binders place no constraint on `b`, `c`
  beyond `0 < rate`; the only closed-form exact propagator shipped is diagonal; `hU` is
  discharged from physical data only at `b = c = 0`. It closes "at `b ≠ 0` the theorem applies
  to whatever exact propagator the reader supplies, and no such object is shipped here."
- **Evidence:** Verified against the binder list at `:1118-1130` and against the only closed-form
  propagators in the file (`commutingDrivePropagator :1282`, `diagonalExactPropagator :1430`),
  both diagonal.
- **Expected:** The scoping is correct and the claim should be kept, not deleted — the theorem is
  non-vacuous via `diagonal_drive_propagator_bound`, and the disclosure is more honest than most
  in the corpus. The one gap: a reader cannot tell from this note whether the b ≠ 0 hypothesis
  set is *inhabited at all* or merely unformalised.
- **Fix:** Add one clause: existence at b ≠ 0 is standard (linear matrix ODE with continuous
  coefficients; both propagators are `ℓ^∞`-bounded, `‖·‖ ≤ √2`), but is not formalised here.
  That distinguishes "not shipped" from "possibly empty".
- **Cache:** n/a

### 2.1 — 🟡 REQUIRED — §3 header states a strictly stronger bound than the theorem proves — the exact error its own capstone docstring names

- **Severity:** REQUIRED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/BanachAveraging.lean:76-79`
- **Observed:** §3 header: "A pointwise bound on `G` would give `O(‖G‖·T)`; **this gives
  `B·(1 + T(Kp+Kq))`**".
- **Evidence:** `norm_integral_mul_mul_le` (`:111`) concludes
  `‖∫₀ᵀ L·G·U‖ ≤ KL * KU * B * (1 + T * (Kp + Kq))`. The `KL·KU` prefactor is dropped by the
  header. The file's own `norm_propagator_sub_le` docstring (`:213-215`) says of exactly this:
  "The three factor bounds are part of the constant and are written out here — **dropping them to
  `B·(1 + T·(Kp+Kq))` would state a strictly stronger bound than the theorem proves**."
- **Expected:** `KL·KU·B·(1 + T(Kp+Kq))`, or an explicit `O(·)` framing with `KL`, `KU` named as
  the absorbed constants.
- **Fix:** Write the prefactor out at `:77`, matching the capstone docstring's own standard.
- **Cache:** n/a

### 2.2 — 🔵 RECOMMENDED — "within `O(Ω/ω)`" drops the linear-in-T growth the bound actually carries

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:1075-1076`; `Control/DriveCalibration.lean:71-72`
- **Observed:** RotatingWave §4.1b: "whatever the exact propagator is, it is **within `O(Ω/ω)`**
  of the co-rotating one." DriveCalibration: "Any device claim lifted from this identity inherits
  that `O(Ω/ω)` error bar."
- **Evidence:** `rwa_propagator_difference_bound_physical` (`:1129-1130`) bounds by
  `KUr·(KL·KU·2(Ω/ω)ℓ¹·(1 + T(Kp+Kq)))` — linear in `T`, not uniform in it. `O(Ω/ω)` is correct
  only at fixed `T`. Note the theorem's own docstring (`:1041`) writes the constant out in full,
  so the section prose is looser than the declaration it introduces.
- **Expected:** "`O(Ω/ω)` at fixed `T`" or the full constant.
- **Fix:** Add the fixed-`T` qualifier at both sites.
- **Cache:** n/a

### 3.1 — 🔴 BLOCKER — `rwaRate`'s docstring is off by a factor of two, contradicted by the theorem it cites as its justification and by DriveCalibration

- **Severity:** BLOCKER
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:841-842`
- **Observed:** "The co-rotating rotation RATE, `√(Δ² + Ω²m²)/2` — **half the magnitude of
  `rwaGenerator`**. The 'half the magnitude' is `rwaRate_sq` below read against `rwaGenerator_sq`:
  `H_RWA² = rate²·1`."
- **Evidence:** `H_RWA² = rate²·1` says the magnitude of `rwaGenerator` **is** `rate`, not
  `2·rate` — the docstring's own cited justification refutes its claim. Confirmed by
  `rwaGenerator_sq` (`:726`), `rwaRate_sq` (`:850`), and directly by
  `DriveCalibration.lean:102-105`, whose theorem is titled "**The rate in the calibration formula
  IS the generator magnitude**" and whose body is `rw [rwaGenerator_sq, rwaRate_sq]`. Two modules'
  docstrings state contradictory factors for the same quantity. (Contrast
  `DriveCalibration.lean:344-345`, which says "half the **Bloch-sphere rotation rate**" — correct,
  because the Bloch rate is `2·rate`. The RotatingWave site says "half the magnitude of
  `rwaGenerator`", which is a different and false referent.)
- **Expected:** "the magnitude of `rwaGenerator`" — or, if the Bloch-sphere reading was intended,
  "half the Bloch-sphere rotation rate `√(Δ²+Ω²m²)`", matching DriveCalibration's phrasing.
- **Fix:** Correct `:841-842`. This is the same factor-of-two class that
  `calibrated_duration_divisor_eq_rate` was added to eliminate; that theorem is correct (see
  Confirmations) but it did not reach the `rwaRate` docstring itself.
- **Cache:** n/a

### 3.2 — 🔵 RECOMMENDED — "magnitude" is unqualified in a file that fixes a different norm; "traceless involution" is not what `rwaGenerator` is

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:721-723`
- **Observed:** "Since a traceless involution generates a rotation, this pins the generator's
  **magnitude** EXACTLY at `√(Δ² + Ω²m²)/2`."
- **Evidence:** The module header (`:25-26`) declares "Matrix norm: the `ℓ^∞` operator norm
  (max row sum)". Under that norm, for Δ ≠ 0 and b ≠ 0, `‖rwaGenerator‖ = (|Δ| + Ω|b|)/2`, which
  strictly exceeds `√(Δ²+Ω²b²)/2`. The statement `rwaGenerator_sq` pins the *eigenvalues* (±rate),
  i.e. the Pauli-vector / spectral magnitude — the intended and correct reading, but not the
  norm the file otherwise uses. Separately, `rwaGenerator` is not an involution; `H_RWA/rate` is.
- **Expected:** "spectral magnitude" or "Pauli-vector magnitude"; and "a traceless matrix squaring
  to a positive multiple of `1`".
- **Fix:** Two word changes at `:721-723`.
- **Cache:** n/a

### 4.1 — 🟡 REQUIRED — §6 SCOPE points at the wrong theorem and claims a composition that no declaration performs

- **Severity:** REQUIRED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:808-810`
- **Observed:** "SCOPE. This bounds the CONJUGATED integrated remainder `‖∫₀ᵀ L·V·U‖`. The literal
  `‖U-exact(T) − U_rwa(T)‖` form is **`rwa_propagator_difference_bound`** below, which **composes
  this** with the discrepancy identity and the unitarity transfer from `BanachAveraging`."
- **Evidence:** Two errors. (a) `rwa_propagator_difference_bound` (`:1048`) concludes
  `‖U T - Ur‖` over an *abstract* `Ur` with `hinv : Ur * L T = 1`; it is precisely the theorem
  whose docstring-only identification §4.1b (`:1069-1072`) was written to fix — "the
  identification `L = U_rwa⁻¹`, `U = U-exact` … lived only in its docstring". The theorem that is
  literally about `U_rwa` is `rwa_propagator_difference_bound_physical` (`:1118`). (b)
  `rwa_propagator_difference_bound`'s body (`:1061-1065`) is a direct call to
  `norm_propagator_sub_le`; it does **not** compose
  `norm_integral_counterRotating_conjugated_le`. A repo-wide grep finds that theorem referenced
  in exactly two places — its own declaration (`RotatingWave.lean:815`) and
  `BanachAveraging.lean:84` — and called by nothing.
- **Expected:** "…is `rwa_propagator_difference_bound_physical` below, which instantiates
  `BanachAveraging.norm_propagator_sub_le` (discrepancy identity + unitarity transfer) at the same
  antiderivative. This section's theorem is a parallel leaf, not a step in that chain."
- **Fix:** Retarget and drop "composes this".
- **Cache:** n/a

### 4.2 — 🟡 REQUIRED — same wrong-target pointer in DriveCalibration

- **Severity:** REQUIRED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/DriveCalibration.lean:67-69`
- **Observed:** "The exact propagator differs from the co-rotating one by the counter-rotating
  remainder that **`rwa_propagator_difference_bound`** bounds at Bloch–Siegert scale."
- **Evidence:** Same as 4.1(a): the abstract theorem does not mention `rwaPropagator`. The
  statement about "the exact propagator" vs "the co-rotating one" is
  `rwa_propagator_difference_bound_physical`.
- **Expected:** `rwa_propagator_difference_bound_physical`.
- **Fix:** One-token retarget. Note that this pointer resolves as an identifier, which is why
  `validate.py --check lean_docstring_refs_resolve` (now strict for `SKEFTHawking.Control.`,
  verified passing with zero `Control` findings) cannot catch it.
- **Cache:** n/a

### 5.1 — 🟡 REQUIRED — §4.1's "stated at every `t` and every `T`" is false of the resonance witness, and its stated reason is the opposite of that witness's design

- **Severity:** REQUIRED
- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:665-668`
- **Observed:** "Both witnesses use a unit transverse drive (`b = 1`, others zero) and differ only
  in `ω/Ω`. **They are stated at every `t` and every `T`, so neither is an artefact of a lucky
  time.**"
- **Evidence:** `integral_counterRotating_witness_valid (T : ℝ)` (`:672`) is universally quantified
  in `T` ✓. `integral_counterRotating_witness_resonance` (`:693`) has **no** `T` binder — it is
  stated at the single time `T = π/2`. Its own docstring (`:685-686`) says so: "the integrated
  counter-rotating drive *attains* `1/2` **at `T = π/2`**", and (`:691-692`) defends the choice
  precisely because it is a computed value at a point rather than a bound.
- **Expected:** "The validity witness is stated at every `T`; the failure witness is an exact
  value at `T = π/2`, which is stronger than a bound at that point, not weaker."
- **Fix:** Rewrite the second sentence of the §4.1 header.
- **Cache:** n/a

### 5.2 — 🟡 REQUIRED — conjunct 3 of `diagonal_drive_nondegenerate_instantiation` is glossed as a ∀-claim the statement does not carry

- **Severity:** REQUIRED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:1679` (docstring) vs `:1706` (statement)
- **Observed:** Docstring bullet 3: "the drive operator is **not** a multiple of the identity (so
  the drive is not a global phase)". Statement conjunct 3:
  `driveOp a 0 0 d ≠ (a : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)`.
- **Evidence:** The conjunct excludes exactly one scalar multiple, `z = a`. "Not a multiple of the
  identity" is `∀ z : ℂ, driveOp a 0 0 d ≠ z • 1`. The stronger form is available and is used in
  the sibling theorem — `zRotation_not_scalar` (`:1598`) and
  `diagonal_drive_propagator_bound`'s third conjunct (`:1647`) both quantify over all `z`. So the
  file demonstrates it knew the difference and did not apply it here.
- **Expected:** Either strengthen conjunct 3 to the ∀-form (the proof at `:1723-1727` generalises:
  `driveOp a 0 0 d = diag(a+d, a−d)`, equal to `z•1` iff `d = 0`), or downgrade the docstring to
  "differs from `a·1`".
- **Fix:** Prefer strengthening the statement — the ∀-form is what "not a global phase" means.
- **Cache:** n/a

### 5.3 — 🟡 REQUIRED — "deliberately weaker binders" is false in the Ω coordinate

- **Severity:** REQUIRED
- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:1695-1697`
- **Observed:** "⚠️ This theorem collects the *nondegeneracy facts*; … (and its binders `ω ≠ 0`,
  `Ω ≠ 0` are **deliberately weaker** than the bound's `0 < ω`, `0 ≤ Ω`)."
- **Evidence:** `ω ≠ 0` is weaker than `0 < ω` ✓. But `Ω ≠ 0` and `0 ≤ Ω` are **incomparable**
  (`Ω = −1` satisfies the former only; `Ω = 0` the latter only), and `Ω ≠ 0` is *required* here —
  it discharges conjunct 4 (`counterRotating ≠ 0`, proof at `:1735-1736`) — while
  `diagonal_drive_propagator_bound` does not need it at all. In that coordinate the binder set is
  strictly stronger, not weaker.
- **Expected:** "`ω ≠ 0` is weaker than the bound's `0 < ω`; `Ω ≠ 0` is incomparable to `0 ≤ Ω`
  and is needed here for the nonvanishing-remainder conjunct."
- **Fix:** Rewrite the parenthetical.
- **Cache:** n/a

### 5.4 — 🟡 REQUIRED — §5 header states the resonance-only calibration identity without the resonance qualifier the module proves is necessary

- **Severity:** REQUIRED
- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:701-705`
- **Observed:** "## 5. Rotation-angle calibration at the RWA level … With this convention **the
  calibration identity is `θ = (m/2)·Ω·T`**, where `m = |⟨0|O_drive|1⟩|`."
- **Evidence:** Stated flatly, with no detuning qualifier, in the header of the section that then
  proves it false off resonance. `rwaRotationAngle`'s own docstring (`:756-758`) carries
  "⚠️ ON RESONANCE ONLY"; `rwaGenerator_sq`'s (`:722-725`) says "the familiar `(m/2)·Ω·T` is the
  `Δ = 0` case, **NOT the general one**. Detuning genuinely changes the rotation rate; a
  calibration that ignores it is wrong off resonance"; and
  `rwaRotationAngle_lt_generalRotationAngle` (`:773`) proves the strict inequality. The section
  header is the one place in §5 that omits the caveat — and it is the first thing a reader hits.
- **Expected:** "…the calibration identity **at zero detuning** is `θ = (m/2)·Ω·T`; the general
  form is `θ = (T/2)√(Δ² + Ω²m²)`."
- **Fix:** Add the qualifier at `:704`.
- **Cache:** n/a

### 6.1 — 🟡 REQUIRED — §4.1's exclusion argument rests on two Hermiticity facts the module never states, under a standard the module itself sets

- **Severity:** REQUIRED
- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:1009-1013`
- **Observed:** "stating the propagator bound against `S` itself would force `P + Q =
  counterRotating` … which no Schrödinger propagator pair with a nonvanishing remainder satisfies
  (**`P + Q` is anti-Hermitian, `V` is Hermitian, so they agree only where both are zero**)".
- **Evidence:** The claim is true, but neither supporting fact is a declaration. The module ships
  `driveOp_conjTranspose` (`:211`), `driveOp_isHermitian` (`:235`), `rwaGenerator_conjTranspose`
  (`:937`) — and **no** `counterRotating_conjTranspose` or `interactionHamiltonian_conjTranspose`
  (grep over `Control/RotatingWave.lean` for `conjTranspose|IsHermitian` returns exactly the seven
  declarations listed, none of them about `counterRotating`). §4.1d (`:1154-1157`) sets the
  standard explicitly: "That is a satisfiability assertion about a hypothesis set — exactly the
  category in which review 2 found a BLOCKER — **so it is proved here rather than asserted**."
  §4.1's exclusion claim is the same category and is asserted.
- **Expected:** Either a two-line `counterRotating_conjTranspose` (immediate from
  `driveOp_conjTranspose` + `sigmaY_conjTranspose`, exactly as `rwaGenerator_conjTranspose` is
  proved) plus the anti-Hermiticity of `i·H`, or the prose demoted from an exclusion claim to a
  motivation.
- **Fix:** Ship `counterRotating_conjTranspose`; it is cheap and it makes the §4.1 argument
  self-supporting to the standard §4.1d states.
- **Cache:** n/a

### 7.1 — 🟡 REQUIRED — `kramers_degeneracy_instantiated` supplies every hypothesis, but its witness is degenerate and *necessarily* so at ℂ² — undisclosed

- **Severity:** REQUIRED
- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/Control/DriveCalibration.lean:612-641`
- **Observed:** The asked-for confirmation holds: the ∃-statement supplies `hanti`, `hconj`,
  `hsq`, `hcomm`, `hreal`, `hv0`, `hv` and runs `kramers_degeneracy` on the complete bundle
  (`:640-641`), so the degeneracy theorem is no longer at risk of vacuity. The witness is
  `H = LinearMap.id`, `lam = 1`, `v = (1,0)`. The docstring discloses "this exhibits ONE
  admissible system (`H = id`, `lam = 1`)" and "it does not claim to characterise which `H` are
  admissible on `ℂ²`".
- **Evidence:** With `H = id` the eigenspace is the whole of ℂ², so the conclusion ("the
  eigenspace has dimension ≥ 2") is trivially true of a 2-dimensional space and the Kramers
  mechanism is not exercised. Worse, this is **forced, not chosen**: for the exhibited
  `Θ (z₀,z₁) = (−conj z₁, conj z₀) = J∘K`, a linear `H` commutes with `Θ` iff `J H̄ = H J`, i.e.
  `H ∈ {[[α, −β̄],[β, ᾱ]] : α,β ∈ ℂ}` (the quaternion algebra). Its characteristic polynomial has
  discriminant `−4(Im(α)² + |β|²) ≤ 0`, so `H` has a real eigenvalue **only** when `Im α = 0` and
  `β = 0` — i.e. only when `H` is a real scalar. So on ℂ² *every* witness of the full hypothesis
  set is scalar and hence maximally degenerate; a nondegenerate Kramers witness needs
  `dim ≥ 4`. The docstring's "does not claim to characterise which `H` are admissible" sidesteps
  exactly the fact a reader needs.
- **Expected:** The disclosure discipline the sibling module already applies — compare
  `RotatingWave.lean:1271` "⚠️ **This witness is DEGENERATE and must not be cited as more.**"
  and `:1330` "⚠️ DEGENERATE (see the section header)". The Kramers witness has no such marker
  despite being degenerate in the same way.
- **Fix:** Add "⚠️ DEGENERATE: at `dim = 2` the admissible `H` are forced to be scalars (real
  eigenvalue + `Θ`-commutation ⇒ `H ∈ ℝ·1`), so the exhibited eigenspace is the whole space. This
  establishes non-vacuity only; a witness where the Kramers partner is informative requires
  `dim ≥ 4`."
- **Cache:** n/a

### 7.2 — 🔵 RECOMMENDED — "six hypotheses" undercounts `kramers_degeneracy`'s binders by one

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/DriveCalibration.lean:612-614`
- **Observed:** "`kramers_hypotheses_inhabited` inhabits three of `kramers_degeneracy`'s **six**
  hypotheses; the other three — a commuting `H`, a real eigenvalue, a nonzero eigenvector — are
  supplied here."
- **Evidence:** `kramers_degeneracy` (`:575-579`) has **seven** explicit hypothesis binders:
  `hanti`, `hconj`, `hsq`, `hcomm`, `hreal`, `hv0` (`v ≠ 0`), `hv` (`H v = lam • v`). The gloss
  bundles `hv0` and `hv` into "a nonzero eigenvector", which is a defensible grouping but does not
  match the binder count a reader will get from the declaration.
- **Expected:** "three of seven", with the grouping made explicit.
- **Fix:** One-numeral edit.
- **Cache:** n/a

### 8.1 — 🟡 REQUIRED — roadmap line 79's reconciliation overshoots from four witnesses to five, and contradicts itself in the same sentence

- **Severity:** REQUIRED
- **Gate:** CrossPaperConsistency
- **Location:** `docs/roadmaps/Phase6EE_Roadmap.md:79`
- **Observed:** "a BITES/does-not-BITE witness pair for **all five** ceilings, every BITES half
  proved *through its own ceiling theorem* … and **every does-not-BITE half now *calling* its
  ceiling theorem** rather than restating that ceiling's bound expression by hand — … so this row
  is now an UNDERSTATEMENT of what **the four** witnesses prove".
- **Evidence:** `relaxation_ceiling_does_not_bite` (`CompositeReadoutCeilings.lean:524-535`) is
  the fifth does-not-bite witness and calls **no** ceiling: it is
  `∃ e0 e1, 0 ≤ e0 ∧ readoutDecayProb (1/1000) 1 ≤ e1 ∧ 999/1000 ≤ assignmentFidelity e0 e1`,
  proved from `expNeg_enclosure` by unfolding `assignmentFidelity`/`avgAssignmentError`. The Lean
  gets this right — §4.1's header (`:537-552`) is scoped "for the remaining four ceilings" and
  says "the description above can be stated of **all four**", and §4's header (`:500-503`)
  describes the relaxation witness separately as one that "exhibits a readout". The roadmap
  generalised the four-witness claim to five and then referred to "the four" in the same clause.
- **Expected:** "…and four of the five does-not-BITE halves now call their ceiling theorem; the
  relaxation one is an existential exhibiting a readout, which is a different and stronger shape."
- **Fix:** Rewrite line 79's clause. This is the requested overshoot check: **line 79 overshot.**
- **Cache:** n/a

### 8.2 — 🟡 REQUIRED — roadmap decl counts are stale against a freshly regenerated `lean_deps.json`

- **Severity:** REQUIRED
- **Gate:** CountFreshness
- **Location:** `docs/roadmaps/Phase6EE_Roadmap.md:76-79` (the `Decls` column)
- **Observed / Expected:**

  | Module | Roadmap | `lean_deps.json` |
  |---|---:|---:|
  | `RotatingWave` | 112 | **117** |
  | `BanachAveraging` | 8 | 8 ✓ |
  | `DriveCalibration` | 36 | **45** |
  | `CompositeReadoutCeilings` | 35 | **44** |

- **Evidence:** `lean/lean_deps.json` regenerated `2026-08-01T04:40:53Z` — after the class sweep,
  so the sweep's 14 new theorems are in it. Counted by `module` field over 40 262 entries.
  `validate.py --check count_literals` scans `papers/**` only and does not cover roadmap tables,
  so this drift is ungated.
- **Fix:** Refresh the three counts. See the QI candidate below for the gating gap.
- **Cache:** n/a

### 9.1 — 🔵 RECOMMENDED — duplicate section number and scrambled section ordering in `RotatingWave.lean`

- **Severity:** RECOMMENDED
- **Gate:** NarrativeGrounding
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:665` and `:1002`
- **Observed:** Two distinct sections are both numbered `### 4.1` — "Witnesses: where the reduction
  is controlled" (`:665`) and "The Schrödinger-picture antiderivative" (`:1002`). File order of
  headings is: §1, §2, §2.0, §2.1, §2.2, §3, §3.1, §3.15, §3.2, §4, **§4.1**, §5, §6, §3.5,
  **§4.1**, §4.1b, §4.1d, §4.2, §4.1c.
- **Evidence:** §4.1b's opening (`:1069`) — "§4.1's theorem is stated over abstract `L`, `U`, `P`,
  `Q`" — is ambiguous between the two §4.1s (it means the second). §6 (`:793`) precedes §3.5
  (`:830`); §4.1d (`:1152`) precedes §4.2 (`:1262`) which precedes §4.1c (`:1371`).
- **Fix:** Renumber the witnesses section (e.g. §3.3) and reorder or renumber so headings ascend.
- **Cache:** n/a

### 9.2 — 🔵 RECOMMENDED — `rotFrame_ode`'s docstring asserts uniqueness its statement does not carry

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/RotatingWave.lean:136-137`
- **Observed:** "**The defining ODE.** `R'(t) = i(ω/2)·σ_z · R(t)` — **so `rotFrame` is the unique
  solution with `R(0) = 1`**, i.e. genuinely `exp(i(ωt/2)σ_z)`."
- **Evidence:** `rotFrame_ode` (`:138-141`) is an *algebraic identity* between two matrices; it is
  not even a `HasDerivAt` statement (that is `rotFrame_hasDerivAt`, `:120`), and it carries no
  uniqueness. Uniqueness is `rotFrame_unique` (`:160`). The §2.0 header (`:106-112`) states this
  correctly — "The first two alone would leave 'pinned uniquely' as prose; the third is what
  discharges it" — so the theorem docstring contradicts its own section header.
- **Fix:** Replace "so `rotFrame` is the unique solution" with a pointer to `rotFrame_unique`.
- **Cache:** n/a

### 9.3 — 🔵 RECOMMENDED — `calibrated_duration_transverse_propagator_full` attributes axis-blindness to a theorem that proves only direction-blindness

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/DriveCalibration.lean:152-154`
- **Observed:** "The trace form above is **even in `θ`**: `U` and its time reverse share it — which
  is `trace_blind_to_rotation_direction` below, proved rather than observed — **so it certifies
  neither the rotation DIRECTION nor the AXIS**."
- **Evidence:** `trace_blind_to_rotation_direction` (`:172-177`) proves only that `U(−t)` and
  `U(t)` share a trace while differing — direction. Axis-blindness is nowhere stated; it is
  immediate from `rwaPropagator_trace` (which is independent of `b`, `c`, `φ`), but in a module
  whose idiom is "proved rather than observed", half of a two-part claim carries no declaration.
- **Fix:** Either cite `rwaPropagator_trace` for the axis half, or say the axis half is immediate
  from it.
- **Cache:** n/a

### 9.4 — 🔵 RECOMMENDED — two small numeral/proof-description slips

- **Severity:** RECOMMENDED
- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/Control/DriveCalibration.lean:286`; `Control/CompositeReadoutCeilings.lean:501-502`
- **Observed:** (a) `calibrated_duration_longitudinal`: "Carries the same co-rotating-model caveat
  as **the two** transverse identities above" — three transverse identities above carry it
  (`calibrated_duration_transverse` `:67`, `calibrated_duration_general` `:82`,
  `calibrated_duration_transverse_propagator` `:140`). (b) CompositeReadoutCeilings §4: "the BITES
  half calls `relaxation_ceiling` and **settles under `norm_num` alone**" — the proof
  (`:513-515`) is `norm_num at h; linarith`.
- **Fix:** "the transverse identities above"; "settles under `norm_num` + `linarith`".
- **Cache:** n/a

---

## Confirmations (verified true — the sweep's own instances)

Every one of these was checked against the Lean, not accepted from the sweep log.

1. **`calibrated_duration_divisor_eq_rate`** (`DriveCalibration.lean:96-100`) — identity **correct**:
   `rwaRate = √(Δ²+Ω²m²)/2`, so `θ/rwaRate = 2θ/√(…)` ✓. The "unconditional" claim is **correct**:
   at a vanishing radicand `√ = 0` and `rwaRate = 0`, and both sides are `0` under Lean's division
   convention ✓. Divisor sweep: `calibrated_duration_general:81` ("`T = 2θ/√(Δ²+Ω²m²)`") ✓,
   `calibrated_duration_transverse:57` ("`T = 2θ/(m·Ω)`") ✓, `rwaGenerator_sq_eq_rate_sq:105`
   ("it is `2·rwaRate`") ✓, `rwaAxisPhasor:345` ("half the Bloch-sphere rotation rate") ✓.
   **No other docstring carries a wrong divisor.** But see finding 3.1 — the reciprocal error
   survives in `rwaRate`'s own docstring.
2. **`kramers_degeneracy_instantiated`** — all seven binders supplied and `kramers_degeneracy`
   actually run on the bundle ✓. Non-degeneracy: **not** established, and cannot be at ℂ² — see 7.1.
3. **`photon_budget_ceiling_does_not_bite`** (`:621`) — `refine ⟨photon_budget_ceiling hδ, ?_⟩` ✓.
   **`relaxation_thermal_ceiling_does_not_bite`** (`:581`) —
   `refine ⟨relaxation_thermal_ceiling he0 hd hth, ?_⟩` ✓. The §4.1 roster claim now holds of all
   four ✓ (`filtered_readout_ceiling_does_not_bite:828` and
   `detector_chain_ceiling_does_not_bite:851` also call theirs).
4. **`rwa_propagator_difference_bound_physical` scoping** — **honest; keep the claim.** The theorem
   is non-vacuous (`diagonal_drive_propagator_bound`), the b ≠ 0 limitation is stated precisely,
   and "no such object is shipped here" does not overclaim non-existence. One clarity gap: 1.2.
5. **Roadmap line 93** (M3 row) — reconciled correctly; no residual "first cross-layer composite".
   Matches the Lean at `CompositeReadoutCeilings.lean:335-342` ("⚠️ No priority is claimed here,
   and none is provable from the statement") ✓.
6. **Roadmap line 351** ("the deepest chain … `bolometer_error_floor` calls
   `error_floor_from_budget` + `nep_quadrature_add`") — **verified in the body**:
   `Electrothermal/BolometricFloors.lean:816` calls `nep_quadrature_add`, `:818` calls
   `error_floor_from_budget` ✓. No overshoot.
7. **DriveCalibration §5's characterisation of `MajoranaKramers`** (`:491-496`) — **verified
   accurate**: `kramers_anticommutation` (`MajoranaKramers.lean:127-130`) is
   `(j2_a a_j2 : ℝ) (h : j2_a + a_j2 = 0) : j2_a = -a_j2 := by linarith`; and
   `kramers_pfaffian_definite_sign` (`:142-148`) is
   `(pf1 pf2 : ℝ) (h_kramers : ∀ (a : ℝ), a = a) … : pf1 * pf2 ≥ 0 := by positivity`, with the
   placeholder hypothesis exactly as described ✓.
8. **CompositeReadoutCeilings module-header roster** (`:16-22`) — verified:
   `avgAssignmentError_combined_floor` (`ThermalAssignmentFloor.lean:230-234`) proves the max-form
   directly by `max_cases`/`linarith` and does **not** route through
   `avgAssignmentError_thermal_floor` ✓. `avgAssignmentError e0 e1 = (e0+e1)/2` ✓
   (`ReadoutRelaxationBound.lean:143`).
9. **§4.2's `76 %` figure** — `3/25 = 0.12` against `Q(1) = 0.1586553` is 75.6 % ✓, consistent with
   the upstream docstring at `Detection/GaussianThreshold.lean:638-642`.
10. **§4.3's recomputation** — `x = 2Q/(1−2Q)` with `Q(1) = 0.15865525` gives `0.464795…` ✓;
    the retracted `0.4651` does solve to `Q = 0.158726` ✓.
11. **`combined_ceiling_gap_witness`** — `1/200` gap arithmetic ✓
    (`1 − 1/100 = 0.99`, `1 − 3/200 = 0.985`), derived through `combined_ceiling_add_lt_max` ✓.
12. **`validate.py --check lean_docstring_refs_resolve`** passes with **zero** `Control` findings —
    confirming the strict-family widening landed, and confirming that every finding above is
    outside what that gate can see (all mis-pointed identifiers *exist*).

---

## Verdict on the confirmation/discovery question

**Discovery pass.** The instances the sweep enumerated were genuinely closed — all twelve
confirmations above check out, including the two theorem-level restatements and the new
`calibrated_duration_divisor_eq_rate`. What was not closed is the class:

- The satisfiability counterfactual (1.1) is the *same category* §4.1d was built to discharge.
  §4.1d shipped a proof for one family (`rwaPropagator ω ω Ω 0 1 0 t`) and left three docstrings
  asserting a universal. That is instance-depth remediation of a class-depth defect, and the
  refutation is sitting in the same file (`norm_zRotation`, `norm_rwaPropagator_diagonal`) and in
  the file's own headline instantiation (`KL = KU = KUr = 1`).
- The factor-of-two (3.1) is the same category `calibrated_duration_divisor_eq_rate` was added
  for. The new theorem is correct; the docstring of the very definition it is about still says
  "half the magnitude of `rwaGenerator`", contradicted by the theorem it cites as justification
  and by a second module.
- The mis-pointed `rwa_propagator_difference_bound` (4.1, 4.2) is the same category as the
  "corrected 2026-07-30" note at `:1698-1701`, which fixed one such pointer and left two.

None of the three carries a numeral, a superlative, or an unresolvable identifier, so none was
reachable by the author's regex — consistent with the stated measurement, and consistent with the
brief's expectation of residue.

---

## QI Candidate

**Class-sweep completion is not verifiable by the predicate that scoped it, and nothing gates
the gap.**

Three independent signals here point at one pipeline hole:

1. `lean_docstring_refs_resolve` is now strict for `SKEFTHawking.Control.` and passes clean, yet
   findings 4.1 and 4.2 are wrong-target citations. The gate checks *resolution*, not *reference
   correctness* — a docstring naming an existing-but-wrong sibling is invisible to it. The
   highest-yield mechanisable strengthening available: for any docstring that names a declaration
   `X` with a sibling `X_physical` / `X_inhabited` / `X_general`, flag the bare name as
   ambiguous-by-family and require disambiguation. Cheap, and it would have caught both.
2. Counterfactual and satisfiability claims ("would exclude every…", "would make the
   hypotheses unsatisfiable…", "no pair satisfies…") are the class in which reviews 2 and 6 both
   found BLOCKERs and in which 1.1 and 6.1 sit now. They carry no numeral and no superlative, so
   the sweep's predicate had **zero** recall on them. A modal predicate does far better:
   `grep -nE "would (exclude|make|force|be|have|leave|state|carry|survive)"` over `Control/`
   returns 16 candidate sites, and 1.1's RotatingWave sites (`:1154`, `:1208`, `:1221`, `:1247`,
   `:1250`) plus 6.1 (`:1009`, `:1012`) and 2.1 (`BanachAveraging:214`) are all among them —
   good recall, mediocre precision (the remaining 8 are legitimate contrastive prose, so this is
   an adjudication queue, not a defect list, exactly as the sweep log says of its own predicate).
   **Important mechanical caveat measured here:** that same grep **misses**
   `BanachAveraging.lean:94-95`, the primary site of 1.1, purely because the docstring is
   hard-wrapped mid-phrase ("…`‖L s‖ ≤ 1` would" / "exclude every rotation…"). Any line-oriented
   predicate over this corpus under-reports; the enumeration must run over **unwrapped doc
   blocks**. That alone may account for part of the "reported `RotatingWave.lean` CLEAN" miss.

3. Roadmap decl-count tables are outside `count_literals`' scope (papers only), so 8.2's
   three-module drift shipped silently one day after `lean_deps.json` was regenerated. Extending
   `count_literals` to `docs/roadmaps/*.md` tables is mechanical.

The systemic point for the register: **a sweep whose completion criterion is its own enumeration
predicate cannot report residual class members, and three rounds have now confirmed that the
predicate's blind spot and the defect class's centre of mass are the same region** (modal
counterfactuals, quantifier scope, and sibling-name citations — none numeral-bearing). Sweep
closure should require a predicate-independent reading pass over the class, not a re-run of the
predicate.
