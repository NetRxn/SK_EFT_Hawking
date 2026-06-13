# ADR-002 — `native_decide` policy (compiler-trust axiom in the anyon/TQFT computation layer)

- **Status:** **ACCEPTED (2026-05-30).** Policy + execution plan vetted and executed: the Bucket-B sweep
  is complete (63 modules → kernel `decide`) and the publication-critical Category-A flagships are hardened
  (the two D4 Fibonacci QCyc5 modules). Both open items from the 2026-05-29 vetting addendum are resolved
  (see "2026-05-30 execution outcome" below): (i) **Route 1′ is DEFERRED** — the high-degree types
  (`QCyc16` Ising / `QCyc40` D6 / `QCyc5Ext` matrix reps) stay documented `native_decide`, gated on a
  future Route-1′ metaprogram as a separate substrate project; (ii) the **quantified-`decide` wall-clock**
  is resolved empirically (small `+revert` enumerations like `SU2kFusion` convert fine; large ones like
  `KacWaltonFusion`'s alcove enumeration are too slow and stay `native_decide`).
  - *History:* Accepted 2026-05-28 → DRAFT 2026-05-29 (vetting) → ACCEPTED 2026-05-30 (executed).
- **Deciders:** John Roehm (project owner); investigation + draft by Claude.
- **Context source:** P4 `axiom_closure_allowlist` gate (`docs/AI-Defect-Defense-Layer.md`, commit `1798633`) +
  triage report (`temporary/working-docs/native_decide_triage.md`, commit `e021fe0`) + this investigation.
- **Related:** [ADR-001](ADR-001-commring-qcyc5ext-roadmap.md) (QCyc5 CommRing / ext roadmap — supplies the
  kernel-pure machinery used below); Pipeline Invariant #15 (no undocumented project axioms).
- **See also:** [ADR-004](ADR-004-substrate-integrity-gates.md) (Substrate Integrity Gates) — this ADR's
  **P4 gate** (`validate.py --check axiom_closure_allowlist`) remains the sole owner of the `native_decide`
  compiler-trust surface and its elimination policy. ADR-004 builds *on top of* it without changing it:
  **R4** surfaces the P4-gate decl-closure count (546 as of 2026-06-10) into `counts.json` with a
  regression threshold; **R2's** proxy-body detector explicitly *excludes* the `native_decide`/finite-
  combinatorial-`decide` class (deferred here); **R5** enforces Decision #2's "kernel-checked modulo
  `native_decide`" prose-precision at the paper-claim level.

## Context

The P4 axiom-closure gate surfaced that, while the project has **0 declared `axiom`s**
(`counts.json` `Axioms: 0`, Invariant #15 genuinely clean) **and 0 genuinely-unexpected axioms**, the
kernel trust base is larger than the three standard axioms `{propext, Classical.choice, Quot.sound}`:

- **1005 `native_decide` call sites across 98 files**; **811 declarations** carry a `native_decide`
  compiler-trust axiom (`Lean.ofReduceBool`, emitted per-decl as `*._native.native_decide.ax_*`) in
  their transitive closure. `native_decide` trusts the *compiled evaluator*, not just the kernel.

`counts.json 'Axioms: 0'` counts declared axioms, so it does not capture this. We investigated four
questions before deciding policy.

### Q1 — Is Aristotle the right tool to remove these? **No (capable, but wrong economically).**
Category-B goals don't need it (`decide` works). Category-A goals are decidable finite ring identities
that Aristotle *could* close, but Aristotle is a whole-project ~1-day batch on Mathlib 4.28; feeding it
hundreds of "the computation just needs to reduce" goals is the wrong tool. The natural fix is a local
componentwise/`ext` proof (see Decision) or reducible instances.

### Q2 — Mechanical limitation, or does the math need rethinking? **Mechanical.**
`decide` reports *"did not reduce to isTrue/isFalse"* purely because the custom `Decidable`/arithmetic
instances don't reduce under kernel whnf. The facts are not uncertain. Refactoring is a trust/purity
choice, not a correctness necessity.

### Q3 — Are the facts established physics/math? **Yes, essentially all.**
The `native_decide` modules verify *known* literature results: fusion rules (Kac–Walton, Verlinde,
SU(2)_k/SU(3)_k Clebsch–Gordan), braiding/R-matrices (FLW 2002, Kitaev, Ising MTC over Q(ζ₁₆)),
Frobenius–Perron dimensions (Etingof–Nikshych–Ostrik), WRT 3-manifold invariants
(Witten–Reshetikhin–Turaev). The recurring "FIRST verified … in any proof assistant" framing is the tell:
**the novelty is the formalization, not the facts.** The compiler-trust is therefore low-stakes — we are
computationally confirming independently-established results, not deriving novel claims a compiler bug
could silently invent.

### Q4 — Are any `native_decide` in the upstream-Mathlib-intended pieces? **No — clean (the key result).**
`native_decide` is **banned in Mathlib proper**, so any in upstream-PR-bound code would be a hard
blocker. Checked the explicitly-upstream modules (`*MathlibPR.lean` — Cartan, SK length bound, matrix-exp
homeomorphism; `MathlibAux/Pfaffian`): **zero `native_decide`, directly or transitively** (full axiom
closures verified). Expected — the PR targets are general analysis/algebra, while `native_decide` lives
entirely in the finite anyon/TQFT computation layer, which is not a PR candidate. **So `native_decide` is
not a blocker for any planned or future Mathlib PR**, and the Phase-6z Wave-2/4 upstream pieces (unitary
spectral theorem via `JointEigenspace`, etc.) are `native_decide`-free by construction.

### Feasibility spot-check (measured) — two categories

| Category | Modules | kernel `decide` | Convertible |
|---|---|---|---|
| **A. custom-type arithmetic** (cyclotomic `QCyc*`) | `FibonacciBraiding`, `QCyc5/40`, `A1Ring`, … | **fails** (instances don't whnf-reduce) | ✓ via `ext`+componentwise (confirmed below) |
| **B. `Fin`/`Nat` fusion tables** | `SU2kFusion`, `SU3kFusion`, … | **works** (module rebuilds clean) | ✓ near-drop-in |

**Category-A kernel-pure conversion is confirmed with a compiling proof** (same machinery as the QCyc5
CommRing instance, ADR-001). Working template (`FibonacciBraiding.F_sq_00`, verified 2026-05-28):

```lean
theorem F_sq_00 : F00 * F00 + F01 * F10 = 1 := by
  ext <;>
    simp [F00, F01, F10, phi_inv, QCyc5.mul_c0, QCyc5.mul_c1, QCyc5.mul_c2, QCyc5.mul_c3,
      PolyQuotQ.mulReduce_coeffs, QCyc5.toPoly, Fin.sum_univ_four,
      QCyc5.powerTable_0_0, …, QCyc5.powerTable_6_3]   -- all 28 powerTable_m_k rfl-lemmas
```

**Gotcha (the one non-obvious bit):** do **not** put `QCyc5.reduction` in the simp set. It unfolds
`reduction` to `![-1,-1,-1,-1]`, after which the `powerTable_m_k` lemmas (stated over `QCyc5.reduction`)
no longer match and the power-table lookups never resolve. Keep `reduction` symbolic.

## Decision

1. **Adopt `native_decide` as explicit, documented policy** for finite combinatorial facts in the
   anyon/TQFT/quantum-group computation layer. It is a standard, accepted Lean mechanism; given Q3
   (established facts) + Q4 (no PR blocker), the residual compiler-trust is acceptable here.

2. **Word "kernel-verified" claims precisely.** Project/paper statements must say *"kernel-checked modulo
   `native_decide` for finite combinatorial facts (anyon fusion/braiding, modular data)"* rather than
   implying a pure three-axiom base. This removes the only real inaccuracy (`Axioms: 0` reading as
   "pure-kernel"). The headline analytic results (Phase-6x/6z substrate, the upstream-PR pieces, the new
   Phase-6z Wave-1 seed) remain pure `{propext, Classical.choice, Quot.sound}` — verified by `lean_verify`
   and Q4.

3. **Keep the P4 gate as-is** (`validate.py --check axiom_closure_allowlist`): WARN-first, recognizes
   `native_decide` as a distinct accepted-but-visible category, hard-fails under `--strict` on any
   *genuinely-unexpected* axiom (currently 0). It is the standing backstop for Invariant #15.

4. **Convert Category B opportunistically** (`Fin`/`Nat` fusion tables → kernel `decide`). Near-drop-in,
   free trust-surface reduction; verify per module that `decide` compiles in reasonable time (large
   `+revert` enumerations may need `intro`-then-`decide` or stay `native_decide`).

5. **Do NOT mass-convert Category A.** Harden Category A to kernel-pure (`ext` + the
   `mul_cᵢ`/`powerTable_m_k` template above) **only for genuinely publication-critical theorems** — the
   Fibonacci/Ising universality matrices, WRT invariant values, the FP-dimension derivations — where a
   "fully kernel-checked" claim adds publication value. The remainder stays documented `native_decide`.
   (A future `QCyc*` reducible-`DecidableEq` refactor could make these `decide`-able directly and is a
   candidate reusable contribution, but is out of scope here.)

6. **Aristotle is not used for this** (Q1): wrong economic tool; the local `ext`-template is cheaper and
   kernel-pure.

## Consequences

**Positive.** Accurate trust narrative; the P4 gate makes the trust surface permanently visible and
prevents *new* undocumented axioms; upstream Mathlib PRs are unaffected; Category-B conversions shrink the
surface for free; a verified, reusable kernel-pure template exists for any Category-A theorem that needs it.

**Negative / accepted.** ~811 declarations retain a compiler-trust dependency (mitigated by Q3: all verify
established facts). Category-A `ext` proofs are more verbose than `native_decide` (28 `powerTable` lemmas in
the simp set), so we convert only where it earns its keep.

**Follow-ups (not blocking).** (a) Category-B sweep to `decide`; (b) per-bundle cross-reference
(`docs/agents/claims-reviewer-bundle-prompts.md`) of which paper-anchor theorems hit Category-A
`native_decide`, to scope the targeted hardening; (c) ~~optional `QCyc*` reducible-instance refactor~~ →
see the 2026-05-29 addendum: the `decide`-reducible refactor is a dead end over `ℚ`; the real enabler is
the Route-1′ metaprogram.

---

## 2026-05-29 vetting addendum (status → DRAFT)

Scouting the execution plan (companion: `temporary/working-docs/native_decide_cleanup_checklist.md`) produced two findings
that revise the path, so the ADR is back to DRAFT until re-vetted:

1. **Base-type readiness (decisive).** Of the `QCyc*`/`QSqrt*` family, **only `QCyc5`/`QCyc5Ext` have the
   ADR-001 kernel-pure machinery** (`CommRing` + `mul_cᵢ` + `powerTable_m_k`). Every other base type
   (`QCyc3/15/16/40/80`, `QSqrt2/3/5`, `QLevel3`, extensions) delegates `*` to `PolyQuotQ.mulReduce` (the
   simp-opaque `Array.ofFn`/bang-indexed rep) with **no** `CommRing` instance and **none** of the lemma
   set. So Category-A hardening (Decision #5) is gated on building that machinery per type, and the cost
   scales `O(deg²)`: ~6 lemmas at deg 2, ~28 at deg 4 (QCyc5, shipped), ~120 at deg 8 (`QCyc16`, Ising),
   ~480 at deg 16 (`QCyc40`, D6 T-gate), ~2000 at deg 32 (`QCyc80`).

2. **`decide`-reducibility is a dead end over `ℚ` (empirically confirmed).** Kernel `decide` fails on `ℚ`
   arithmetic *itself* — `(3 : ℚ) * 2 = 6 := by decide` gets stuck at `(Rat.mul 3 2).num` because
   `Rat.mul`/`Rat.add` are irreducible-by-design (`Rat.normalize`/`Nat.gcd` don't whnf-reduce). No
   `Array→List` / `Finset→Nat.fold` refactor of `mulReduce` changes this; the coefficient comparison is a
   `ℚ` equality. This is *why* ADR-001 used `ext`+`simp[powerTable]`+`ring`/`norm_num` (symbolic, no
   `decide`). Q4's earlier characterization of a "reducible-instance refactor" as a possible win is
   **retracted** for the `decide` reading.

**Revised path (supersedes the loose "type refactor" suggestion):**
- **Route 1** (powerTable + `ext`/`ring`, per type) is the only proven kernel-pure method; works at any
  degree, but `O(deg²)` lemmas by hand.
- **Route 1′** (the recommended substrate investment): a `simproc` / `norm_num` extension (~200–500 LoC)
  that reduces `(mulReduce n r x y).coeffs k` symbolically (or auto-generates the per-type `powerTable`
  simp set), making Route 1 degree-scalable. Prototype on `QCyc16` (deg 8) before committing. This is the
  enabler for any high-degree (D6/Ising) hardening.
- **Route 2** (coefficient-rep change away from `ℚ` to recover genuine `decide`): cross-cutting rewrite,
  marginal payoff over Route 1′, `ℚ` genuinely needed for F-symbol denominators — **not recommended.**

**Mathlib check (does a built-in already do this?):** No. `AdjoinRoot` / `CyclotomicField` / `Polynomial`
are all `Finsupp`+`Classical.decEq` → noncomputable for `decide` (this is exactly what `PolyQuotQ` was built
to bypass; see its module docstring). There is no kernel-`decide`-able number field in Mathlib, and there
fundamentally can't be one over `ℚ` given `Rat`'s irreducible arithmetic. The correct Mathlib tools for this
job are the *symbolic* ones (`ring`, `norm_num`, `Fin.sum_univ_*`), which ADR-001 already uses — we are not
missing a built-in. A reusable Route-1′ `simproc` would itself be a plausible Mathlib-PR-quality contribution.

**Decision items (resolved by the 2026-05-30 execution — see next section):** (i) **defer Route 1′** — the
high-degree/tower modules stay documented `native_decide`; (ii) quantified-`decide` is fine for small
`+revert` enumerations (`SU2kFusion`) but too slow for the large ones (`KacWaltonFusion` alcove → stays
`native_decide`).

---

## 2026-05-30 execution outcome (status → ACCEPTED)

The cleanup was executed in an isolated `/goal` session against the post-Phase-6x baseline
(115 files / 1036 `native_decide` call sites / **852** declarations carrying the `native_decide`
compiler-trust axiom in their transitive closure).

**Result: decl-closure 852 → 587 (−265 declarations now kernel-pure); call sites 1036 → 712; files
115 → 53.** (The raw call-site count fell less than the decl count because the cleanup *added* documenting
comments that themselves contain the literal word `native_decide`; the **decl-closure 587** is the
authoritative trust-surface metric — 265 declarations no longer reach a `native_decide` compiler-trust
axiom.) P4 gate PASS; Invariant #15 clean; full `lake build SKEFTHawking` green throughout; Stage-13
adversarial review GREEN-WITH-RECOMMENDED.

### Bucket B — converted (Decision #4): 63 modules
Probe-first (whole-file `native_decide`→`decide` build, reverted on failure) sorted A from B definitively —
the reliable signal is the **value type of the `decide`'d equality**, not the module/index name. All
axiom-verified kernel-pure via `#print axioms`:
- **Fusion/MTC:** SU2kFusion (incl quantified `decide +revert`), SU3kFusion, SU2kMTC, RepUqFusion,
  KacWaltonFusion (hDual/alcove `Nat` facts), FusionExamples.
- **A(1)-Ext / Steenrod (publication D2/L2):** A1Ring, A1Ext, SteenrodA1 — `Matrix _ _ F2` value types that
  DO kernel-reduce, so a *free kernel-pure upgrade of a publication anchor* (probe-first §0 paid off: they
  were mis-classifiable as Category-A on name alone).
- **Constraint-counting / SK / physics (12):** incl the L2/D2 headline `three_gen_with_nu_R_anomaly_free`.
- **Fracton / topology / physics-model (16); FKLW/Ross–Selinger + FaultTolerance/ETH (24); list/struct (4).**

### Category A — publication-critical hardening (Decision #5)
The ADR-001 §3-A `ext`/`powerTable` template, registered as a **file-local simp set** (the 28
`powerTable_m_k` rfl-lemmas + `mul_cᵢ` + `mulReduce_coeffs` + `toPoly`; `QCyc5.reduction` excluded per the
gotcha):
- **FibonacciBraiding** (D4 "FIRST verified universal quantum gates"): **20 of 30** theorems kernel-pure —
  F²=I involution (F_sq_00/01/10/11), F11_eq, det F, σ₁ det/trace/non-triviality, σ₂ trace, the σ₁σ₂
  off-diagonal non-scalar facts, `R1_order_5`, `Rtau_order_divides_10`, `R1_not_one`. Equalities use
  `ext <;> simp [<defs>]`; inequalities `intro h; rw [QCyc5.ext_iff] at h; simp [<defs>] at h`. The **10
  retained** (`sigma2_det`, the 4 Yang-Baxter `braid_*`, the 5 (σ₁σ₂)³ `s1s2_cu_*` center/scalar facts, the
  intermediate R-power inequalities) hit the heartbeat budget under full symbolic expansion (σ₂ = F·R·F, then
  cubed); per Invariant #10 we do **not** raise `maxHeartbeats`, so they stay documented `native_decide`.
- **FibonacciMTC**: `fib_tau_sq` (Fin/Nat) → kernel `decide`.

### Documented native_decide (Decision #2, "kernel-checked modulo native_decide", with module comments)
FibonacciUniversality + FibonacciQutrit (the QCyc5Ext two-level tower Q(ζ₅,√φ) / 3×3 `Mat3K`), QSqrt5
(FibonacciMTC F-symbols), the heartbeat-bound FibonacciBraiding braid/σ₂/`s1s2_cu` identities, A1Resolution
(8×8-expanded F2-matrix products, kernel-`decide`-able in principle but impractically slow), KacWaltonFusion
(alcove enumerations), SU2kMTC (Q(√2)), and the Route-1′-gated high-degree QCyc16 (Ising) / QCyc40 (D6)
modules.

### Key finding (the technical lesson)
The `ext`/`powerTable` template is viable for a **base powerTable-equipped field** (`QCyc5`) but **NOT for the
higher towers** (`QCyc5Ext` = Q(ζ₅,√φ), `QSqrt5`, `QCyc16/40`, or matrices over them): the nested
base-`powerTable`-inside-`mulReduce2` (and 3×3-matrix) expansion exceeds the heartbeat budget on every
theorem. This confirms Decision (i): **defer Route 1′** (the ~200–500 LoC simproc/`norm_num` metaprogram) to a
separate substrate project; high-degree/tower modules stay documented `native_decide`. (Likewise QSqrt5 would
need a degree-2 CommRing substrate.) The headline D4 universal-gate result is hardened kernel-pure where it
counts — the base-field `QCyc5` facts in FibonacciBraiding — and the tower layers verify established literature
(FLW 2002; Q3): the formalization, not the fact, is the contribution.

### Process notes (for the next cleanup)
- **Restrict the substitution to TACTIC positions — do NOT blind-replace the word.** A file-wide
  `perl -i -pe 's/\bnative_decide\b/decide/g'` also rewrites `native_decide` *inside comments and
  docstrings* of files whose proofs are not converted, producing false provenance (e.g. "kernel-pure, no
  `decide`", "`decide` / `decide`", or a perf claim that `decide` is tractable on a deg-16 cyclotomic
  matrix). This happened on 2026-05-30 and was repaired on 2026-05-31. Match only tactic occurrences —
  `:= by native_decide`, a line-final `by native_decide`, `<;> native_decide`, `by native_decide⟩` — not
  the bare word. macOS/BSD `sed` lacks `\b`; use `perl`. Guard a probe driver with `diff -q` (a no-op
  replace must not report "CONVERTED") + a tactic-position grep.
- **If a file-wide replace is used anyway, two extra gates are MANDATORY before commit:**
  (i) **read the FULL diff of every changed file — not a spot-check.** The comment damage concentrates in
  files whose *proofs* never changed, so reviewing only the converted theorems misses it entirely.
  (ii) run `uv run python scripts/lint_native_decide_comments.py` (ERROR-tier must be clean) and
  `--strict` to review the WARN-tier contrastive-phrase hits. The linter catches the duplication and
  "no/never/not/tracked `decide`" artifacts but **not** high-degree perf-claim mangles (the Rouabah class:
  "30-deep `decide`" on QCyc40Ext) — those are textually identical to legitimate finite `decide` and are
  caught only by the full-diff read plus the fact that a genuinely-converted high-degree `decide` fails to
  build or retains the native axiom.
- Verify every conversion with `#print axioms` (no `*._native.native_decide.ax_*`), never on build-success
  alone — a no-op edit also builds green; and never commit before a full `lake build SKEFTHawking` is green.

---

## 2026-05-31 Route-1′ scope (deferred substrate project)

The 2026-05-30 execution deferred Route-1′ (Decision i). This section scopes it concretely so the decision to
build it later is a costed one rather than a deferred unknown. **Status: deferred, not scheduled.** Nothing
below is committed work; it is the design a future substrate wave would execute if the trigger (bottom) fires.

### Goal
Make the kernel-pure `ext`/`powerTable` template (the method that hardened the `QCyc5` base-field facts in
`FibonacciBraiding`, 20/30) **degree-scalable**, so the higher cyclotomic types can be hardened without
hand-authoring O(deg²) `powerTable_m_k` rfl-lemmas: `QCyc16` (deg 8, ~120 lemmas), `QCyc40` (deg 16, ~480),
`QCyc80` (deg 32, ~2000), plus the two-level towers (`QCyc5Ext`, `QSqrt5`) and matrices over them.

### Obstruction (two compounding walls)
1. **Lemma blow-up.** A degree-d field needs ≈(2d−1)·d `powerTable_m_k` lemmas for `simp` to fold ζ-power
   products. 28 by hand at deg 4 (`QCyc5`, shipped) is fine; 120/480/2000 is not.
2. **Tower nesting.** `QCyc5Ext = QCyc5[√φ]` delegates `*` to `mulReduce2`, which nests the *base* `QCyc5`
   `powerTable` reduction inside the degree-2 extension. Even with a base powerTable the fully-symbolic
   expansion blows the heartbeat budget — this is why the hand-template tops out at base `QCyc5` (confirmed
   empirically 2026-05-30; see "Key finding" above).

### Hard design constraint (the ℚ-wall)
The metaprogram **must be symbolic** — emit ℚ-equalities closed by `norm_num`/`ring` — **not** an attempt to
make `decide` reduce. Kernel `decide` is dead over ℚ (`Rat.mul`/`Rat.add` irreducible by design; addendum
finding 2). The output tactic stays `simp [<simproc>] <;> norm_num`, kernel-pure
`{propext, Classical.choice, Quot.sound}`. No Mathlib built-in does this (`AdjoinRoot`/`CyclotomicField` are
`Finsupp + Classical.decEq` → noncomputable; addendum Mathlib check).

### Two implementation routes
- **Route 1′-a — coeff-level simproc (RECOMMENDED).** A `simproc` on the pattern
  `(PolyQuotQ.mulReduce _ r _ _).coeffs _` that (i) evaluates the coefficient convolution symbolically over
  ℚ, (ii) folds degrees ≥ d back via the reduction vector `r`, (iii) emits a `norm_num`-closable ℚ equality.
  Degree-agnostic, and the **only** route that also handles *towers* (recurse into coeffs that are themselves
  base-field elements) and *matrices* (`Mat3K`). The Mathlib-PR-grade artifact: a kernel-decidable
  cyclotomic-arithmetic simproc over ℚ is genuinely novel.
- **Route 1′-b — auto-generate the per-type `powerTable` simp set** via a macro from the reduction vector.
  Simpler, but unlocks only *single-level* high-degree fields (`QCyc16`/`QCyc40`); it does **not** solve the
  tower nesting (`QCyc5Ext`).

### Effort: ~200–500 LoC Lean metaprogramming
- simproc skeleton + coeff-projection pattern match: ~80–120
- ℚ convolution + reduction-fold over `Fin`/array: ~80–150
- tower recursion (base-field coeff descent): ~40–100
- per-type glue (`QCyc16`/`QCyc40`, `QCyc5Ext`) + tests: ~50–100

Main risk = simproc **performance**: it must stay under the heartbeat budget at the target degree (Invariant
#10 forbids raising `maxHeartbeats`). It does **not** need to beat `native_decide`'s compiled speed.

### De-risked prototype plan (go/no-go before the full build)
1. Build Route 1′-a for the single-level case; target **`QCyc16` (deg 8)** — the smallest tower the
   hand-template cannot reach.
2. Convert **one** `IsingBraiding` R-matrix entry over Q(ζ₁₆); confirm kernel-pure (`#print axioms` shows no
   `Lean.ofReduceBool`) **and** under the heartbeat budget. ← **decision gate.**
3. If green: add tower recursion → `QCyc5Ext` (unlocks `FibonacciUniversality`/`FibonacciQutrit`); add matrix
   support → `Mat3K`.
4. Sweep `QCyc40` (D6) + the 10 retained heartbeat-bound `FibonacciBraiding` identities (`sigma2_det`, the 4
   `braid_*`, the 2 `s1s2_cu_*`, the R-power inequalities). The direct coeff reduction sidesteps the nesting
   blow-up that timed out the simp-set template, so this would also take **`FibonacciBraiding` to 30/30**.

### Trigger to actually build it
Per Q3, the modules Route-1′ unlocks verify *established literature* (Ising/D6/SU(3) density, FLW 2002) — the
payoff is formalization completeness, not new-claim trust. Build it only if **either** (a) a publication
arises where a fully-kernel-pure Ising/D6/SU(3) result earns its keep, **or** (b) the simproc is pursued as a
standalone Mathlib contribution. Routine trust-surface cleanup does not clear the bar.

### Gate outcome — RAN 2026-05-31: 🔴 RED (naive template port does NOT survive degree 8)

The decision gate (step 2 above) was executed in a throwaway scratch module (`QCyc16Route1Gate.lean`,
deleted). QCyc16 (deg 8, `x⁸ = −1`) was hand-equipped with the QCyc5 `ext`/`powerTable` template
mechanically generalized to degree 8: 8 `mul_cᵢ` rfl-lemmas + **120** `powerTable_m_k` lemmas (rows 0–7 by
`rfl`; rows 8–14 each via `show <k nested shiftByXArr>; simp [shiftByXArr, reduction]`, k up to 7), then the
`IsingBraiding.R_product` theorem (`ζ⁻¹·ζ³ = ζ²`) reproved by `ext <;> (simp only [mul_cᵢ]; rw
[mulReduce_coeffs]; simp [toPoly, Fin.sum_univ_eight]; ring)`.

**Result: FAILED.** `lake env lean` (authoritative per-file check) reported **16 `timeout at isDefEq`
(200000 heartbeats)** plus `maximum recursion depth` errors — all on the **row-8–14 powerTable step-lemmas**,
not on the final `R_product` ring-step — and `#print axioms g_R_product` = `[propext, sorryAx,
Classical.choice, Quot.sound]` (the `sorryAx` confirms the proof did not close). *(A concurrent `lake build`
emitted a spurious "exit 0"; its own log shows `build failed` with the same errors — the per-file run is
authoritative.)*

**Diagnosis — and a correction to the optimistic scoping above.** The earlier note "QCyc16 is easy because
every powerTable entry is a single ±1/0" was half right and misleading: the entry *values* are trivial, but
*proving* each entry forces Lean to unfold `(buildPowerTable reduction)[m]!` by definitional reduction
through `m−7` nested `shiftByXArr` applications over a length-8 array (vs. ≤3 over length-4 for QCyc5), and
that `show`-driven `isDefEq` unfolding is what blows the heartbeat/recursion budget. The bottleneck is the
**table-entry proofs**, not the final ring arithmetic — so the cost is in the *machinery port*, exactly where
Route 1′-b (a macro emitting these same `show`+`simp` lemmas) would land. **Route 1′-b is therefore NOT
validated at degree 8 as a naive port** — contrary to the first-pass hope, the cheap path does not "just
work."

**Revised recommendation.** Route-1′ remains deferred (triggers unchanged), but the gate downgrades the plan:
a degree-8 hardening needs a *better table-entry strategy* before any macro is worth writing — candidates:
(i) prove `powerTable_m_k` by `decide`/`norm_num` on the array lookup instead of deep `show`-defeq; (ii) a
closed-form characterisation lemma for `buildPowerTable` entries that sidesteps iterated `shiftByXArr`
unfolding; or (iii) Route 1′-a's coeff-level simproc, which never materializes the table at all. The gate did
its job: it converted a multi-session metaprogram gamble into a known, bounded sub-problem (kill the
table-entry defeq blowup first), for ~1 session of work — and corrected a wrong assumption before any code
was committed. A re-prototype on the table-entry lemma is the next concrete step if/when a trigger fires.

### Follow-up probe 2026-05-31 — candidate (i) ELIMINATED

A second scratch probe tried the three "cheap" tactics directly on a single deg-8 entry
(`(buildPowerTable QCyc16.reduction)[8]![0]! = -1`): `decide`, `norm_num [buildPowerTable, shiftByXArr,
reduction]`, and `simp [buildPowerTable, shiftByXArr, reduction]`. **All three failed.** `decide` got stuck
on `buildPowerTable`'s `Nat.fold`/`Array.push`/`Array.ofFn` machinery ("did not reduce to isTrue/isFalse" —
the ℚ-wall plus array-bang-index non-reduction); `norm_num` and `simp` both unfold the table but leave an
unsimplified materialized-array goal (`Nat.fold` is opaque to them). So **candidate (i) is dead**: there is
no one-liner for the table entry — the QCyc5 template only worked because its `show <nested shiftByXArr>`
spelled out the fold by hand, which is exactly the deg-8 defeq blowup. The viable paths narrow to **(ii)** a
closed-form `buildPowerTable`-entry characterisation lemma (proved once by induction on the fold — real
lemma-proving, the generalization of ADR-001 Unit 1b) **or (iii)** the Route 1′-a coeff-simproc. Both are
genuine engineering, not a quick experiment — which confirms the deferral rather than reversing it. (Scratch
deleted; no source/build/count changes.)

### Path (ii) bounded crack 2026-05-31 — 🟢 GREEN (recurrence works at degree 8)

Path (ii) was prototyped and **succeeds**. The recon for this had surfaced that ADR-001 Unit 1b already
shipped the *generic* (any-`n`) machinery in `PolyQuotQCharacterisation.lean`:
`buildPowerTable_getElem!_lt` (base rows `m < n` = unit vectors) and **`buildPowerTable_getElem!_step`**
(`[n+j+1]! = shiftByXArr r [n+j]!`, the recurrence) — both kernel-pure, proved by a from-scratch induction
over `Nat.fold` via the local `Nat.fold_push_preserve` invariant. **My RED gate failed for the wrong reason:**
it proved each entry by `show <k-deep nested shiftByXArr>`, forcing the kernel to discharge a depth-7 `isDefEq`
unfold of `Nat.fold`. The shipped recurrence instead rewrites *propositionally* (`rw`) — it never unfolds the
fold — a fundamentally cheaper mechanism I had not tried.

In a throwaway scratch (deleted) I added the one missing companion — the **boundary** row `n` (= first fold
output, covered by neither base nor step), `buildPowerTable_getElem!_boundary : [n]! = shiftByXArr r [n-1]!`,
whose only `show`-defeq is **depth 1** — and reproved the *exact* entry the gate died on:
`(buildPowerTable QCyc16.reduction)[8]![0]! = -1`. Authoritative `lake build` green (8252 jobs);
**`#print axioms` on both the boundary lemma and the entry = `[propext, Classical.choice, Quot.sound]`** — no
`Lean.ofReduceBool`, no `native_decide`, no `maxHeartbeats`, no `sorry`. The chained-recurrence stress test
(`rw`-ing rows 14→8 down to a 7-deep `shiftByXArr` stack) also peeled cleanly with **zero heartbeat timeout**
at every step — exactly where the defeq `show` blew up.

**Conclusion: candidate (ii) is the path, and Route 1′-a (the simproc) is NOT needed for single-level
high-degree fields.** A real degree-n hardening needs only: (1) ship the boundary lemma generically into
`PolyQuotQCharacterisation.lean` (drop the n=8 specialization; it mirrors the existing `_step` proof), (2) a
small `simp`-set / `macro` wrapper that, for a target type, chains `_step` down through `_boundary` to `_lt`
and evaluates the `shiftByXArr` stack — i.e. **Route 1′-b is now de-risked and viable.** The earlier
"candidate (i) eliminated / both paths are real engineering" framing stands, but (ii)'s engineering is now
*scoped and proven feasible*, not speculative. Route-1′ stays **deferred** (the trigger conditions are
unchanged — these modules verify established literature), but if a trigger fires, the build is (ii)/1′-b, and
this prototype is the starting point. Path (iii)/the simproc and its deep-research question are **not needed**.
(Scratch deleted; no source/build/count changes to the committed tree.)
