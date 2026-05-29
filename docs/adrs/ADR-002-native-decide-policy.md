# ADR-002 — `native_decide` policy (compiler-trust axiom in the anyon/TQFT computation layer)

- **Status:** **DRAFT — re-opened for vetting (2026-05-29).** Was "Accepted (2026-05-28)"; the policy
  (document `native_decide`; convert B; harden publication-critical A) still stands, but the *execution
  plan* is being vetted before commitment. Open items being resolved: base-type readiness (only
  `QCyc5`/`QCyc5Ext` equipped — see `docs/native_decide_cleanup_checklist.md` §2b), and the **Route 1
  (per-type powerTable) vs Route 2 (kernel-reducible `PolyQuotQ.mulReduce`)** fork for high-degree types.
  Do not treat as final until re-marked Accepted.
- **Deciders:** John Roehm (project owner); investigation + draft by Claude.
- **Context source:** P4 `axiom_closure_allowlist` gate (`docs/AI-Defect-Defense-Layer.md`, commit `1798633`) +
  triage report (`docs/native_decide_triage.md`, commit `e021fe0`) + this investigation.
- **Related:** [ADR-001](ADR-001-commring-qcyc5ext-roadmap.md) (QCyc5 CommRing / ext roadmap — supplies the
  kernel-pure machinery used below); Pipeline Invariant #15 (no undocumented project axioms).

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

Scouting the execution plan (companion: `docs/native_decide_cleanup_checklist.md`) produced two findings
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

**Decision items still open before re-marking Accepted:** (i) commit to Route 1′ (build the metaprogram)
vs. stay Route-1-manual + accept that high-degree A modules keep `native_decide`; (ii) confirm the
quantified-`decide` wall-clock for the large Category-B `+revert` enumerations.
```
