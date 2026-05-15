# ADR-001: Roadmap to `CommRing QCyc5Ext` (and the wider `QCyc*`/`PolyQuot*` family)

**Status:** Proposed.
**Date:** 2026-05-15.
**Scope:** Upstream Mathlib-shaped typeclass registration for the
computable cyclotomic number fields built on `PolyQuotQ` and
`PolyQuotOver`.
**Owner:** Lean infrastructure (SKEFTHawking namespace).

---

## Context

The downstream consumers of `QCyc5Ext` — most notably
`Mat5K = Fin 5 → Fin 5 → QCyc5Ext` in `FibonacciQuintetUniversality.lean`,
`FibonacciQuintetUniversalityExt.lean`, and
`FibonacciQuintetTrueRep.lean` — currently work around the absence of a
`NonUnitalSemiring QCyc5Ext` (let alone `Ring`/`CommRing`) by:

1. Hand-rolling a matrix multiplication on `Mat5K` (a five-term
   unrolled sum, *not* `Matrix.mul`).
2. Discharging every algebraic identity via `native_decide`.
3. Forgoing `Matrix.mul_assoc` (Mathlib `Data/Matrix/Mul.lean:482`,
   needs `[NonUnitalSemiring α]`) and related abstract lemmas.

Pattern (2) works beautifully for *evaluable* equalities at concrete
inputs and is the project's deliberate design choice (see the
`PolyQuotQ` module docstring), but it cannot express
*quantifier-laden* facts — anything of the form "for all `A B C : Mat5K`,
`(A · B) · C = A · (B · C)`" must be discharged abstractly.

Future Phase 1.D.2c, 1.D.3, and downstream Wave-block work needs
exactly that: it composes braid generators, takes commutators of
commutators, builds Lie-algebra brackets, and wants to apply
`Matrix.mul_assoc` to flatten parenthesization without re-`native_decide`ing.

This ADR documents **why a same-session `CommRing QCyc5Ext` lift is not
feasible**, what the dependency graph looks like, and the multi-PR plan
to discharge it.

---

## What was attempted

Three implementation paths were prototyped in `lean_run_code` / `lean_multi_attempt`:

### Path (A) — Direct via Mathlib `AdjoinRoot`

Define `QCyc5Ext := AdjoinRoot (X^2 - C φ_qcyc5)` and inherit
`[CommRing R] (f : R[X]) → CommRing (AdjoinRoot f)`.

**Blockers:**
1. Requires `CommRing QCyc5` first — itself unregistered (see Path B).
2. Re-engineers `QCyc5Ext` from a `@[ext] structure with re/im fields`
   to an opaque `Quotient`-wrapped polynomial. **Breaks all existing
   `native_decide` proofs** that pattern-match on `⟨_, _⟩` literals
   (~25 theorems across the Fibonacci stack — yang-baxter, F²=I,
   spanning closure, trefoil/Hopf, ...).
3. `AdjoinRoot` carries `Classical.decEq` (Finsupp-based polynomial
   infrastructure), which the project deliberately avoids (`PolyQuotQ`
   exists precisely to bypass this — see the module docstring).

**Verdict:** rejected; incompatible with the project's evaluable-by-`native_decide`
discipline and would require rewriting every existing QCyc5/QCyc5Ext consumer.

### Path (B) — Manual `CommRing QCyc5` via `funext` + `ring`

Use the canonical project pattern (`DrinfeldDoubleRing.DG.instRing`,
`SymTFTAudit.WittClass.*`): every axiom becomes
`ext <;> simp [...]; ring`.

**Blockers (verified empirically):**
- `(· * ·)` on `QCyc5` is `ofPoly (PolyQuotQ.mulReduce 4 reduction (toPoly x) (toPoly y))`.
- `PolyQuotQ.mulReduce` is implemented via `Array.ofFn`, bang-indexing
  (`outArr[k.val]!`), and `Finset.univ.sum` (or `Nat.fold` in the
  `mulReduceFast` variant) over a precomputed `buildPowerTable`.
- **`simp` cannot reduce `(Array.ofFn f)[i]!` for symbolic `i.val`**
  (verified: heartbeat timeout at 200 000 trying `simp +decide` with
  unfolds for `mulReduce, toPoly, reduction, buildPowerTable, shiftByXArr`).
- **`decide` cannot resolve a universally quantified `QCyc5` equality**
  because `Decidable (∀ x y, P x y)` requires the type to be `Fintype`
  (which `QCyc5` is not — ℚ⁴ is infinite).
- Even an *intermediate* lemma like
  `(QCyc5.mk a₀ a₁ a₂ a₃ * QCyc5.mk b₀ b₁ b₂ b₃).c0 = a₀b₀ + … (16 terms)`
  with free ℚ variables `aᵢ, bⱼ` cannot be proved by the standard
  unfold-and-`ring` recipe; the `Array.ofFn` machinery refuses to
  evaluate symbolically.

**Verdict:** rejected at the per-axiom level; the multiplication
*representation* is structurally hostile to symbolic ring-axiom proofs
even though it is fast for `native_decide`. Would require either:
- A refactor of `PolyQuotQ.mulReduce` to a pattern-match form (see Path D), or
- A bridge to a *parallel* representation that *is* symbolic-friendly (Path C).

### Path (C) — Generic `CommRing` on `PolyQuotOver`

Try to register `CommRing (PolyQuotOver K m)` whenever
`CommRing K` is available, then have `QCyc5Ext` inherit via the
`toPoly`/`ofPoly` round trip.

**Blockers:**
1. Inherits Path (B)'s structural obstacle: `mulReduceOver` /
   `mulReduce2` use the same `Array`-based, bang-indexed
   representation, with the same simp-opacity.
2. *And* requires `CommRing K` (i.e., Path B at a higher level of
   generality).

**Verdict:** strictly harder than Path B; rejected.

---

## What is actually feasible in a single session

### Delivered now (this PR)

- **`AddCommGroup QCyc5`** registered (pointwise lift from ℚ⁴).
- **`AddCommGroup QCyc5Ext`** registered (componentwise lift from
  `AddCommGroup QCyc5`).
- 24 `rfl`-tagged `@[simp]` projection lemmas for `+`, `-`, `neg`, `0`,
  `n •` on `QCyc5`; 8 analogous projection lemmas for `QCyc5Ext`.
- Module-summary updates noting "CommRing is intentionally not
  registered — see ADR-001".

**Effect on downstream:** `Mat5K = Fin 5 → Fin 5 → QCyc5Ext` now
inherits `AddCommGroup` *automatically* through Pi types. Likewise
`Fin n → QCyc5` for coefficient-vector reasoning. `Finsupp` and
free-module constructions over `QCyc5` become available. This is
strictly additive; multiplication still goes through the existing
hand-rolled `Mat5K.mul` and `native_decide`.

**Standard kernel only.** Verified: axioms = `{propext, Classical.choice, Quot.sound}`.

### Deferred (multi-PR plan)

The path from `AddCommGroup` to `CommRing QCyc5Ext` decomposes into the
work units below. Each unit is independently shippable; later units
depend on earlier ones.

#### Unit 1: Refactor `PolyQuotQ.mulReduce` to a simp-friendly form

**Goal:** Reformulate the *symbolic* surface of `mulReduce` so that
`(mulReduce n r x y).coeffs k` unfolds to an explicit sum-of-products
expression via `simp` (no `Array.ofFn`, no bang-indexing).

**Approach options:**
- **(1a)** Keep the `Array`-based runtime form (preserves
  `native_decide` performance), but add an `@[simp]` *characterisation*
  lemma:
  `(mulReduce n r x y).coeffs k = ∑ p, ∑ q, x.coeffs p * y.coeffs q * (powerTable r (p+q)).coeffs k`
  proved once (by `Array` reasoning), then used for all subsequent
  symbolic work.
- **(1b)** Define an alternative `mulReduceSym` directly as the double
  `Finset.sum`, prove `mulReduce = mulReduceSym` as a definitional
  lemma, use `mulReduceSym` for all algebra. *Two implementations
  diverging is a maintenance hazard; prefer (1a).*

**Estimated effort:** 1–2 days (one focused PR). The key technical
challenge is the `Array.ofFn[i]!` → `Finset.sum` bridge lemma; the rest
is mechanical `unfold + simp`.

**Risk:** the characterisation lemma may not simp efficiently enough to
make per-axiom proofs tractable. Mitigation: profile against the
QCyc5 mul_comm proof early; fall back to per-degree specialisations.

#### Unit 2: `CommRing QCyc5`

**Depends on:** Unit 1.

**Goal:** Register `CommRing QCyc5` with all axioms proved via
`ext <;> simp [mulReduce_characterisation, ...]; ring`.

**Concretely 11 axioms:** `mul_assoc, one_mul, mul_one, left_distrib,
right_distrib, mul_zero, zero_mul, mul_comm, plus the AddCommGroup ones
already shipped`. Each unfolds to 4 component identities (one per `cᵢ`)
in 16 ℚ-bilinear monomials, closed by `ring`.

**Estimated effort:** 1–2 days (one PR). Once Unit 1's characterisation
fires, every axiom proof is mechanical.

**Risk:** `ring` may time out on the 16-term-per-component goals
post-reduction (the QCyc5 multiplication is dense — 4 `× ζ^k` reduction
terms each contribute). Mitigation: split each axiom into 4 per-component
lemmas; use `ring_nf` + explicit term ordering.

**Side-effect:** `Field QCyc5` is then a small additional PR
(`mul_inv_cancel` requires writing the inverse formula — 8 elements
contribute to each component of `x⁻¹`; doable by Cramer's-rule or by
norm-form `N(x)⁻¹ · x* `).

#### Unit 3: `CommRing PolyQuotOver` (parameterised)

**Depends on:** Unit 1 (generalised to `PolyQuotOver`).

**Goal:** Generic instance
`[CommRing K] [DecidableEq K] (m : ℕ) → CommRing (PolyQuotOver K m)`
provided the reduction-rule monic polynomial is fixed by the call
site.

**Estimated effort:** 2–3 days (one PR). Trickier than Unit 2 because
the dependency on the reduction rule must be threaded through the type
class — likely via a `[Fact (IsMonicReduction r)]` or explicit
`structure` carrying the reduction rule.

**Risk:** `mulReduceOver` (the general-`m` form) has known performance
issues (the docstring flags exponential branching at dense reductions).
Mitigation: register `CommRing` only via the degree-2 form
`mulReduce2` for now; defer general-`m` instance to Unit 5.

#### Unit 4: `CommRing QCyc5Ext` (the headline goal)

**Depends on:** Unit 2 (for the base) + Unit 3 (specialised to
`m = 2, K = QCyc5`).

**Goal:** Register `CommRing QCyc5Ext` by inheritance through the
`toPoly`/`ofPoly` bijection.

**Estimated effort:** 1 day (one PR). Almost mechanical once Units 2
and 3 are in place — register the `RingHom` round-trip, invoke
`RingEquiv.commRing` or write the instance directly using the
component-wise simp lemmas this PR is adding.

**Side-effect:** `Mat5K = Fin 5 → Fin 5 → QCyc5Ext` becomes
definitionally compatible with `Matrix (Fin 5) (Fin 5) QCyc5Ext` — the
`Mat5K.mul` can be replaced by `Matrix.mul` and downstream gains
`Matrix.mul_assoc`, `Matrix.one_mul`, `Matrix.mul_one`,
`Matrix.transpose_mul`, etc.

#### Unit 5 (optional): Higher-degree generalisation

Mirror Units 2–4 for the other `QCyc*` substrates (`QCyc3`, `QCyc15`,
`QCyc16`, `QCyc40`, `QCyc80`, `QCyc40Ext`, `QCyc80Ext`, `QCyc15SqrtPhi`).
Each gets its own `CommRing` instance via the same recipe; the work is
mechanical *if* Unit 3 has produced the generic infrastructure.

**Estimated effort:** 0.5–1 day per substrate (each is one PR), or
batched as one omnibus PR.

---

## Decision

**Accept the multi-PR plan as the canonical path; do not attempt a
same-session `CommRing QCyc5Ext` lift.**

**Now (this PR):** ship `AddCommGroup QCyc5` + `AddCommGroup QCyc5Ext`
+ projection simp lemmas + this ADR. This unblocks Pi-type
`AddCommGroup` derivation for `Mat5K`, `Fin n → QCyc5`, etc. — strictly
additive structure, no regression in any existing `native_decide`
proof. 8605-job build verified clean.

**Next (sequenced PRs):** Units 1 → 2 → 3 → 4 as scheduled above,
~5–9 person-days end-to-end. The work is bottlenecked by Unit 1
(the simp-friendly `mulReduce` characterisation), which is the only
non-mechanical step.

---

## Consequences

### Positive

- Honest about scope: no toy `CommRing` instance that secretly fails
  on `mul_assoc`, no shipped `axiom` to paper over the
  representation/abstract-algebra mismatch.
- The `AddCommGroup` foothold is real and immediately useful: Pi-type
  `AddCommGroup`, `Finsupp`-based reasoning, additive abstract algebra
  all open up.
- The 5-unit plan is concrete enough that any future contributor (or
  Aristotle submission) can pick up Unit 1 and execute.
- Decision is reversible: future Mathlib evolution (better `Array`
  simp tactics, a `Polynomial` reformulation in pure pattern-match
  style) could collapse Units 1–2 into a single trivial PR.

### Negative

- Phase 1.D.2c / 1.D.3 — if they need `Matrix.mul_assoc` *now* —
  remain blocked. Workaround: continue the `Mat5K.mul` + `native_decide`
  pattern, or hand-roll the specific associativity lemma needed
  (`(A * B) * C = A * (B * C)` at fixed `A, B, C`) via `funext + ext +
  native_decide` per use site.
- The `axiom`-budget posture (pipeline invariant #15: no new axioms
  without sign-off) is respected — we ship structure, not assumptions.
- Maintenance: two more layers of `@[simp]` lemmas in
  `QCyc5.lean`/`QCyc5Ext.lean` to keep in sync with future structural
  changes.

### Neutral

- The 24 projection `@[simp]` lemmas on `QCyc5` and 8 on `QCyc5Ext` are
  `rfl`-true and free in terms of build cost; they fire only when
  reasoning about the relevant projections.

---

## References

- `lean/SKEFTHawking/PolyQuotQ.lean` — base-ℚ polynomial-quotient
  infrastructure; module docstring explicitly notes the
  `AdjoinRoot`-bridge as future work.
- `lean/SKEFTHawking/PolyQuotOver.lean` — generic tower extensions; the
  `mulReduce2` docstring notes degree-2 closed form.
- `lean/SKEFTHawking/DrinfeldDoubleRing.lean` — canonical reference for
  the project's `ext <;> exact ...` `Ring`-instance pattern on a
  function-wrapped struct.
- `Mathlib/Data/Matrix/Mul.lean` `Matrix.mul_assoc` (the downstream
  consumer this ADR ultimately unblocks).
- `Mathlib/RingTheory/AdjoinRoot.lean` — the abstract-algebra target;
  `[CommRing R] (f : R[X]) → CommRing (AdjoinRoot f)` is the lemma we
  would *use* once Path A's representation hurdle is overcome (or
  bypassed via Units 1–4).

## Glossary

- **`QCyc5`** — `Q(ζ₅)`, the 5th cyclotomic number field; elements are
  4-tuples `(c₀, c₁, c₂, c₃)` of `ℚ` over `{1, ζ, ζ², ζ³}`.
- **`QCyc5Ext`** — `K = Q(ζ₅, √φ)`, the degree-8 number field for
  Fibonacci universality; elements are pairs `(re, im) ∈ QCyc5²` over
  `{1, w}` with `w² = φ = -ζ²-ζ³`.
- **`PolyQuotQ n`** — generic `ℚ[x]/(p(x))` at degree `n`, the
  computable substrate for all cyclotomic constructions.
- **`PolyQuotOver K m`** — generic `K[w]/(p(w))` tower extension.
- **`Mat5K`** — `Fin 5 → Fin 5 → QCyc5Ext`, the matrix space carrying
  the true 4-strand Fibonacci representation.
- **simp-opaque** — a representation whose surface syntax does not
  unfold under `simp` even with the natural set of `@[simp]` lemmas
  enabled; here, `Array.ofFn (fun k : Fin n => ...)[i.val]!` qualifies.
