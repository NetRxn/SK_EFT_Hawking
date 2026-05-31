# `native_decide` triage report

*Produced 2026-05-28 by the P4 `axiom_closure_allowlist` follow-up. Decision input — no conversions
performed yet. Re-run the audit with `uv run python scripts/validate.py --check axiom_closure_allowlist`.*

## TL;DR

The project has **0 declared `axiom`s** (`counts.json` `Axioms: 0`, Pipeline Invariant #15 genuinely
clean) and **0 genuinely-unexpected axioms**, but **1005 `native_decide` call sites across 98 files**
pull the compiler-trust axiom (`Lean.ofReduceBool`, surfaced as per-decl `*._native.native_decide.ax_*`)
into the closures of **811 declarations**. `native_decide` trusts the *compiled* evaluator — a strictly
larger trust base than the three kernel axioms `{propext, Classical.choice, Quot.sound}`.

**The feasibility spot-check shows `native_decide` splits into two sharply different categories:**

| Category | Example modules | `decide` (kernel) result | Convertible? |
|---|---|---|---|
| **A. Custom-type arithmetic** (cyclotomic `QCyc*`, ring elements) | `FibonacciBraiding`, `QCyc5`, `QCyc40`, `A1Ring`, `RouabahExplicit` | **FAILS** — `Tactic 'decide' failed … did not reduce to 'isTrue' or 'isFalse'` | ✗ not without a type refactor or manual proofs |
| **B. `Fin`/`Nat`-indexed tables** (fusion rules, integer dims) | `SU2kFusion`, `SU3kFusion`, `KacWaltonFusion`(partly) | **WORKS** — module rebuilds clean with `decide` for the concrete (non-`+revert`) facts | ✓ drop-in for concrete facts |

So "eliminate all `native_decide`" is **not** realistic (Category A genuinely needs it as-is), but a
meaningful fraction (Category B concrete facts) is a near-drop-in conversion.

## 1. Footprint

- **1005** `native_decide` occurrences across **98** `.lean` files (`grep -rc native_decide`).
- **811** declarations carry a `native_decide` axiom in their *transitive* closure (per `AxiomAudit`);
  1094 distinct per-decl native axioms.
- Heaviest modules (call sites): `KacWaltonFusion` 58, `FibonacciSextetTrueRep` 47, `SU2kFusion` 43,
  `FibonacciBraiding` 32, `FibonacciQuintetTrueRep` 30, `IsingBraiding` 25, `FPDimension` 23,
  `WRTComputation` 22, `QCyc5` 22, `RouabahExplicit` 21, `QCyc40` 21, `IsingGates` 20, … (long tail).
- Domains: anyon fusion/braiding (Fibonacci, Ising, SU(2)_k, SU(3)_k), modular/TQFT data (S-matrices,
  WRT invariants, FP-dimensions), quantum-group instantiations, cyclotomic-integer arithmetic
  (`QCyc*`), and a scattering of physics-model checks (fractons, ADW, E8 lattice).

## 2. Feasibility spot-check (the key data — measured, not assumed)

**Category A — `FibonacciBraiding` (Q(ζ₅) cyclotomic arithmetic).** Replaced all `by native_decide`
with `by decide` and rebuilt: **fails** on every cyclotomic fact, e.g.

```
SKEFTHawking/FibonacciBraiding.lean:56:50: Tactic `decide` failed for proposition
did not reduce to `isTrue` or `isFalse`.
```

The `QCyc5` `Decidable`/arithmetic instances do not reduce under kernel whnf (the underlying `Int`
representation + structure equality block kernel evaluation). `native_decide` was chosen here for a real
reason, not laziness.

**Category B — `SU2kFusion` (`Fin (k+1)` fusion table `N_{ij}^m`).** Replaced the concrete
`by native_decide` facts with `by decide` and rebuilt: **`Build completed successfully`**. The `Nat`/`Fin`
arithmetic (`%`, `min`, `≥`, small `Int.natAbs`) kernel-reduces. (The quantified `native_decide +revert`
facts — fusion commutativity/associativity over all `Fin` — were left untouched in this probe; whether
`decide +revert` or `intro; decide` covers them is a small follow-up.)

## 3. Publication exposure (qualitative; precise cross-ref recommended if we go deeper)

The `native_decide` modules are the **anyon/TQFT computational backbone**, and some are *directly*
publication-load-bearing — e.g. `FibonacciBraiding` ("FIRST verified universal quantum gates in any
proof assistant"; Fibonacci-anyon universality) and the Ising/SU(2)_k fusion-category results are
headline claims for the topological-order / anyon / FTQC bundles. **Note the tension:** the
publication-critical facts are concentrated in **Category A** (cyclotomic braiding/universality) —
precisely the category `decide` cannot easily replace. A precise per-bundle cross-reference (which
paper-anchor theorems in `docs/agents/claims-reviewer-bundle-prompts.md` transitively hit
`native_decide`) is the recommended next drill-down if we decide to harden the published subset.

## 4. Recommendation (per-category policy)

1. **Make `native_decide` an explicit, documented policy** (do regardless of conversion choices). It is
   a standard, widely-accepted Lean mechanism for large finite computations; the honest move is to (a)
   keep the P4 gate surfacing it (already shipped — it recognizes the pattern as a distinct category),
   and (b) word the project's "kernel-verified" claims precisely: *"kernel-checked modulo `native_decide`
   for finite combinatorial facts (anyon fusion/braiding, modular data)."* This removes the only real
   inaccuracy — that `Axioms: 0` reads as "pure 3-axiom" when 811 decls trust the compiler.

2. **Convert Category B opportunistically** (`Fin`/`Nat` tables → `decide`). Near-drop-in, removes a
   chunk of the trust surface for free, and `decide` is kernel-checked. Bound to modules where it
   compiles in reasonable time (verify per module — large `+revert` enumerations may be slow).

3. **For Category A, do NOT mass-convert.** Two honest options, decided per *publication need*:
   - *Keep `native_decide` + document* (default) — these are finite cyclotomic identities; the
     compiler-trust risk is low and standard.
   - *Harden the published subset only* — for the specific paper-anchor theorems that rest on Category A,
     either (i) refactor the `QCyc*` types to a kernel-reducible representation (make `DecidableEq` +
     arithmetic reduce under whnf — a per-type effort, reusable, and arguably a Mathlib-PR-quality
     `Cyclotomic`/`decide`-friendliness contribution), or (ii) replace with `norm_num`/manual proofs.

4. **Do not gate CI on it yet.** The P4 check is WARN-first by design; keep it advisory until the policy
   above is chosen, then (optionally) flip Category-A modules to an explicit allow-list and
   `--strict`-fail on anything *new* outside it.

**Suggested immediate step:** (1) + (2) — adopt the documented policy and convert Category B — which is
low-risk and high-clarity, then revisit Category A hardening only for genuinely publication-critical
theorems via the per-bundle cross-reference.

## Appendix — reproduce

```bash
# footprint
grep -rc native_decide lean/SKEFTHawking/ | grep -v ':0' | sort -t: -k2 -rn
# per-decl closures (811 decls / 1094 native axioms; {} would mean clean)
cd lean && lake env lean --run SKEFTHawking/AxiomAudit.lean
# gate (WARN-first; --strict hard-fails on non-allow-listed, non-native_decide axioms)
uv run python scripts/validate.py --check axiom_closure_allowlist
# feasibility: edit a module's `by native_decide` → `by decide`, `lake build <Module>`, then `git checkout`
```
