# `native_decide` cleanup — execution checklist (prep)

*Scouting + groundwork produced 2026-05-29. **Execution gated:** do NOT start conversions until the
parallel Phase 6x closeout lands (avoids Lean-file collisions). This document is read-only prep — no
source was modified to produce it.*

**Reads with:** [ADR-002](adrs/ADR-002-native-decide-policy.md) (the policy), [ADR-001](adrs/ADR-001-commring-qcyc5ext-roadmap.md)
(the kernel-pure QCyc machinery that makes Category-A tractable), [`native_decide_triage.md`](native_decide_triage.md)
(the original feasibility split). Backstopped by the P4 gate `validate.py --check axiom_closure_allowlist`.

---

## 0. The method: probe-first, not categorize-first

The honest finding from scouting: **A vs B cannot be reliably read off a module name or even a grep** —
the signal is the *value type of the `native_decide`'d equality*, and several modules are deceptive:

- `SU3k2SMatrix` is quantified over `Fin 6` but its values are **cyclotomic** (`sA * zeta5 = sG`) → **A**, not B.
- `A1Ring`/`A1Ext`/`A1Resolution`/`Mat13K5Ext` are over `Matrix _ _ F2` (a *finite* ring) → may `decide`
  even though the type is "custom" → **probe-needed**.

So the per-module step 0 is a mechanical probe that sorts it definitively:

```bash
# In a throwaway: replace `by native_decide` → `by decide` in the module, then
lake build SKEFTHawking.<Module>     # then `git checkout` to revert
#   build clean  → Category B (drop-in `decide`)
#   "did not reduce to isTrue/isFalse" → Category A (needs the ext/powerTable template)
#   "failed to synthesize Decidable"   → quantified; try `decide +revert` / `intro; decide` first
```

The categorization table in §4 is a best-effort static draft (value-type signal) to *order* the work;
the probe is authoritative. Do not trust a label over a failed build.

---

## 1. Bucket B — convert opportunistically (the immediate, low-risk win)

`Fin`/`Nat`/`Int` (and finite-`Fintype`) goals where kernel `decide` works. **Drop-in**, free
trust-surface reduction, kernel-checked. ADR-002 decision #4.

| Module | sites | sub-type | action |
|---|---:|---|---|
| `SU2kFusion` | 43 | `Fin 2` fusion `N_{ij}^m`; mix concrete + `∀ (i j m : Fin 2)` | concrete → `decide`; quantified → `decide +revert` |
| `KacWaltonFusion` | 58 | `Nat` Dynkin/`hDual` + alcove-membership Bool | mostly `decide`; verify the heavy alcove enumerations don't time out |
| `SU3kFusion` | 12 | finite inductive `SU3k1Obj` (Fintype) + `∀`-quantified | `decide` / `decide +revert` |
| `SU2kMTC` | 10 | `Fin`/`Nat` MTC data | probe → `decide` |
| `SU2kSMatrix` | 2 | **check value type** — if cyclotomic, this is A | probe first |
| `FusionExamples` | 3 | `Fin`/`Nat` worked examples | `decide` |
| `QTheoryNoGoTheorem` | 1 | `Nat` constraint count | `decide` |
| `GenerationConstraint` | 1 | `Nat` (3 ∣ N_f chain) | `decide` (**headline L2/D2 — see §2**) |
| `ModularityTheorem` | 1 | `Nat` | `decide` |
| `GoltermanShamir` | 1 | `Nat` anomaly label | `decide` |

**Probe-then-likely-B (physics-model checks — value type is plausibly `Nat`/`Int`, confirm per module):**
`FermiPointTopology` (16), `ChiralityWall` (14), `ADWMechanism` (13), `FractonGravity` (14),
`FractonNonAbelian` (12), `FractonDarkMatter` (10), `FractonHydro` (8), `FractonFormulas` (5),
`SFDMMergerForecast` (10), `VestigialGravity` (5), `VillainHamiltonian` (8), `LatticeHamiltonian` (7),
`InstantonZeroModes` (7), `SPTClassification` (7), `DarkSectorSynthesis` (4), `ClassificationTableDark` (2),
`SecondOrderSK` (7), `ThirdOrderSK` (4), `KMatrixAnomaly` (4), `E8Lattice` (11), `FKGappedInterface` (8),
`TPFDisentangler` (6), `ETH/Predicates` (1), `ETH/ConcreteWitness` (1),
`FaultTolerance/{SteaneCode,Malignant,ExRec}` (3/1/1), `BHEntropyMicroscopic` (1), `ArrayHelpers` (1),
`SurgeryPresentation` (2), `StringNet` (1).

> ⚠️ Several of these "physics-model" modules will turn out **A** (if a check is over a cyclotomic or
> matrix-over-custom value). Probe each; don't batch-convert sight-unseen.

---

## 2. Bucket A — harden ONLY the publication-critical subset

ADR-002 decision #5: do **not** mass-convert A. Convert to kernel-pure (via the §3 template) **only**
where a "fully kernel-checked, 3-axiom" claim adds publication value — i.e. the "FIRST verified … in any
proof assistant" headlines. Cross-referenced against the Stage-13 bundle anchors
(`docs/agents/claims-reviewer-bundle-prompts.md`). Everything else in A stays **documented `native_decide`**.

### 2a. Publication-critical A — the hardening target (priority order)

**D4 — Topological QC (anyon/MTC/knot first-claims):**
| Module | sites | value type | headline it backs |
|---|---:|---|---|
| `FibonacciBraiding` | 32 | `QCyc5` | Fibonacci universal gates (ADR-002's confirmed template lives here: `F_sq_00`) |
| `FibonacciUniversality` | 8 | `QCyc5Ext` | `fibonacci_universality` (D4 headline) |
| `FibonacciMTC` | 12 | `QCyc5Ext` | Fibonacci MTC |
| `FibonacciQutrit` / `FibonacciQutritUniversality` | 7 / 9 | `QCyc5` | qutrit universality |
| `FibonacciQuintetTrueRep` / `…Universality` / `…UniversalityExt` | 30 / 16 / 9 | `QCyc5Ext` matrices | true 4-strand rep |
| `FibonacciSextetTrueRep` | 47 | `Mat13K_5Ext` (13×13 over `QCyc5Ext`) | largest single A module |
| `IsingBraiding` / `IsingGates` | 25 / 20 | `QCyc16`/`QCyc8` | Ising MTC, trefoil = −1 |
| `WRTComputation` | 22 | `QCyc5`/`QCyc16` | WRT 3-manifold invariants |
| `FigureEightKnot` | 7 | `Mat2` over cyclotomic | figure-eight knot invariant |
| `FPDimension` | 23 | `QSqrt2`/`QSqrt5` | FP-dimensions (Etingof–Nikshych–Ostrik) |
| `SU3k2SMatrix` / `SU3k2FSymbols` | 15 / 9 | cyclotomic (`zeta5`) | first SU(3)₂ fusion category |
| `SU3kFusion`*, `SU2kSMatrix`*, `MugerCenter` (12), `RepUqFusion` (6), `TQFTPartition` (14), `StringNet`* | — | mixed | verify value type per probe |

**D2 / L2 — anomaly + three generations (Ext over Steenrod A(1) first-claim):**
| Module | sites | value type | headline |
|---|---:|---|---|
| `A1Ring` | 13 | `Matrix _ _ F2` | **probe** — finite, may `decide` (then it's a free B win) |
| `A1Ext` | 11 | `Matrix`/`F2` | Ext over A(1) |
| `A1Resolution` | 17 | `Matrix _ _ F2` | minimal resolution `d∘d = 0` |
| `SteenrodA1` | 4 | `F2[x]/(x²)` | Steenrod module |
| `Mat13K5Ext` | 11 | `Mat13K_5Ext` | matrix substrate |
| `GenerationConstraint` | 1 | `Nat` (already in B) | `generation_constraint_iff` (the L2 headline) |

**D6 — fault-tolerant / T-gate compiler:**
| Module | sites | value type | headline |
|---|---:|---|---|
| `TgateFibBraid` | 12 | `QCyc40` | T-gate over cyclotomic |
| `GateCompilation` | 14 | `QCyc40` + `Nat` (MIXED) | Clifford gate compilation |
| `CNOTBraidTQSim` | 4 | cyclotomic | CNOT braiding |
| `RouabahExplicit` / `FKLW/RouabahSplitBraid` | 21 / 10 | `QCyc40` | R-matrix elements |

*\* probe to confirm value type before committing to A vs B.*

### 2b. Base number-field types (foundational — convert if their consumers above need kernel-pure base lemmas)

`QCyc5` (22), `QCyc5Ext` (21), `QCyc40` (21), `QCyc40Ext` (12), `QCyc16` (6), `QCyc3` (9), `QCyc15` (8),
`QCyc15SqrtPhi` (4), `QCyc80` (10), `QCyc80Ext` (2), `QSqrt2` (5), `QSqrt3` (7), `QSqrt5` (8), `QLevel3` (19),
`PolyQuotQ` (9), `PolyQuotOver` (5), `PolyQuotQCharacterisation` (3),
`FKLW/RossSelinger/{ZOmega,ZOmegaSqrt2,KMM,GdeSqrt2,CliffordTGate}`.

**Base-type readiness matrix (scouted 2026-05-29 — DECISIVE):** only `QCyc5`/`QCyc5Ext` are equipped.
**Every other base type delegates `*` to `PolyQuotQ.mulReduce` (the `Array.ofFn`/bang-indexed
representation ADR-001 Path B proved is simp-opaque/kernel-hostile) and has NO `CommRing` instance, NO
`mul_cᵢ`, NO `powerTable_m_k`.** The §3-A template cannot be retargeted by swapping lemma names — the
machinery must be *built* per type first (ADR-001 Unit-5 generation = a real prerequisite, not a swap).

| Type | degree | `CommRing` | `mul_cᵢ` | `powerTable_*` | est. powerTable lemmas (~`(2·deg−1)·deg`) | verdict |
|---|---:|:--:|:--:|:--:|---:|---|
| `QCyc5` | 4 | ✓ | ✓ (4) | ✓ (35) | — shipped | **equipped** (ADR-001) |
| `QCyc5Ext` | 2/QCyc5 | ✓ | — | — (uses `mulReduce2` closed form over QCyc5) | — shipped | **equipped** (ADR-001) |
| `QSqrt2` `QSqrt3` `QSqrt5` | 2 | ✗ | ✗ | ✗ | ~6 | **cheap** — degree-2 closed form like QCyc5Ext |
| `QCyc3` | 2 | ✗ | ✗ | ✗ | ~6 | **cheap** |
| `QLevel3` | 4 | ✗ | ✗ | ✗ | ~28 | moderate (QCyc5-scale) |
| `QCyc16` | 8 | ✗ | ✗ | ✗ | ~120 | notable (backs Ising `IsingGates`/`IsingBraiding`/`WRTComputation`) |
| `QCyc15` | 8 | ✗ | ✗ | ✗ | ~120 | notable |
| `QCyc40` `QCyc40Ext` | 16 (+2) | ✗ | ✗ | ✗ | ~480 | **expensive** (backs D6 `TgateFibBraid`/`RouabahExplicit`/`GateCompilation`) |
| `QCyc80` `QCyc80Ext` | 32 (+2) | ✗ | ✗ | ✗ | ~2000 | **brute powerTable impractical** (already uses precomputed `powerTable80` for runtime) |
| `QCyc15SqrtPhi` | ext | ✗ | ✗ | ✗ | — | depends on QCyc15 first |
| `PolyQuotQ` `PolyQuotOver` | generic | ✗ | n/a | n/a | — | generic substrate; `mulReduce_coeffs` bridge exists (`PolyQuotQCharacterisation`, Unit 1c) |

**Why `decide` can't be made to work here — the ℚ wall (empirically confirmed 2026-05-29 via
`lean_run_code`):** kernel `decide` fails on `ℚ` arithmetic *itself*, independent of `PolyQuotQ`.
`example : (3 : ℚ) * 2 = 6 := by decide` and `(1/2 : ℚ) + 1/2 = 1 := by decide` both fail — reduction
gets **stuck at `(Rat.mul 3 2).num`** because `Rat.mul`/`Rat.add` are irreducible-by-design (they protect
the `num/den` coprimality invariant; their `Rat.normalize`/`Nat.gcd` core does not whnf-reduce). `decide`
succeeds on `Nat`/`Fin`/`Nat.gcd` (Category B) but **cannot** on any `ℚ`-valued equality. So:

- **No Array→List or Finset→`Nat.fold` refactor of `mulReduce` makes it `decide`-able** — the final
  coefficient comparison is a `ℚ` equality, which is the actual wall. (`Finset.sum` is a *secondary* wall,
  already sidestepped by `mulReduceFast`/`mulReduceWithTable` using `Nat.fold`.)
- **This is why ADR-001 used `ext` + `simp[powerTable]` + `ring`/`norm_num`, NOT `decide`:** the symbolic
  tactics discharge `ℚ` arithmetic *without* kernel reduction. The powerTable route is the kernel-pure path
  precisely *because* it avoids `decide`.

**Corrected fork (the earlier "Route 2 = make decide work" is largely infeasible):**
- **Route 1 — powerTable + `ext`/`simp`/`ring`, per type (ADR-001 method).** The ONLY proven kernel-pure
  path. Works at any degree. Cost is `O(deg²)` rfl-lemmas per type: fine for `QSqrt*`/`QCyc3` (~6) and
  `QLevel3` (~28); tedious for `QCyc16` (~120); painful-by-hand for `QCyc40` (~480) / `QCyc80` (~2000).
- **Route 1′ — Route 1 made degree-scalable with a metaprogram.** Write a `simproc` / `elab` (or `norm_num`
  extension) that recognizes `(mulReduce n r x y).coeffs k`, expands it to the explicit `ℚ`-sum, and lets
  `norm_num`/`ring` finish — OR that auto-generates the per-type `powerTable_m_k` simp set. **One focused
  module (~200–500 LoC), then any QCyc* type hardens at ~O(1) marginal cost.** This is the high-leverage
  investment and the realistic enabler for the D6 (`QCyc40`) / Ising (`QCyc16`) targets.
- **Route 2 — change the coefficient representation away from `ℚ`** (e.g. `Fin n → ℤ` + shared denominator,
  or a custom unnormalized-rational with cross-multiplying `DecidableEq` that dodges `Rat.normalize`) so the
  whole thing becomes `decide`-able. This is the only way to get genuine `decide`, but it is a cross-cutting
  substrate rewrite (every QCyc* literal + every consumer reproven), `ℚ` is genuinely needed for cyclotomic
  F-symbol denominators, and the payoff over Route 1′ is marginal. **Not recommended.**

So: `QCyc5`-based hardening (Fibonacci stack) is unblocked **now** (machinery shipped); `QSqrt*`
(`FPDimension`, D4) is a **cheap** Route-1 prereq; the **D6 (`QCyc40`) / Ising (`QCyc16`) targets are gated
on the Route-1′ metaprogram**, which is the substrate worth building. `decide`-reducibility (old "Route 2")
is a dead end over `ℚ`.

### 2c. Non-publication-critical A — LEAVE as documented `native_decide`

Any A module not in §2a (e.g. physics-model checks over custom types that have no "first kernel-verified"
headline). Per ADR-002 these keep `native_decide` + the precise wording. Don't spend the verbosity budget.

---

## 3. Conversion templates (both confirmed)

**Bucket B (drop-in):**
```lean
theorem foo : <Fin/Nat goal> := by decide            -- concrete
theorem bar (i j : Fin n) : <goal> := by decide +revert   -- quantified (or `intro i j; decide`)
```

**Bucket A (kernel-pure, confirmed `FibonacciBraiding.F_sq_00`, machinery from ADR-001):**
```lean
theorem F_sq_00 : F00 * F00 + F01 * F10 = 1 := by
  ext <;>
    simp [F00, F01, F10, phi_inv,
      QCyc5.mul_c0, QCyc5.mul_c1, QCyc5.mul_c2, QCyc5.mul_c3,
      PolyQuotQ.mulReduce_coeffs, QCyc5.toPoly, Fin.sum_univ_four,
      QCyc5.powerTable_0_0, …, QCyc5.powerTable_6_3]   -- all 28 powerTable_m_k rfl-lemmas
```
**Gotcha (load-bearing):** never put `QCyc5.reduction` in the simp set — it unfolds to `![-1,-1,-1,-1]`
and the `powerTable_m_k` lemmas (stated over `QCyc5.reduction`) stop matching, so the power-table lookups
never resolve. Keep `reduction` symbolic. (For `QCyc40`/etc. swap in that type's `mul_cᵢ`/`powerTable`
lemma names — confirm they exist first, §2b.)

---

## 4. Footprint (ground truth, 2026-05-29)

**100 files · 996 `native_decide` call sites.** (Was 98/1005 at 2026-05-28 triage; Phase 6z added modules.)
Per-module counts: see `grep -rc native_decide lean/SKEFTHawking/ | grep -v ':0$' | sort -t: -k2 -rn`.
Per-decl transitive closure (811→ now re-run): `cd lean && lake env lean --run SKEFTHawking/AxiomAudit.lean`.

Rough bucket split (static draft — **probe is authoritative**):
- **B (drop-in `decide`)**: ~10 confirmed + ~30 "probe-then-likely-B" physics modules.
- **A publication-critical** (§2a): ~25 modules, the bulk of the call sites, concentrated in the
  Fibonacci/Ising/WRT/SU(3) anyon stack + A(1)-Ext stack.
- **A base types** (§2b): ~20 modules, mostly already kernel-equipped by ADR-001.
- **A non-critical** (§2c): the remainder — leave documented.

---

## 5. Suggested execution order (once 6x closeout lands)

1. **Re-baseline (INCREMENTAL — do NOT nuke `.lake/build`):** `cd lean && lake build SKEFTHawking` (confirms
   6x's state compiles green; warm cache) → `lake build SKEFTHawking.ExtractDeps` (ensures the audit/graph
   olean) → `validate.py --check axiom_closure_allowlist` (memoized AxiomAudit; re-walks once because 6x
   changed sources — that re-walk *is* the measurement, no clean build needed since the closure is a property
   of the compiled oleans) + `grep -rc native_decide lean/SKEFTHawking/`. Capture both as the starting
   numbers. **Reserve `rm -rf lean/.lake/build` ONLY for** (a) 6x touched `lean-toolchain`/`lakefile.toml`/
   Mathlib pin, or (b) the *final* trusted-clean baseline before declaring the cleanup done — not to start.
2. **Bucket B sweep** (§1): probe → `decide` per module, one module per commit, rebuild that module +
   `lean_verify` a sample theorem to confirm the native axiom dropped. Cheapest, safest, biggest count win.
3. **A1* probe** (§2a D2/L2): these `Matrix _ _ F2` modules might fall to plain `decide` — if so they're
   a free B-style win on a *publication-critical* module. Probe before assuming the verbose template.
4. **Publication-critical A hardening** (§2a), gated by base-type readiness (§2b): start with the
   `QCyc5`-based Fibonacci stack (machinery confirmed present), then Ising/WRT, then SU(3)/D6 only after
   confirming `QCyc40`/`QCyc16` have the `powerTable` lemma set (generate via ADR-001 Unit-5 recipe if not).
5. **Re-word claims** (ADR-002 #2) in any paper/bundle whose anchor theorems were *not* hardened:
   "kernel-checked modulo `native_decide` for finite combinatorial facts."
6. **Optionally flip P4 to `--strict`** on an explicit allow-list once the publication subset is pure.

**Per-conversion verification gate:** module rebuilds clean + `lean_verify <Module>.<thm>` shows axioms
`{propext, Classical.choice, Quot.sound}` (no `*._native.native_decide.ax_*`). Don't mark an item done on
"build passed" alone — confirm the native axiom is actually gone from the closure.

---

## 6. Open scoping questions to resolve at execution start

- ~~**Base-type readiness for D6/SU(3):**~~ **RESOLVED 2026-05-29 (§2b):** only `QCyc5`/`QCyc5Ext` equipped.
  `decide`-reducibility ("Route 2") is a **dead end over `ℚ`** (`Rat.mul`/`add` irreducible — confirmed).
  The path is **Route 1** (powerTable+`ext`/`ring`), and for the high-degree D6/Ising targets the enabler is
  **Route 1′** — a `simproc`/`norm_num`-extension metaprogram (~200–500 LoC) that makes the symbolic
  reduction degree-scalable. **Decide whether to build Route 1′ before scoping D6/Ising hardening.**
  `QCyc5` unblocked now; `QSqrt*` cheap.
- **Route 1′ design open question:** `simproc` that expands `(mulReduce …).coeffs k` → explicit `ℚ`-sum for
  `norm_num`/`ring`, vs. an `elab` that emits the per-type `powerTable_m_k` simp set. Former is degree-blind
  and reusable; latter mirrors the shipped QCyc5 artifact. Prototype both on `QCyc16` (deg 8) before committing.
- **Quantified-`decide` cost:** do the large `+revert` enumerations (`SU2kFusion` assoc over all `Fin 2`,
  `KacWaltonFusion` alcove) `decide` in reasonable wall-clock, or do they need to stay `native_decide`?
  (Triage left this untested.)
- **MIXED modules** (`GateCompilation`, `QuantumGroup*`): split per-goal; the `Nat` half → `decide`,
  the cyclotomic half → template or leave.
