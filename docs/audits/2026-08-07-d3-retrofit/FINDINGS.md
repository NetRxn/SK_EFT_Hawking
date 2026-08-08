# D3 apex retrofit — the program's central synthesis claim has no Lean witness

**Date:** 2026-08-07 · Ninth bundle retrofitted under ADR-010 §D5a. The heaviest bundle.

**Read IN FULL before anything was declared,** per ADR-010 C4: `papers/D3/paper_draft.tex`
(2,885 lines, every line, including the commented material after §28), `bundle_metadata.json`,
`append_log.json` (all 33 events), and — for the claims that became findings — the dependency
edges of every declaration in D3's heat-kernel, linearised-EFE and coefficient-match modules.

---

## 1. What was declared

**89 apexes → 332 declarations across 37 modules, depth 3, 5 private truncations.**

D3's draft names 222 `\texttt{}` tokens; 137 resolve to live theorems. The other 85 are module
names, tracked-hypothesis `Prop`s, and abbreviated suffix fragments. The 89 declared are the
result-level subset — one per statement the manuscript presents as something it established,
across all 22 main sections and 5 appendices.

**Every tracked-hypothesis `Prop` was excluded, and each is a `def` or `structure`** — verified,
not assumed: `H_VergelesPositivity`, `H_CriticalLimitCollapse`, `H_DeepGapReducesToAdler`,
`H_HorizonBoundaryCondition`, `H_TopologicalOrderBeyondLG`, `H_TetradQuarkScalesNatural`,
`H_RegimePartition`, `IsADWPenroseApplicable`, and the rest. The check enforces the exclusion
independently (`apexes_are_theorems`).

---

## 2. ⚠️ The finding: "the substrate is one object" is asserted, never formalized

The program's architectural claim — stated in D3 §1, D3 §28.1, and elevated by F to *"the
synthesis claim NEW to this flagship, absent from any individual sibling bundle and load-bearing
for the architectural argument"* — is that **the `N_f` in the Sakharov coefficient
`G_N = 12π/(N_f Λ²)` and the `N_f = 16` that fixes the Standard-Model anomaly classification are
the same `N_f`.**

Three independent measurements, none of which finds a link:

| measurement | result |
|---|---|
| **D3 ∩ D1** (declared closures) | **0** |
| D3's heat-kernel / linearised-EFE / coefficient-match declarations depending on **any** `Z16*`, `Modular*`, `SPT*` or `Chirality*` module | **none** |
| declarations anywhere in the tree whose name bridges an `N_f` to an anomaly/modular/generation count | **none** — the three near-misses are lattice-signature and SymTFT theorems about `16 ∣ σ`, a different statement |

**D3 ∩ F = 126**, concentrated in `BHEntropyMicroscopic` (18), `NonlinearDiffInvariance` (14),
`GaugeErasure` (12), `GravitationalWaves` (10) — F's substrate is largely D3's, as expected.
**D3 ∩ D1 = 0** is the one that matters: the two bundles F says are faces of one object share no
declaration.

### What this does and does not say

**It does not say the claim is false.** Two formalizations of different facets of one physical
object can perfectly well have disjoint proof DAGs; sharing a Lean declaration is a sufficient
witness for identity, not a necessary one.

**It says the claim is unformalized, in a corpus whose selling point is that its claims are
formalized.** A referee reading *"the substrate is one object; its faces are the sibling bundles'
worth of predictive register"* will ask what backs it. The answer today is prose in two drafts.
Everything else in D3 that carries this much weight ships a theorem.

**D3 is the more careful of the two.** §1 attributes the `N_f` identity to *"Bundle L2, lifting
from [Roehm2026Modular]"* — a citation to a companion paper. F §1.4 and §12.1 state it flatly as
an identity and label it F's own novel contribution. Filed as **TODO-D16**.

⚠️ **Not yet measurable:** D2 and L2 are undeclared, so `D3 ∩ D2` cannot be computed. The
dependency check above is independent of declaration and already answers the question at module
granularity — no D3 gravity-side declaration reaches the anomaly-side tree at all — but the
closure-level confirmation waits on D2's retrofit.

---

## 3. Two dangling `\ref`s, both inside the audit-transparency registry

`sec:cfl-z3-matching` and `sec:singularity-thms` are referenced and never defined; both render
as `??` in the compiled PDF. Their locations are the problem:

- `\S\ref{sec:cfl-z3-matching}` is where §28.3 sends a reader to resolve
  `CFLChiralLagrangian.H_TopologicalOrderBeyondLG`.
- `\S\ref{sec:singularity-thms}` is where §28.3 sends a reader to resolve
  `PenroseSingularity.IsADWPenroseApplicable`, and §24.3 uses it again for the Riccati route.

§28.3 is the **tracked-hypothesis registry** — the mechanism D3 offers as its accountability
device, closing with *"A reader with auditing intent can resolve every open obligation in this
list."* Two of its pointers do not resolve. Filed as **TODO-D17**.

---

## 4. Seven more empty `Lift-section` events — TODO-D14 is a corpus pattern

`append_log.json` records **26 `Lift-section` events**; seven produced no manuscript content:

| source | target § |
|---|---|
| `_phase6n_W1a_lean_only` | §6 |
| `_phase6n_W2c_lean_only` | §3 |
| `_phase6o_W1a_lean_only` | §3 |
| `_phase6o_W1b_lean_only` | §6 |
| `_phase6o_W3b_lean_only` | §6 |
| `_phase6o_W1c_writeup` | §10 |
| `_phase6o_W2a_lean_only` | §17 |

With D1's four, that is **eleven empty `Lift-section` events across two bundles**.

**D3 handles them better than D1 did**, and the difference is worth copying: each stub carries an
in-line note — *"D3 Stage-13 fix-pass 2026-05-11: header commented out per BLOCKER 4.1 … Lift
body content remains pending; restore `\section` + `\label` once content lands"* — so a reader of
the source knows the state. D1's stubs say only that a bookkeeping anchor was preserved. The log
is wrong in both. TODO-D14 broadened.

The named content is substantial and unpublished anywhere: a Kerr-Schild double-copy on Petrov-D
acoustic geometry with a three-obstruction BCJ no-go, an APS η-invariant substrate for analog
horizons, an Itô/LDP cross-bridge, and a dissipative-SK-EFT bootstrap-uniqueness no-go.

---

## 5. What D3 gets right — and one place F understates it

**§28.3's tracked-hypothesis registry is the model the other bundles should copy.** Every open
`Prop` is listed by module-qualified identifier with a one-line closure path, including the ones
that are merely *"shipped at the Lean-formalization scope"* and the one that has since been
**discharged** (`H_VerlindeKMLiteralSumDerivation`, Wave 7B). Nothing in the retrofit so far
comes close to this standard of disclosure.

Also honest, and each checked:

- **Decision Gate E.1 is listed as cleared *and* the Vergeles trio as open**, which is consistent
  because §5.2 states the gate's closure *requires* those Props and §5.4 says the one-loop
  calculation is open. ⚠️ **F drops that qualifier**: its §6.3 bullet says the triple *"discharges
  cleanly"* with no caveat, while F's own §10 register carries *"on the substrate's
  tracked-hypothesis Prop record bundle."* The flagship contradicts itself, and the version in
  the *cleared register* is the honest one. Folded into TODO-D15.
- **The horizon-Crooks unification is scoped to Stage 1**, with the witnesses named as
  placeholders and the `Sakharov_iff_horizon_Crooks` bridge explicitly deferred — and indeed that
  declaration does not exist in the tree, exactly as the draft says.
- **The Witt sharpening states its own vacuity**: `horizon_wave8_anomalyMatch_always` holds for
  every `N_f`, *"so on its own it does not constrain the ADW model"* — the draft says this rather
  than banking the weaker condition as evidence.
- **The Penrose first-formalization claim states its scope precisely** — predicate-level
  hypothesis bundle, not a differential-geometric proof of the 1965 theorem.

**And F understates D3's substrate in one place.** F §6.2 and §10 both say the factor-6000
Wen-ADW figure *"is an informal extrapolation … not separately Lean-verified at the
Newton-constant level."* D3 §4.1 ships `EmergentGravityBounds.wen_adw_factor_6000`, which proves
`1/6202 < G_Wen/G_c < 1/6000` for every nonzero cutoff — a theorem, resolved and kernel-pure.
The hedge was true when written and is now stale in the conservative direction. Recorded under
TODO-D15 with the flagship's other staleness.

---

## 6. Ledger

| artifact | change |
|---|---|
| `papers/D3/bundle_metadata.json` | `apex_theorems` added — 89 entries |
| `scripts/validation/checks/bundles_readiness.py` | `UNDECLARED_APEX_CEILING` 13 → 12 |
| `docs/architecture/.working-docs/ARCHITECTURE_TODOs.MD` | TODO-D16 (the unformalized synthesis claim), TODO-D17 (dangling refs); D14 and D15 broadened |
| `docs/architecture/.working-docs/ACCURACY_LEDGER.md` | V25 |

Gate: `validate.py --check bundle_apex_resolves` — PASS, 320 apexes across 9 bundles.
Suite: 5,676 passed / 5 skipped.
