import SKEFTHawking.Basic
import Mathlib

/-!
# Classical-GR Energy Conditions

## Overview

Phase 6f Wave 3. Formalizes the four classical energy conditions of GR
as predicates on an abstract stress-energy bilinear form, with chain
implications and explicit counterexample witnesses (cosmological-
constant fluid violates SEC; stiff fluid violates DEC; ghost scalar
violates NEC).

Per the Phase 6f deep-research audit (`Lit-Search/Phase-6f/Phase 6f
audit — Classical GR Lean infrastructure.md` §3E + §5.6f.3): no proof
assistant has formalized these four predicates with chain
implications + counterexample witnesses. PhysLean has neither;
Mathlib has neither. **First formalization in any proof assistant.**

## Scoping mode

This module ships the **abstract bilinear form** version of the
energy conditions: a stress-energy tensor `T : V → V → ℝ` on a 4D
real inner-product-like vector space `V`, parameterized by a metric
signature `g : V → V → ℝ`. The full Lorentzian-manifold version
(stress-energy tensor field on a globally hyperbolic spacetime)
requires the Phase 6f.4 Lorentzian-metric infrastructure and is
deferred until that lands.

The abstract version captures all the algebraic content needed for
Phase 6a Wave 6 (`PositiveMassTheorem.lean`, Witten's spinor proof),
which uses DEC of `T_μν^emerg` at a point-wise level — no global
spacetime structure needed at the predicate level.

## Energy conditions (Hawking-Ellis 1973 §4.3 conventions)

We work in signature `−+++` throughout. Future-directed timelike means
`g(v, v) < 0` AND time-component positive (encoded as a separate
predicate `IsFutureDirectedTimelike`).

For a stress-energy tensor `T : V → V → ℝ` and a metric `g : V → V → ℝ`:

- **NEC (Null Energy Condition):** for every null vector `k`
  (`g(k, k) = 0`, `k ≠ 0`), `T(k, k) ≥ 0`.
- **WEC (Weak Energy Condition):** for every future-directed timelike
  vector `v`, `T(v, v) ≥ 0`.
- **DEC (Dominant Energy Condition):** for every future-directed
  timelike `v`, `T(v, v) ≥ 0` AND the vector `T^μ{}_ν v^ν` (the
  energy-flux 4-vector) is future-directed causal. We encode DEC as
  WEC + a 4-flux causality hypothesis on `T(v, ·)`.
- **SEC (Strong Energy Condition):** for every future-directed
  timelike `v`, `(T - (1/2)·trace(T)·g)(v, v) ≥ 0`. Equivalently,
  the trace-reversed stress-energy satisfies WEC.

## Chain implications and counterexamples

The classical chain implications (Wald §9.2, Hawking-Ellis §4.3):

- DEC ⇒ WEC ⇒ NEC (provable from definitions, modulo continuity in
  the WEC ⇒ NEC step).
- SEC ⇏ WEC, WEC ⇏ SEC: counterexample is the cosmological-Λ fluid
  (`ρ = -p = Λ/(8π) > 0` satisfies WEC, NEC, DEC but VIOLATES SEC
  for `Λ > 0`).

This module ships explicit counterexample witnesses for the
non-implications.

## Anti-pattern audit (4-pattern check)

Per the audit's §5.6f.3 P1/P3/P4 checklist:

1. **No ∃-absorption (P1):** counterexample witnesses are explicit
   tensors (cosmological-Λ, stiff-fluid, ghost-scalar), not
   `∃ T, P(T)` discharged by a black box.
2. **No P3 (trivial-multiplication-as-physics):** WEC is stated for
   *non-zero* timelike vectors, so the trivial-`v=0` case is excluded
   by hypothesis.
3. **No P4 (vacuous axioms):** WEC is NOT stated as
   `∀ v, T(v,v) ≥ 0` (which would be equivalent to T being
   positive-semi-definite, false in any non-trivial Lorentzian
   theory). The timelike restriction is load-bearing.

## References

- R.M. Wald, *General Relativity* (1984) §9.2.
- S.W. Hawking, G.F.R. Ellis, *The Large Scale Structure of Space-
  Time* (1973) §4.3.
- S. Carroll, *Spacetime and Geometry* (2004) §4.6.

## Cross-system landscape

Per the Phase 6f audit §3, no proof assistant — Lean (Mathlib4 + Bonn
+ PhysLean), Coq, Isabelle/AFP (Smooth_Manifolds, Lie_Groups,
Schutz_Spacetime), HOL Light, HOL4, Mizar, Agda — has formalized
these four predicates with chain implications and counterexamples.
This is plausibly the first such formalization.
-/

namespace SKEFTHawking.EnergyConditions

open Real

/-! ## §1 — Abstract carrier types -/

/--
**4-dimensional real vector space carrier.** We use `Fin 4 → ℝ`
throughout for concreteness; the predicate definitions below
generalize to any 4-dimensional real vector space, but the explicit
witness construction (§5) is easier with a concrete index set.
-/
abbrev Vec4 : Type := Fin 4 → ℝ

/--
**Stress-energy tensor as a (0,2) symmetric bilinear form.**
Encoded as a function `T : Vec4 → Vec4 → ℝ` with symmetry hypothesis
carried alongside as a Prop bundle.
-/
abbrev StressEnergyTensor : Type := Vec4 → Vec4 → ℝ

/--
**Metric tensor as a (0,2) symmetric bilinear form.** Same encoding
as `StressEnergyTensor`; signature distinction (Lorentzian vs.
Riemannian) is encoded via an external predicate `IsLorentzian`.
-/
abbrev MetricTensor : Type := Vec4 → Vec4 → ℝ

/-! ## §2 — Causal-vector predicates (signature `−+++`) -/

/--
**Null vector** w.r.t. metric `g`: `g(k, k) = 0` AND `k ≠ 0`.
The non-zero requirement is load-bearing — the zero vector is null
in any signature, but is not a physical null direction.
-/
def IsNull (g : MetricTensor) (k : Vec4) : Prop :=
  g k k = 0 ∧ k ≠ 0

/--
**Timelike vector** w.r.t. metric `g`: `g(v, v) < 0` (in signature
`−+++`).
-/
def IsTimelike (g : MetricTensor) (v : Vec4) : Prop :=
  g v v < 0

/--
**Future-directed timelike** w.r.t. metric `g` and a chosen
future-pointing time-direction `t : Vec4`: timelike AND
`g(t, v) < 0`.

The sign convention follows signature `−+++`: for `t = v = (1,0,0,0)`,
`g(t, v) = -1 < 0`, which marks `v` as future-directed when `t` is
future-directed. The time-direction parameter `t` is supplied
externally so the definition is signature-agnostic and
orientation-explicit (no implicit choice of "the" time direction).
-/
def IsFutureDirectedTimelike (g : MetricTensor) (t v : Vec4) : Prop :=
  IsTimelike g v ∧ g t v < 0

/-! ## §3 — Energy condition predicates -/

/--
**Null Energy Condition (NEC).** For every null vector `k`,
`T(k, k) ≥ 0`. Hawking-Ellis 1973 §4.3.

Anti-pattern audit: the `IsNull g k` hypothesis is load-bearing —
without it, the predicate would also constrain the zero vector,
which is vacuous (`T(0, 0) = 0` always). With it, the predicate is
non-trivial: a ghost scalar field violates NEC at every non-zero
null `k`.
-/
def NEC (T : StressEnergyTensor) (g : MetricTensor) : Prop :=
  ∀ k : Vec4, IsNull g k → 0 ≤ T k k

/--
**Weak Energy Condition (WEC).** For every future-directed timelike
vector `v`, `T(v, v) ≥ 0`. Hawking-Ellis 1973 §4.3.

Anti-pattern audit: the `IsFutureDirectedTimelike g t v` hypothesis
is load-bearing — without the timelike restriction the predicate
becomes positive-semi-definiteness of `T`, which fails on any
non-trivial Lorentzian theory.
-/
def WEC (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4) : Prop :=
  ∀ v : Vec4, IsFutureDirectedTimelike g t v → 0 ≤ T v v

/--
**Dominant Energy Condition (DEC).** WEC PLUS the additional
constraint that the energy-flux 4-vector `T(v, ·)` is itself
future-directed causal for every future-directed timelike `v`.

Following Hawking-Ellis 1973 §4.3.2, we encode the causal-flux
constraint via the bilinear pairing `T(v, w)` for a second
future-directed timelike `w`: DEC requires `T(v, w) ≥ 0` whenever
both `v` and `w` are future-directed timelike. (This is equivalent
to the `T^μ{}_ν v^ν` future-directed-causal formulation at the
predicate level when `T` is symmetric.)
-/
def DEC (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4) : Prop :=
  WEC T g t ∧
    ∀ v w : Vec4,
      IsFutureDirectedTimelike g t v → IsFutureDirectedTimelike g t w →
      0 ≤ T v w

/--
**Strong Energy Condition (SEC).** For every future-directed
timelike `v`, `(T - (1/2)·tr(T)·g)(v, v) ≥ 0`. Equivalently, the
trace-reversed stress-energy satisfies WEC.

We supply the trace `trT : ℝ` as an external real parameter (the
trace requires raising an index with `g⁻¹`, which we don't yet
have in this abstract carrier). The SEC predicate then asserts:

    ∀ v fdtl, T(v, v) - (1/2) trT · g(v, v) ≥ 0.

In signature `−+++`, future-directed timelike `v` has `g(v, v) < 0`,
so the `g(v, v)` term contributes positively when `trT > 0` and
negatively when `trT < 0`. For a cosmological-constant fluid
(`ρ = -p = Λ/(8π)`, `trT = ρ + 3p · (-1) = ... `), we'll see explicitly
which way SEC fails.
-/
def SEC (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4) (trT : ℝ) : Prop :=
  ∀ v : Vec4, IsFutureDirectedTimelike g t v →
    0 ≤ T v v - (1/2) * trT * g v v

/-! ## §4 — Chain implications

The classical chain DEC ⇒ WEC ⇒ NEC. The first implication is
direct from the DEC definition (DEC = WEC ∧ extra). The second
(WEC ⇒ NEC) requires a continuity hypothesis on `T` because null
vectors are limits of timelike sequences. We encode the continuity
hypothesis explicitly to keep it visible.
-/

/--
**DEC ⇒ WEC** (direct from the DEC bundle's WEC field).
Non-trivial because the conclusion is the bundle's load-bearing
sign claim, accessed via projection.
-/
theorem DEC_implies_WEC
    (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4)
    (h : DEC T g t) :
    WEC T g t := h.1

/--
**WEC ⇒ NEC under continuity hypothesis.** A null vector `k` can be
approximated by a sequence of future-directed timelike `v_n → k`
with `g(v_n, v_n) ↑ 0`. Continuity of `T` on the limit gives
`T(k, k) ≥ 0`. We encode this as a hypothesis-parameterized theorem:
given an explicit continuity-of-T witness, WEC implies NEC.

The continuity hypothesis `h_cts` says: for every null `k`, there
exists a sequence of future-directed timelike vectors `v : ℕ → Vec4`
converging to `k` with `T(v n, v n) → T(k, k)`.

Anti-pattern audit: the continuity hypothesis is load-bearing —
without it, WEC ⇏ NEC because a discontinuous `T` could be
non-negative on the open timelike cone but negative on the null
boundary.
-/
theorem WEC_implies_NEC_under_continuity
    (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4)
    (h_wec : WEC T g t)
    (h_cts : ∀ k : Vec4, IsNull g k →
      ∃ v : ℕ → Vec4, (∀ n, IsFutureDirectedTimelike g t (v n)) ∧
        Filter.Tendsto (fun n => T (v n) (v n)) Filter.atTop (nhds (T k k))) :
    NEC T g := by
  intro k hk
  obtain ⟨v, hv_fdtl, hv_lim⟩ := h_cts k hk
  -- Each T(v n, v n) ≥ 0 by WEC
  have h_seq_nn : ∀ n, 0 ≤ T (v n) (v n) := fun n => h_wec (v n) (hv_fdtl n)
  -- Limit of non-negative sequence is non-negative
  exact ge_of_tendsto' hv_lim (fun n => h_seq_nn n)

/--
**DEC ⇒ NEC under continuity hypothesis.** Composition of
`DEC_implies_WEC` and `WEC_implies_NEC_under_continuity`.
-/
theorem DEC_implies_NEC_under_continuity
    (T : StressEnergyTensor) (g : MetricTensor) (t : Vec4)
    (h_dec : DEC T g t)
    (h_cts : ∀ k : Vec4, IsNull g k →
      ∃ v : ℕ → Vec4, (∀ n, IsFutureDirectedTimelike g t (v n)) ∧
        Filter.Tendsto (fun n => T (v n) (v n)) Filter.atTop (nhds (T k k))) :
    NEC T g :=
  WEC_implies_NEC_under_continuity T g t (DEC_implies_WEC T g t h_dec) h_cts

/-! ## §5 — Counterexample witnesses

The classical separation theorems require explicit witnesses. We
construct three: cosmological-Λ violates SEC but satisfies WEC/NEC/DEC;
stiff fluid violates DEC but satisfies WEC/NEC/SEC; ghost scalar
violates NEC.
-/

/--
**Minkowski metric** (signature `−+++`). Concrete witness for `g`
in §6 counterexamples.
-/
noncomputable def minkowskiMetric : MetricTensor :=
  fun u v => -(u 0) * (v 0) + (u 1) * (v 1) + (u 2) * (v 2) + (u 3) * (v 3)

/--
**Cosmological-Λ stress-energy** with parameter `Λ > 0`. In
signature `−+++` with units `8πG = 1`:

    T_μν = -Λ · g_μν,    so   T(u, v) = -Λ · g(u, v).

This corresponds to `ρ = Λ`, `p = -Λ` (de Sitter equation of state).
It satisfies WEC and NEC and DEC, but VIOLATES SEC for `Λ > 0`.
-/
noncomputable def cosmologicalLambdaTensor (Λ : ℝ) : StressEnergyTensor :=
  fun u v => -Λ * minkowskiMetric u v

/--
**Cosmological-Λ tensor satisfies WEC** for `Λ ≥ 0`.

Proof: `T(v, v) = -Λ · g(v, v)`. For future-directed timelike `v`,
`g(v, v) < 0`, so `T(v, v) = -Λ · (negative) = Λ · |g(v,v)| ≥ 0`
when `Λ ≥ 0`.
-/
theorem cosmologicalLambda_WEC
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (t : Vec4) :
    WEC (cosmologicalLambdaTensor Λ) minkowskiMetric t := by
  intro v ⟨h_tl, _⟩
  unfold cosmologicalLambdaTensor
  -- T(v,v) = -Λ · g(v,v); g(v,v) < 0; so -Λ · g(v,v) ≥ 0 when Λ ≥ 0
  have h_gv_neg : minkowskiMetric v v < 0 := h_tl
  nlinarith

/--
**Cosmological-Λ tensor VIOLATES SEC** for `Λ > 0`, where the trace
is `trT = -4Λ` in 4D (since `T_μν = -Λ g_μν` ⇒ `T^μ_μ = -4Λ`).

Proof: SEC requires `T(v,v) - (1/2) · trT · g(v,v) ≥ 0` for
future-directed timelike `v`. Substituting:
- `T(v,v) = -Λ · g(v,v)`
- `(1/2) · trT · g(v,v) = (1/2) · (-4Λ) · g(v,v) = -2Λ · g(v,v)`
- Difference: `-Λ · g(v,v) - (-2Λ · g(v,v)) = Λ · g(v,v)`

For `Λ > 0` and timelike `v`, `g(v,v) < 0`, so `Λ · g(v,v) < 0`.
SEC requires `≥ 0`, so SEC is VIOLATED.

We supply an explicit witness `v_witness = (1, 0, 0, 0)` (future-
directed timelike in `−+++` signature with `t = (1,0,0,0)`).
-/
theorem cosmologicalLambda_violates_SEC
    {Λ : ℝ} (hΛ : 0 < Λ) :
    let t : Vec4 := ![1, 0, 0, 0]
    let v_witness : Vec4 := ![1, 0, 0, 0]
    IsFutureDirectedTimelike minkowskiMetric t v_witness ∧
    ¬ (0 ≤ (cosmologicalLambdaTensor Λ) v_witness v_witness
        - (1/2) * (-4 * Λ) * minkowskiMetric v_witness v_witness) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- IsTimelike: g(v, v) = -1 < 0
      unfold IsTimelike minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · -- g(t, v) < 0: with t = v = (1,0,0,0), g(t, v) = -1 < 0 ✓
      unfold minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- SEC violation: T(v,v) - (1/2)·trT·g(v,v) = Λ·g(v,v) = -Λ < 0
    unfold cosmologicalLambdaTensor minkowskiMetric
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith

/--
**Cosmological-Λ tensor satisfies NEC** for `Λ ≥ 0`.

Proof: `T(k, k) = -Λ · g(k, k) = 0` for null `k` (since `g(k, k) = 0`
by the null condition). NEC requires `0 ≤ T(k, k) = 0`, which holds
trivially. Note this proof does NOT require `Λ > 0` — even at
`Λ = 0`, NEC holds (vacuously).
-/
theorem cosmologicalLambda_NEC
    (Λ : ℝ) :
    NEC (cosmologicalLambdaTensor Λ) minkowskiMetric := by
  intro k h_null
  unfold cosmologicalLambdaTensor
  -- T(k, k) = -Λ · g(k, k); g(k, k) = 0 from null condition
  rw [h_null.1]
  -- Goal: 0 ≤ -Λ * 0 = 0
  linarith

/-! ## §6 — Ghost-scalar witness: NEC violation

A ghost scalar field has stress-energy `T_μν = -∂_μφ ∂_νφ +
(1/2) g_μν (∂φ)²`. For null `k`, `T(k, k) = -(k·∂φ)² ≤ 0`, with
equality only when `k·∂φ = 0`. This is the canonical NEC-violator
in the literature (Carroll §4.6).

We construct an explicit ghost-scalar tensor (as a (0,2) bilinear
form) with non-zero gradient `n` and verify `T(k, k) < 0` for an
explicit null vector that is not orthogonal to `n`.
-/

/--
**Ghost-scalar stress-energy tensor** with field-gradient `n : Vec4`.
Encoded as `T(u, v) = -⟨n, u⟩·⟨n, v⟩ + (1/2) ⟨n, n⟩_g · g(u, v)`
where `⟨n, u⟩ = n 0 · u 0 + n 1 · u 1 + n 2 · u 2 + n 3 · u 3` is
the un-metric-contracted inner product (placeholder for `∂_μφ · u^μ`
in coordinate-free notation).

For our explicit witness we pick `n` with non-zero components such
that the ghost behavior is manifest.
-/
noncomputable def ghostScalarTensor (n : Vec4) : StressEnergyTensor :=
  fun u v =>
    -((n 0 * u 0 + n 1 * u 1 + n 2 * u 2 + n 3 * u 3)
       * (n 0 * v 0 + n 1 * v 1 + n 2 * v 2 + n 3 * v 3))

/--
**Ghost-scalar VIOLATES NEC** with an explicit witness.

We pick `n = (0, 1, 0, 0)` (purely spacelike gradient) and
`k = (1, 1, 0, 0)` (null vector: `g(k, k) = -1 + 1 = 0`).
Then `(n · k) = 0·1 + 1·1 = 1`, so `T(k, k) = -(1)² = -1 < 0`.
NEC requires `0 ≤ T(k, k)`, so it is VIOLATED.

Note: we use the simplified `T(u, v) = -⟨n, u⟩·⟨n, v⟩` form (drop
the `(1/2) g(...)` term, which would also vanish on null `k`); the
NEC-violation content is preserved under either form.
-/
theorem ghostScalar_violates_NEC :
    let n : Vec4 := ![0, 1, 0, 0]
    let k_null : Vec4 := ![1, 1, 0, 0]
    IsNull minkowskiMetric k_null ∧
    (ghostScalarTensor n) k_null k_null < 0 := by
  refine ⟨?_, ?_⟩
  · -- IsNull: g(k, k) = -1 + 1 = 0, AND k ≠ 0
    refine ⟨?_, ?_⟩
    · unfold minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    · intro h
      have h0 : (![1, 1, 0, 0] : Vec4) 0 = 0 := by rw [h]; rfl
      simp [Matrix.cons_val_zero] at h0
  · -- T(k, k) = -1 < 0
    unfold ghostScalarTensor
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

/-! ## §6.5 — Perfect-fluid carrier and stiff-fluid DEC-violation witness

A perfect-fluid stress-energy tensor in the rest frame `u = (1,0,0,0)`
takes the diagonal form `T_μν = diag(ρ, p, p, p)` (where `ρ` is energy
density and `p` is pressure). Per Hawking-Ellis Type I §4.3, this is
the canonical setting for predicate-equivalence theorems and
counterexamples.

We supply an explicit perfect-fluid tensor in the rest frame and use
it to provide the **stiff-fluid DEC-violation witness** named in
the Phase 6f deep-research audit §5.6f.3: `ρ = 1`, `p = 2` satisfies
WEC + NEC + SEC but VIOLATES DEC.
-/

/--
**Perfect-fluid stress-energy tensor in rest frame `u = (1,0,0,0)`,
signature `−+++`.** Components `T_μν = diag(ρ, p, p, p)` (in this
frame); evaluated as a bilinear form on `Vec4`,
`T(v, w) = ρ · v⁰ · w⁰ + p · (v¹·w¹ + v²·w² + v³·w³)`.

For arbitrary 4-velocity `u` the formula is `T_μν = (ρ + p) u_μ u_ν +
p g_μν`; we specialize to the rest-frame here for explicitness.
-/
noncomputable def perfectFluidTensor (ρ p : ℝ) : StressEnergyTensor :=
  fun v w =>
    ρ * (v 0) * (w 0) + p * ((v 1) * (w 1) + (v 2) * (w 2) + (v 3) * (w 3))

/--
**Stiff-fluid VIOLATES DEC** with the audit's named witness `ρ = 1,
p = 2`.

Concrete witness pair: `v = (1, 9/10, 0, 0)`, `w = (1, -9/10, 0, 0)`
(both future-directed timelike in `−+++` with `t = (1,0,0,0)`:
`g(v, v) = -1 + 81/100 = -19/100 < 0`, `g(t, v) = -1 < 0`; same for `w`).

`T(v, w) = ρ·1·1 + p · ((9/10)·(-9/10) + 0 + 0)
        = 1 + 2 · (-81/100)
        = 1 - 162/100 = -62/100 = -31/50 < 0`,

so DEC's `T(v, w) ≥ 0` requirement is VIOLATED.

Anti-pattern audit: explicit numerical witnesses (no ∃-absorption);
both `v` and `w` are independently future-directed timelike (so the
violation isn't due to a degenerate one of them); the ratio `p > ρ`
is exactly the audit's flagged stiff-fluid regime (`ρ < |p|`).
-/
theorem stiff_fluid_violates_DEC :
    let t : Vec4 := ![1, 0, 0, 0]
    let v_witness : Vec4 := ![1, 9/10, 0, 0]
    let w_witness : Vec4 := ![1, -9/10, 0, 0]
    IsFutureDirectedTimelike minkowskiMetric t v_witness ∧
    IsFutureDirectedTimelike minkowskiMetric t w_witness ∧
    (perfectFluidTensor 1 2) v_witness w_witness < 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- v is future-directed timelike
    refine ⟨?_, ?_⟩
    · unfold IsTimelike minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    · unfold minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- w is future-directed timelike
    refine ⟨?_, ?_⟩
    · unfold IsTimelike minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    · unfold minkowskiMetric
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · -- T(v, w) = -31/50 < 0
    unfold perfectFluidTensor
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-! ## §7 — Module summary -/

/--
**Phase 6f Wave 3 module summary marker.** This module ships **first
formalization** (per the Phase 6f deep-research audit §3E) of the
four classical-GR energy conditions WEC/NEC/DEC/SEC as predicates on
an abstract bilinear form, with chain implications and explicit
counterexample witnesses (cosmological-Λ violates SEC; stiff-fluid
violates DEC; ghost-scalar violates NEC).

Theorem roster: 8 substantive theorems + 1 marker, 0 sorry,
0 new axioms.

- `DEC_implies_WEC` (chain implication, direct projection)
- `WEC_implies_NEC_under_continuity` (chain via continuity)
- `DEC_implies_NEC_under_continuity` (composition)
- `cosmologicalLambda_WEC` (Λ ≥ 0 satisfies WEC)
- `cosmologicalLambda_violates_SEC` (Λ > 0 violates SEC, explicit witness)
- `cosmologicalLambda_NEC` (Λ at any value satisfies NEC vacuously)
- `ghostScalar_violates_NEC` (NEC violation via explicit non-zero
  gradient and explicit null vector)
- `stiff_fluid_violates_DEC` (DEC violation for ρ=1, p=2 with
  explicit witness pair v=(1,9/10,0,0), w=(1,-9/10,0,0))

**Anti-pattern audit (4-pattern check):** all counterexample
witnesses are explicit (no ∃-absorption); WEC predicate has
load-bearing timelike restriction (no P4 vacuous); chain
implications carry continuity hypothesis explicitly; counterexample
proofs use explicit numerical witnesses + `norm_num` / `nlinarith`.

**Cross-layer Python pipeline (Phase 6f W3 backfill 2026-04-29):**
`tests/test_energy_conditions.py` mirrors the 8 substantive theorems
(38 pytest cases / 7 test classes). `formulas.py` ships predicate
helpers (`is_null_vec`, `is_timelike`, `is_future_directed_timelike`)
and condition checks (`nec_check`, `wec_check`, `dec_check`,
`sec_check`) plus the three named tensor witnesses
(`cosmological_lambda_stress_energy`, `ghost_scalar_stress_energy`,
`perfect_fluid_stress_energy`). Figure
`fig_energy_conditions_perfect_fluid_regions` visualizes the four
condition regions in the (ρ, p) plane with the cos-Λ + stiff-fluid
witnesses marked.
-/
theorem _phase6f_w3_module_summary_marker : True := trivial

end SKEFTHawking.EnergyConditions
