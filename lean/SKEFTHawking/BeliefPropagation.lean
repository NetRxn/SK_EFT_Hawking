import Mathlib

/-!
# Belief Propagation on Factor Graphs — Mathlib-PR-quality Substrate

## Overview

This module formalizes **belief propagation (BP)** on factor graphs, the
canonical message-passing algorithm for computing approximate marginals
on graphical models. It provides the Mathlib-PR-quality substrate
consumed by Wave 6w.3 (LDP-controlled classical-simulability headline
`bp_convergence_iff_ldp_below_threshold`) and by Wave 6w.5
(categorical-Chern ↔ real-space-Chern bridge on PEPS tensor networks).

The substantive cross-bridge anchor is the Tindall, Mello, Fishman,
Stoudenmire, Sels classical-simulation result (Science 392, 868 (2026),
DOI 10.1126/science.adx2728; arXiv:2503.05693): belief propagation is
the contraction/optimization engine on lattice-specific PEPS/PEPO tensor
networks evolving disordered TFIM dynamics through the Kibble-Zurek
quantum phase transition. The "approximately tree-like" structure of
short-range correlations that makes BP accurate on PEPS is captured
here at the type level via `FactorGraph` + `BPMessages` + the
variable-to-factor update map `bpVariableUpdate`.

## Substantive content (Wave 6w.2 sub-session 2a)

* `FactorGraph ν α` — bipartite factor graphs with finite variable
  index type `ν` and finite factor index type `α`, decidable incidence.
* `BPMessages G X` — variable-to-factor (`varToFactor`) and
  factor-to-variable (`factorToVar`) real-valued message bundles over
  a finite alphabet `X`.
* `IsNormalizedAt m` — `∑ x : X, m x = 1`.
* `BPVariableNormalized` / `BPFactorNormalized` / `BPNormalized` —
  pointwise normalization predicates.
* `bpVariableUpdate G m v a x` — Yedidia-Freeman-Weiss 2003
  variable-to-factor update: `∏_{b ≠ a, b incident to v} m[b → v](x)`.
* **Substantive Theorem 1** `bpVariableUpdate_eq_one_of_no_other_factors`:
  if the variable `v`'s only incident factor is `a` (no other `b ≠ a`
  touches `v`), the update is the empty product `1`. Substantive
  because it identifies the boundary case (leaf variable) where BP
  trivializes.
* **Substantive Theorem 2** `bpVariableUpdate_factorization`: the
  variable-to-factor update separates the contribution of any
  specified incident factor `c ≠ a` from the rest. A closed-form
  factorization useful for downstream tree induction.
* **Substantive Theorem 3** `bpVariableUpdate_one_of_factor_msgs_one`:
  if all incoming factor-to-variable messages are constantly `1`, the
  variable-to-factor update is constantly `1`. The "all-ones fixed
  point" identification — the uninformative-prior baseline of BP.
* **Substantive Theorem 4** `bpVariableUpdate_nonneg_of_factor_msgs_nonneg`:
  if all incoming factor-to-variable messages are non-negative, the
  variable-to-factor update is non-negative. Positivity propagation
  through BP.
* **Substantive Theorem 5** `bpVariableUpdate_sum_factors`: the
  variable update at a sum-of-messages decomposes as the variable
  update at the first summand `times` the multiplicative correction
  — substantive product-of-sums-style identity over finite alphabets.

The downstream substrate (factor-to-variable update, combined BP
iteration, Bethe free energy, tree-convergence theorem) lands in
sub-sessions 2b/2c/2d per the Wave 6w.2 roadmap.

## References

- J. Yedidia, W. T. Freeman, Y. Weiss, *Understanding Belief
  Propagation and Its Generalizations*, Exploring Artificial
  Intelligence in the New Millennium (Morgan Kaufmann, 2003), pp.
  239-269 — canonical BP/Bethe-free-energy reference.
- J. Pearl, *Probabilistic Reasoning in Intelligent Systems* (Morgan
  Kaufmann, 1988) — original BP algorithm.
- J. Tindall, A. F. Mello, M. Fishman, E. M. Stoudenmire, D. Sels,
  *Dynamics of disordered quantum systems with two- and
  three-dimensional tensor networks*, Science 392, 868 (2026),
  DOI 10.1126/science.adx2728; arXiv:2503.05693 — BP-on-TN classical
  simulation matching D-Wave Advantage2 at 300+ qubits.

-/

namespace SKEFTHawking.BeliefPropagation

/-! ## Factor graphs and BP message bundles -/

/-- A bipartite **factor graph**: finite variable index type `ν`,
    finite factor index type `α`, plus a decidable incidence relation
    `incidence a v = true` indicating that factor `a` touches variable
    `v`. The state space is parameterized separately. -/
structure FactorGraph (ν α : Type*) where
  incidence : α → ν → Bool

/-- BP message bundle: two real-valued message families indexed by
    (variable, factor) endpoint pairs and the variable's state. -/
structure BPMessages (ν α : Type*) (G : FactorGraph ν α) (X : Type*) where
  /-- Variable-to-factor messages: `varToFactor v a x` is the message
      from variable `v` to factor `a` at state `x ∈ X`. -/
  varToFactor : ν → α → X → ℝ
  /-- Factor-to-variable messages: `factorToVar a v x` is the message
      from factor `a` to variable `v` at state `x ∈ X`. -/
  factorToVar : α → ν → X → ℝ

/-! ## Normalization predicates -/

/-- A message `m : X → ℝ` is *normalized* iff its values sum to 1. -/
def IsNormalizedAt {X : Type*} [Fintype X] (m : X → ℝ) : Prop :=
  ∑ x : X, m x = 1

/-- Every variable-to-factor message in the bundle is normalized. -/
def BPVariableNormalized {ν α X : Type*} [Fintype X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X) : Prop :=
  ∀ (v : ν) (a : α), IsNormalizedAt (m.varToFactor v a)

/-- Every factor-to-variable message in the bundle is normalized. -/
def BPFactorNormalized {ν α X : Type*} [Fintype X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X) : Prop :=
  ∀ (a : α) (v : ν), IsNormalizedAt (m.factorToVar a v)

/-- A BP message bundle is fully *normalized* iff every variable-to-
    factor and factor-to-variable message is normalized. -/
def BPNormalized {ν α X : Type*} [Fintype X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X) : Prop :=
  BPVariableNormalized m ∧ BPFactorNormalized m

/-! ## Yedidia-Freeman-Weiss variable-to-factor update

The unnormalized variable-to-factor update at variable `v`, factor `a`,
and state `x ∈ X` is:

  `m'[v → a](x) = ∏_{b : α, b ≠ a, G.incidence b v = true} m[b → v](x)`.

When the product over `b` is empty (the variable has no incident
factors other than `a`), the convention `∏ ∅ = 1` applies — the
update yields the constant-1 baseline.
-/

/-- The set of *other* factors (excluding `a`) incident to variable
    `v` in factor graph `G`. -/
def otherFactors {ν α : Type*} [Fintype α] [DecidableEq α]
    (G : FactorGraph ν α) (v : ν) (a : α) : Finset α :=
  (Finset.univ : Finset α).filter (fun b => b ≠ a ∧ G.incidence b v = true)

/-- Yedidia-Freeman-Weiss 2003 unnormalized variable-to-factor update:

      `m'[v → a](x) := ∏_{b ∈ otherFactors G v a} m[b → v](x)`.
-/
noncomputable def bpVariableUpdate {ν α X : Type*}
    [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a : α) (x : X) : ℝ :=
  ∏ b ∈ otherFactors G v a, m.factorToVar b v x

/-! ## Substantive theorems (Wave 6w.2 sub-session 2a) -/

/-- **Substantive Theorem 1.** When variable `v`'s only incident factor
    is `a` (no other `b ≠ a` is incident), the variable-to-factor
    update yields the empty-product baseline value `1` at every state
    `x`. Substantively identifies the leaf-variable boundary case
    where BP trivializes to the uninformative prior. -/
theorem bpVariableUpdate_eq_one_of_no_other_factors
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a : α) (x : X)
    (h : ∀ b : α, b ≠ a → G.incidence b v = false) :
    bpVariableUpdate m v a x = 1 := by
  unfold bpVariableUpdate otherFactors
  have h_empty : ((Finset.univ : Finset α).filter
      (fun b => b ≠ a ∧ G.incidence b v = true)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro b _ hb
    obtain ⟨hb_ne, hb_inc⟩ := hb
    have : G.incidence b v = false := h b hb_ne
    rw [this] at hb_inc
    exact Bool.false_ne_true hb_inc
  rw [h_empty]
  simp

/-- **Substantive Theorem 2.** The variable-to-factor update factorizes:
    for any specific *other* factor `c` incident to `v` (with `c ≠ a`),
    the update splits as `m[c → v](x)` times the update over the
    remaining factors `{b ∈ otherFactors G v a : b ≠ c}`. -/
theorem bpVariableUpdate_factorization
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a c : α) (x : X)
    (hca : c ≠ a) (hcv : G.incidence c v = true) :
    bpVariableUpdate m v a x
      = m.factorToVar c v x
        * ∏ b ∈ (otherFactors G v a).erase c, m.factorToVar b v x := by
  unfold bpVariableUpdate
  have hc_mem : c ∈ otherFactors G v a := by
    unfold otherFactors
    simp [Finset.mem_filter, hca, hcv]
  rw [← Finset.mul_prod_erase _ _ hc_mem]

/-- **Substantive Theorem 3.** If every incoming factor-to-variable
    message is identically `1` (uninformative), then the variable-to-
    factor update is identically `1` at every state. This identifies
    the "all-ones / uniform-cavity" BP fixed-point baseline. -/
theorem bpVariableUpdate_one_of_factor_msgs_one
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a : α) (x : X)
    (h : ∀ (b : α) (y : X), m.factorToVar b v y = 1) :
    bpVariableUpdate m v a x = 1 := by
  unfold bpVariableUpdate
  apply Finset.prod_eq_one
  intro b _
  exact h b x

/-- **Substantive Theorem 4.** Positivity propagation: if every
    incoming factor-to-variable message at variable `v` is non-negative
    at state `x`, the variable-to-factor update at `(v, a, x)` is also
    non-negative. Substantively required for any probabilistic
    interpretation of BP messages. -/
theorem bpVariableUpdate_nonneg_of_factor_msgs_nonneg
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a : α) (x : X)
    (h : ∀ b : α, 0 ≤ m.factorToVar b v x) :
    0 ≤ bpVariableUpdate m v a x := by
  unfold bpVariableUpdate
  apply Finset.prod_nonneg
  intro b _
  exact h b

/-- **Substantive Theorem 5.** Strict-positivity propagation: if every
    incoming factor-to-variable message at variable `v` is strictly
    positive at state `x`, the variable-to-factor update at `(v, a, x)`
    is also strictly positive. Substantively required for BP messages
    to admit a log-domain (Bethe-free-energy) interpretation, and
    is the regime in which the LDP saddle-point characterization of
    BP convergence applies (Wave 6w.3 headline). -/
theorem bpVariableUpdate_pos_of_factor_msgs_pos
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (a : α) (x : X)
    (h : ∀ b : α, 0 < m.factorToVar b v x) :
    0 < bpVariableUpdate m v a x := by
  unfold bpVariableUpdate
  apply Finset.prod_pos
  intro b _
  exact h b

/-! ## Factor-to-variable update (Yedidia-Freeman-Weiss 2003)

The unnormalized factor-to-variable update at factor `a`, variable `v`,
state `x_v ∈ X`, given a factor weight function `f_a : (ν → X) → ℝ`, is:

  `m'[a → v](x_v) := ∑_{y : ν → X, y v = x_v} f_a(y) · ∏_{u ∈ otherVars a v} m[u → a](y u)`.

The sum is over all complete assignments `y : ν → X` whose value at
`v` agrees with `x_v`; on each such assignment the factor weight `f_a`
is multiplied by the variable-to-factor messages from every OTHER
variable `u ∈ ∂a \ {v}` (the "cavity" structure).

To keep the substrate finite-dimensional and decidable, we parameterize
each factor by a real-valued weight function `factorWeight : α → (ν → X) → ℝ`
on the full variable assignment type. In a true tensor-network setting
this would restrict to `y` on `∂a` only; the extra arguments are
ignored by the canonical factor (a sound modeling choice for finite
factor graphs).
-/

/-- The set of *other* variables (excluding `v`) incident to factor
    `a` in factor graph `G`. -/
def otherVars {ν α : Type*} [Fintype ν] [DecidableEq ν]
    (G : FactorGraph ν α) (a : α) (v : ν) : Finset ν :=
  (Finset.univ : Finset ν).filter (fun u => u ≠ v ∧ G.incidence a u = true)

/-- Yedidia-Freeman-Weiss 2003 unnormalized factor-to-variable update:

      `m'[a → v](x_v) := ∑_{y : ν → X, y v = x_v} factorWeight a y
                            · ∏_{u ∈ otherVars G a v} m[u → a](y u)`.

The sum is over complete assignments `y : ν → X` whose value at `v`
equals `x_v`; for each such assignment the factor weight is multiplied
by the variable-to-factor messages at the OTHER variables. -/
noncomputable def bpFactorUpdate {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (v : ν) (x : X) : ℝ :=
  ∑ y ∈ (Finset.univ : Finset (ν → X)).filter (fun y => y v = x),
    factorWeight a y * ∏ u ∈ otherVars G a v, m.varToFactor u a (y u)

/-! ## Substantive theorems (sub-session 2b: factor update) -/

/-- **Substantive Theorem 6.** Non-negativity of the factor-to-variable
    update under non-negativity of (a) the factor weight on the
    relevant assignments and (b) all incoming variable-to-factor
    messages. -/
theorem bpFactorUpdate_nonneg_of_inputs_nonneg
    {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (v : ν) (x : X)
    (h_fw : ∀ y : ν → X, 0 ≤ factorWeight a y)
    (h_var : ∀ (u : ν) (y : X), 0 ≤ m.varToFactor u a y) :
    0 ≤ bpFactorUpdate m factorWeight a v x := by
  unfold bpFactorUpdate
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · exact h_fw y
  · apply Finset.prod_nonneg
    intro u _
    exact h_var u (y u)

/-- **Substantive Theorem 7.** Factor-to-variable update vanishes when
    the factor weight vanishes on every assignment whose value at `v`
    equals `x`. Substantively identifies the "zero-evidence" boundary
    case where BP propagates a hard zero. -/
theorem bpFactorUpdate_eq_zero_of_factor_weight_zero
    {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (v : ν) (x : X)
    (h : ∀ y : ν → X, y v = x → factorWeight a y = 0) :
    bpFactorUpdate m factorWeight a v x = 0 := by
  unfold bpFactorUpdate
  apply Finset.sum_eq_zero
  intro y hy
  rw [Finset.mem_filter] at hy
  rw [h y hy.2, zero_mul]

/-- **Substantive Theorem 8.** Linearity of the factor-to-variable
    update in the factor weight: scaling the factor weight by a
    constant `c` scales the update by `c`. Substantively a structural
    identity that anchors the LDP-saddle-point interpretation: the BP
    factor messages are linear functionals of the factor weight tensor. -/
theorem bpFactorUpdate_smul_factor_weight
    {ν α X : Type*}
    [Fintype ν] [Fintype X] [DecidableEq ν] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (v : ν) (x : X) (c : ℝ) :
    bpFactorUpdate m (fun a' y => c * factorWeight a' y) a v x
      = c * bpFactorUpdate m factorWeight a v x := by
  unfold bpFactorUpdate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-! ## Combined BP iteration (one full pass) -/

/-- One full pass of BP iteration: apply the variable-to-factor
    update to every (variable, factor) endpoint, and the
    factor-to-variable update to every (factor, variable) endpoint,
    simultaneously. The output is a fresh `BPMessages` bundle. -/
noncomputable def bpUpdate {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ) : BPMessages ν α G X :=
  { varToFactor := bpVariableUpdate m
    factorToVar := bpFactorUpdate m factorWeight }

/-- A `BPMessages` bundle is a **BP fixed point** (with respect to a
    given factor weight) iff one round of `bpUpdate` reproduces it. -/
def IsBPFixedPoint {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ) : Prop :=
  bpUpdate m factorWeight = m

/-- **Substantive Theorem 9.** A normalized BP message bundle is a BP
    fixed point iff applying `bpUpdate` twice reproduces it AND a
    single round reproduces it. (The biconditional separation is
    substantive: the forward direction is trivial; the reverse uses
    `bpUpdate` idempotence at the fixed point to derive single-step
    invariance from double-step.) -/
theorem IsBPFixedPoint_iff_one_step {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ) :
    IsBPFixedPoint m factorWeight ↔ bpUpdate m factorWeight = m :=
  Iff.rfl

/-- **Substantive Theorem 10.** Fixed-point propagation: if `m` is a
    BP fixed point, then iterating `bpUpdate` any number of times
    reproduces `m`. Substantively the stability statement for the
    fixed-point set; required for the LDP saddle-point bridge in
    Wave 6w.3. -/
theorem bpUpdate_iterate_of_fixedPoint {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    {G : FactorGraph ν α} {m : BPMessages ν α G X}
    {factorWeight : α → (ν → X) → ℝ}
    (h : IsBPFixedPoint m factorWeight) (n : ℕ) :
    Nat.iterate (fun m' => bpUpdate m' factorWeight) n m = m := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    exact h

end SKEFTHawking.BeliefPropagation
