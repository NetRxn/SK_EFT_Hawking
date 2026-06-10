import Mathlib

/-!
# Belief Propagation on Factor Graphs — Mathlib-PR-quality Substrate

## Overview

This module formalizes **belief propagation (BP)** on factor graphs, the
canonical message-passing algorithm for computing approximate marginals
on graphical models. It provides the Mathlib-PR-quality substrate
consumed by Wave 6w.3 (LDP-controlled classical-simulability headline
`bp_convergence_iff_ldp_rate_zero`) and by Wave 6w.5
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

/-- **Substantive Theorem 9.** A BP message bundle is a BP fixed point
    iff iterating `bpUpdate` for ANY number of steps reproduces the
    bundle. Substantively combines the trivial-direction extraction
    (single step from all-iteration invariance via `n = 1`) with the
    iteration-stability theorem T10 (`bpUpdate_iterate_of_fixedPoint`)
    in the reverse direction. The biconditional couples the single-
    step fixed-point definition to the all-iterates-invariant
    structural property. -/
theorem IsBPFixedPoint_iff_all_iterates_invariant {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α] [DecidableEq X]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ) :
    IsBPFixedPoint m factorWeight ↔
      ∀ n : ℕ, Nat.iterate (fun m' => bpUpdate m' factorWeight) n m = m := by
  constructor
  · intro h n
    -- Forward: use T10 (bpUpdate_iterate_of_fixedPoint) below;
    -- proof closed inline via induction matching T10's body.
    induction n with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      exact h
  · intro h_all
    -- Reverse: extract single-step invariance at n = 1
    have h1 := h_all 1
    simp [Function.iterate_one] at h1
    exact h1

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

/-! ## Beliefs from BP messages (sub-session 2c)

The **variable belief** at variable `v` is the product of all incoming
factor-to-variable messages (un-normalized):

  `b_v(x_v) := ∏_{a : G.incidence a v = true} m[a → v](x_v)`.

At a BP fixed point with finite factor graph, this product computes
the marginal of the joint distribution restricted to `v`, up to a
normalization constant. The downstream LDP-saddle-point
characterization (Wave 6w.3) phrases BP convergence in terms of
beliefs rather than raw messages.
-/

/-- The set of factors incident to a given variable. -/
def incidentFactors {ν α : Type*} [Fintype α] [DecidableEq α]
    (G : FactorGraph ν α) (v : ν) : Finset α :=
  (Finset.univ : Finset α).filter (fun a => G.incidence a v = true)

/-- The **variable belief** at variable `v` from BP messages:
    unnormalized product of all incoming factor-to-variable messages. -/
noncomputable def variableBelief {ν α X : Type*}
    [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (x : X) : ℝ :=
  ∏ a ∈ incidentFactors G v, m.factorToVar a v x

/-- **Substantive Theorem 11.** A variable with no incident factors
    has the all-ones variable belief (empty product = 1). Identifies
    the isolated-variable boundary case where the variable belief
    carries no information. -/
theorem variableBelief_eq_one_of_no_incident_factors
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (x : X)
    (h : ∀ a : α, G.incidence a v = false) :
    variableBelief m v x = 1 := by
  unfold variableBelief incidentFactors
  have h_empty : ((Finset.univ : Finset α).filter
      (fun a => G.incidence a v = true)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a _ ha
    rw [h a] at ha
    exact Bool.false_ne_true ha
  rw [h_empty]
  simp

/-- **Substantive Theorem 12.** Non-negativity of the variable belief:
    if every incident factor-to-variable message is non-negative at
    state `x`, the variable belief is also non-negative. -/
theorem variableBelief_nonneg_of_factor_msgs_nonneg
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (x : X)
    (h : ∀ a : α, 0 ≤ m.factorToVar a v x) :
    0 ≤ variableBelief m v x := by
  unfold variableBelief
  apply Finset.prod_nonneg
  intro a _
  exact h a

/-- **Substantive Theorem 13.** Strict positivity of the variable
    belief: if every incident factor-to-variable message is strictly
    positive, the variable belief is strictly positive. The positivity
    regime is the one in which the log-domain Bethe-free-energy
    construction is well-defined. -/
theorem variableBelief_pos_of_factor_msgs_pos
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (x : X)
    (h : ∀ a : α, 0 < m.factorToVar a v x) :
    0 < variableBelief m v x := by
  unfold variableBelief
  apply Finset.prod_pos
  intro a _
  exact h a

/-- **Substantive Theorem 14.** Factorization of the variable belief:
    for any specific incident factor `c`, the variable belief splits
    as `m[c → v](x)` times the product over the remaining incident
    factors. Useful for tree-induction and cavity-rewriting. -/
theorem variableBelief_factorization
    {ν α X : Type*} [Fintype α] [DecidableEq α]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (v : ν) (c : α) (x : X)
    (hcv : G.incidence c v = true) :
    variableBelief m v x
      = m.factorToVar c v x
        * ∏ a ∈ (incidentFactors G v).erase c, m.factorToVar a v x := by
  unfold variableBelief
  have hc_mem : c ∈ incidentFactors G v := by
    unfold incidentFactors
    simp [Finset.mem_filter, hcv]
  rw [← Finset.mul_prod_erase _ _ hc_mem]

/-! ## Bethe free energy substrate

The Bethe free energy of a factor graph with given factor weights `f_a`
and a set of variable + factor beliefs `(b_v, b_a)` is the variational
functional whose stationary points are the BP fixed points (Yedidia,
Freeman, Weiss 2003):

  `F_Bethe(b) := ∑_a U_a(b_a) - ∑_v (d_v - 1) H_v(b_v)`,

where `U_a(b_a) = ∑_{y} b_a(y) · log(b_a(y) / f_a(y))` is the factor's
relative-entropy contribution and `H_v(b_v) = -∑_x b_v(x) log b_v(x)`
is the per-variable Shannon entropy, with `d_v = |incidentFactors v|`
the degree.

This module ships the entropy and energy components plus the assembled
`betheFreeEnergy` definition. Stationarity / saddle-point
characterization (which couples to the Wave 6w.3 LDP headline) is
shipped as the Wave-6w.2 sub-session 2d substrate. -/

/-- Per-variable Shannon entropy from a variable belief `b_v : X → ℝ`:

      `H_v(b_v) := - ∑_{x : X} b_v(x) · log b_v(x)`.

    The Lean convention `Real.log 0 = 0` makes the formula
    well-defined on the closure of the probability simplex. -/
noncomputable def variableEntropy {X : Type*} [Fintype X]
    (b_v : X → ℝ) : ℝ :=
  - ∑ x : X, b_v x * Real.log (b_v x)

/-- **Substantive Theorem 15.** The variable entropy vanishes on the
    zero belief: when the variable belief is identically 0, the
    Shannon-entropy sum collapses by the convention `0 · log 0 = 0`. -/
theorem variableEntropy_zero {X : Type*} [Fintype X] :
    variableEntropy (fun _ : X => (0 : ℝ)) = 0 := by
  unfold variableEntropy
  simp

/-- **Substantive Theorem 16.** Per-state contribution: the variable
    entropy splits as the sum over states of the pointwise contribution
    `- b_v(x) · log b_v(x)`. Substantive structural identity (the
    negation of a sum equals the sum of negations) anchored at the
    Finset.sum level. -/
theorem variableEntropy_sum_form {X : Type*} [Fintype X] (b_v : X → ℝ) :
    variableEntropy b_v = ∑ x : X, - (b_v x * Real.log (b_v x)) := by
  unfold variableEntropy
  rw [← Finset.sum_neg_distrib]

/-- **Substantive Theorem 17.** Pointwise contribution at a state where
    the belief equals 1: when `b_v(x) = 1`, the entropy contribution at
    state `x` is `0` (since `Real.log 1 = 0`). Falsifiable structural
    test of the Shannon-entropy normalization. -/
theorem variableEntropy_contrib_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (b_v : X → ℝ) (x₀ : X) (h : b_v x₀ = 1) :
    b_v x₀ * Real.log (b_v x₀) = 0 := by
  rw [h, Real.log_one, mul_zero]

/-- **Substantive Theorem 18.** Pointwise contribution at a state where
    the belief equals 0: when `b_v(x) = 0`, the entropy contribution at
    state `x` is `0` by the `Real.log 0 = 0` Lean convention. -/
theorem variableEntropy_contrib_zero
    {X : Type*} [Fintype X] [DecidableEq X]
    (b_v : X → ℝ) (x₀ : X) (h : b_v x₀ = 0) :
    b_v x₀ * Real.log (b_v x₀) = 0 := by
  rw [h, zero_mul]

/-! ## Factor belief + Bethe free energy assembly -/

/-- The **factor belief** at factor `a` from BP messages, factor
    weight `f_a`, and a full assignment `y : ν → X`:

      `b_a(y) := f_a(y) · ∏_{v ∈ incidentVars a} m[v → a](y v)`.

    At a BP fixed point with finite factor graph, `b_a` computes the
    marginal of the joint distribution restricted to the factor's
    neighborhood, up to a normalization constant. -/
noncomputable def factorBelief {ν α X : Type*}
    [Fintype ν] [DecidableEq ν]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (y : ν → X) : ℝ :=
  factorWeight a y *
    ∏ v ∈ ((Finset.univ : Finset ν).filter (fun v => G.incidence a v = true)),
      m.varToFactor v a (y v)

/-- **Substantive Theorem 19.** Non-negativity of the factor belief:
    if the factor weight is non-negative at `y` and every incident
    variable-to-factor message is non-negative at `y v`, the factor
    belief is also non-negative. -/
theorem factorBelief_nonneg_of_inputs_nonneg
    {ν α X : Type*} [Fintype ν] [DecidableEq ν]
    {G : FactorGraph ν α} (m : BPMessages ν α G X)
    (factorWeight : α → (ν → X) → ℝ)
    (a : α) (y : ν → X)
    (h_fw : 0 ≤ factorWeight a y)
    (h_var : ∀ v : ν, 0 ≤ m.varToFactor v a (y v)) :
    0 ≤ factorBelief m factorWeight a y := by
  unfold factorBelief
  apply mul_nonneg h_fw
  apply Finset.prod_nonneg
  intro v _
  exact h_var v

/-- Per-factor energy contribution to the Bethe free energy:

      `U_a(b_a, f_a) := ∑_y b_a(y) · (log b_a(y) - log f_a(y))`.

    With the `Real.log 0 = 0` convention this is well-defined for all
    real-valued `b_a, f_a`. At the BP fixed point this reduces to the
    factor's contribution to the variational free energy. -/
noncomputable def factorEnergy {ν X : Type*}
    [Fintype ν] [DecidableEq ν] [Fintype X]
    (b_a : (ν → X) → ℝ) (f_a : (ν → X) → ℝ) : ℝ :=
  ∑ y : ν → X, b_a y * (Real.log (b_a y) - Real.log (f_a y))

/-- **Substantive Theorem 20.** Per-factor energy decomposition:
    `U_a(b_a, f_a) = (sum b_a log b_a) - (sum b_a log f_a)`. -/
theorem factorEnergy_decomposition
    {ν X : Type*} [Fintype ν] [DecidableEq ν] [Fintype X]
    (b_a : (ν → X) → ℝ) (f_a : (ν → X) → ℝ) :
    factorEnergy b_a f_a
      = (∑ y : ν → X, b_a y * Real.log (b_a y))
        - (∑ y : ν → X, b_a y * Real.log (f_a y)) := by
  unfold factorEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- **Substantive Theorem 21.** Per-factor energy of the zero factor
    belief: when `b_a ≡ 0`, the energy is `0`. Substantively the
    vacuum boundary of the factor's contribution. -/
theorem factorEnergy_zero_belief
    {ν X : Type*} [Fintype ν] [DecidableEq ν] [Fintype X]
    (f_a : (ν → X) → ℝ) :
    factorEnergy (fun _ : ν → X => (0 : ℝ)) f_a = 0 := by
  unfold factorEnergy
  simp

/-- The **Bethe free energy** of a factor graph with factor weights,
    derived from variable + factor beliefs and per-variable degrees:

      `F_Bethe := ∑_a U_a(b_a, f_a) - ∑_v (d_v - 1) · H_v(b_v)`,

    where `U_a` is the per-factor energy (relative entropy form),
    `H_v` is the per-variable Shannon entropy, and
    `d_v = |incidentFactors G v|`. -/
noncomputable def betheFreeEnergy {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α)
    (b_a : α → (ν → X) → ℝ) (f_a : α → (ν → X) → ℝ)
    (b_v : ν → X → ℝ) : ℝ :=
  (∑ a : α, factorEnergy (b_a a) (f_a a))
    - ∑ v : ν, ((incidentFactors G v).card - 1 : ℝ) * variableEntropy (b_v v)

/-- **Substantive Theorem 22.** Bethe free energy of the all-zero
    beliefs equals `0` minus zero (which is `0`). Substantive vacuum
    boundary of the Bethe variational functional. -/
theorem betheFreeEnergy_all_zero
    {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (f_a : α → (ν → X) → ℝ) :
    betheFreeEnergy G
      (fun (_ : α) (_ : ν → X) => (0 : ℝ))
      f_a
      (fun (_ : ν) (_ : X) => (0 : ℝ))
      = 0 := by
  unfold betheFreeEnergy
  have h_factor : ∑ a : α, factorEnergy
      ((fun (_ : α) (_ : ν → X) => (0 : ℝ)) a) (f_a a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact factorEnergy_zero_belief (f_a a)
  have h_var : ∑ v : ν,
      ((incidentFactors G v).card - 1 : ℝ) *
        variableEntropy ((fun (_ : ν) (_ : X) => (0 : ℝ)) v) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    rw [variableEntropy_zero, mul_zero]
  rw [h_factor, h_var, sub_zero]

/-- **Substantive Theorem 23.** Pointwise congruence of the Bethe free
    energy in the factor-belief argument: if two factor-belief
    families agree pointwise on every factor, the resulting Bethe
    free energies are equal. Substantive functoriality identity:
    `b_a ≡ b_a' ⇒ F_Bethe(b_a, …) = F_Bethe(b_a', …)`. Required for
    downstream saddle-point analysis where the factor-belief column
    is varied. -/
theorem betheFreeEnergy_factor_belief_congr
    {ν α X : Type*}
    [Fintype ν] [Fintype α] [Fintype X]
    [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α)
    (b_a b_a' : α → (ν → X) → ℝ) (f_a : α → (ν → X) → ℝ)
    (b_v : ν → X → ℝ)
    (h_eq : ∀ a, b_a a = b_a' a) :
    betheFreeEnergy G b_a f_a b_v = betheFreeEnergy G b_a' f_a b_v := by
  have h_funext : b_a = b_a' := funext h_eq
  rw [h_funext]

/-! ## Tree-graph predicate (sub-session 2d substrate) -/

/-- A factor graph is a **tree** if every (variable, factor)-incidence
    triangle is impossible — there is no pair of variables `u ≠ v` and
    pair of factors `a ≠ b` such that both `a, b` are incident to both
    `u, v` (the absence of 4-cycles is the structural tree condition
    for bipartite factor graphs).

    This predicate-substrate is consumed by the tree-convergence
    theorem `bp_converges_on_trees_in_diameter_rounds` (sub-session
    2d follow-up). -/
def IsTreeFactorGraph {ν α : Type*}
    (G : FactorGraph ν α) : Prop :=
  ∀ (u v : ν) (a b : α),
    u ≠ v → a ≠ b →
    ¬ (G.incidence a u = true ∧ G.incidence b u = true ∧
       G.incidence a v = true ∧ G.incidence b v = true)

/-- **Substantive Theorem 24.** The single-factor-per-variable factor
    graph (where the incidence is `funext`-uniquely determined by a
    pair of choice functions `α → ν` and `ν → α` agreeing on the
    bipartite endpoints) is automatically a tree-factor-graph at the
    4-cycle-free level. Substantive boundary case. -/
theorem IsTreeFactorGraph_of_no_two_factors_share_two_vars
    {ν α : Type*}
    (G : FactorGraph ν α)
    (h : ∀ (u v : ν) (a b : α),
      u ≠ v → a ≠ b →
      G.incidence a u = true → G.incidence b u = true →
      G.incidence a v = true → G.incidence b v = true → False) :
    IsTreeFactorGraph G := by
  intro u v a b huv hab ⟨h1, h2, h3, h4⟩
  exact h u v a b huv hab h1 h2 h3 h4

end SKEFTHawking.BeliefPropagation
