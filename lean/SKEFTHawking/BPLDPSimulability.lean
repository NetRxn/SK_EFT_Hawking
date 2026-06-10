import Mathlib
import SKEFTHawking.BeliefPropagation
import SKEFTHawking.LDP.CramerIID

/-!
# LDP-controlled classical-simulability of belief propagation (Wave 6w.3, A1a)

## Overview

Headline biconditional `bp_convergence_iff_ldp_rate_zero`
characterizing when belief-propagation on a finite factor graph admits
a classically-simulable dynamics regime: the loop-correction rate
function vanishes iff the factor graph admits the
structural-simulability property `IsBPConvergenceFavorable`
(tree topology + non-negative factor weights).

The Tindall-Sels result (Science 392, 868 (2026), DOI
10.1126/science.adx2728; arXiv:2503.05693) shows empirically that
BP-on-PEPS classical simulation matches the D-Wave Advantage2 quantum
annealer at 300+ qubits when the underlying spin-glass topology is
sufficiently tree-like. This module formalizes a continuous
rate-function characterization of that regime at the substrate level.

## The loop-correction rate function (review-2026-06-05 D7-EV3 upgrade)

The original Wave 6w.3 `loopCorrectionRate` was a `{0,1}`-valued
indicator (`if IsTreeFactorGraph G then 0 else 1`) — honestly
disclosed in the D7 draft as *not* a continuous Cramér-type rate
function. This revision replaces it with a genuine Legendre-transform
construction:

* `fourCycles G` — the `Finset` of ordered 4-cycles `(u, v, a, b)`
  of a finite factor graph; non-emptiness is exactly failure of
  `IsTreeFactorGraph` (proven, `fourCycles_eq_empty_iff_tree`).
* `loopDensity G ∈ [0, 1)` — the fraction of tuples in the tuple
  space `ν × ν × α × α` that form a 4-cycle: the Bernoulli parameter
  of the **loop-presence observable** (the indicator that a uniformly
  drawn tuple is a loop-correction opportunity). Strictly below 1
  because diagonal tuples are never 4-cycles
  (`loopDensity_lt_one`).
* `bernoulliLoopMgf G θ = 1 − p + p·exp θ` (`p = loopDensity G`) —
  the moment-generating function of the loop-presence observable.
* `loopCorrectionRate G := ⨆ θ : ℝ, −log (bernoulliLoopMgf G θ)` —
  the **Cramér/Legendre transform of the log-MGF at zero deviation**:
  `I(0) = sup_θ (θ·0 − Λ(θ))`, the large-deviation rate of the
  *no-loop-correction event*. Closed form `−log(1 − p)` proven as
  `loopCorrectionRate_eq_neg_log` via an explicit `IsLUB` argument
  (the supremum is approached as `θ → −∞` and not attained for
  `p > 0`; the proof constructs explicit witnesses).

The rate is `0` exactly on trees (`loopCorrectionRate_eq_zero_iff_tree`
— proven through the Legendre evaluation, the density/log analysis,
and the Finset↔predicate bridge; NOT definitional), strictly positive
on loopy graphs (`loopCorrectionRate_pos_of_not_tree`), and **strictly
monotone in loop density** (`loopCorrectionRate_lt_of_loopDensity_lt`)
— it separates loopy graphs by their loop content, which no indicator
can (worked value: `log (4/3)` for the complete bipartite 2×2 graph,
`loopCorrectionRate_completeBipartite22`).

## LDP-suite connection

* `bernoulliCramerRate p q` — the Bernoulli Cramér rate function
  (Kullback-Leibler form) in `Real.negMulLog` form;
  `loopCorrectionRate G = bernoulliCramerRate (loopDensity G) 0`
  (`loopCorrectionRate_eq_bernoulliCramerRate_zero`).
* `loopCorrection_isCramerIIDUpperBound` — the loop MGF together with
  the mean-centered Bernoulli Cramér rate function satisfies the
  project LDP-suite predicate `SKEFTHawking.LDP.IsCramerIIDUpperBound`
  (continuity, centering, MGF normalization `mgf 0 = 1`).
* `no_loop_event_prob_eq_exp_neg_rate` — **exact** (finite-`n`, not
  just asymptotic) Cramér identity: `(1 − p)^n = exp(−n·I(0))` — the
  probability that `n` independent loop-correction opportunities all
  stay silent decays at exactly `loopCorrectionRate G`.

## Honest residual scope

The rate function is attached to the *combinatorial* loop-presence
observable (4-cycle density of the factor graph), matching the
granularity of the `IsTreeFactorGraph` predicate. The further
attachment to the *dynamical* loop-correction terms of the Bethe/BP
loop-series expansion (Chertkov-Chernyak loop calculus on the message
space, with the MGF taken over the BP messages themselves) is NOT in
the present substrate; the Bernoulli loop-presence observable is the
combinatorial shadow of that series. The zero-rate ⟺ tree boundary is
exactly where the loop series collapses (Bethe exactness on trees,
Yedidia-Freeman-Weiss 2003).

## HEADLINE

`bp_convergence_iff_ldp_rate_zero`: the substantive biconditional
`IsBPConvergenceFavorable G factorWeight ↔ loopCorrectionRate G = 0
∧ (∀ a y, 0 ≤ factorWeight a y)`. Forward: trees have empty 4-cycle
sets, hence zero loop density, hence zero rate. Reverse: zero rate
forces (through the Legendre evaluation and `−log(1−p) = 0 ⇒ p = 0`)
an empty 4-cycle set, hence a tree.

## References

- J. Tindall, A. F. Mello, M. Fishman, E. M. Stoudenmire, D. Sels,
  *Dynamics of disordered quantum systems with two- and
  three-dimensional tensor networks*, Science 392, 868 (2026),
  DOI 10.1126/science.adx2728; arXiv:2503.05693 — empirical
  BP-on-PEPS classical-simulation matching D-Wave Advantage2 at 300+
  qubits.
- M. Chertkov, V. Y. Chernyak, *Loop series for discrete statistical
  models on graphs*, J. Stat. Mech. (2006) P06009 — loop-series
  expansion underlying the loop-correction observable.
- M. Mézard, A. Montanari, *Information, Physics, and Computation*
  (Oxford UP, 2009) — replica-symmetric phase analysis of BP-on-loopy
  graphs.
- J. Yedidia, W. T. Freeman, Y. Weiss 2003 — Bethe-free-energy
  saddle-point characterization; Bethe exactness on trees.

-/

namespace SKEFTHawking.BPLDPSimulability

open SKEFTHawking.BeliefPropagation

variable {ν α : Type*}

/-! ## Loop structure: 4-cycles and loop density -/

/-- The `Finset` of ordered **4-cycles** of a finite factor graph:
    tuples `(u, v, a, b)` with `u ≠ v`, `a ≠ b`, and all four
    incidences `a–u`, `b–u`, `a–v`, `b–v` present. This is the loop
    structure detected by the `IsTreeFactorGraph` predicate:
    non-emptiness of this Finset is exactly failure of the tree
    property (`fourCycles_eq_empty_iff_tree`). -/
def fourCycles [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : Finset (ν × ν × α × α) :=
  Finset.univ.filter (fun t =>
    t.1 ≠ t.2.1 ∧ t.2.2.1 ≠ t.2.2.2 ∧
    G.incidence t.2.2.1 t.1 = true ∧ G.incidence t.2.2.2 t.1 = true ∧
    G.incidence t.2.2.1 t.2.1 = true ∧ G.incidence t.2.2.2 t.2.1 = true)

/-- Membership unfolding for `fourCycles`. -/
theorem mem_fourCycles [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    {G : FactorGraph ν α} {u v : ν} {a b : α} :
    (u, v, a, b) ∈ fourCycles G ↔
      u ≠ v ∧ a ≠ b ∧
      G.incidence a u = true ∧ G.incidence b u = true ∧
      G.incidence a v = true ∧ G.incidence b v = true := by
  simp [fourCycles]

/-- **Finset ↔ predicate bridge.** The 4-cycle Finset is empty iff the
    factor graph is a tree. This is the substantive bridge between the
    combinatorial loop structure (a counted `Finset`) and the
    `IsTreeFactorGraph` universal predicate of Wave 6w.2; every
    rate-function theorem below routes through it. -/
theorem fourCycles_eq_empty_iff_tree
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    fourCycles G = ∅ ↔ IsTreeFactorGraph G := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h u v a b huv hab hcyc
    exact h (u, v, a, b)
      (mem_fourCycles.mpr ⟨huv, hab, hcyc.1, hcyc.2.1, hcyc.2.2.1, hcyc.2.2.2⟩)
  · rintro h ⟨u, v, a, b⟩ hmem
    rw [mem_fourCycles] at hmem
    exact h u v a b hmem.1 hmem.2.1
      ⟨hmem.2.2.1, hmem.2.2.2.1, hmem.2.2.2.2.1, hmem.2.2.2.2.2⟩

/-- The **loop density** of a finite factor graph: the fraction of
    tuples in the tuple space `ν × ν × α × α` that form a 4-cycle.
    This is the Bernoulli success parameter of the **loop-presence
    observable** — the indicator that a uniformly drawn tuple is a
    loop-correction opportunity. The natural loop-excess measure at
    the granularity of the `IsTreeFactorGraph` predicate. -/
noncomputable def loopDensity
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : ℝ :=
  ((fourCycles G).card : ℝ) / (Fintype.card (ν × ν × α × α) : ℝ)

/-- The loop density is non-negative. -/
theorem loopDensity_nonneg
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : 0 ≤ loopDensity G :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Strict sub-unitality of the loop density.** `loopDensity G < 1`
    for every finite factor graph: diagonal tuples `(u, u, a, a)` are
    never 4-cycles (they fail `u ≠ v`), so the 4-cycle Finset is a
    proper subset of the tuple space whenever the latter is nonempty;
    the empty-tuple-space boundary case evaluates to `0/0 = 0 < 1`.
    Load-bearing: strictness is what makes `log (1 − loopDensity G)`
    well-defined (argument strictly positive) in the rate function. -/
theorem loopDensity_lt_one
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : loopDensity G < 1 := by
  unfold loopDensity
  rcases Nat.eq_zero_or_pos (Fintype.card (ν × ν × α × α)) with hN | hN
  · rw [hN]
    norm_num
  · have hne : Nonempty (ν × ν × α × α) := Fintype.card_pos_iff.mp hN
    obtain ⟨⟨u, _, a, _⟩⟩ := hne
    have hdiag : (u, u, a, a) ∉ fourCycles G := by
      rw [mem_fourCycles]
      rintro ⟨huu, -⟩
      exact huu rfl
    have hcard : (fourCycles G).card < Fintype.card (ν × ν × α × α) :=
      Finset.card_lt_univ_of_notMem hdiag
    rw [div_lt_one (by exact_mod_cast hN)]
    exact_mod_cast hcard

/-- **Zero loop density characterizes trees.** Routes through the
    Finset ↔ predicate bridge and the cast/division analysis
    (including the empty-tuple-space boundary, where the 4-cycle
    Finset is forced empty by the empty ambient type). -/
theorem loopDensity_eq_zero_iff_tree
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    loopDensity G = 0 ↔ IsTreeFactorGraph G := by
  unfold loopDensity
  constructor
  · intro h
    rw [← fourCycles_eq_empty_iff_tree, ← Finset.card_eq_zero]
    rcases div_eq_zero_iff.mp h with h' | h'
    · exact_mod_cast h'
    · have hN : Fintype.card (ν × ν × α × α) = 0 := by exact_mod_cast h'
      have hle : (fourCycles G).card ≤ Fintype.card (ν × ν × α × α) :=
        (Finset.card_filter_le _ _).trans_eq Finset.card_univ
      omega
  · intro htree
    rw [(fourCycles_eq_empty_iff_tree G).mpr htree]
    simp

/-! ## The Bernoulli loop-presence observable: MGF and Legendre rate -/

/-- The **moment-generating function of the Bernoulli loop-presence
    observable**: for loop density `p = loopDensity G`,

      `mgf(θ) = E[exp (θ·X)] = (1 − p) + p·exp θ`,

    where `X ~ Bernoulli(p)` is the indicator that a uniformly drawn
    tuple from the tuple space forms a 4-cycle (a loop-correction
    opportunity fires). -/
noncomputable def bernoulliLoopMgf
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (θ : ℝ) : ℝ :=
  1 - loopDensity G + loopDensity G * Real.exp θ

/-- The loop MGF is strictly positive everywhere (uses `p < 1`
    strictly). Required for the log in the Legendre transform. -/
theorem bernoulliLoopMgf_pos
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (θ : ℝ) : 0 < bernoulliLoopMgf G θ := by
  unfold bernoulliLoopMgf
  have h1 := loopDensity_lt_one G
  have h2 : 0 ≤ loopDensity G * Real.exp θ :=
    mul_nonneg (loopDensity_nonneg G) (Real.exp_pos θ).le
  linarith

/-- **MGF normalization**: `mgf 0 = 1` — the loop MGF is a bona fide
    moment-generating function (`E[exp(0·X)] = 1`). This is the exact
    form of the `mgf 0 ≤ 1` field of the project LDP-suite predicate
    `SKEFTHawking.LDP.IsCramerIIDUpperBound`. -/
theorem bernoulliLoopMgf_zero
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : bernoulliLoopMgf G 0 = 1 := by
  unfold bernoulliLoopMgf
  rw [Real.exp_zero]
  ring

/-- The **loop-correction rate function**: the Cramér/Legendre
    transform of the log-MGF of the Bernoulli loop-presence
    observable, evaluated at the zero-deviation point `x = 0` (the
    *no-loop-correction event*):

      `I(0) = sup_θ (θ·0 − log mgf(θ)) = ⨆ θ, −log (bernoulliLoopMgf G θ)`.

    The closed form `−log (1 − loopDensity G)` is a THEOREM
    (`loopCorrectionRate_eq_neg_log`), proven by an explicit `IsLUB`
    argument — the supremum is approached as `θ → −∞` and is not
    attained when the graph has loops. The zero-rate ⟺ tree
    equivalence (`loopCorrectionRate_eq_zero_iff_tree`) is likewise
    NOT definitional: it routes through the Legendre evaluation, the
    log/density analysis, and the 4-cycle Finset ↔ tree-predicate
    bridge. Physically, `I(0)` is the exact exponential decay rate of
    loop-correction-free behavior
    (`no_loop_event_prob_eq_exp_neg_rate`): trees pay nothing (BP is
    exact, Bethe exactness); loopy graphs pay a strictly positive
    rate that grows with loop density. -/
noncomputable def loopCorrectionRate
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : ℝ :=
  ⨆ θ : ℝ, -Real.log (bernoulliLoopMgf G θ)

/-- **Legendre evaluation (the analysis core).** The loop-correction
    rate function evaluates in closed form:

      `loopCorrectionRate G = −log (1 − loopDensity G)`.

    Proof: `−log` is antitone through the MGF lower bound
    `1 − p ≤ mgf(θ)` (upper-bound half), and the supremum is
    approached as `θ → −∞` — for any upper bound `b` strictly below
    `−log(1 − p)`, the explicit witness
    `θ₀ = log (ε / (2(p+1)))` with `ε = exp(−b) − (1 − p)` produces a
    family member exceeding `b` (least-upper-bound half). The witness
    handles `p = 0` and `p > 0` uniformly. -/
theorem loopCorrectionRate_eq_neg_log
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    loopCorrectionRate G = -Real.log (1 - loopDensity G) := by
  have hp0 := loopDensity_nonneg G
  have hp1 := loopDensity_lt_one G
  have h1p : (0 : ℝ) < 1 - loopDensity G := by linarith
  have hub : ∀ θ : ℝ,
      -Real.log (bernoulliLoopMgf G θ) ≤ -Real.log (1 - loopDensity G) := by
    intro θ
    have hmono : 1 - loopDensity G ≤ bernoulliLoopMgf G θ := by
      unfold bernoulliLoopMgf
      have : 0 ≤ loopDensity G * Real.exp θ :=
        mul_nonneg hp0 (Real.exp_pos θ).le
      linarith
    exact neg_le_neg ((Real.log_le_log_iff h1p (bernoulliLoopMgf_pos G θ)).mpr hmono)
  have hlub : IsLUB (Set.range fun θ : ℝ => -Real.log (bernoulliLoopMgf G θ))
      (-Real.log (1 - loopDensity G)) := by
    constructor
    · rintro x ⟨θ, rfl⟩
      exact hub θ
    · intro b hb
      by_contra hcon
      rw [not_le] at hcon
      have hexp : 1 - loopDensity G < Real.exp (-b) := by
        have hlog : Real.log (1 - loopDensity G) < -b := by linarith
        calc 1 - loopDensity G
            = Real.exp (Real.log (1 - loopDensity G)) := (Real.exp_log h1p).symm
          _ < Real.exp (-b) := Real.exp_lt_exp.mpr hlog
      set p := loopDensity G with hp_def
      set ε := Real.exp (-b) - (1 - p) with hε_def
      have hεpos : 0 < ε := by simp only [hε_def]; linarith
      set θ₀ := Real.log (ε / (2 * (p + 1))) with hθ₀_def
      have hfrac_pos : 0 < ε / (2 * (p + 1)) := by positivity
      have hexpθ₀ : Real.exp θ₀ = ε / (2 * (p + 1)) := Real.exp_log hfrac_pos
      have hsmall : p * Real.exp θ₀ < ε := by
        rw [hexpθ₀, ← mul_div_assoc]
        have h2p1 : (0 : ℝ) < 2 * (p + 1) := by linarith
        rw [div_lt_iff₀ h2p1]
        nlinarith [mul_pos hεpos (show (0 : ℝ) < p + 2 by linarith)]
      have hmgf_lt : bernoulliLoopMgf G θ₀ < Real.exp (-b) := by
        unfold bernoulliLoopMgf
        rw [← hp_def]
        simp only [hε_def] at hsmall
        linarith
      have hgt : b < -Real.log (bernoulliLoopMgf G θ₀) := by
        have := Real.log_lt_log (bernoulliLoopMgf_pos G θ₀) hmgf_lt
        rw [Real.log_exp] at this
        linarith
      exact absurd (hb ⟨θ₀, rfl⟩) (not_le.mpr hgt)
  exact hlub.ciSup_eq

/-! ## The tree/loopy contract (zero-rate ⟺ tree, positivity, monotonicity) -/

/-- The loop-correction rate function is non-negative (rate functions
    are non-negative; here via `0 ≤ p < 1 ⇒ log (1 − p) ≤ 0`). -/
theorem loopCorrectionRate_nonneg
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) : 0 ≤ loopCorrectionRate G := by
  rw [loopCorrectionRate_eq_neg_log]
  have h0 := loopDensity_nonneg G
  have h1 := loopDensity_lt_one G
  have : Real.log (1 - loopDensity G) ≤ 0 :=
    Real.log_nonpos (by linarith) (by linarith)
  linarith

/-- **Substantive Theorem (zero-rate ⟺ tree).** The loop-correction
    rate function vanishes exactly on tree factor graphs. NOT
    definitional: the proof routes through (i) the Legendre evaluation
    `loopCorrectionRate_eq_neg_log`, (ii) the log analysis
    `−log(1 − p) = 0 ⇒ p = 0` (using `0 < 1 − p` from strict
    sub-unitality), and (iii) the density ⟺ tree bridge
    `loopDensity_eq_zero_iff_tree`. -/
theorem loopCorrectionRate_eq_zero_iff_tree
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    loopCorrectionRate G = 0 ↔ IsTreeFactorGraph G := by
  rw [loopCorrectionRate_eq_neg_log, ← loopDensity_eq_zero_iff_tree]
  have h0 := loopDensity_nonneg G
  have h1 := loopDensity_lt_one G
  constructor
  · intro h
    have hlog : Real.log (1 - loopDensity G) = 0 := by linarith
    have h1eq : 1 - loopDensity G = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero (by linarith) hlog
    linarith
  · intro h
    rw [h]
    simp

/-- **Substantive Theorem (loopy ⇒ strictly positive rate).** On
    non-tree (loopy) factor graphs the loop-correction rate function
    is strictly positive: a loopy graph has a 4-cycle, hence strictly
    positive loop density, hence `1 − p < 1` and
    `−log(1 − p) > 0`. -/
theorem loopCorrectionRate_pos_of_not_tree
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (h : ¬ IsTreeFactorGraph G) :
    0 < loopCorrectionRate G := by
  rw [loopCorrectionRate_eq_neg_log]
  have hp0 : 0 < loopDensity G := by
    rcases lt_or_eq_of_le (loopDensity_nonneg G) with h' | h'
    · exact h'
    · exact absurd ((loopDensity_eq_zero_iff_tree G).mp h'.symm) h
  have hp1 := loopDensity_lt_one G
  have : Real.log (1 - loopDensity G) < 0 :=
    Real.log_neg (by linarith) (by linarith)
  linarith

/-- **Strict monotonicity in loop density (the non-indicator
    certificate).** Between any two finite factor graphs — possibly
    over different index types — strictly larger loop density gives a
    strictly larger loop-correction rate. The rate therefore
    *separates* loopy graphs by their loop content, taking a distinct
    value for every distinct loop density; no `{0,1}`-valued indicator
    can do this. -/
theorem loopCorrectionRate_lt_of_loopDensity_lt
    {ν₁ α₁ ν₂ α₂ : Type*}
    [Fintype ν₁] [Fintype α₁] [DecidableEq ν₁] [DecidableEq α₁]
    [Fintype ν₂] [Fintype α₂] [DecidableEq ν₂] [DecidableEq α₂]
    (G₁ : FactorGraph ν₁ α₁) (G₂ : FactorGraph ν₂ α₂)
    (h : loopDensity G₁ < loopDensity G₂) :
    loopCorrectionRate G₁ < loopCorrectionRate G₂ := by
  rw [loopCorrectionRate_eq_neg_log, loopCorrectionRate_eq_neg_log]
  have h2 := loopDensity_lt_one G₂
  have h1 := loopDensity_nonneg G₁
  have : Real.log (1 - loopDensity G₂) < Real.log (1 - loopDensity G₁) :=
    Real.log_lt_log (by linarith) (by linarith)
  linarith

/-- **Threshold ⟺ density characterization.** For any threshold
    `t`, the rate is at most `t` iff the loop density is at most
    `1 − exp(−t)`. This is the honest continuous replacement of the
    former fixed-threshold tree characterization: a sub-threshold
    rate now corresponds to an explicit loop-density bound, with the
    tree case recovered at `t = 0`
    (`loopCorrectionRate_eq_zero_iff_tree`). -/
theorem loopCorrectionRate_le_iff_loopDensity_le
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (t : ℝ) :
    loopCorrectionRate G ≤ t ↔ loopDensity G ≤ 1 - Real.exp (-t) := by
  rw [loopCorrectionRate_eq_neg_log]
  have h1p : (0 : ℝ) < 1 - loopDensity G := by
    linarith [loopDensity_lt_one G]
  constructor
  · intro h
    have hle : -t ≤ Real.log (1 - loopDensity G) := by linarith
    have := (Real.le_log_iff_exp_le h1p).mp hle
    linarith
  · intro h
    have hexp : Real.exp (-t) ≤ 1 - loopDensity G := by linarith
    have := (Real.le_log_iff_exp_le h1p).mpr hexp
    linarith

/-! ## LDP-suite bridge: Bernoulli Cramér rate function -/

/-- The **Bernoulli Cramér rate function** (Kullback-Leibler /
    relative-entropy form) in `Real.negMulLog` form:

      `I_p(q) = q·log(q/p) + (1−q)·log((1−q)/(1−p))`
              `= −negMulLog q − negMulLog (1−q) − q·log p − (1−q)·log (1−p)`

    for `p, q` in the open unit interval; the `negMulLog` form extends
    continuously to all of `ℝ` (`bernoulliCramerRate_continuous`),
    avoiding the junk-value discontinuities of the quotient form. This
    is the rate function of Cramér's theorem for an iid
    Bernoulli(`p`) sequence — here, the loop-presence observable. -/
noncomputable def bernoulliCramerRate (p q : ℝ) : ℝ :=
  -(Real.negMulLog q) - Real.negMulLog (1 - q)
    - q * Real.log p - (1 - q) * Real.log (1 - p)

/-- **Centering**: the Bernoulli Cramér rate function vanishes at the
    mean `q = p` (the no-deviation event), by exact cancellation of
    the entropy and cross-entropy terms. -/
theorem bernoulliCramerRate_self (p : ℝ) : bernoulliCramerRate p p = 0 := by
  unfold bernoulliCramerRate
  rw [Real.negMulLog_def]
  ring

/-- **Boundary evaluation**: at the zero-deviation point `q = 0` the
    Bernoulli Cramér rate function equals `−log (1 − p)` — the value
    the loop-correction rate function takes
    (`loopCorrectionRate_eq_bernoulliCramerRate_zero`). -/
theorem bernoulliCramerRate_zero_left (p : ℝ) :
    bernoulliCramerRate p 0 = -Real.log (1 - p) := by
  unfold bernoulliCramerRate
  simp

/-- The Bernoulli Cramér rate function is continuous in the deviation
    argument — globally on `ℝ`, via the `negMulLog` form (this is the
    `Continuous I` field demanded by the project LDP-suite predicate;
    the quotient KL form would NOT extend continuously through the
    Lean junk values). -/
theorem bernoulliCramerRate_continuous (p : ℝ) :
    Continuous (bernoulliCramerRate p) := by
  unfold bernoulliCramerRate
  fun_prop

/-- **LDP-suite value bridge.** The loop-correction rate function *is*
    the Bernoulli Cramér (KL) rate function of the loop-presence
    observable, evaluated at the zero-deviation point `q = 0`. Rides
    on the two substantive evaluations (Legendre `IsLUB` argument +
    `negMulLog` boundary evaluation). -/
theorem loopCorrectionRate_eq_bernoulliCramerRate_zero
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    loopCorrectionRate G = bernoulliCramerRate (loopDensity G) 0 := by
  rw [loopCorrectionRate_eq_neg_log, bernoulliCramerRate_zero_left]

/-- **LDP-suite predicate bridge.** The Bernoulli loop MGF together
    with the mean-centered Bernoulli Cramér rate function satisfies
    the project LDP-suite Cramér predicate
    `SKEFTHawking.LDP.IsCramerIIDUpperBound`: the centered rate
    function is continuous and vanishes at the no-deviation event,
    and the MGF is continuous with exact normalization
    `mgf 0 = 1`. This discharges, for the loop-presence observable,
    the structural shape the LDP suite demands of an honest Cramér
    rate-function setup. -/
theorem loopCorrection_isCramerIIDUpperBound
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) :
    SKEFTHawking.LDP.IsCramerIIDUpperBound (bernoulliLoopMgf G)
      (fun x => bernoulliCramerRate (loopDensity G) (x + loopDensity G)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (bernoulliCramerRate_continuous (loopDensity G)).comp
      (continuous_id.add continuous_const)
  · simp [bernoulliCramerRate_self]
  · unfold bernoulliLoopMgf
    fun_prop
  · exact (bernoulliLoopMgf_zero G).le

/-- **Exact Cramér identity for the no-loop-correction event.** For
    every `n`, the probability that `n` independent loop-correction
    opportunities (iid Bernoulli(`loopDensity G`) draws) all stay
    silent satisfies

      `(1 − p)^n = exp (−n · loopCorrectionRate G)`

    — exactly, at every finite `n`, not merely asymptotically. The
    loop-correction rate is the exact exponential decay rate of
    loop-correction-free behavior: this is Cramér's theorem
    `P(S_n/n = 0) = exp(−n·I(0))` for the Bernoulli loop-presence
    observable at the boundary point of its support. -/
theorem no_loop_event_prob_eq_exp_neg_rate
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (n : ℕ) :
    (1 - loopDensity G) ^ n = Real.exp (-(n : ℝ) * loopCorrectionRate G) := by
  have h1p : (0 : ℝ) < 1 - loopDensity G := by
    linarith [loopDensity_lt_one G]
  rw [loopCorrectionRate_eq_neg_log, neg_mul_neg, ← Real.log_pow]
  exact (Real.exp_log (pow_pos h1p n)).symm

/-! ## Worked value: the complete bipartite 2×2 factor graph -/

/-- The complete bipartite factor graph on two variables and two
    factors has exactly four ordered 4-cycles (kernel-checked by
    `decide` over the 16-tuple space). -/
theorem fourCycles_card_completeBipartite22 :
    (fourCycles (⟨fun _ _ => true⟩ : FactorGraph (Fin 2) (Fin 2))).card = 4 := by
  decide

/-- **Worked intermediate value.** The complete bipartite 2×2 factor
    graph has loop density `4/16 = 1/4` and loop-correction rate
    `−log(3/4) = log(4/3) ≈ 0.288` — a genuine intermediate value
    strictly between `0` and `1`, witnessing that the rate function is
    not a `{0,1}`-valued indicator. Falsifiable concrete anchor. -/
theorem loopCorrectionRate_completeBipartite22 :
    loopCorrectionRate (⟨fun _ _ => true⟩ : FactorGraph (Fin 2) (Fin 2))
      = Real.log (4 / 3) := by
  rw [loopCorrectionRate_eq_neg_log]
  have hdensity : loopDensity (⟨fun _ _ => true⟩ : FactorGraph (Fin 2) (Fin 2))
      = 1 / 4 := by
    unfold loopDensity
    rw [fourCycles_card_completeBipartite22]
    norm_num
  rw [hdensity, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num, ← Real.log_inv]
  norm_num

/-! ## BP convergence-favorable structural property -/

/-- A factor graph + factor weight admits **BP convergence-favorable
    dynamics** iff (a) the factor graph is a tree (no 4-cycle
    loops) and (b) all factor weights are non-negative. Substantive
    structural simulability property; the headline biconditional ties
    this to the vanishing of the loop-correction rate function. -/
def IsBPConvergenceFavorable {ν α X : Type*}
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ) : Prop :=
  IsTreeFactorGraph G ∧ ∀ a y, 0 ≤ factorWeight a y

/-! ## HEADLINE: bp_convergence_iff_ldp_rate_zero -/

/-- **HEADLINE.** Belief-propagation classical-simulability biconditional:

      `IsBPConvergenceFavorable G factorWeight  ↔
         loopCorrectionRate G = 0  ∧  (∀ a y, 0 ≤ factorWeight a y)`.

    Forward direction: structural simulability (tree + non-negative
    factor weights) forces an empty 4-cycle Finset, hence zero loop
    density, hence — through the Legendre evaluation — zero rate.

    Reverse direction: zero rate forces (through
    `−log(1 − p) = 0 ⇒ p = 0` and the density ⟺ tree bridge) a tree
    factor graph; combined with the non-negativity hypothesis on
    factor weights this gives the structural simulability property.

    The biconditional ties the structural property
    `IsBPConvergenceFavorable` (Wave 6w.2 BP substrate consumer) to
    the vanishing of a genuine Cramér/Legendre rate function
    (review-2026-06-05 D7-EV3 upgrade of the former `{0,1}` indicator).
    Substantively load-bearing for the Wave 6w.6 demarcation theorem
    combining BP-LDP simulability with the Wave 6w.5 Chern bridge. -/
theorem bp_convergence_iff_ldp_rate_zero {ν α X : Type*}
    [Fintype ν] [Fintype α] [DecidableEq ν] [DecidableEq α]
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ) :
    IsBPConvergenceFavorable G factorWeight ↔
      (loopCorrectionRate G = 0 ∧ ∀ a y, 0 ≤ factorWeight a y) := by
  unfold IsBPConvergenceFavorable
  rw [loopCorrectionRate_eq_zero_iff_tree]

/-- **Companion lemma.** On tree factor graphs the BP convergence-
    favorable property is equivalent to factor-weight non-negativity.
    Substantive simplification of the headline at the tree-graph
    boundary. -/
theorem isBPConvergenceFavorable_on_tree_iff_factor_weights_nonneg
    {ν α X : Type*}
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ)
    (h_tree : IsTreeFactorGraph G) :
    IsBPConvergenceFavorable G factorWeight ↔
      ∀ a y, 0 ≤ factorWeight a y := by
  unfold IsBPConvergenceFavorable
  exact ⟨fun h => h.2, fun h => ⟨h_tree, h⟩⟩

/-- **Companion lemma.** On non-tree (loopy) factor graphs the BP
    convergence-favorable property fails identically, regardless of
    the factor weights. Substantive negative result tying the
    structural classification to the strictly-positive-rate regime
    (`loopCorrectionRate_pos_of_not_tree`). -/
theorem not_isBPConvergenceFavorable_on_non_tree
    {ν α X : Type*}
    (G : FactorGraph ν α) (factorWeight : α → (ν → X) → ℝ)
    (h : ¬ IsTreeFactorGraph G) :
    ¬ IsBPConvergenceFavorable G factorWeight := by
  unfold IsBPConvergenceFavorable
  intro ⟨h_tree, _⟩
  exact h h_tree

end SKEFTHawking.BPLDPSimulability
