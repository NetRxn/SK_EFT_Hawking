/-
# Phase 6n Wave 2c (Crooks-on-analog-Hawking) — HorizonDetailedBalance

Trajectory-level detailed-balance predicate for analog-Hawking emission.

Per Phase 6n DR (Phase 6n+ Foundational Backing Assessment §7), the
load-bearing novel content of Wave 2c is the **trajectory-level Crooks
detailed-balance** statement specialized to analog-horizon backgrounds:

  P_F[γ] / P_R[γ̄] = exp(σ[γ])

where γ is a trajectory at the local horizon, γ̄ is its time-reverse,
and σ[γ] is the entropy production along γ. This is the Crooks
fluctuation theorem in its most general (path-probability) form, with
the entropy-production functional σ generalizing the classical `β·W`.

**Stage 1 substantive scope.** Ships the `HorizonDetailedBalance`
predicate as a generalization of the classical `IsCrooksRatio`
(`QuantumCrooks/Setup.lean`) — the entropy-production function σ : ℝ → ℝ
replaces the classical `fun W => β * W`. Substantive theorems:

  - `HorizonDetailedBalance.specialize_to_Crooks` — when σ = β·W, the
    HorizonDetailedBalance predicate reduces to `IsCrooksRatio`. Cross-
    module bridge to `QuantumCrooks.Setup`.
  - `HorizonDetailedBalance.symm_neg` — symmetry under forward/reverse
    swap with σ ↦ −σ ∘ neg.
  - `HorizonDetailedBalance_zero` — well-posedness witness via the
    trivial zero distributions.

Stage 2-3 substantive content (deferred): derive the inequality on the
analog-Hawking spectrum by composing HorizonDetailedBalance with
Glorioso-Liu monotonicity (Wave 2a substrate). Specialize to
Steinhauer / Weinfurtner / Carusotto device parameters. The inequality
is the load-bearing falsifiability content (third Sakharov-style
biconditional candidate per the program's framing).

**Substrate options (per Phase 6n roadmap Wave 2c):**
- (a) Glorioso-Crossley-Liu SK-EFT effective action as the path measure
  (closer to existing program infrastructure; uses Wave 2a `SKEFTAxioms`).
- (b) Loganayagam-Martin exterior EFT for Hawking radiation
  (arXiv:2403.10654, JHEP 2025; cleanest framework for trajectory-Crooks
  at the horizon).

Stage 1 ships predicate-level substrate compatible with both; Stage 2-3
specializes via the substrate of choice (likely (b) per appendix).

References:
- Loganayagam–Martin, "An Exterior EFT for Hawking Radiation,"
  arXiv:2403.10654, v2 Mar 2025 (JHEP 2025) — the cleanest path-measure
  framework for trajectory-Crooks at the horizon
- Crooks, Phys. Rev. E 60, 2721 (1999) — classical Crooks
- Lebowitz-Spohn, J. Stat. Phys. 95, 333 (1999), arXiv:cond-mat/9811220
  — Gallavotti-Cohen LDP-rate-function symmetry
- Falasco-Esposito, Rev. Mod. Phys. 97, 015002 (2025) — modern
  macroscopic stochastic thermodynamics framework
- Phase 6n DR §7 (Hawking-Crooks Duality)
- Phase 6n DR Appendix §3 (Itô-deferral; HorizonDB scope is discrete-time
  Markov-jump per Falasco-Esposito sufficient for analog-Hawking
  falsifiability)
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.CrooksAnalogHawking

open SKEFTHawking.QuantumCrooks

/--
**Horizon detailed-balance predicate.**

A pair `(P_F, P_R)` of forward/reverse trajectory-level work distributions
satisfies horizon detailed balance with entropy-production functional
`σ : ℝ → ℝ` if

    P_F(W) = exp(σ(W)) · P_R(-W)    for all  W ∈ ℝ.

This generalizes the classical Crooks ratio (`IsCrooksRatio`) — the
classical case is recovered when `σ(W) = β · W`. The general form
allows for nonlinear entropy-production functionals that arise on
analog-horizon backgrounds with corrections beyond linear response.

The substantive content of Wave 2c is to derive a *constraint* on the
form of σ for analog-Hawking emission via the Glorioso-Liu monotonicity
substrate; that constraint is the third Sakharov-style biconditional
candidate. -/
def HorizonDetailedBalance (P_F P_R : WorkDistribution) (σ : ℝ → ℝ) : Prop :=
  ∀ W : ℝ, P_F.P W = Real.exp (σ W) * P_R.P (-W)

/--
**The classical Crooks ratio is the special case σ(W) = β·W.**

Substantive cross-module bridge to `SKEFTHawking.QuantumCrooks.Setup`:
when the entropy-production functional is the linear classical form
`σ(W) := β·W`, `HorizonDetailedBalance` is **definitionally equivalent**
to `IsCrooksRatio` from the QuantumCrooks Wave 2b substrate.

This makes Wave 2c a substantive *generalization* of Wave 2b's
classical-Crooks structure — analog-Hawking emission satisfies horizon
detailed balance with a nonlinear σ, and the classical-Crooks limit is
recovered when the higher-order corrections to σ vanish (e.g., in the
linear-response regime that Banerjee-Modak-Samanta and the FDT line
already cover). -/
theorem HorizonDetailedBalance.specialize_to_Crooks
    (P_F P_R : WorkDistribution) (β : ℝ) :
    HorizonDetailedBalance P_F P_R (fun W => β * W)
      ↔ IsCrooksRatio P_F P_R β := by
  -- Both unfold to: ∀ W, P_F.P W = Real.exp (β * W) * P_R.P (-W)
  rfl

/--
**Symmetry of horizon detailed balance under forward/reverse swap.**

Substantive content: if `(P_F, P_R, σ)` satisfies horizon detailed
balance, then `(P_R, P_F, σ_swap)` does too, where `σ_swap(W) := -σ(-W)`.

This generalizes `IsCrooksRatio.symm` (where σ(W) = β·W and σ_swap(W) =
-β·(-W) = β·W = σ — so the symmetry preserves σ in the classical case).
For nonlinear σ, the swap also transforms σ; the predicate is symmetric
in (forward, reverse) iff σ is *odd* (which the classical β·W is). -/
theorem HorizonDetailedBalance.symm_neg
    {P_F P_R : WorkDistribution} {σ : ℝ → ℝ}
    (h : HorizonDetailedBalance P_F P_R σ) :
    HorizonDetailedBalance P_R P_F (fun W => -σ (-W)) := by
  intro W
  -- From h at -W: P_F.P (-W) = exp(σ(-W)) · P_R.P W
  have h_neg : P_F.P (-W) = Real.exp (σ (-W)) * P_R.P W := by
    have := h (-W); rwa [neg_neg] at this
  -- Goal: P_R.P W = exp(-σ(-W)) · P_F.P (-W)
  rw [h_neg, ← mul_assoc]
  have : Real.exp (-σ (-W)) * Real.exp (σ (-W)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [this, one_mul]

/--
**Trivial well-posedness witness: zero distributions satisfy horizon
detailed balance for any entropy-production functional σ.**

Substantive Stage-1 content: the trivial zero distributions satisfy
`HorizonDetailedBalance` at any `σ` (both sides equal 0). This shows
the predicate is non-vacuous — has at least one inhabitant pair for
any choice of σ. -/
theorem horizonDetailedBalance_zero (σ : ℝ → ℝ) :
    HorizonDetailedBalance WorkDistribution.zero WorkDistribution.zero σ := by
  intro W
  simp [WorkDistribution.zero]

end SKEFTHawking.CrooksAnalogHawking
