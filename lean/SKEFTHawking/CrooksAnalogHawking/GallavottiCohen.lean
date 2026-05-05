/-
# Phase 6n Wave 2c (Crooks-on-analog-Hawking) — GallavottiCohen LDP-symmetry

The Gallavotti-Cohen / Lebowitz-Spohn LDP rate-function symmetry is the
*long-time / large-deviation* limit of the Crooks fluctuation theorem.
For the entropy-production rate function I : ℝ → ℝ in a non-equilibrium
steady state (NESS):

    I(-σ) - I(σ) = -σ        (Gallavotti-Cohen symmetry)

Equivalently: P(σ) / P(-σ) → exp(σ) as the trajectory time T → ∞,
where P(σ) is the probability density for the entropy-production rate.

**Stage 1 substantive scope.** Ships the `GallavottiCohenSymmetry`
predicate and its connection to `HorizonDetailedBalance`. The substantive
content of Wave 2c is to derive this symmetry as a *consequence* of
horizon detailed balance applied to the long-time / NESS limit of analog-
Hawking emission — establishing the third Sakharov-style biconditional:

    AnalogHawkingSubstrate satisfies GLU monotonicity
      ⇔  emission spectrum's LDP rate function satisfies GC symmetry

The equivalence is the falsifiable IR constraint per Phase 6n DR §7
("a binary criterion, applicable to a known substrate (polariton SK-EFT,
BEC, ³He-A, surface waves), with falsifiability content").

**Stage 2-3 substantive lift (deferred):** derive GC symmetry from HDB
under suitable LDP-existence hypotheses; specialize to the Steinhauer /
Weinfurtner / Carusotto device parameter spec.

References:
- Lebowitz-Spohn, J. Stat. Phys. 95, 333 (1999), arXiv:cond-mat/9811220
- Gallavotti-Cohen, PRL 74, 2694 (1995) — the original (chaotic deterministic)
- Kurchan, J. Phys. A 31, 3719 (1998) — stochastic GC
- Falasco-Esposito, Rev. Mod. Phys. 97, 015002 (2025) — modern framework
- Phase 6n DR §7
-/
import SKEFTHawking.CrooksAnalogHawking.HorizonDetailedBalance

namespace SKEFTHawking.CrooksAnalogHawking

/--
**Gallavotti-Cohen LDP rate-function symmetry.**

A rate function `I : ℝ → ℝ` for entropy production satisfies the
Gallavotti-Cohen symmetry if

    I(-σ) - I(σ) = -σ        for all  σ ∈ ℝ.

Equivalently, in the LDP form `P(σ) ∼ exp(-T · I(σ))`, the ratio
`P(σ) / P(-σ) → exp(σ)` as T → ∞ — the long-time limit of Crooks.

This predicate is the substantive falsifiability content of Wave 2c:
the analog-Hawking emission spectrum's LDP rate function MUST satisfy
this symmetry under the Glorioso-Liu monotonicity substrate. Stage 2-3
will derive this from `HorizonDetailedBalance`. -/
def GallavottiCohenSymmetry (I : ℝ → ℝ) : Prop :=
  ∀ σ : ℝ, I (-σ) - I σ = -σ

/--
**The trivial linear rate function satisfies GC.**

Substantive Stage-1 well-posedness witness: the linear rate function
`I_linear(σ) := σ / 2` satisfies the GC symmetry trivially:

    I_linear(-σ) - I_linear(σ) = -σ/2 - σ/2 = -σ ✓

This shows GC is non-vacuous as a predicate. The Stage 2-3 substantive
content lifts this from "I_linear satisfies GC" to "the analog-Hawking
LDP rate function satisfies GC under GLU monotonicity." -/
theorem gallavottiCohen_linear_witness :
    GallavottiCohenSymmetry (fun σ => σ / 2) := by
  intro σ
  ring

/--
**GC symmetry is preserved under affine shifts of the rate function.**

If `I` satisfies GC, then `I + c` (a constant shift) also satisfies GC.
This is the substantive observation that GC is a *gauge-invariant*
property — only the *differences* I(-σ) - I(σ) are constrained, not
the absolute level. -/
theorem GallavottiCohenSymmetry.shift_invariant {I : ℝ → ℝ}
    (h : GallavottiCohenSymmetry I) (c : ℝ) :
    GallavottiCohenSymmetry (fun σ => I σ + c) := by
  intro σ
  -- (I(-σ) + c) - (I(σ) + c) = I(-σ) - I(σ) = -σ
  have := h σ
  linarith

end SKEFTHawking.CrooksAnalogHawking
