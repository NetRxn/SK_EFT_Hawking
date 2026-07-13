import Mathlib
import SKEFTHawking.RP2EquatorialInclusion
import SKEFTHawking.RP4WuAssembly
import SKEFTHawking.RP2IntersectionForm
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.RP4CupLadder
import SKEFTHawking.RP2CupLadder

/-!
# W-A (n = 2 witness) — the characteristic-surface pushforward identity (`hchar`), ARCHITECTURE

The second named `hchar` obligation of the `ℝP⁴` faithful-carrier witness: the equatorial
`emb : ℝP² ↪ ℝP⁴` sends the mod-2 fundamental class `[ℝP²]` to the Poincaré dual of `w₁²(ℝP⁴)`.
In the ∀-pairing form the v4 design mandates (`W_A_FAITHFUL_INSTANCE_DESIGN.md`), this reads:

> for all `a ∈ H²(ℝP⁴;ℤ/2)`, `⟨a, emb₊[ℝP²]⟩ = μ(a ⌣ x²)`   (`x = ` RP4 degree-1 generator).

**This module banks the entire naturality reduction of that identity to a single degree-1 crux.**
By the Kronecker adjunction (`kroneckerH_cohomologyPullback`, `⟨a, emb₊β⟩ = ⟨emb* a, β⟩`), the cup
compatibility of the pullback (`cohomologyPullback_cupH`), the one-dimensionality of `H²(ℝP⁴)`
(`cohomology_eq_smul_xpow`), and the two merged pairing facts
(`RP2IntersectionForm.mu_xpow2_eq_one` on `ℝP²`, `RP4WuAssembly.mu_cupH24_xpow2_xpow2` on `ℝP⁴`),
the whole identity collapses to the **degree-1 pullback compatibility**

  `emb* x = xRP2`   (`cohomologyPullback ⟨embRP2,_⟩ 1 (xpow 1) = xRP2`),

the statement that the cohomology pullback of the RP4 generator is the RP2 generator. That crux is
the residual geometry (covering/transfer naturality of the degree-1 Smith class); it is carried here
as an explicit hypothesis so the rest of the identity is banked GREEN and kernel-pure.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.RP2PointSet SKEFTHawking.RP4PointSet
open SKEFTHawking.SingularSurfaceIntersectionForm
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu

namespace SKEFTHawking.RP4CharSurfacePushforward

open SKEFTHawking.RP2EquatorialInclusion

/-- **The equatorial inclusion as a bundled `ContinuousMap`** `ℝP² → ℝP⁴` — the argument of the
homology pushforward / cohomology pullback functors. -/
noncomputable def embRP2C : C(↑(TopCat.of RP2), ↑(TopCat.of RP4)) :=
  ⟨embRP2, continuous_embRP2⟩

/-- **The degree-1 crux** (the residual geometry): the cohomology pullback of the RP4 degree-1
generator `x = xpow 1` along `emb` is the RP2 generator `xRP2 = xpow 1`, i.e. `emb* x = xRP2`.
This is the covering/transfer naturality of the Smith class; the single degree-1 open input. -/
abbrev CruxPullbackGen : Prop :=
  cohomologyPullback embRP2C 1 (RP4CohomologyLadder.xpow 1) = RP2IntersectionForm.xRP2

/-- **Degree-2 consequence of the crux**: `emb* (x²) = xRP2²`, i.e.
`cohomologyPullback emb 2 (xpow 2) = xpow 2` on `ℝP²`. Cup-multiplicativity of the pullback plus the
degree-1 crux, using `xpow 2 = x ⌣ x` on both projective spaces. -/
theorem cohomologyPullback_xpow2 (hcrux : CruxPullbackGen) :
    cohomologyPullback embRP2C 2 (RP4CohomologyLadder.xpow 2)
      = RP2CohomologyLadder.xpow 2 := by
  rw [RP4CupLadder.xpow_two_eq_cupH, cohomologyPullback_cupH, hcrux,
    ← RP2IntersectionForm.cupSquare_xRP2, cupSquare, RP2IntersectionForm.xRP2]

/-! ## §2. Reduction of the degree-1 crux to Smith-connecting naturality

`x = xpow 1 = δS(1)` on `ℝP⁴` and `xRP2 = xpow 1 = δS(1)` on `ℝP²` are both the Smith connecting
map applied to the unit class. The pullback of the unit class is the unit class (`emb* 1 = 1`,
`emb_pullback_unitClass`, immediate — pullback of the constant-`1` cocycle), so the crux
`emb* x = xRP2` is exactly the **naturality of the degree-0 Smith connecting map** under the
covering-compatible pullback (`crux_of_smithConnecting_natural`). That naturality is the residual
geometry: `emb` lifts to the equivariant `embS2` on the double covers, so it induces a map of the
Smith transfer short exact sequences and the connecting maps commute — the honest remaining core. -/

/-- **`emb* 1 = 1`**: the cohomology pullback of the RP4 unit class is the RP2 unit class — the
pullback of the constant-`1` `0`-cocycle is the constant-`1` `0`-cocycle. -/
theorem emb_pullback_unitClass :
    cohomologyPullback embRP2C 0 (RP4CohomologyLadder.unitClass (TopCat.of RP4))
      = RP2CohomologyLadder.unitClass (TopCat.of RP2) := by
  rw [RP4CohomologyLadder.unitClass, cohomologyPullback_mk]
  refine congrArg (Cohomology.mk (TopCat.of RP2) 0) (Subtype.ext ?_)
  rfl

/-- **The degree-1 crux from Smith-connecting naturality.** Given that the degree-0 Smith connecting
map is natural under the `emb`-pullbacks — `emb* (δS_{ℝP⁴} w) = δS_{ℝP²} (emb* w)` — the crux
`emb* x = xRP2` follows: both generators are `δS(1)`, and `emb* 1 = 1`. This isolates the entire
residual geometry to `hnat` (connecting-map naturality of the covering transfer SES). -/
theorem crux_of_smithConnecting_natural
    (hnat : ∀ w : Cohomology (TopCat.of RP4) 0,
      cohomologyPullback embRP2C 1 (RP4SmithCochain.smithCoConnecting 0 w)
        = RP2SmithCochain.smithCoConnecting 0 (cohomologyPullback embRP2C 0 w)) :
    CruxPullbackGen := by
  show cohomologyPullback embRP2C 1 (RP4CohomologyLadder.xpow 1) = RP2IntersectionForm.xRP2
  rw [show RP4CohomologyLadder.xpow 1
      = RP4SmithCochain.smithCoConnecting 0 (RP4CohomologyLadder.unitClass (TopCat.of RP4))
      from rfl, hnat, emb_pullback_unitClass]
  rfl

/-- **The `hchar` pairing identity, in the ∀-pairing form (GIVEN the degree-1 crux).** For every
`a ∈ H²(ℝP⁴;ℤ/2)`, the pairing of `a` against the pushed-forward fundamental class `emb₊[ℝP²]`
equals `μ(a ⌣ x²)` — the characteristic-surface condition dual to `w₁² = x²`. The whole identity is
the naturality collapse to `emb* x² = xRP2²` (`cohomologyPullback_xpow2`) plus `μ(x²)_{ℝP²} = 1`
(`mu_xpow2_eq_one`) and `μ(x²⌣x²)_{ℝP⁴} = 1` (`mu_cupH24_xpow2_xpow2`). -/
theorem hchar_pairing (hcrux : CruxPullbackGen) (a : Cohomology (TopCat.of RP4) 2) :
    kroneckerH 2 a (Homology.map embRP2C 2 (surfaceFundamentalClass (M := RP2)))
      = (poincareDual4Mid_of_closed (M := RP4)).mu
          (cupH24 a (RP4CohomologyLadder.xpow 2)) := by
  obtain ⟨c, rfl⟩ := RP4CohomologyLadder.cohomology_eq_smul_xpow (by norm_num) a
  -- LHS: pull the scalar out, apply Kronecker naturality, then the degree-2 crux consequence.
  rw [map_smul, LinearMap.smul_apply,
    ← kroneckerH_cohomologyPullback embRP2C (RP4CohomologyLadder.xpow 2)
      (surfaceFundamentalClass (M := RP2)),
    cohomologyPullback_xpow2 hcrux]
  -- kroneckerH 2 (xpow 2 : ℝP²) [ℝP²] = surfaceFundamentalFunctional (xpow 2) = 1
  rw [show kroneckerH (X := TopCat.of RP2) 2 (RP2CohomologyLadder.xpow 2)
        (surfaceFundamentalClass (M := RP2))
      = surfaceFundamentalFunctional (M := RP2) (RP2CohomologyLadder.xpow 2) from rfl,
    RP2IntersectionForm.mu_xpow2_eq_one]
  -- RHS: pull the scalar out and use μ(x²⌣x²) = 1.
  rw [map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul,
    RP4WuAssembly.mu_cupH24_xpow2_xpow2, mul_one, smul_eq_mul, mul_one]

end SKEFTHawking.RP4CharSurfacePushforward
