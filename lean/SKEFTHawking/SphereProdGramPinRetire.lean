/-
# Phase 5q.H — RETIRING the S²×S² Gram pin: the consumer slot, discharged

`PinPlusKTSpinSigmaStock.SphereProdGramPin` was introduced as "the single geometric residual …
the explicit input the s2s2 discharge consumes (not in-tree — no manifold cup product on the
product basis in Mathlib)". **That disclosure is now stale**: the S²×S² intersection-form content
IS in tree, unconditionally, via `SphereProdBasisIdInt.sphereProd_interMatrix_intCongr_hyp`
(the MV cup–Stokes peel `SphereProdHemiUnitInt.hcross_pm` + the basis-ID
`crossFamily_basis_intCongr`).

This module does three things.

## §1–§2. The consumer slot, discharged UNCONDITIONALLY

The Stock consumers state their conclusions at `sphereProdHDataComputed.intH2Basis`; the landed
content is stated at `sphereProdIntH2Basis`. These are the SAME datum (`⟨2, sphereProdBasis2Computed⟩`
both ways — `sphereProdHDataComputed_intH2Basis`, a `rfl`), so every hypothesis-free fact transports
verbatim. Shipped at the consumer's own basis expression, with NO `hgram`:

* `sphereProd_interMatrix_intCongr_hyp'` — the SHARP form: congruent to `Hyp` ITSELF;
* `sphereProd_s2s2_hyp'` — the `s2s2_hyp` field shape (`∃ N` hyperbolic, congruent);
* `sphereProd_s2s2_evenUnimodular'` / `sphereProd_s2s2_latticeSig'` / `sphereProd_s2s2_htopo'` —
  the `even_unimod`, σ and `htopo` legs.

Every downstream conclusion of the pin is a CONGRUENCE invariant, so the literal matrix equality the
pin asserts was never needed.

## §3. Why the literal equality is NOT provable — the obstruction, named and kernel-checked

`sphereProd_interMatrix_computed_eq` computes the intersection matrix on the computed (UCT-dual)
basis EXACTLY:

`interMatrix fc B = !![-(2·s·u·ε), u·ε; u·ε, 0]`

with `s = ⟨fst* xS, deltaGen⟩` (the α-coordinate on generator 2), `u = ⟨xS, snd_* deltaGen⟩`
(`deltaSnd_isUnit`) and `ε` the EZ cross value (`hcross_pm`). Hence
`sphereProdGramPin_iff : SphereProdGramPin ↔ (s = 0 ∧ u * ε = 1)` — TWO independent obstructions:

* **the normalization obstruction `s = 0`.** `deltaGen` is an `Exists.choose` section pinned only
  modulo `sumInto` (`SphereProdHTwoInt`), and `fst_* sumInto ≠ 0` (`sumInto_prodFst`), so `s` is not
  determined by any in-tree spec: replacing `deltaGen` by `deltaGen + k · sumInto 1` shifts `s` by `k`
  and the (0,0) entry by `-2ku ε`. The Gram matrix on the computed basis is therefore literally
  choice-dependent, and `SphereProdGramPin` is INDEPENDENT of the in-tree data — not merely unproved.
* **the orientation/sign obstruction `u · ε = 1`.** Both `u` and `ε` are pinned only as UNITS
  (`deltaSnd_isUnit`, `hcross_pm`); fixing their product to `+1` needs an orientation convention on
  `[S²×S²]` and on the split generator that the arc never fixes (and never needs).

So `SphereProdGramPin` is retired at the CONSUMER level, not proved: the substrate that the pin was
standing in for exists and is stronger than the pin's congruence-invariant consequences, while the
pin's extra literal content is a basis-normalization artifact with no geometric meaning.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdBasisIdInt

namespace SKEFTHawking.SphereProdGramPinRetire

open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdCrossInt (alphaOf betaOf)
open SKEFTHawking.SphereProdCrossWitnessInt (xS)
open SKEFTHawking.SphereWitnessTowerInt (SphereProdT sphereProdIntH2Basis sphereProdHDataComputed
  sphereProdBasis2Computed sphereProdCohomTwoEquivInt)
open SKEFTHawking.SpinSigmaRoute (sphereProdFormDatum sphereProdFormDatum_even_unimod
  sphereProdFormDatum_latticeSig sphereProdFormDatum_hyp_pin)
open SKEFTHawking.PinPlusKTSpinSigmaStock (SphereProdGramPin)
open SKEFTHawking.SphereProdBasisIdInt (deltaSnd deltaSnd_isUnit basis2_expand alphaOf_xS_fst
  betaOf_xS_fst betaOf_xS_snd)

/-! ## §1. The two bases are the SAME datum -/

/-- **The Stock consumer's basis IS the landed content's basis.** `SphereProdHData.intH2Basis d`
packages `⟨2, d.basis2⟩` and `sphereProdHDataComputed := ⟨sphereProdBasis2Computed⟩`, while
`sphereProdIntH2Basis := ⟨2, sphereProdBasis2Computed⟩` — the same `IntH2Basis SphereProdT`. So no
transport is needed between the consumer slot and the unconditional S²×S² arc. -/
theorem sphereProdHDataComputed_intH2Basis :
    sphereProdHDataComputed.intH2Basis = sphereProdIntH2Basis := rfl

/-! ## §2. The consumer slot, discharged UNCONDITIONALLY (no `hgram`) -/

/-- **THE SHARP UNCONDITIONAL PIN AT THE CONSUMER'S BASIS**: the S²×S² intersection matrix on the
Stock consumer's own basis expression (`sphereProdHDataComputed.intH2Basis`) is integrally congruent
to the hyperbolic plane ITSELF — no `SphereProdGramPin` hypothesis. This is the hypothesis-free
replacement for everything `sphereProd_s2s2_*_of_gram` produced: `Hyp` is named, not existentially
quantified. -/
theorem sphereProd_interMatrix_intCongr_hyp' :
    IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis) Hyp :=
  SphereProdBasisIdInt.sphereProd_interMatrix_intCongr_hyp

/-- **The `s2s2_hyp` field shape, UNCONDITIONALLY** — the `∃ N, IsHyperbolicForm N ∧ IntCongr … N`
obligation of `SpinSigmaAtoms` / `SpinSigmaPresentation` at the distinguished S²×S², now with NO
Gram-pin hypothesis (contrast `sphereProd_s2s2_hyp_of_gram`). The existential is an extraction of the
sharp `sphereProd_interMatrix_intCongr_hyp'` above. -/
theorem sphereProd_s2s2_hyp' :
    ∃ N, IsHyperbolicForm N ∧
      IntCongr (interMatrix sphereProdIntFundClassHonest sphereProdHDataComputed.intH2Basis) N := by
  obtain ⟨N, hN, hcong⟩ := sphereProdFormDatum_hyp_pin
  exact ⟨N, hN, sphereProd_interMatrix_intCongr_hyp'.trans hcong⟩

/-- **The S²×S² intersection matrix is even unimodular, UNCONDITIONALLY** — the `even_unimod`
obligation at the distinguished `s2s2`, with the `hgram` of `sphereProd_s2s2_evenUnimodular_of_gram`
DROPPED. Even-unimodularity is a congruence invariant (`IntCongr.isEvenUnimodular`), so the sharp
congruence to `Hyp` suffices; the literal matrix equality the pin asserted was never needed. -/
theorem sphereProd_s2s2_evenUnimodular' :
    IsEvenUnimodular (interMatrix sphereProdIntFundClassHonest
      sphereProdHDataComputed.intH2Basis) :=
  sphereProd_interMatrix_intCongr_hyp'.symm.isEvenUnimodular sphereProdFormDatum_even_unimod

/-- **σ(S²×S²) = 0, UNCONDITIONALLY** — the `hgram` of `sphereProd_interMatrix_latticeSig_of_gram`
DROPPED, via Sylvester congruence-invariance of `latticeSig`. -/
theorem sphereProd_s2s2_latticeSig' :
    latticeSig (interMatrix sphereProdIntFundClassHonest
      sphereProdHDataComputed.intH2Basis) = 0 := by
  rw [← IntCongr.latticeSig sphereProd_interMatrix_intCongr_hyp']
  exact sphereProdFormDatum_latticeSig

/-- **The σ÷16 leg's `htopo` binder at S²×S², UNCONDITIONALLY** (`2 ∣ σ/8`) — the `hgram` of
`sphereProd_interMatrix_htopo_of_gram` DROPPED. Together with `sphereProd_s2s2_evenUnimodular'`,
BOTH geometric Props the σ÷16 leg consumes at the second witness are now hypothesis-free. -/
theorem sphereProd_s2s2_htopo' :
    (2 : ℤ) ∣ latticeSig (interMatrix sphereProdIntFundClassHonest
      sphereProdHDataComputed.intH2Basis) / 8 := by
  rw [sphereProd_s2s2_latticeSig']
  norm_num

/-! ## §3. The exact computed-basis Gram matrix, and the pin's precise obstruction -/

/-- The α-coordinate on generator 2 — `⟨fst* xS, deltaGen⟩`. NOT pinned by any in-tree spec:
`deltaGen` is a chosen section modulo `sumInto` and `fst_* sumInto ≠ 0`. -/
noncomputable def alphaSnd : ℤ := (sphereProdCohomTwoEquivInt (alphaOf xS)).2

/-- The `deltaSnd` unit — `⟨xS, snd_* deltaGen⟩`, a unit by `deltaSnd_isUnit`, sign unfixed. -/
noncomputable def deltaU : ℤ := topSphereIsoInt 1 deltaSnd

/-- The Eilenberg–Zilber cross value `⟨fst* xS ∪ snd* xS, [S²×S²]⟩`, a unit by `hcross_pm`,
sign unfixed. -/
noncomputable def crossEps : ℤ :=
  interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS)

theorem deltaU_isUnit : IsUnit deltaU := deltaSnd_isUnit

theorem crossEps_isUnit : IsUnit crossEps := SphereProdHemiUnitInt.hcross_pm

theorem deltaU_mul_self : deltaU * deltaU = 1 := by
  rcases Int.isUnit_iff.mp deltaU_isUnit with h | h <;> rw [h] <;> norm_num

/-- Bilinear expansion in a two-element family — pure `Module` algebra, stated over a generic
`CommRing` to dodge the `zsmul`-vs-`Module`-smul diamond at `R := ℤ`. -/
theorem bilin_expand_two {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M →ₗ[R] R) (a b c d : R) (x y : M) :
    f (a • x + b • y) (c • x + d • y)
      = a * c * f x x + a * d * f x y + b * c * f y x + b * d * f y y := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- `α = fst* xS` in the computed basis: `α = b₀ + s · b₁`. -/
theorem alphaOf_xS_expand :
    alphaOf xS = (1 : ℤ) • sphereProdBasis2Computed 0 + alphaSnd • sphereProdBasis2Computed 1 := by
  conv_lhs => rw [basis2_expand (alphaOf xS)]
  rw [alphaOf_xS_fst, alphaSnd]

/-- `β = snd* xS` in the computed basis: `β = u · b₁` (its generator-1 coordinate vanishes). -/
theorem betaOf_xS_expand :
    betaOf xS = (0 : ℤ) • sphereProdBasis2Computed 0 + deltaU • sphereProdBasis2Computed 1 := by
  conv_lhs => rw [basis2_expand (betaOf xS)]
  rw [betaOf_xS_fst, betaOf_xS_snd, deltaU]

/-- **The `b₁` diagonal vanishes**: `⟨b₁ ∪ b₁, [M]⟩ = 0`, from `⟨β ∪ β, [M]⟩ = 0` and `β = u·b₁`
with `u² = 1`. -/
theorem gram_one_one :
    interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed 1)
      (sphereProdBasis2Computed 1) = 0 := by
  have h0 : interFormInt sphereProdIntFundClassHonest (betaOf xS) (betaOf xS) = 0 :=
    SphereProdGramInt.interFormInt_honest_snd_eq_zero xS xS
  rw [betaOf_xS_expand, bilin_expand_two] at h0
  have hd := deltaU_mul_self
  linear_combination h0 - (interFormInt sphereProdIntFundClassHonest
    (sphereProdBasis2Computed 1) (sphereProdBasis2Computed 1)) * hd

/-- **The off-diagonal**: `⟨b₀ ∪ b₁, [M]⟩ = u · ε`. -/
theorem gram_zero_one :
    interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed 0)
      (sphereProdBasis2Computed 1) = deltaU * crossEps := by
  have hε : interFormInt sphereProdIntFundClassHonest (alphaOf xS) (betaOf xS) = crossEps := rfl
  rw [alphaOf_xS_expand, betaOf_xS_expand, bilin_expand_two] at hε
  rw [gram_one_one] at hε
  have hd := deltaU_mul_self
  linear_combination deltaU * hε - (interFormInt sphereProdIntFundClassHonest
    (sphereProdBasis2Computed 0) (sphereProdBasis2Computed 1)) * hd

/-- **The `b₀` diagonal**: `⟨b₀ ∪ b₀, [M]⟩ = −2·s·u·ε` — the choice-dependent entry. -/
theorem gram_zero_zero :
    interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed 0)
      (sphereProdBasis2Computed 0) = -(2 * alphaSnd * deltaU * crossEps) := by
  have h0 : interFormInt sphereProdIntFundClassHonest (alphaOf xS) (alphaOf xS) = 0 :=
    SphereProdGramInt.interFormInt_honest_fst_eq_zero xS xS
  rw [alphaOf_xS_expand, bilin_expand_two] at h0
  have hsym : interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed 1)
      (sphereProdBasis2Computed 0)
      = interFormInt sphereProdIntFundClassHonest (sphereProdBasis2Computed 0)
        (sphereProdBasis2Computed 1) := interFormInt_symm _ _ _
  rw [hsym, gram_one_one, gram_zero_one] at h0
  linear_combination h0

/-- **THE EXACT COMPUTED-BASIS INTERSECTION MATRIX.** On the computed (UCT-dual) basis the S²×S²
intersection matrix is `!![-(2·s·u·ε), u·ε; u·ε, 0]`. The off-diagonal is a unit (so the form is
unimodular and, by §2, congruent to `Hyp`), but the (0,0) entry carries the free coordinate `s` of
the chosen split generator. -/
theorem sphereProd_interMatrix_computed_eq :
    interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis
      = !![-(2 * alphaSnd * deltaU * crossEps), deltaU * crossEps; deltaU * crossEps, 0] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_zero_zero
  · exact gram_zero_one
  · exact (interFormInt_symm _ _ _).trans gram_zero_one
  · exact gram_one_one

/-- **THE PIN'S PRECISE OBSTRUCTION.** `SphereProdGramPin` — the literal equality
`interMatrix fc B = Hyp` — holds **iff** the split generator's α-coordinate vanishes (`s = 0`) and
the two unit signs multiply to `+1` (`u·ε = 1`). Neither conjunct is available in tree: `s` is
choice-dependent (`deltaGen` is pinned only modulo `sumInto`, whose `fst_*` image is nonzero), and
`u`, `ε` are pinned only as units. This is why the pin is retired at the consumer level (§2) rather
than proved — its extra content over the congruence is a basis-normalization artifact. -/
theorem sphereProdGramPin_iff :
    SphereProdGramPin ↔ (alphaSnd = 0 ∧ deltaU * crossEps = 1) := by
  have hue : deltaU * crossEps ≠ 0 := by
    have h1 : IsUnit (deltaU * crossEps) := deltaU_isUnit.mul crossEps_isUnit
    rcases Int.isUnit_iff.mp h1 with h | h <;> rw [h] <;> norm_num
  constructor
  · intro hgram
    have h : (!![-(2 * alphaSnd * deltaU * crossEps), deltaU * crossEps;
        deltaU * crossEps, 0] : Matrix (Fin 2) (Fin 2) ℤ) = sphereProdFormDatum := by
      rw [← sphereProd_interMatrix_computed_eq]
      exact hgram
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, sphereProdFormDatum, Hyp, Matrix.of_apply] at h00 h01
    refine ⟨?_, h01⟩
    have : alphaSnd * (deltaU * crossEps) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hue
  · rintro ⟨hs, hue1⟩
    show interMatrix sphereProdIntFundClassHonest sphereProdIntH2Basis = sphereProdFormDatum
    rw [sphereProd_interMatrix_computed_eq, hs, hue1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sphereProdFormDatum, Hyp]

end SKEFTHawking.SphereProdGramPinRetire
