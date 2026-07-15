/-
# Phase 5q.H (W-A arm 4) — the ℤ/2 reduction of local-cross injectivity to ONE nonvanishing

The frozen reduction `PoincareLefschetzRelFundClassCylinderCrossLocalReduce` discharges the terminal
`hcls` of the concrete cylinder datum *given* the injectivity of the local cross
`crossHloc : H_{m'+2}(M, M∖σ) → H_{m'+3}(M×I, (M×I)∖x)` at every interior point `x = (σ,t)`. This
module sharpens that hypothesis to its **minimal honest form**: because the source
`H_{m'+2}(M, M∖σ)` is the **two-element** local homology `≅ ℤ/2` (`SingularChartBridge.manifoldLocalIso`),
a ℤ/2-linear map out of it is injective **iff** it does not kill the (unique) nonzero class — and
`M`'s local fundamental class `[M]|_σ = mLocalClass` is that nonzero class (`mLocalClass_ne_zero`). So

  `crossHloc` injective at `x`  ⟺  `crossHloc ([M]|_σ) ≠ 0`,

the single interior local-Künneth nonvanishing "`[prismOp graphHom z] ≠ 0`". We package:

* **§1 — the ℤ/2 linear-algebra core**: over `ZMod 2`, a space `V ≃ₗ ZMod 2` has exactly two elements
  (`eq_zero_or_eq_of_equiv_zmod2`); a linear map out of it is injective iff its value on one nonzero
  generator is nonzero (`injective_of_apply_gen_ne_zero`).
* **§2 — the bridge**: `crossHloc` injective at `x` ⟺ `crossHloc (mLocalClass) ≠ 0`
  (`crossHloc_injective_iff_localClass_ne_zero`), instantiating the core at `e = manifoldLocalIso σ`,
  `g = mLocalClass`.
* **§3 — the direct terminal**: `hasRelFundClass_cylGen_of_localClass_ne_zero` — the concrete
  cylinder `HasRelFundClass`, discharged straight from the single nonvanishing (via the naturality
  square `restrictBd candidate = crossHloc ([M]|_σ)`, no injectivity detour).

The residual crux is unchanged in substance — the interior local-Künneth `crossHloc ([M]|_σ) ≠ 0`,
"the prism of a chart-local generator is not a puncture-relative boundary" — but is now isolated as a
**single ℤ/2 nonvanishing**, the sharpest possible statement.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocal
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalReduce
open SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalInj

noncomputable section

/-! ## §1. The ℤ/2 linear-algebra core -/

variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- **A `ZMod 2`-space with `V ≃ₗ ZMod 2` has exactly two elements**: every `a : V` is either `0` or
the nonzero generator `g` (any `g ≠ 0`). The `ZMod 2`-dichotomy `y = 0 ∨ y = 1` transported by the
equivalence. -/
theorem eq_zero_or_eq_of_equiv_zmod2 (e : V ≃ₗ[ZMod 2] ZMod 2) {g : V} (hg : g ≠ 0) (a : V) :
    a = 0 ∨ a = g := by
  have hdich : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  have hg1 : e g = 1 := by
    rcases hdich (e g) with h | h
    · exact absurd (e.map_eq_zero_iff.1 h) hg
    · exact h
  rcases hdich (e a) with h | h
  · exact Or.inl (e.map_eq_zero_iff.1 h)
  · exact Or.inr (e.injective (h.trans hg1.symm))

/-- **Injectivity from a single nonvanishing** over `ZMod 2`: if `V ≃ₗ ZMod 2` (so `V` is
two-element) and a ℤ/2-linear `f : V →ₗ W` does not kill some nonzero generator `g`, then `f` is
injective (its kernel — a subspace of the two-element `V` — cannot contain `g`, so is `⊥`). -/
theorem injective_of_apply_gen_ne_zero (f : V →ₗ[ZMod 2] W) (e : V ≃ₗ[ZMod 2] ZMod 2) {g : V}
    (hg : g ≠ 0) (hfg : f g ≠ 0) : Function.Injective f := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  rcases eq_zero_or_eq_of_equiv_zmod2 e hg a with h | h
  · exact h
  · exact absurd (h ▸ ha) hfg

/-- **Conversely**, an injective ℤ/2-linear map does not kill a nonzero generator (trivial, but
completes the equivalence at the linear-algebra level). -/
theorem apply_gen_ne_zero_of_injective (f : V →ₗ[ZMod 2] W) {g : V} (hg : g ≠ 0)
    (hf : Function.Injective f) : f g ≠ 0 := by
  intro h; exact hg (hf (by rw [h, map_zero]))

end

/-! ## §2. The bridge — `crossHloc` injective ⟺ `crossHloc (mLocalClass) ≠ 0` -/

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **`crossHloc` is injective at `x` iff it does not kill `[M]|_σ`.** The source local homology
`H_{m'+2}(M, M∖σ)` is two-element (`manifoldLocalIso σ`) with nonzero generator `mLocalClass x z`
(`mLocalClass_ne_zero`, `z` a fundamental cycle rep), so injectivity of the ℤ/2-linear `crossHloc`
collapses to the single nonvanishing `crossHloc (mLocalClass x z) ≠ 0`. -/
theorem crossHloc_injective_iff_localClass_ne_zero
    (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M))
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    Function.Injective (crossHloc (M := TopCat.of M) (interior_slice_one x hx)
        (interior_slice_zero x hx) (interior_punc x) (m' + 1))
      ↔ crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
          (interior_punc x) (m' + 1) (mLocalClass x z) ≠ 0 := by
  constructor
  · exact fun hinj =>
      apply_gen_ne_zero_of_injective _ (mLocalClass_ne_zero x z hz) hinj
  · exact fun hne =>
      injective_of_apply_gen_ne_zero _ (SKEFTHawking.SingularChartBridge.manifoldLocalIso
        (m := m') x.1) (mLocalClass_ne_zero x z hz) hne

/-! ## §3. The direct terminal — `HasRelFundClass` from the single nonvanishing -/

/-- **The concrete cylinder `HasRelFundClass`, discharged from the single interior nonvanishing.**
If at every interior point `x = (σ,t)` the local cross of `M`'s local fundamental class is nonzero
(`crossHloc (mLocalClass x z) ≠ 0`, the interior local-Künneth), the terminal `hcls` hole is filled —
directly via the naturality square `restrictBd candidate = crossHloc ([M]|_σ)`, no injectivity
detour. This is the sharpest reduction of `cylFundClassCandidate_restricts`: the sole remaining
obligation is that ONE explicit prism class is nonzero in the two-element interior local homology. -/
theorem hasRelFundClass_cylGen_of_localClass_ne_zero [T1Space (cylW M)]
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z)
    (hne : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      crossHloc (M := TopCat.of M) (interior_slice_one x hx) (interior_slice_zero x hx)
        (interior_punc x) (m' + 1) (mLocalClass x z) ≠ 0) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_of_candidate_ne_zero
    (fun x hx => by rw [restrictBd_candidate_eq_crossHloc x hx z hz]; exact hne x hx)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalInj
