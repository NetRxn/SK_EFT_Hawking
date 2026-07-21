/-
# Phase 5q.H — K7 residual (a): the `H₂(Q;ℤ)` Smith solve

The interlocking-LES walk computing the free-quotient homology `H₂(Q;ℤ)` from the banked Smith
sequences (`KummerQuotientSmithSES`) and the `τ_*`-eigenvalue detection
(`KummerT4CycleDetection`), against the **puncture-window interface** — the inclusion
`T⁴° ↪ T⁴` inducing injections on `H₁`/`H₂` and the `H₂(T⁴°) ≅ ℤ⁶` identification (discharged by
the puncture Mayer–Vietoris in `KummerPuncturedMV`):

* `X_H1_fixed_eq_zero` / `X_H2_anti_eq_zero` — `ker(1−τ_*) = 0` on `H₁(T⁴°)` and
  `ker(1+τ_*) = 0` on `H₂(T⁴°)` (naturality along the inclusion + the `T⁴` eigen-vanishing);
* `inclBH_one_injective` — `H₁(B) ↪ H₁(T⁴°)` (via `ι_B ∘ D̄ = 1 − τ_*` and `D̄` onto);
* `deltaIII_one_eq_zero` → **`projH_two_surjective`**;
* `transferH ∘ projH = 1 + τ_*` → **`projH_two_injective`**;
* **`qH2EquivOfWindow`** — `H₂(Q;ℤ) ≅ ℤ⁶`, the single open input `hQ` of the landed K7
  `b₂ = 22` window, fed to `kummerK3_b2_window_of_qH2` as `kummerK3_b2_window_of_puncture`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerQuotientSmithSES
import SKEFTHawking.KummerT4CycleDetection
import SKEFTHawking.KummerK7MVAssembly

namespace SKEFTHawking.KummerQuotientH2Solve

open CategoryTheory Opposite
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop tauC qmkC)
open SKEFTHawking.KummerPuncturedTorus (puncturedTorus)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.SingularHomologyInt (Homology chainBoundary)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt Homology.mapInt Homology.mapInt_comp)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerQuotientSmithSES
open SKEFTHawking.KummerT4CycleDetection (tauT4C t4_H1_fixed_eq_zero t4_H2_anti_eq_zero)

noncomputable section

/-! ## §1. The puncture inclusion and the `τ`-naturality square -/

/-- The inclusion `T⁴° ↪ T⁴`, unbundled. -/
def inclXFun : ↥puncturedTorus → TorusFour := fun x => x

theorem inclXFun_continuous : Continuous inclXFun := continuous_subtype_val

/-- The inclusion `T⁴° ↪ T⁴` as a continuous map of carriers. -/
def inclXC : C(↑PTtop, ↑(TopCat.of TorusFour)) :=
  ⟨inclXFun, inclXFun_continuous⟩

/-- The inclusion intertwines the deck involution with the Kummer involution. -/
theorem inclXC_comp_tauC : inclXC.comp tauC = tauT4C.comp inclXC := by
  refine ContinuousMap.ext fun x => ?_
  show inclXFun (SKEFTHawking.KummerQuotientCovering.tauFun x)
    = SKEFTHawking.KummerInvolution.torusFourInvolution (inclXFun x)
  exact SKEFTHawking.KummerFreeQuotient.neg_one_smul_val x

/-- Naturality on homology. -/
theorem mapInt_incl_tau (n : ℕ) (y : Homology PTtop n) :
    Homology.mapInt tauT4C n (Homology.mapInt inclXC n y)
      = Homology.mapInt inclXC n (Homology.mapInt tauC n y) := by
  have h1 : Homology.mapInt tauT4C n (Homology.mapInt inclXC n y)
      = Homology.mapInt (tauT4C.comp inclXC) n y := by
    rw [Homology.mapInt_comp]
    rfl
  have h2 : Homology.mapInt inclXC n (Homology.mapInt tauC n y)
      = Homology.mapInt (inclXC.comp tauC) n y := by
    rw [Homology.mapInt_comp]
    rfl
  rw [h1, h2, inclXC_comp_tauC]

/-- **`ker(1−τ_*) = 0` on `H₁(T⁴°)`** — against the puncture-window degree-1 injectivity. -/
theorem X_H1_fixed_eq_zero (hX1 : Function.Injective (Homology.mapInt inclXC 1))
    (y : Homology PTtop 1) (h : Homology.mapInt tauC 1 y = y) : y = 0 := by
  apply hX1
  rw [map_zero]
  refine t4_H1_fixed_eq_zero _ ?_
  rw [mapInt_incl_tau, h]

/-- **`ker(1+τ_*) = 0` on `H₂(T⁴°)`** — against the puncture-window degree-2 injectivity. -/
theorem X_H2_anti_eq_zero (hX2 : Function.Injective (Homology.mapInt inclXC 2))
    (y : Homology PTtop 2) (h : Homology.mapInt tauC 2 y = -y) : y = 0 := by
  apply hX2
  rw [map_zero]
  refine t4_H2_anti_eq_zero _ ?_
  rw [mapInt_incl_tau, h, map_neg]

/-! ## §2. The `Hml`-engine bridge at positive degree -/

/-- The engine's homology-level deck action IS the project's induced map (both quotient-lift the
same chain map; the carriers agree definitionally at positive degree). -/
theorem tauH_eq_mapInt (n : ℕ) (x : Hml (chainBoundary PTtop) (n + 1)) :
    tauH (n + 1) x = Homology.mapInt tauC (n + 1) x := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary PTtop) (n + 1) x
  rfl

/-! ## §3. The walk: `inclBH₁` injective, `projH₂` bijective -/

/-- **`H₁(B) ↪ H₁(T⁴°)`**: the composite `ι_B ∘ D̄ = 1 − τ_*` is injective on `H₁` and `D̄` is
onto. -/
theorem inclBH_one_injective (hX1 : Function.Injective (Homology.mapInt inclXC 1)) :
    Function.Injective (inclBH 1) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro y hy
  rw [LinearMap.mem_ker] at hy
  obtain ⟨x, rfl⟩ := diffH_one_surjective y
  have h1 : x - tauH 1 x = 0 := by rw [← inclBH_diffH, hy]
  have h2 : Homology.mapInt tauC 1 x = x :=
    (tauH_eq_mapInt 0 x).symm.trans (sub_eq_zero.mp h1).symm
  rw [X_H1_fixed_eq_zero hX1 x h2]
  exact map_zero _

/-- The SES-III connecting `δ₁ : H₂(Q) → H₁(B)` vanishes. -/
theorem deltaIII_one_eq_zero (hX1 : Function.Injective (Homology.mapInt inclXC 1))
    (z : Hml (chainBoundary Qtop) 2) : deltaIII 1 z = 0 := by
  apply inclBH_one_injective hX1
  rw [map_zero]
  exact (exact_deltaIII_inclBH 1).apply_apply_eq_zero z

/-- **`p̄₂ : H₂(T⁴°) → H₂(Q)` is surjective.** -/
theorem projH_two_surjective (hX1 : Function.Injective (Homology.mapInt inclXC 1)) :
    Function.Surjective (projH 2) := fun z =>
  (exact_projH_deltaIII 1 z).mp (deltaIII_one_eq_zero hX1 z)

/-- **`p̄₂ : H₂(T⁴°) → H₂(Q)` is injective** — `t ∘ p̄ = 1 + τ_*` has kernel the anti-fixed
classes, which vanish. -/
theorem projH_two_injective (hX2 : Function.Injective (Homology.mapInt inclXC 2)) :
    Function.Injective (projH 2) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  have h1 : transferH 2 (projH 2 x) = x + tauH 2 x := transferH_projH 2 x
  rw [hx, map_zero] at h1
  have h3 : tauH 2 x + x = 0 := by
    rw [add_comm]
    exact h1.symm
  have h2 : Homology.mapInt tauC 2 x = -x :=
    (tauH_eq_mapInt 1 x).symm.trans (eq_neg_of_add_eq_zero_left h3)
  exact X_H2_anti_eq_zero hX2 x h2

/-! ## §4. The `hQ` equivalence and the fed `b₂ = 22` window -/

/-- **`H₂(Q;ℤ) ≅ ℤ⁶`** — the K7 `hQ` input, from the Smith walk against the puncture-window
interface (degree-1/2 injectivity of `T⁴° ↪ T⁴` and the `H₂(T⁴°) ≅ ℤ⁶` identification). -/
def qH2EquivOfWindow (hX1 : Function.Injective (Homology.mapInt inclXC 1))
    (hX2 : Function.Injective (Homology.mapInt inclXC 2))
    (hiso : Homology PTtop 2 ≃ₗ[ℤ] (Fin 6 → ℤ)) :
    Homology (TopCat.of FreeQuotient) 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  ((SKEFTHawking.KummerRP3SmithSES.hmlEquivHomology Qtop 2).symm.trans
    ((LinearEquiv.ofBijective (projH 2)
        ⟨projH_two_injective hX2, projH_two_surjective hX1⟩).symm.trans
      ((SKEFTHawking.KummerRP3SmithSES.hmlEquivHomology PTtop 2).trans hiso)))

/-- **The `b₂ = 22` rank window, fed**: given the puncture-window interface, a rank-22 free block
`ℤ⁶ × ℤ¹⁶` embeds in `H₂(K3;ℤ)` and contains `2·H₂(K3;ℤ)` — the landed K7 window
`kummerK3_b2_window_of_qH2` discharged at its single open input `hQ`. -/
theorem kummerK3_b2_window_of_puncture
    (hX1 : Function.Injective (Homology.mapInt inclXC 1))
    (hX2 : Function.Injective (Homology.mapInt inclXC 2))
    (hiso : Homology PTtop 2 ≃ₗ[ℤ] (Fin 6 → ℤ)) :
    ∃ φ : ((Fin 6 → ℤ) × (SKEFTHawking.KummerWeld.EIndex → ℤ)) →ₗ[ℤ]
        Homology SKEFTHawking.KummerK7Opener.KummerK3top 2,
      Function.Injective φ ∧ ∀ x, ∃ v, φ v = (2 : ℤ) • x :=
  SKEFTHawking.KummerK7MVAssembly.kummerK3_b2_window_of_qH2
    (qH2EquivOfWindow hX1 hX2 hiso)

end

end SKEFTHawking.KummerQuotientH2Solve
