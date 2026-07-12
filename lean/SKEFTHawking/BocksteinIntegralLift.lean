/-
# Phase 5q.H (N6 seam, layer 1) — the Bockstein annihilates integrally-liftable homology classes

The generic engine behind "oriented ⟹ `v₁ = 0`": for any space `X` and any mod-2 class
`x ∈ Hⁿ⁺¹(X;ℤ/2)`, the Bockstein `Sq¹x` **pairs to zero against the ℤ→ℤ/2 reduction of any
integral homology class** — `⟨Sq¹x, red h⟩ = 0` for all `h ∈ Hₙ₊₂(X;ℤ)`.

This is the classical adjointness vanishing (the cohomology Bockstein is Kronecker-adjoint to the
homology Bockstein, which kills classes lifting to ℤ), realised here **without ℤ/4 chains** via
the *integral-lift presentation* of the in-tree cochain Bockstein:

* for a mod-2 `n`-cocycle `a`, the `{0,1}`-valued **integral** lift `liftInt a` has signed integral
  coboundary divisible by 2 (`two_dvd_coboundary_liftInt` — mod 2 the signs collapse and
  `δ_ℤ(liftInt a)` reduces to `δ₂a = 0`);
* the halved cochain `bockLiftInt a := δ_ℤ(liftInt a)/2` reduces mod 2 **pointwise on the nose** to
  the ℤ/4-defined `Sq1cochain a` (`Sq1cochain_eq_redC_bockLiftInt` — the ℤ/4 lift is the mod-4
  reduction of the integral lift, and `half ∘ (2·) = red₂` on evens);
* against an integral cycle `z`, `2·⟨bockLiftInt a, z⟩ = ⟨δ_ℤ(liftInt a), z⟩ = ⟨liftInt a, ∂z⟩ = 0`
  by the signed Stokes adjunction (`kronecker_coboundary_chainBoundary`), so the integer pairing
  vanishes and its mod-2 shadow (`kronecker_redCompat`) is the Kronecker pairing of `Sq¹`.

Consumed by `WuClass1Orientation` (E1↔E4 seam): at a closed oriented 4-manifold the first Wu class
`v₁` represents `x ↦ ⟨Sq¹x, [M]₂⟩` under PD, and `[M]₂ = red [M]_ℤ` (`IntOrientation.redCompat`),
so `v₁ = 0` — the Wu-formula fact `v₁ = w₁ = 0` for orientable `M`, derived (not frozen).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularBockstein
import SKEFTHawking.KroneckerRedCompat

namespace SKEFTHawking.BocksteinIntegralLift

open SKEFTHawking
open SKEFTHawking.SingularCohomologyInt (redC redC_apply redC_coboundary SingularCochainInt)
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularBockstein

variable {X : TopCat} {n : ℕ}

/-- The canonical `{0,1}`-valued **integral** lift of a mod-2 cochain:
`(liftInt a)(σ) = ((a σ).val : ℤ)`. The ℤ-companion of the ℤ/4 lift `SingularBockstein.lift`. -/
noncomputable def liftInt (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n) :
    SingularCochainInt X n :=
  fun σ => ((a σ).val : ℤ)

@[simp] theorem liftInt_apply (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    liftInt a σ = ((a σ).val : ℤ) := rfl

/-- The integral lift reduces mod 2 back to the original cochain: `redC (liftInt a) = a`. -/
theorem redC_liftInt (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n) :
    redC X n (liftInt a) = a := by
  funext σ
  rw [redC_apply, liftInt_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]

/-- The ℤ/4 lift is the mod-4 reduction of the integral lift (pointwise):
`((liftInt a σ : ℤ) : ZMod 4) = lift a σ`. -/
theorem liftInt_cast_zmod4 (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ((liftInt a σ : ℤ) : ZMod 4) = SingularBockstein.lift a σ := by
  rw [liftInt_apply, lift_apply, Int.cast_natCast]

/-- **The signed integral coboundary of the lift of a cocycle is even** (pointwise): mod 2 the
signs collapse and `δ_ℤ(liftInt a)` reduces to `δ₂ a = 0`, so each value is an even integer. -/
theorem two_dvd_coboundary_liftInt (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (ha : SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n a = 0)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (2 : ℤ) ∣ SingularCohomologyInt.coboundary X n (liftInt a) σ := by
  have h2 : ((SingularCohomologyInt.coboundary X n (liftInt a) σ : ℤ) : ZMod 2) = 0 := by
    have h := congrFun (redC_coboundary X n (liftInt a)) σ
    rw [redC_apply] at h
    rw [h, redC_liftInt]
    exact congrFun ha σ
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h2

/-- The **halved integral coboundary** `bockLiftInt a := δ_ℤ(liftInt a)/2` — the integral cochain
whose mod-2 reduction is the Bockstein `Sq1cochain a` (for a cocycle `a`). -/
noncomputable def bockLiftInt (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n) :
    SingularCochainInt X (n + 1) :=
  fun σ => SingularCohomologyInt.coboundary X n (liftInt a) σ / 2

/-- The defining property of the halved coboundary: `2 · bockLiftInt a = δ_ℤ(liftInt a)`
(pointwise, for a cocycle `a` — where the divisibility holds). -/
theorem two_mul_bockLiftInt (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (ha : SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n a = 0)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    2 * bockLiftInt a σ = SingularCohomologyInt.coboundary X n (liftInt a) σ :=
  Int.mul_ediv_cancel' (two_dvd_coboundary_liftInt a ha σ)

/-- **The integral-lift presentation of the Bockstein**: for a mod-2 cocycle `a`, the in-tree
ℤ/4-defined `Sq1cochain a` is pointwise the mod-2 reduction of the halved integral coboundary,
`Sq1cochain a = redC (bockLiftInt a)`. The bridge from the ℤ/4 connecting-map construction to
integral chain-level arguments (Stokes against integral cycles). -/
theorem Sq1cochain_eq_redC_bockLiftInt
    (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (ha : SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n a = 0) :
    Sq1cochain a = redC X (n + 1) (bockLiftInt a) := by
  funext σ
  -- the ℤ/4 coboundary of the ℤ/4 lift is the mod-4 reduction of the ℤ coboundary of the ℤ lift
  have hA : coboundary4 X n (SingularBockstein.lift a) σ
      = ((SingularCohomologyInt.coboundary X n (liftInt a) σ : ℤ) : ZMod 4) := by
    rw [coboundary4_apply, SingularCohomologyInt.coboundary_apply, Int.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, liftInt_cast_zmod4]
    rfl
  rw [Sq1cochain_apply, hA, ← two_mul_bockLiftInt a ha σ, Int.cast_mul]
  rw [show ((2 : ℤ) : ZMod 4) = 2 from rfl, half_two_smul, map_intCast, redC_apply]

/-- **Chain-level core: the Bockstein of a cocycle pairs to zero with the reduction of an
integral cycle.** `⟨Sq1cochain a, red₂ z⟩ = 0` for a mod-2 `n`-cocycle `a` and an integral
`(n+1)`-cycle `z`: the pairing is the mod-2 shadow of `⟨bockLiftInt a, z⟩ ∈ ℤ`, and
`2·⟨bockLiftInt a, z⟩ = ⟨δ_ℤ(liftInt a), z⟩ = ⟨liftInt a, ∂z⟩ = 0` by the signed Stokes
adjunction — so the integer itself vanishes. -/
theorem kronecker_Sq1cochain_redChain
    (a : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
    (ha : SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n a = 0)
    (z : SingularChainInt X (n + 1)) (hz : chainBoundary X n z = 0) :
    SKEFTHawking.SingularHomologyMod2.kronecker (Sq1cochain a) (redChain X (n + 1) z) = 0 := by
  rw [Sq1cochain_eq_redC_bockLiftInt a ha, ← kronecker_redCompat]
  have hzero : kronecker (bockLiftInt a) z = 0 := by
    have h2 : 2 * kronecker (bockLiftInt a) z = 0 := by
      have hsmul : (2 : ℤ) • bockLiftInt a = SingularCohomologyInt.coboundary X n (liftInt a) := by
        funext σ
        rw [Pi.smul_apply, smul_eq_mul, two_mul_bockLiftInt a ha]
      calc 2 * kronecker (bockLiftInt a) z
          = kronecker ((2 : ℤ) • bockLiftInt a) z := by rw [kronecker_smul_left, smul_eq_mul]
        _ = kronecker (liftInt a) (chainBoundary X n z) := by
            rw [hsmul]; exact kronecker_coboundary_chainBoundary _ _
        _ = 0 := by rw [hz, kronecker_apply, Finsupp.sum_zero_index]
    omega
  rw [hzero, Int.cast_zero]

/-- **The Bockstein annihilates integrally-liftable homology classes**:
`⟨Sq¹x, red h⟩ = 0` for every mod-2 class `x ∈ Hⁿ⁺¹(X;ℤ/2)` and every integral class
`h ∈ Hₙ₊₂(X;ℤ)`. The class-level adjointness vanishing — the homology Bockstein of a class that
lifts to ℤ is zero, expressed through the Kronecker pairing. The engine for "oriented ⟹ `v₁ = 0`"
(the first Wu class kills against `[M]₂ = red [M]_ℤ`). -/
theorem kroneckerH_Sq1_redHomology
    (x : SKEFTHawking.SingularCohomologyMod2.Cohomology X (n + 1))
    (h : Homology X (n + 1 + 1)) :
    SKEFTHawking.SingularHomologyMod2.kroneckerH (n + 1 + 1)
      (SingularBockstein.Sq1 x) (redHomology X (n + 1 + 1) h) = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  have hz : chainBoundary X (n + 1) z.1 = 0 :=
    LinearMap.mem_ker.mp (z.2 : z.1 ∈ LinearMap.ker (chainBoundary X (n + 1)))
  show SKEFTHawking.SingularHomologyMod2.kronecker (Sq1cochain a.1) (redChain X (n + 1 + 1) z.1) = 0
  exact kronecker_Sq1cochain_redChain a.1 (LinearMap.mem_ker.mp a.2) z.1 hz

end SKEFTHawking.BocksteinIntegralLift
