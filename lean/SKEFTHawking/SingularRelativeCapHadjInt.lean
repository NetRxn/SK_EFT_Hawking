import Mathlib
import SKEFTHawking.SingularRelativeCapConnectingInt
import SKEFTHawking.SingularRelativeCohomDeltaInt
import SKEFTHawking.SingularPullbackDualityCapSubInt

/-!
# Phase 5q.H close-out — the substrate `hadj` PD-square, integral core: `⟨ι*a ∪ v, [∂W]⟩ = ⟨a, δv⟩`

The final geometric assembly of the σ+hcob unlock's `hadj` gap, at the **integral** level (before the
`⊗ℝ` base-change). The substrate's PD-intertwining `hadj : ⟨ι*a ∪ v, [∂W]⟩ = pairing a (δv)` — the single
relation coupling the boundary intersection form to the pair connecting map — is here PROVED over ℤ as

  `⟨ι*v, ι*a ⌢ [∂W]⟩ = ⟨δv, a ⌢ [W,∂W]⟩`   (`hadj_integral_core`),

with the `pairing a x := ⟨x, a ⌢ [W,∂W]⟩` realized via the integral relative cap `capRelHInt`. It stitches
the three banked mediators:

* **(cap–boundary)** `connectingInt_capRelHInt` — `∂(a ⌢ [W,∂W]) = (ι*a) ⌢ ∂[W,∂W]` (`k = 2`, sign `+1`);
* **(δ ⊣ ∂)** `SingularRelativeCohomDeltaInt.relKroneckerHInt_deltaRelHInt` — `⟨δz, [c]⟩ = ⟨z, ∂c⟩`;
* **(chainIncl adjoint)** `kronecker_chainIncl_eq_pullbackCochainInt` — `⟨z, ι w⟩ = ⟨ι*z, w⟩`,

through the M2-to-class bridge `kroneckerHInt_connectingInt`
(`⟨ι*v, ∂W'⟩ = ⟨δv, W'⟩`). The remaining wiring to the `Fin n → ℝ` lattice substrate — the `⊗ℝ`
class-level base-change and the lift-parametric δ packaging — is the separate scalar-extension layer
(documented in `SingularRelativeCohomDeltaInt`), not this module.

Dimension discipline: `W` 5-dim, `∂W` 4-dim; `a, v ∈ H²`; `δ : H²(∂W) → H³(W,∂W)`; the cap
`H²(W) × H₅(W,∂W) → H₃(W,∂W)`; the square at the pair's degree-2/3/4.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularRelativeCohomDeltaInt
open SKEFTHawking.SingularRelativeCapHomologyInt
open SKEFTHawking.SingularRelativeCapConnectingInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularCapChainInclInt (pullbackCochainInt pullbackCochainInt_apply)

namespace SKEFTHawking.SingularRelativeCapHadjInt

variable {X : TopCat} {S : Set X} {n : ℕ}

/-! ## §1. The chainIncl–pullback Kronecker adjoint `⟨z, ι w⟩ = ⟨ι*z, w⟩` -/

/-- **The integral `chainIncl` / `pullbackCochainInt` Kronecker adjoint.** `⟨z, chainIncl w⟩ = ⟨ι*z, w⟩`
— pairing an absolute cochain `z` against the inclusion of a `∂W`-chain `w` equals pairing the restriction
`ι*z = pullbackCochainInt z` against `w`. On a basis simplex both are `s · z(simplexIncl τ)`. The integral
mirror of `SingularConnSquareCloseNC.kronecker_chainIncl_eq_pullbackCochain`. -/
theorem kronecker_chainIncl_eq_pullbackCochainInt (z : SingularCochainInt X n)
    (c : SingularChainInt (sub S) n) :
    kronecker z (chainIncl S n c) = kronecker (pullbackCochainInt S n z) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, kronecker_add_right, kronecker_add_right, hc, hd]
  | single τ s => rw [chainIncl_single, kronecker_single, kronecker_single, pullbackCochainInt_apply]

/-! ## §2. The restriction of a boundary-cocycle lift to `∂W` -/

/-- **The pullback of a δ-relative lift is a `∂W`-cocycle.** If `z`'s coboundary `δz` annihilates the
subcomplex (`δz ∈ relCochainsInt S`), then `ι*z = pullbackCochainInt z` is a genuine cocycle on `∂W`
(`δ(ι*z) = ι*(δz) = 0`, the latter since `δz` vanishes on subspace simplices). -/
theorem pullbackCochainInt_coboundary_eq_zero (z : SingularCochainInt X n)
    (hz : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    coboundaryₗ (sub S) n (pullbackCochainInt S n z) = 0 := by
  show coboundary (sub S) n (pullbackCochainInt S n z) = 0
  rw [SKEFTHawking.SingularPullbackDualityCapSubInt.coboundary_pullbackCochainInt]
  funext τ
  show pullbackCochainInt S (n + 1) (coboundary X n z) τ = 0
  rw [pullbackCochainInt_apply]
  have hmem := (mem_relCochainsInt S (n + 1) (coboundaryₗ X n z)).mp hz
    (chainIncl S (n + 1) (Finsupp.single τ 1)) ⟨Finsupp.single τ 1, rfl⟩
  rwa [chainIncl_single, kronecker_single, one_mul] at hmem

/-- **The restriction `ι* : Hⁿ(X;ℤ) → Hⁿ(∂W;ℤ)` on a δ-relative lift**, as a `∂W`-cocycle representative.
For a lift `z` with `δz` relative (`δz ∈ relCochainsInt S`), `ι*z = pullbackCochainInt z` is a cocycle on
`∂W` — the cochain representing the `H²(∂W)` class whose `δ` is `deltaRelHInt z hz`. -/
noncomputable def restrictLiftCocycleInt (z : SingularCochainInt X n)
    (hz : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    LinearMap.ker (coboundaryₗ (sub S) n) :=
  ⟨pullbackCochainInt S n z, LinearMap.mem_ker.mpr (pullbackCochainInt_coboundary_eq_zero z hz)⟩

@[simp] theorem restrictLiftCocycleInt_coe (z : SingularCochainInt X n)
    (hz : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) :
    (restrictLiftCocycleInt (S := S) z hz : SingularCochainInt (sub S) n) = pullbackCochainInt S n z :=
  rfl

/-! ## §3. The M2-to-class bridge `⟨ι*v, ∂W'⟩ = ⟨δv, W'⟩` -/

/-- **The δ ⊣ ∂ adjunction on (co)homology classes** `⟨ι*v, ∂W'⟩ = ⟨δv, W'⟩`. For a δ-relative lift `z`
(representing `v ∈ Hⁿ(∂W)` with `δv = deltaRelHInt z hz`) and a relative class `W' ∈ Hₙ₊₁(X,S;ℤ)`, the
absolute Kronecker of the restriction `ι*v` against the boundary `∂W' ∈ Hₙ(∂W)` equals the relative
Kronecker of `δv` against `W'`. Descends `relKroneckerHInt_deltaRelHInt` through `connectingInt` /
`connectingLift`, using the `chainIncl` adjoint. This lifts the banked chain-level `δ ⊣ ∂` to the class
pairing the substrate `hadj` consumes. -/
theorem kroneckerHInt_connectingInt (z : SingularCochainInt X n)
    (hz : coboundaryₗ X n z ∈ relCochainsInt S (n + 1)) (W : RelHomologyInt S (n + 1)) :
    kroneckerHInt n (Cohomology.mk (sub S) n (restrictLiftCocycleInt z hz)) (connectingInt S n W)
      = relKroneckerHInt S (deltaRelHInt z hz) W := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S n W
  rw [connectingInt_relCycleToHom, connectingLift_apply, relCycleToHom_apply,
    relKroneckerHInt_deltaRelHInt z hz c.1 (mk_mem_relCyclesInt S n c.1 c.2)]
  show kronecker (pullbackCochainInt S n z) (boundaryExtract S n c) = kronecker z (chainBoundary X n c.1)
  rw [← chainIncl_boundaryExtract, kronecker_chainIncl_eq_pullbackCochainInt]

/-! ## §4. The `hadj` PD-square, integral core -/

/-- **The substrate PD-intertwining `hadj`, integral core.** `⟨ι*v, (ι*a) ⌢ [∂W]⟩ = ⟨δv, a ⌢ [W,∂W]⟩` —
the boundary intersection form of the restrictions `ι*a`, `ι*v` (LHS, via the absolute cap on `∂W` against
`[∂W] = ∂[W,∂W]`) equals the relative Kronecker of `δv` against the relative cap `a ⌢ [W,∂W]` (RHS, the
substrate's `pairing a (δv)`). This is the integral realization of the substrate field
`hadj : polarBilin Q (rest2 a) v = pairing a (delta v)` for a `[W,∂W]`-carrying witness, `k = 2`. Proof:
the cap–boundary naturality `connectingInt_capRelHInt` (`k = 2`, sign `+1`) rewrites the LHS cap to
`∂(a ⌢ [W,∂W])`, then the M2-to-class bridge `kroneckerHInt_connectingInt` converts the `∂`-pairing to the
`δ`-pairing. -/
theorem hadj_integral_core (a : LinearMap.ker (coboundaryₗ X 2)) (v : SingularCochainInt X 2)
    (hv : coboundaryₗ X 2 v ∈ relCochainsInt S (2 + 1)) (Z : relCycleLift S (2 + 1 + 1)) :
    kroneckerHInt 2 (Cohomology.mk (sub S) 2 (restrictLiftCocycleInt v hv))
        (capHInt (X := sub S) 2 1 (Cohomology.mk (sub S) 2 (restrictCocycleInt a))
          (connectingInt S (2 + 1 + 1) (relCycleToHom S (2 + 1 + 1) Z)))
      = relKroneckerHInt S (deltaRelHInt v hv)
          (capRelHInt 2 2 (Cohomology.mk X 2 a) (relCycleToHom S (2 + 1 + 1) Z)) := by
  have hM1 := connectingInt_capRelHInt (k := 2) (d := 1) a Z
  rw [show ((-1 : ℤ) ^ 2) = 1 from by norm_num, one_smul] at hM1
  rw [← hM1]
  exact kroneckerHInt_connectingInt v hv
    (capRelHInt 2 2 (Cohomology.mk X 2 a) (relCycleToHom S (2 + 1 + 1) Z))

end SKEFTHawking.SingularRelativeCapHadjInt
