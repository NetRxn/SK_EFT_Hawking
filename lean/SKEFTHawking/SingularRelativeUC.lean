import Mathlib
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.SingularUniversalCoeff

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4d) — relative universal coefficients over ℤ/2

The relative analogue of the two absolute universal-coefficients facts
(`PoincareDualityConstruct.homology_eq_zero_of_kroneckerH` and
`SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH`): the relative Kronecker pairing
`relKroneckerH : Hᵏ(M,S) → Hₙ(M,S) → ℤ/2` (`SingularRelativePairing`) is **non-degenerate in each
argument** over the field `ℤ/2`. Combined with `Hₙ(M|x) ≅ ℤ/2` (`manifoldLocalIso`), this gives the
local cohomology `Hⁿ(M|x) ≅ ℤ/2` in the Poincaré-duality base case (PD-4e).

The one new ingredient over the absolute proofs is `exists_relCochain_of_functional`: every functional
on the relative chains `RelativeChain S n` is `relKronecker` of a relative cochain — proved by pulling
the functional back along the quotient map `mkQ` to a functional on `SingularChain X n` that vanishes
on the subspace chains, realizing *that* as `kronecker f` (absolute
`SingularUniversalCoeff.exists_cochain_of_functional`), and noting `f` then vanishes on the subspace
chains (so `f ∈ relCochains S n`). With that, both non-degeneracies mirror the absolute proofs on the
relative complex (`relCochains` / `RelativeChain` / `relBoundary` / `relCoboundaryₗ`), using the relative
adjunction `relKronecker_relBoundary`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing

namespace SKEFTHawking.SingularRelativeUC

variable {X : TopCat} (S : Set X)

/-- **Every relative-chain functional is `relKronecker` of a relative cochain.** A functional
`φ : RelativeChain S n →ₗ ℤ/2` pulls back along the quotient map `mkQ : C_n(X) → C_n(X,S)` to a
functional `ψ = φ ∘ mkQ` on the absolute chains that vanishes on the subspace chains; realize `ψ` as
`kronecker f` (absolute `exists_cochain_of_functional`); then `f ∈ relCochains S n` (it kills the
subspace chains, since `mkQ` does), and `relKronecker ⟨f,·⟩ = φ`. The relative analogue of
`SingularUniversalCoeff.exists_cochain_of_functional`. -/
theorem exists_relCochain_of_functional {n : ℕ} (φ : RelativeChain S n →ₗ[ZMod 2] ZMod 2) :
    ∃ a : relCochains S n, relKronecker S a = φ := by
  set ψ : SingularChain X n →ₗ[ZMod 2] ZMod 2 := φ.comp (Submodule.mkQ (subspaceChains S n)) with hψ
  obtain ⟨f, hf⟩ := SingularUniversalCoeff.exists_cochain_of_functional ψ
  have hfrel : f ∈ relCochains S n := by
    intro c hc
    rw [hf, hψ, LinearMap.comp_apply]
    show φ (Submodule.Quotient.mk c) = 0
    rw [(Submodule.Quotient.mk_eq_zero _).2 hc]
    exact map_zero φ
  refine ⟨⟨f, hfrel⟩, ?_⟩
  ext q
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show relKronecker S ⟨f, hfrel⟩ (RelativeChain.mk S n c) = φ (RelativeChain.mk S n c)
  rw [relKronecker_mk, hf, hψ, LinearMap.comp_apply]
  rfl

/-- **The relative Kronecker pairing is non-degenerate in the homology argument** (relative universal
coefficients over `ℤ/2`): a relative homology class `β ∈ Hₙ(M,S)` pairing to `0` with every relative
cohomology class is `0`. The relative analogue of
`PoincareDualityConstruct.homology_eq_zero_of_kroneckerH`. If `β = [z] ≠ 0` then the relative cycle `z`
is not a relative boundary, so (over the field `ℤ/2`) a functional `φ` separates it; realize `φ` as
`relKronecker a` for a relative cochain `a` (`exists_relCochain_of_functional`), check `a` is a relative
cocycle (`relKronecker_relBoundary` adjunction), and get `⟨[a], β⟩ = φ z ≠ 0` — contradiction. -/
theorem relHomology_eq_zero_of_relKroneckerH {N : ℕ} (β : RelativeHomology S (N + 1))
    (h : ∀ ω : RelativeCohomology S (N + 1), relKroneckerH S ω β = 0) : β = 0 := by
  by_contra hβ
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  have hznb : (z : RelativeChain S (N + 1)) ∉ relBoundaries S (N + 1) := by
    intro hz
    exact hβ ((RelativeHomology.mk_eq_zero_iff S (N + 1) z).mpr hz)
  obtain ⟨φ, hφv, hφker⟩ := Submodule.exists_le_ker_of_notMem hznb
  obtain ⟨a, ha⟩ := exists_relCochain_of_functional S φ
  -- `a` is a relative cocycle: `relCoboundaryₗ a = 0`, since `δ`-of-its-cochain kills every basis
  -- via `⟨a, ∂(single σ)⟩ = φ (relBoundary [single σ]) = 0` (relative boundaries lie in `ker φ`).
  have hcocycle : (a : relCochains S (N + 1)) ∈ LinearMap.ker (relCoboundaryₗ S (N + 1)) := by
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show coboundary X (N + 1) a.1 = 0
    funext σ
    rw [← kronecker_boundaryBasis a.1 σ]
    have hbb : (RelativeChain.mk S (N + 1) (boundaryBasis X (N + 1) σ)) ∈ relBoundaries S (N + 1) :=
      ⟨RelativeChain.mk S (N + 2) (Finsupp.single σ 1), by
        rw [relBoundary_mk, chainBoundary_single]⟩
    have hcalc : kronecker a.1 (boundaryBasis X (N + 1) σ)
        = φ (RelativeChain.mk S (N + 1) (boundaryBasis X (N + 1) σ)) := by
      rw [← relKronecker_mk S a, ha]
    rw [hcalc]
    exact LinearMap.mem_ker.mp (hφker hbb)
  -- contradiction: `⟨[a], β⟩ = relKronecker a z = φ z ≠ 0`.
  have hc := h (RelativeCohomology.mk S (N + 1) ⟨a, hcocycle⟩)
  rw [show (Submodule.Quotient.mk z : RelativeHomology S (N + 1)) = RelativeHomology.mk S (N + 1) z
      from rfl, relKroneckerH_mk_mk] at hc
  rw [show relKronecker S a z.1 = φ z.1 from congrFun (congrArg DFunLike.coe ha) z.1] at hc
  exact hφv hc

/-- **The relative Kronecker pairing is non-degenerate in the cohomology argument** (relative universal
coefficients over `ℤ/2`): a relative cohomology class `ω ∈ Hⁿ(M,S)` (degree `N+1`) pairing to `0` with
every relative homology class is `0`. The relative analogue of
`SingularUniversalCoeff.cohomology_eq_zero_of_kroneckerH`. `ω = [a]` for a relative cocycle `a`; the
functional `φ = relKronecker a` vanishes on relative cycles (`ker (relBoundary S N)`) by hypothesis, so
(over the field) factors `φ = g ∘ relBoundary S N` (`exists_factor_of_ker_le_ker`); realize `g` as
`relKronecker b` (`exists_relCochain_of_functional`); then the relative adjunction gives
`a = relCoboundaryₗ b` (a relative coboundary), so `ω = 0`. -/
theorem relCohomology_eq_zero_of_relKroneckerH {N : ℕ} (ω : RelativeCohomology S (N + 1))
    (h : ∀ β : RelativeHomology S (N + 1), relKroneckerH S ω β = 0) : ω = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ ω
  set φ : RelativeChain S (N + 1) →ₗ[ZMod 2] ZMod 2 := relKronecker S a.1 with hφ
  have hvanish : LinearMap.ker (relBoundary S N) ≤ LinearMap.ker φ := by
    intro z hz
    rw [LinearMap.mem_ker] at hz ⊢
    rw [hφ]
    have hzcyc : z ∈ relCycles S (N + 1) := hz
    have hh := h (RelativeHomology.mk S (N + 1) ⟨z, hzcyc⟩)
    rwa [show (Submodule.Quotient.mk a : RelativeCohomology S (N + 1))
        = RelativeCohomology.mk S (N + 1) a from rfl, relKroneckerH_mk_mk] at hh
  obtain ⟨g, hg⟩ := SingularUniversalCoeff.exists_factor_of_ker_le_ker (relBoundary S N) φ hvanish
  obtain ⟨b, hb⟩ := exists_relCochain_of_functional S g
  have hcobound : (a : relCochains S (N + 1)) = relCoboundaryₗ S N b := by
    apply Subtype.ext
    show (a.1 : SingularCochain X (N + 1)) = coboundary X N b.1
    funext σ
    have e1 : kronecker a.1.1 (Finsupp.single σ 1) = a.1.1 σ := by
      rw [kronecker_single, one_mul]
    have e2 : kronecker (coboundary X N b.1) (Finsupp.single σ 1) = coboundary X N b.1 σ := by
      rw [kronecker_single, one_mul]
    rw [← e1, ← e2,
      ← relKronecker_mk S a.1 (Finsupp.single σ 1),
      show relKronecker S a.1 (RelativeChain.mk S (N + 1) (Finsupp.single σ 1)) = φ (RelativeChain.mk S (N + 1) (Finsupp.single σ 1)) from rfl,
      show φ (RelativeChain.mk S (N + 1) (Finsupp.single σ 1))
        = g (relBoundary S N (RelativeChain.mk S (N + 1) (Finsupp.single σ 1)))
        from (LinearMap.congr_fun hg (RelativeChain.mk S (N + 1) (Finsupp.single σ 1))).symm,
      relBoundary_mk, ← hb, relKronecker_mk, kronecker_coboundary_chainBoundary]
  refine (RelativeCohomology.mk_eq_zero_iff S (N + 1) a).mpr ?_
  rw [hcobound]
  exact ⟨b, rfl⟩

end SKEFTHawking.SingularRelativeUC
