import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD4b) — the relative Kronecker pairing

The Kronecker pairing descends to relative (co)homology: a **relative cochain** `a` (vanishing on the
subspace chains `subspaceChains S`) pairs with a **relative chain** `[c] ∈ RelativeChain S n` via
`⟨a, [c]⟩ = ⟨a, c⟩`, well-defined because `a` kills the subspace chains. This is the relative analogue of
`kroneckerH` and the pairing that exhibits `Hᵏ(M, S)` as dual to `Hₙ(M, S)` (relative universal
coefficients), used for the local cohomology `Hⁿ(M|x) ≅ ℤ/2` in the Poincaré-duality base case.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.SingularRelativePairing

variable {X : TopCat} (S : Set X)

/-- **The relative Kronecker pairing on relative chains** `relKronecker a : RelativeChain S n → ℤ/2`,
`[c] ↦ ⟨a, c⟩` for a relative cochain `a` (`a ∈ relCochains S n`, i.e. `a` vanishes on `subspaceChains S`).
Well-defined: `a` kills the subspace chains, so `kronecker a.1 ·` descends through `RelativeChain`. -/
noncomputable def relKronecker {n : ℕ} (a : relCochains S n) :
    RelativeChain S n →ₗ[ZMod 2] ZMod 2 :=
  Submodule.liftQ (subspaceChains S n) (kroneckerₗ n a.1) (fun c hc => a.2 c hc)

@[simp] theorem relKronecker_mk {n : ℕ} (a : relCochains S n) (c : SingularChain X n) :
    relKronecker S a (RelativeChain.mk S n c) = kronecker a.1 c := rfl

/-- **The relative Kronecker pairing is `ℤ/2`-bilinear** `relCochains S n →ₗ (RelativeChain S n →ₗ ℤ/2)`
(linear in the relative chain by construction, in the relative cochain since `kroneckerₗ` is). -/
noncomputable def relKroneckerₗ {n : ℕ} :
    relCochains S n →ₗ[ZMod 2] RelativeChain S n →ₗ[ZMod 2] ZMod 2 where
  toFun := relKronecker S
  map_add' a b := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(a + b)) c = kronecker (↑a) c + kronecker (↑b) c
    rw [Submodule.coe_add, kronecker_add_left]
  map_smul' s a := by
    ext q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show kronecker (↑(s • a)) c = s * kronecker (↑a) c
    rw [SetLike.val_smul, kronecker_smul_left, smul_eq_mul]

/-- **The relative adjunction** `⟨a, ∂[w]⟩ = ⟨δa, [w]⟩` for the relative Kronecker pairing — descends the
absolute adjunction `kronecker_coboundary_chainBoundary` through the relative chain quotient. -/
theorem relKronecker_relBoundary {n : ℕ} (a : relCochains S n) (w : RelativeChain S (n + 1)) :
    relKronecker S a (relBoundary S n w) = relKronecker S (relCoboundaryₗ S n a) w := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  show relKronecker S a (relBoundary S n (RelativeChain.mk S (n + 1) c))
    = kronecker (relCoboundaryₗ S n a).1 c
  rw [relBoundary_mk, relKronecker_mk, relCoboundaryₗ_coe, kronecker_coboundary_chainBoundary]

/-- **The relative Kronecker pairing descends to relative homology** for a fixed **relative cocycle** `a`
(`a ∈ ker (relCoboundaryₗ S n)`): `relKroneckerRightH a : RelativeHomology S n → ℤ/2`, `[z] ↦ ⟨a, z⟩`.
Well-defined: `a` a relative cocycle ⟹ `relKronecker a` kills the relative boundaries (relative
adjunction `relKronecker_relBoundary`). The relative analogue of `kroneckerRightH`. -/
noncomputable def relKroneckerRightH {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S n)) :
    RelativeHomology S n →ₗ[ZMod 2] ZMod 2 :=
  Submodule.liftQ _ ((relKronecker S a.1).domRestrict (relCycles S n))
    (fun z hz => by
      obtain ⟨w, hw⟩ := hz
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply,
        show (z : RelativeChain S n) = relBoundary S n w from hw.symm,
        relKronecker_relBoundary, show relCoboundaryₗ S n a.1 = 0 from LinearMap.mem_ker.mp a.2]
      exact congrFun (congrArg DFunLike.coe (map_zero (relKroneckerₗ S))) w)

@[simp] theorem relKroneckerRightH_mk {n : ℕ} (a : LinearMap.ker (relCoboundaryₗ S n))
    (z : relCycles S n) :
    relKroneckerRightH S a (RelativeHomology.mk S n z) = relKronecker S a.1 z.1 := rfl

/-- **`relKroneckerRightH` is `ℤ/2`-linear in the relative cocycle** — packaged
`ker (relCoboundaryₗ S n) →ₗ (RelativeHomology S n →ₗ ℤ/2)`. -/
noncomputable def relKroneckerRightHₗ {n : ℕ} :
    LinearMap.ker (relCoboundaryₗ S n) →ₗ[ZMod 2] RelativeHomology S n →ₗ[ZMod 2] ZMod 2 where
  toFun := relKroneckerRightH S
  map_add' a b := by
    ext q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (relKroneckerₗ S (↑(a + b))) z.1 = (relKroneckerₗ S a.1) z.1 + (relKroneckerₗ S b.1) z.1
    rw [Submodule.coe_add, map_add, LinearMap.add_apply]
  map_smul' s a := by
    ext q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    show (relKroneckerₗ S (↑(s • a))) z.1 = s * (relKroneckerₗ S a.1) z.1
    rw [SetLike.val_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **A relative coboundary pairs to `0` with every relative cycle**: `relKroneckerRightH (δg) = 0`. By
the relative adjunction `relKronecker (δg) z = relKronecker g (∂z)` and `∂z = 0` for a relative cycle `z`.
The well-definedness for descending the pairing through the relative cohomology quotient. -/
theorem relKroneckerRightH_relCoboundary {N : ℕ} (g : relCochains S N)
    (hb : (relCoboundaryₗ S N g : relCochains S (N + 1)) ∈
      LinearMap.ker (relCoboundaryₗ S (N + 1))) :
    relKroneckerRightHₗ S ⟨relCoboundaryₗ S N g, hb⟩ = 0 := by
  ext q
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  show relKronecker S (relCoboundaryₗ S N g) z.1 = 0
  rw [← relKronecker_relBoundary, show relBoundary S N z.1 = 0 from
    LinearMap.mem_ker.mp z.2, map_zero]

/-- **The relative Kronecker pairing on (co)homology classes** `relKroneckerH : Hᵏ(M,S) → Hₙ(M,S) → ℤ/2`
(`k = N+1`), the relative analogue of `kroneckerH`. Descends `relKroneckerRightHₗ` through the relative
cohomology quotient — well-defined since a relative coboundary pairs to `0`
(`relKroneckerRightH_relCoboundary`). The pairing that exhibits relative universal coefficients
(`Hⁿ(M,S) ≅ Hom(Hₙ(M,S), ℤ/2)`), used for `Hⁿ(M|x) ≅ ℤ/2`. -/
noncomputable def relKroneckerH {N : ℕ} :
    RelativeCohomology S (N + 1) →ₗ[ZMod 2] RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2 :=
  Submodule.liftQ _ (relKroneckerRightHₗ S) (by
    intro b hb
    rw [LinearMap.mem_ker]
    have hb' : (b : relCochains S (N + 1)) ∈ relCoboundaryRange S (N + 1) := hb
    rw [show relCoboundaryRange S (N + 1) = LinearMap.range (relCoboundaryₗ S N) from rfl,
      LinearMap.mem_range] at hb'
    obtain ⟨g, hg⟩ := hb'
    rw [show b = ⟨relCoboundaryₗ S N g, hg ▸ b.2⟩ from Subtype.ext hg.symm]
    exact relKroneckerRightH_relCoboundary S g _)

@[simp] theorem relKroneckerH_mk_mk {N : ℕ} (a : LinearMap.ker (relCoboundaryₗ S (N + 1)))
    (z : relCycles S (N + 1)) :
    relKroneckerH S (RelativeCohomology.mk S (N + 1) a) (RelativeHomology.mk S (N + 1) z)
      = relKronecker S a.1 z.1 := rfl

end SKEFTHawking.SingularRelativePairing
