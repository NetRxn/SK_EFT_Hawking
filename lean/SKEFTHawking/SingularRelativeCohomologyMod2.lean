/-
# Phase 5q.F — relative singular ℤ/2 cohomology `Hᵏ(M, S)`

The dual / cohomology analogue of `SingularRelativeHomologyMod2.RelativeHomology`, and the first
foundation brick of Poincaré duality (it is capped with the fundamental class). Relative `n`-cochains
are the singular `n`-cochains that **vanish on the subspace chains** `subspaceChains S n` (the image
of `chainIncl S n`) — i.e. the annihilator of the subcomplex `C_•(S) ↪ C_•(X)` under the Kronecker
pairing `⟨·,·⟩`. The coboundary `δ` preserves this annihilator (adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩` plus
`∂` mapping subspace chains to subspace chains), so we get the relative cochain complex and its
cohomology `Hᵏ(M, S) = ker δ / im δ`, mirroring the absolute `SingularCohomologyMod2.Cohomology`.
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularRelativeCohomologyMod2

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2

variable {X : TopCat} (S : Set X)

/-! ## §1. Relative cochains: the annihilator of the subspace subcomplex -/

/-- **Relative `n`-cochains** `Cⁿ(X, S; ℤ/2)`: the singular `n`-cochains `f` that **vanish on the
subspace chains**, `⟨f, c⟩ = 0` for every `c ∈ subspaceChains S n` (the image of the subspace chain
inclusion `chainIncl S n`). A genuine `ℤ/2`-submodule of `SingularCochain X n` — the annihilator of
the subcomplex `C_•(S) ↪ C_•(X)` under the Kronecker pairing. -/
def relCochains (n : ℕ) : Submodule (ZMod 2) (SingularCochain X n) where
  carrier := { f | ∀ c ∈ subspaceChains S n, kronecker f c = 0 }
  zero_mem' := by
    intro c _
    simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
  add_mem' {f g} hf hg := by
    intro c hc
    rw [kronecker_add_left, hf c hc, hg c hc, add_zero]
  smul_mem' s f hf := by
    intro c hc
    rw [kronecker_smul_left, hf c hc, smul_zero]

theorem mem_relCochains (n : ℕ) (f : SingularCochain X n) :
    f ∈ relCochains S n ↔ ∀ c ∈ subspaceChains S n, kronecker f c = 0 :=
  Iff.rfl

/-! ## §2. The relative coboundary `δ : Cⁿ(X,S) → Cⁿ⁺¹(X,S)` -/

/-- **The coboundary preserves relative cochains.** If `f` vanishes on subspace `n`-chains then `δf`
vanishes on subspace `(n+1)`-chains: for `c ∈ subspaceChains S (n+1)`, the adjunction
`⟨δf, c⟩ = ⟨f, ∂c⟩` (`kronecker_coboundary_chainBoundary`) and `∂c ∈ subspaceChains S n`
(`chainBoundary_mem_subspaceChains`) give `⟨δf, c⟩ = 0`. -/
theorem coboundary_mem_relCochains (n : ℕ) (f : SingularCochain X n) (hf : f ∈ relCochains S n) :
    coboundary X n f ∈ relCochains S (n + 1) := by
  intro c hc
  rw [kronecker_coboundary_chainBoundary]
  exact hf _ (chainBoundary_mem_subspaceChains S n c hc)

/-- The relative coboundary `δⁿ : Cⁿ(X,S) →ₗ Cⁿ⁺¹(X,S)`, the absolute `coboundaryₗ` cod-restricted to
the relative-cochain annihilator submodules (well-defined by `coboundary_mem_relCochains`). -/
noncomputable def relCoboundaryₗ (n : ℕ) :
    relCochains S n →ₗ[ZMod 2] relCochains S (n + 1) :=
  ((coboundaryₗ X n).domRestrict (relCochains S n)).codRestrict (relCochains S (n + 1))
    (fun f => coboundary_mem_relCochains S n f.1 f.2)

@[simp] theorem relCoboundaryₗ_coe (n : ℕ) (f : relCochains S n) :
    (relCoboundaryₗ S n f : SingularCochain X (n + 1)) = coboundary X n f.1 := rfl

/-! ## §3. Relative cohomology `Hⁿ(X, S; ℤ/2) = ker δⁿ / im δⁿ⁻¹` -/

/-- The submodule of relative `n`-coboundaries (image of the incoming relative `δⁿ⁻¹`), `⊥` in degree
`0`. -/
noncomputable def relCoboundaryRange (n : ℕ) : Submodule (ZMod 2) (relCochains S n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (relCoboundaryₗ S m)

/-- Relative coboundaries are relative cocycles, `im δⁿ⁻¹ ≤ ker δⁿ` — well-definedness of relative
cohomology, inherited from the absolute `δ² = 0`. -/
theorem relCoboundaryRange_le_ker (n : ℕ) :
    relCoboundaryRange S n ≤ LinearMap.ker (relCoboundaryₗ S n) := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    show LinearMap.range (relCoboundaryₗ S m) ≤ LinearMap.ker (relCoboundaryₗ S (m + 1))
    rw [LinearMap.range_le_ker_iff]
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    show coboundary X (m + 1) (coboundary X m g.1) = 0
    exact coboundary_comp_coboundary X m g.1

/-- **Relative singular ℤ/2 cohomology** `Hⁿ(X, S; ℤ/2) = ker δⁿ / im δⁿ⁻¹` — a genuine quotient
`ℤ/2`-vector space (the relative cohomology of the pair `(X, S)`), the cohomology analogue of
`RelativeHomology`. -/
def RelativeCohomology (n : ℕ) : Type :=
  (LinearMap.ker (relCoboundaryₗ S n)) ⧸
    (relCoboundaryRange S n).submoduleOf (LinearMap.ker (relCoboundaryₗ S n))

noncomputable instance (n : ℕ) : AddCommGroup (RelativeCohomology S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (RelativeCohomology S n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The relative cohomology class of a relative cocycle. -/
noncomputable def RelativeCohomology.mk (n : ℕ) (z : LinearMap.ker (relCoboundaryₗ S n)) :
    RelativeCohomology S n :=
  Submodule.Quotient.mk z

/-- A relative cohomology class `[z]` vanishes iff its representative cocycle is a relative
coboundary. -/
theorem RelativeCohomology.mk_eq_zero_iff (n : ℕ) (z : LinearMap.ker (relCoboundaryₗ S n)) :
    RelativeCohomology.mk S n z = 0 ↔
      (z : relCochains S n) ∈ relCoboundaryRange S n := by
  constructor
  · intro h
    have h2 : z ∈ (relCoboundaryRange S n).submoduleOf (LinearMap.ker (relCoboundaryₗ S n)) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

end SKEFTHawking.SingularRelativeCohomologyMod2
