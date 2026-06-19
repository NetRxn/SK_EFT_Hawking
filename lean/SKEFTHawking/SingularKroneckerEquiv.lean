import Mathlib
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularCohomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick PD6f-c4-L1a) — the absolute perfect-pairing Kronecker `LinearEquiv`

Over the field `ℤ/2` the absolute Kronecker pairing
`kroneckerH : Hᵏ(X) → (Hₖ(X))^*` is a **bijection** — injective by universal coefficients
(`cohomology_eq_zero_of_kroneckerH`, finite-dim-free UC) and surjective by the finite-dim-free
field surjectivity (`kroneckerH_surjective_field`, this file). This packages the two halves
into a `LinearEquiv`
  `kroneckerHEquiv N : Hᵏ(X) ≃ₗ (Hₖ(X))^*`  (`k = N+1`),
the absolute analogue of `SingularRelativeKroneckerEquiv.relKroneckerHEquiv` — the perfect pairing
`Hᵏ(X) ≃ (Hₖ(X))^*` over `ℤ/2`.

The **surjectivity** half mirrors `SingularRelativeUCSurj.relKroneckerH_surjective_field` with the
subspace `S` dropped: lift a functional `φ : Hₖ(X) → ℤ/2` along the cycle quotient to the cycles,
**extend** it to all chains (`LinearMap.exists_extend`, every subspace of a `ℤ/2`-vector space is
complemented), realize the extension as `kronecker f` for a cochain `f`
(`exists_cochain_of_functional`); `f` is a **cocycle** because the extension kills boundaries (the
adjunction `kronecker_coboundary_chainBoundary`), and `[f]` pairs to `φ`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularUniversalCoeff

namespace SKEFTHawking.SingularKroneckerEquiv

variable {X : TopCat}

/-- **Finite-dim-free absolute universal coefficients (surjectivity)**: every functional on
homology `Hₖ(X)` is `kroneckerH` of a cohomology class — over the field `ℤ/2`, no
finite-dimensionality needed. The absolute analogue of `relKroneckerH_surjective_field`. -/
theorem kroneckerH_surjective_field {N : ℕ} :
    Function.Surjective (kroneckerH (X := X) (N + 1)) := by
  intro φ
  -- Pull `φ` back along the homology quotient to a functional on the cycles.
  set ψ : ↥(cycles X (N + 1)) →ₗ[ZMod 2] ZMod 2 :=
    φ.comp ((boundaries X (N + 1)).submoduleOf (cycles X (N + 1))).mkQ with hψ
  -- Extend it to all chains (every subspace is complemented over `ℤ/2`).
  obtain ⟨F, hF⟩ := LinearMap.exists_extend ψ
  -- Realize `F` as `kronecker f` for a cochain `f`.
  obtain ⟨f, hf⟩ := exists_cochain_of_functional F
  -- `F` agrees with `ψ` on cycles.
  have hFcyc : ∀ z : ↥(cycles X (N + 1)), F (z : SingularChain X (N + 1)) = ψ z :=
    fun z => LinearMap.congr_fun hF z
  -- `F` kills boundaries (`ψ` does — they are `0` in homology).
  have hFbd : ∀ w : SingularChain X (N + 2),
      F (chainBoundary X (N + 1) w) = 0 := by
    intro w
    have hmem : chainBoundary X (N + 1) w ∈ boundaries X (N + 1) :=
      ⟨w, rfl⟩
    have hcyc : chainBoundary X (N + 1) w ∈ cycles X (N + 1) :=
      boundaries_le_cycles X (N + 1) hmem
    have hzero : ((boundaries X (N + 1)).submoduleOf (cycles X (N + 1))).mkQ
        ⟨chainBoundary X (N + 1) w, hcyc⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hmem
    have h1 : F (chainBoundary X (N + 1) w) = ψ ⟨chainBoundary X (N + 1) w, hcyc⟩ :=
      hFcyc ⟨chainBoundary X (N + 1) w, hcyc⟩
    rw [h1]
    show φ (((boundaries X (N + 1)).submoduleOf (cycles X (N + 1))).mkQ
      ⟨chainBoundary X (N + 1) w, hcyc⟩) = 0
    rw [hzero]
    exact map_zero φ
  -- Hence `f` is a cocycle: `kronecker (δf) w = kronecker f (∂w) = F (∂w) = 0`.
  have hcocycle : f ∈ LinearMap.ker (coboundaryₗ X (N + 1)) := by
    rw [LinearMap.mem_ker]
    have hkz : ∀ w : SingularChain X (N + 2),
        kronecker (coboundaryₗ X (N + 1) f) w = 0 := by
      intro w
      rw [show (coboundaryₗ X (N + 1) f : SingularCochain X (N + 2))
            = coboundary X (N + 1) f from rfl,
        kronecker_coboundary_chainBoundary, hf, hFbd]
    -- a functional `kronecker (δf)` that is `0` on every chain forces `δf = 0`.
    funext σ
    have := hkz (Finsupp.single σ 1)
    rw [kronecker_single, one_mul] at this
    exact this
  -- `[f]` pairs to `φ`.
  refine ⟨Cohomology.mk X (N + 1) ⟨f, hcocycle⟩, ?_⟩
  ext z'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
  show kronecker f (z : SingularChain X (N + 1)) = φ (Submodule.Quotient.mk z)
  rw [hf (z : SingularChain X (N + 1)), hFcyc z, hψ, LinearMap.comp_apply]
  rfl

/-- **The absolute UC injectivity** — `kroneckerH` is injective: a cohomology class that pairs to `0`
with every homology class is `0` (`cohomology_eq_zero_of_kroneckerH`, finite-dim-free UC). -/
theorem kroneckerH_injective (N : ℕ) :
    Function.Injective (kroneckerH (X := X) (N + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  refine cohomology_eq_zero_of_kroneckerH N ω (fun β => ?_)
  rw [hω, LinearMap.zero_apply]

/-- **The perfect-pairing Kronecker isomorphism** `Hᵏ(X) ≃ (Hₖ(X))^*` over `ℤ/2` (`k = N+1`):
injective (UC) + surjective (field UC), both finite-dim-free. The absolute analogue of
`relKroneckerHEquiv`. -/
noncomputable def kroneckerHEquiv (N : ℕ) :
    Cohomology X (N + 1) ≃ₗ[ZMod 2] (Homology X (N + 1) →ₗ[ZMod 2] ZMod 2) :=
  LinearEquiv.ofBijective (kroneckerH (N + 1))
    ⟨kroneckerH_injective N, kroneckerH_surjective_field⟩

@[simp] theorem kroneckerHEquiv_apply (N : ℕ) (ω : Cohomology X (N + 1)) :
    kroneckerHEquiv N ω = kroneckerH (N + 1) ω :=
  rfl

/-- The defining round-trip of the symm direction in `kroneckerH` form: `⟨(symm φ), ·⟩ = φ`. The
load-bearing identity for the cohomology-MV connecting-map adjunction. -/
theorem kroneckerH_symm (N : ℕ)
    (φ : Homology X (N + 1) →ₗ[ZMod 2] ZMod 2) :
    kroneckerH (N + 1) ((kroneckerHEquiv N).symm φ) = φ := by
  rw [← kroneckerHEquiv_apply, LinearEquiv.apply_symm_apply]

end SKEFTHawking.SingularKroneckerEquiv
