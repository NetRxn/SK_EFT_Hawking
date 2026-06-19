import Mathlib
import SKEFTHawking.SingularRelativeUC

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6d-A1) — finite-dim-free relative UC surjectivity

The relative Kronecker pairing `relKroneckerH S : Hⁿ(M,S) → (Hₙ(M,S))^*` is **surjective over the field
`ℤ/2`** — with **no finite-dimensionality hypothesis** (the finite-dim in `SingularDualityFinrank` was an
artifact of the dimension-count surjectivity proof; over a field, universal coefficients
`Hⁿ ≅ Hom(Hₙ, k)` is *always* an isomorphism). Every functional on relative homology is realized by a
relative cohomology class: pull `φ` back to the relative cycles, **extend** it to all relative chains
(`LinearMap.exists_extend`, every subspace of a `ℤ/2`-vector space is complemented), realize the
extension as `relKronecker a` for a relative cochain `a` (`exists_relCochain_of_functional`); `a` is a
**cocycle** because the extension kills relative boundaries (the adjunction `relKronecker_relBoundary`),
and `[a]` pairs to `φ`.

This **removes the finite-dimensionality hypothesis from `relCohomMv_exact_middle`** (path A), unblocking
the compactly-supported-cohomology colimit Mayer–Vietoris over *all* compacts (no good-compact reframe).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.SingularRelativeUCSurj

variable {X : TopCat} (S : Set X)

/-- **Finite-dim-free relative universal coefficients (surjectivity)**: every functional on relative
homology `Hₙ(M,S)` is `relKroneckerH` of a relative cohomology class — over the field `ℤ/2`, no
finite-dimensionality needed. -/
theorem relKroneckerH_surjective_field {N : ℕ} :
    Function.Surjective (relKroneckerH S (N := N)) := by
  intro φ
  -- Pull `φ` back along the homology quotient to a functional on the relative cycles.
  set ψ : ↥(relCycles S (N + 1)) →ₗ[ZMod 2] ZMod 2 :=
    φ.comp ((relBoundaries S (N + 1)).submoduleOf (relCycles S (N + 1))).mkQ with hψ
  -- Extend it to all relative chains (every subspace is complemented over `ℤ/2`).
  obtain ⟨F, hF⟩ := LinearMap.exists_extend ψ
  -- Realize `F` as `relKronecker a` for a relative cochain `a`.
  obtain ⟨a, ha⟩ := exists_relCochain_of_functional S F
  -- `F` agrees with `ψ` on relative cycles.
  have hFcyc : ∀ z : ↥(relCycles S (N + 1)), F (z : RelativeChain S (N + 1)) = ψ z :=
    fun z => LinearMap.congr_fun hF z
  -- `F` kills relative boundaries (`ψ` does — they are `0` in homology).
  have hFbd : ∀ w : RelativeChain S (N + 2),
      F (relBoundary S (N + 1) w) = 0 := by
    intro w
    have hmem : relBoundary S (N + 1) w ∈ relBoundaries S (N + 1) :=
      ⟨w, rfl⟩
    have hcyc : relBoundary S (N + 1) w ∈ relCycles S (N + 1) :=
      relBoundaries_le_relCycles S (N + 1) hmem
    have hzero : ((relBoundaries S (N + 1)).submoduleOf (relCycles S (N + 1))).mkQ
        ⟨relBoundary S (N + 1) w, hcyc⟩ = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_comap.mpr hmem
    have h1 : F (relBoundary S (N + 1) w) = ψ ⟨relBoundary S (N + 1) w, hcyc⟩ :=
      hFcyc ⟨relBoundary S (N + 1) w, hcyc⟩
    rw [h1]
    show φ (((relBoundaries S (N + 1)).submoduleOf (relCycles S (N + 1))).mkQ
      ⟨relBoundary S (N + 1) w, hcyc⟩) = 0
    rw [hzero]
    exact map_zero φ
  -- Hence `a` is a relative cocycle: `relKronecker (δa) w = relKronecker a (∂w) = F (∂w) = 0`.
  have hcocycle : a ∈ LinearMap.ker (relCoboundaryₗ S (N + 1)) := by
    rw [LinearMap.mem_ker]
    have hkz : ∀ w : RelativeChain S (N + 2),
        relKronecker S (relCoboundaryₗ S (N + 1) a) w = 0 := by
      intro w
      rw [← relKronecker_relBoundary, ha, hFbd]
    -- a functional `relKronecker (δa)` that is `0` on every chain forces `δa = 0`.
    apply Subtype.ext
    show (relCoboundaryₗ S (N + 1) a).1 = 0
    funext σ
    have := hkz (RelativeChain.mk S (N + 2) (Finsupp.single σ 1))
    rw [relKronecker_mk, kronecker_single, one_mul] at this
    exact this
  -- `[a]` pairs to `φ`.
  refine ⟨RelativeCohomology.mk S (N + 1) ⟨a, hcocycle⟩, ?_⟩
  ext z'
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
  rw [show (Submodule.Quotient.mk z : RelativeHomology S (N + 1))
      = RelativeHomology.mk S (N + 1) z from rfl, relKroneckerH_mk_mk,
    LinearMap.congr_fun ha (z : RelativeChain S (N + 1)), hFcyc z, hψ, LinearMap.comp_apply]
  rfl

end SKEFTHawking.SingularRelativeUCSurj
