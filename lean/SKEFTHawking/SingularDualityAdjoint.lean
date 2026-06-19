import Mathlib
import SKEFTHawking.SingularRelativePairing
import SKEFTHawking.SingularRelativeCohomologyRestrict
import SKEFTHawking.SingularRelativeMV

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5b-adj) — the restriction/inclusion Kronecker adjunction

The relative cohomology restriction `relCohomRestrict` (contravariant, `Hᵏ(M,T) → Hᵏ(M,S)` for `S ⊆ T`)
and the relative homology inclusion `relIncl` (covariant, `Hₙ(M,S) → Hₙ(M,T)`) are **Kronecker-adjoint**:
  `⟨relCohomRestrict h ω, β⟩_S = ⟨ω, relIncl h β⟩_T`     (`ω ∈ Hᵏ(M,T)`, `β ∈ Hₙ(M,S)`).
Both sides are `⟨a, c⟩` for the same underlying cochain `a` and chain `c`, because both maps are induced
by `id_M` (the restriction is the identity on the underlying cochain, the inclusion the identity on the
underlying chain). This is the keystone of the **duality-transfer** route to the relative cohomology MV
exactness: over the field `ℤ/2` the perfect pairing (`SingularRelativeUC`) carries the homology MV
exactness (`SingularRelativeMV`) to the cohomology side via this adjunction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeCohomologyRestrict

namespace SKEFTHawking.SingularDualityAdjoint

variable {M : TopCat}

/-- **The restriction/inclusion Kronecker adjunction** `⟨relCohomRestrict h ω, β⟩ = ⟨ω, relIncl h β⟩`
for `S ⊆ T`, a relative cocycle class `[a] ∈ Hᵏ(M,T)`, and a relative cycle class `[z] ∈ Hₙ(M,S)`. Both
sides equal `⟨a, c⟩` for the underlying cochain `a.1.1` and chain `c` (restriction is the identity on the
underlying cochain, `relCocycleRestrict_coe`; inclusion is `id_M` on the underlying chain,
`relMapChain_mk` + `mapChain_id`). -/
theorem relKroneckerH_relCohomRestrict {S T : Set ↑M} (h : S ⊆ T) {N : ℕ}
    (a : LinearMap.ker (relCoboundaryₗ T (N + 1))) (z : relCycles S (N + 1)) :
    relKroneckerH S (relCohomRestrict h (N + 1) (RelativeCohomology.mk T (N + 1) a))
        (RelativeHomology.mk S (N + 1) z)
      = relKroneckerH T (RelativeCohomology.mk T (N + 1) a)
          (relIncl h (N + 1) (RelativeHomology.mk S (N + 1) z)) := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain S (N + 1))
  rw [relCohomRestrict_mk, relKroneckerH_mk_mk,
    show (z : RelativeChain S (N + 1)) = RelativeChain.mk S (N + 1) c from hc.symm,
    relKronecker_mk, relCocycleRestrict_coe, relCochainRestrict_coe,
    show relIncl h (N + 1) (RelativeHomology.mk S (N + 1) z)
      = RelativeHomology.mk T (N + 1) (relCyclesMap (ContinuousMap.id ↑M) (fun _ hx => h hx) (N + 1) z)
      from rfl,
    relKroneckerH_mk_mk, relCyclesMap_coe,
    show (z : RelativeChain S (N + 1)) = RelativeChain.mk S (N + 1) c from hc.symm,
    relMapChain_mk, SingularFunctoriality.mapChain_id, relKronecker_mk]

end SKEFTHawking.SingularDualityAdjoint
