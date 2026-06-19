import Mathlib
import SKEFTHawking.SingularKroneckerFunctoriality
import SKEFTHawking.SingularSubHomologyMV

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-R1b) — the seam-dual pairing transport

Specializing the Kronecker/`Homology.map` naturality `kroneckerH_Homology_map` (R1a) to the two seam
isomorphisms `subSeamEquiv` (= `seamI`) and `seamHomologyEquiv` (= `seamHom`). Both are `Homology.map`
of a homeomorphism, so pairing a cohomology class through them — in the **forward** direction, which is
all the *direct* `hcore` pairing needs (`subHomConnecting = seamI ∘ seamHom ∘ mvConnecting`) — equals the
cochain pullback. These pre-tested abstract reductions de-risk the final whnf-wall-prone LHS assembly.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularSubHomologyMV SKEFTHawking.SingularMayerVietorisLES

namespace SKEFTHawking.SingularSeamDualPairing

variable {X : TopCat}

/-- **Seam-dual transport through `subSeamEquiv`** (= `seamI`): pairing `a` against the seam image of a
cycle class equals pairing the cochain pullback (along `subSeamHomeo`) against the cycle. -/
theorem kroneckerH_subSeamEquiv {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ (sub T) n)) (z : cycles (sub R) n) :
    kroneckerH (X := sub T) n (Submodule.Quotient.mk a)
        (subSeamEquiv hTS hmem n (Homology.mk (sub R) n z))
      = kroneckerH (X := sub R) n
          (Submodule.Quotient.mk
            ⟨pullbackCochainMap ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n a.1,
              pullbackCochainMap_mem_ker _ n a⟩)
          (Homology.mk (sub R) n z) := by
  rw [subSeamEquiv_apply, kroneckerH_Homology_map]

/-- **Seam-dual transport through `seamHomologyEquiv`** (= `seamHom`): same, along `seamHomeo`. -/
theorem kroneckerH_seamHomologyEquiv (A B : Set ↑X) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ (sub (A ∩ B)) n)) (z : cycles (sub (restr A B)) n) :
    kroneckerH (X := sub (A ∩ B)) n (Submodule.Quotient.mk a)
        (seamHomologyEquiv A B n (Homology.mk (sub (restr A B)) n z))
      = kroneckerH (X := sub (restr A B)) n
          (Submodule.Quotient.mk
            ⟨pullbackCochainMap ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n a.1,
              pullbackCochainMap_mem_ker _ n a⟩)
          (Homology.mk (sub (restr A B)) n z) := by
  rw [seamHomologyEquiv, LinearEquiv.ofBijective_apply, kroneckerH_Homology_map]

end SKEFTHawking.SingularSeamDualPairing
