import Mathlib
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularRelativeCohomologyMVConnecting
import SKEFTHawking.SingularRelativeMV

/-!
# Phase 5q.F (PD6f-c4-RHS-final) — firing the `relCohomMvConnecting` adjunction on the RHS

This file lifts the relative cap–Kronecker bridge
`SingularCapSubKDuality.kroneckerH_relativeDualityK_mk_eq_relKroneckerH` from a fixed cocycle
representative `ω` to an arbitrary relative-cohomology *class* `Ω`, then specializes
`S := U' ∪ V'`, `Ω := relCohomMvConnecting U' V' …` and fires the relative-cohomology
Mayer–Vietoris connecting adjunction
`SingularRelativeCohomologyMVConnecting.relKroneckerH_relCohomMvConnecting`
to move the connecting homomorphism off the cohomology side onto the homology side
(as `relMvDelta`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularRelativePairing
  SKEFTHawking.SingularCapSubKDuality SKEFTHawking.SingularRelativeMV
  SKEFTHawking.SingularRelativeCohomologyMVConnecting

namespace SKEFTHawking.SingularConnSquareRHSAdjoint

variable {X : TopCat}

/-- **Class-level relative cap–Kronecker bridge**: the bridge
`kroneckerH_relativeDualityK_mk_eq_relKroneckerH`, lifted from a fixed cocycle representative `ω`
to an arbitrary relative-cohomology class `Ω : RelativeCohomology S (k+1)`. The right-hand homology
class `[chainIncl (a' ⌢ʳ z_sub)]` is `ω`-independent, so the rel-cycle witness is supplied uniformly
by `chainIncl_rcap_mem_relCycles`. -/
theorem kroneckerH_relativeDualityK_eq_relKroneckerH {k m : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1 + m + 1)) (hzK : z ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) (Ω : RelativeCohomology S (k + 1)) :
    kroneckerH (X := sub K) (m + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S K (k + 1) m z hzK hzS Ω)
      = relKroneckerH S Ω (RelativeHomology.mk S (k + 1)
          ⟨RelativeChain.mk S (k + 1)
              (chainIncl K (k + 1) (rcap a'.1
                ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))),
            chainIncl_rcap_mem_relCycles z hzK hzS a'⟩) := by
  induction Ω using Submodule.Quotient.induction_on with
  | _ ω =>
    exact kroneckerH_relativeDualityK_mk_eq_relKroneckerH z hzK hzS ω a'
      (chainIncl_rcap_mem_relCycles z hzK hzS a')

/-- **Firing the relative-cohomology MV connecting adjunction on the RHS of the connecting square.**
Specializing `kroneckerH_relativeDualityK_eq_relKroneckerH` at `S := U' ∪ V'` and
`Ω := relCohomMvConnecting U' V' hU' hV' N σ`, then applying
`SingularRelativeCohomologyMVConnecting.relKroneckerH_relCohomMvConnecting`, moves the
relative-cohomology connecting homomorphism off the cohomology argument `σ` and onto the homology
class as `relMvDelta`. This is the final RHS step of the PD6f connecting square: the `sub K`-Kronecker
pairing of `a'` against the PD image of the MV-connecting class equals the `(U'∩V')`-relative pairing
of `σ` against `relMvDelta` of the (ω-independent) capped cycle. -/
theorem kroneckerH_relativeDualityK_relCohomMvConnecting {p : ℕ} {U' V' K : Set ↑X}
    (hU' : IsOpen U') (hV' : IsOpen V') {N : ℕ}
    (z : SingularChain X (N + 1 + 1 + p + 1)) (hzK : z ∈ subspaceChains K (N + 1 + 1 + p + 1))
    (hzS : chainBoundary X (N + 1 + 1 + p) z ∈ subspaceChains (U' ∪ V') (N + 1 + 1 + p))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (p + 1)))
    (σ : RelativeCohomology (U' ∩ V') (N + 1)) :
    kroneckerH (X := sub K) (p + 1) (Submodule.Quotient.mk a')
        (relativeDualityK (U' ∪ V') K (N + 1 + 1) p z hzK hzS
          (relCohomMvConnecting U' V' hU' hV' N σ))
      = relKroneckerH (U' ∩ V') σ
          (relMvDelta U' V' hU' hV' (N + 1)
            (RelativeHomology.mk (U' ∪ V') (N + 1 + 1)
              ⟨RelativeChain.mk (U' ∪ V') (N + 1 + 1)
                  (chainIncl K (N + 1 + 1) (rcap a'.1
                    ((subspaceChainsEquiv K (N + 1 + 1 + p + 1)).symm ⟨z, hzK⟩))),
                chainIncl_rcap_mem_relCycles z hzK hzS a'⟩)) := by
  rw [kroneckerH_relativeDualityK_eq_relKroneckerH, relKroneckerH_relCohomMvConnecting]

end SKEFTHawking.SingularConnSquareRHSAdjoint
