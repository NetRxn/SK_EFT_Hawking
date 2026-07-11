/-
# Phase 5q.H (E1 CSC-PD tower) — cap of the subdivision homotopy (integral, hcore brick 6e-c1)

The foundational identity for the seam-match core: capping a cochain `g` against the subdivision
chain-homotopy `z − Sdᵐ z = ∂(Dₘ z) + Dₘ(∂z)` (`iterHomotopyInt_chainHomotopy`) gives
  `capInt g z − capInt g (Sdᵐ z) = capInt g (∂(Dₘ z)) + capInt g (Dₘ(∂z))`.
This makes precise the Opus-diagnosed fact that `[capInt g z] = [capInt g (Sdᵐ z)]` is NOT true on the
nose — the two differ by the boundary `∂(capInt g (Dₘ z))` PLUS the `δg`-correction (exposed by
`capInt_leibniz` on the first RHS term) PLUS the `∂z`-term. For a relative cocycle `g` over `(↑K)ᶜ` and
the fundamental cycle `z_K` (whose `∂z_K` sits in `Kᶜ`), the surviving `δg`-correction is exactly the
Mayer–Vietoris connecting content that `relCohomMvConnectingInt` matches (bricks 6e-c2/c3).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularSubdivisionInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt iterHomotopyInt_chainHomotopy)

namespace SKEFTHawking.SingularCapSubdivCorrectionInt

variable {X : TopCat}

/-- **Cap of the subdivision homotopy** (integral). `capInt g z − capInt g (Sdᵐ z)` equals the cap of the
`∂(Dₘ z) + Dₘ(∂z)` homotopy chain — the raw (sign-free) subdivision-correction identity underlying the
seam-match. -/
theorem capInt_sub_singularSd_iterate {k m : ℕ} (g : SingularCochainInt X k) (j : ℕ)
    (z : SingularChainInt X (k + m + 1)) :
    capInt (m := m + 1) g z - capInt (m := m + 1) g ((⇑(singularSdInt X (k + m + 1)))^[j] z)
      = capInt (m := m + 1) g (chainBoundary X (k + m + 1) (iterHomotopyInt X (k + m + 1) j z))
        + capInt (m := m + 1) g (iterHomotopyInt X (k + m) j (chainBoundary X (k + m) z)) := by
  rw [← map_add, iterHomotopyInt_chainHomotopy X j (k + m) z, map_sub]

end SKEFTHawking.SingularCapSubdivCorrectionInt
