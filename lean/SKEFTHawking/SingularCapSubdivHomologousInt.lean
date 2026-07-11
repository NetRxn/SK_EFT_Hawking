/-
# Phase 5q.H (E1 CSC-PD tower) — subdivision-cap difference is a boundary (integral, hcore brick 6e-c2)

**Key correction to the seam-match plan (Opus, 2026-07-11): the "surviving δg-correction" is identically
ZERO.** A relative cocycle `g_rep ∈ ker(relCoboundaryIntₗ S k)` is an ABSOLUTE cocycle (`relCoboundaryIntₗ`
unfolds to the absolute `δg_rep = 0`). So capping `δg_rep` against anything vanishes, and the subdivision
correction `capInt a z − capInt a (Sdʲ z)` is a **clean boundary** — no surviving `δg` term. (The MV
connecting content the RHS matches is carried by the cover-split boundary `∂zB`, not a nonzero `capInt δg`.)

`capInt_sub_singularSd_mem_boundariesInt`: for an ABSOLUTE cocycle `a` (`δa=0`) that `S`-vanishes and a
relative cycle `z` (`∂z` `S`-supported), `capInt a z − capInt a (Sdʲ z) = ∂((-1)^k • capInt a (Dⱼ z))`.
Via (c-1) `capInt_sub_singularSd_iterate`: the `Dⱼ ∂z`-term vanishes (`capInt_subspaceChainInt_eq_zero`,
`Dⱼ ∂z` is `S`-supported), the `∂(Dⱼ z)`-term is a boundary (`capInt_cocycle_chainMap`, `δa=0`). Raw-cochain
form (the packaged `ker` form triggers the `whnf` wall); the consumer instantiates
`a := pullbackCochainInt (A∪B) g_rep`. This discharges the `hw` of the genuine-cap partition.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCapSubdivCorrectionInt
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularSubdivisionInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt iterHomotopyInt singularSdInt_iterate_chainBoundary)
open SKEFTHawking.SingularExcisionIsoInt
  (iterHomotopyInt_mem_subspaceChainsInt singularSdInt_iterate_mem_subspaceChainsInt)

namespace SKEFTHawking.SingularCapSubdivHomologousInt

variable {M : TopCat}

/-- **(c-2)** Subdivision correction of an absolute-cocycle cap is a boundary. For an absolute cocycle `a`
(`δa=0`) that `S`-vanishes, and a relative cycle `z` (`∂z` `S`-supported),
`capInt a z − capInt a (Sdʲ z) = ∂((-1)^k • capInt a (Dⱼ z))`: the `δa`-term of cap-Leibniz vanishes
(`δa=0`), the `Dⱼ ∂z`-term vanishes (`Dⱼ ∂z` is `S`-supported, `a` `S`-vanishes). -/
theorem capInt_sub_singularSd_mem_boundariesInt {k m : ℕ} (S : Set ↑M)
    (a : SingularCochainInt M k) (ha : coboundaryₗ M k a = 0)
    (haS : ∀ τ, a (simplexIncl S k τ) = 0)
    (j : ℕ) (z : SingularChainInt M (k + m + 1))
    (hz : chainBoundary M (k + m) z ∈ subspaceChainsInt S (k + m)) :
    capInt (m := m + 1) a z
        - capInt (m := m + 1) a ((⇑(singularSdInt M (k + m + 1)))^[j] z)
      ∈ boundaries M (m + 1) := by
  have hcorr := SKEFTHawking.SingularCapSubdivCorrectionInt.capInt_sub_singularSd_iterate a j z
  have hzero : capInt (m := m + 1) a
      (iterHomotopyInt M (k + m) j (chainBoundary M (k + m) z)) = 0 :=
    capInt_subspaceChainInt_eq_zero S a haS (iterHomotopyInt_mem_subspaceChainsInt hz j)
  rw [hcorr, hzero, add_zero]
  refine ⟨(-1 : ℤ) ^ k • capInt (m := m + 2) a (iterHomotopyInt M (k + m + 1) j z), ?_⟩
  rw [map_smul, capInt_cocycle_chainMap (m := m + 1) a ha (iterHomotopyInt M (k + m + 1) j z),
    smul_smul, ← pow_add, ← two_mul, pow_mul, show ((-1 : ℤ) ^ 2) ^ k = 1 by norm_num, one_smul]
  rfl

end SKEFTHawking.SingularCapSubdivHomologousInt
