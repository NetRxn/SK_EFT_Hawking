import Mathlib
import SKEFTHawking.SingularCapHomology
import SKEFTHawking.SingularConnSquareLHSExplicit

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — cap–homology subdivision-invariance

`cap_homology_singularSd_iterate`: the homology class of a cap `a ⌢ z` is unchanged by barycentric
subdivision of the cycle `z` — `[a ⌢ z] = [a ⌢ Sdʲz]`. It is just `capHomology` (well-defined on
homology classes) applied to the homology subdivision-invariance `homology_mk_singularSd_iterate`.

The connecting-square `hLHS` chains the legW cap class `[cap g̃ z_K_sub]` to `[cap g̃ Sdᵐz_K_sub]`
(whose EXACT cover-partition `exists_cap_cover_partition` provides), so this is the link that lets the
clean cap-realized V-part be used in place of the given `zB`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularCapHomology SKEFTHawking.SingularConnSquareLHSExplicit

namespace SKEFTHawking.SingularCapHomologySubdiv

variable {X : TopCat}

/-- **Cap–homology subdivision-invariance**: `[a ⌢ z] = [a ⌢ Sdʲz]` (capHomology applied to the homology
subdivision-invariance). -/
theorem cap_homology_singularSd_iterate {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (z : cycles X (k + m + 1)) (j : ℕ) :
    Homology.mk X (m + 1) (capCyclesₗ a z)
      = Homology.mk X (m + 1) (capCyclesₗ a
          ⟨(⇑(SingularSubdivision.singularSd X (k + m + 1)))^[j] z.1,
            singularSd_iterate_mem_cycles X (k + m) j z.1 z.2⟩) := by
  rw [← capHomology_mk, ← capHomology_mk]
  exact congrArg (capHomology a) (homology_mk_singularSd_iterate X (k + m) j z.1 z.2 _)

/-- **Cocycle-absorb / Kronecker class-invariance**: a cocycle `fc` pairs equally against homologous
cycles — `[c] = [c']` ⟹ `⟨fc, c⟩ = ⟨fc, c'⟩`. (The Kronecker pairing `kroneckerH` is well-defined on
homology classes; `kroneckerH_mk_mk` lowers it to the chain pairing.) Lets the connecting-square `hLHS`
swap the given seam cycle `seam ∂zB` for the clean cap-realized `seam ∂zB'` once their classes agree
(`boundaryExtract_class_eq_of_partition_homologous`). -/
theorem kronecker_eq_of_homology_eq {n : ℕ} (fc : LinearMap.ker (coboundaryₗ X n))
    (c c' : cycles X n) (h : Homology.mk X n c = Homology.mk X n c') :
    kronecker fc.1 c.1 = kronecker fc.1 c'.1 := by
  rw [← kroneckerH_mk_mk fc c, ← kroneckerH_mk_mk fc c']
  exact congrArg (kroneckerH n (Submodule.Quotient.mk fc)) h

end SKEFTHawking.SingularCapHomologySubdiv
