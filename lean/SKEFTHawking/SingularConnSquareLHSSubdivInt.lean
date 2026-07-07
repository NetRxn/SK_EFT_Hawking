/-
# Phase 5q.H (E1 CSC-PD tower) — cover-fine subdivision-invariance tools for the integral LHS (hmatch prep)

Integral mirror of the subdivision + cover-partition tools of `SingularConnSquareLHSExplicit` (deferred
from the LHS core). These feed the consumer-site `hmatch` assembly of the integral connecting-square core:
replace the cap cycle `cap g z_K` by its cover-fine iterated subdivision `Sdᵐ(cap g z_K)` (same homology
class), then partition it subordinate to the cover `{val⁻¹U, val⁻¹V}`.

* `homology_mk_singularSd_iterateInt` — subdivision-homology-invariance `[z] = [Sdᵐ z]`. Over ℤ this is
  CLEANER than the mod-2: the chain homotopy `∂Dₘ + Dₘ∂ = 1 − Sdᵐ` (`iterHomotopyInt_chainHomotopy`) gives
  `z − Sdᵐ z = ∂(Dₘ z)` directly — exactly the boundary `Submodule.Quotient.eq` wants, no `x+x=0` juggle.
* `singularSd_iterate_mem_cyclesInt` — `Sdᵐ` preserves cycles.
* `exists_chainIncl_partition_of_mem_mvUnionChainsInt` — `mvUnionChainsInt = C(U') + C(V')` membership
  decomposes as `chainIncl U' zA + chainIncl V' zB` (the cover-partition extraction).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularRelativeMVInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularRelativeMVInt (mvUnionChainsInt)

namespace SKEFTHawking.SingularConnSquareLHSSubdivInt

variable {X : TopCat}

/-- **Subdivision-homology-invariance** (integral). A cycle `z` of degree `n+1` and its iterated
barycentric subdivision `Sdᵐ z` are homologous: `∂(Dₘ z) = z − Sdᵐ z` (`iterHomotopyInt_chainHomotopy`
with `∂z = 0`), so `z − Sdᵐ z` is a boundary and the two classes agree. The homology-level input for
replacing the cap cycle `cap g z_K` by its cover-fine subdivision. (Cleaner over ℤ than the mod-2 —
the signed `1 − Sdᵐ` homotopy lands the difference on the nose.) -/
theorem homology_mk_singularSd_iterateInt (Y : TopCat) (n m : ℕ)
    (z : SingularChainInt Y (n + 1)) (hz : z ∈ cycles Y (n + 1))
    (hSd : (⇑(singularSdInt Y (n + 1)))^[m] z ∈ cycles Y (n + 1)) :
    Homology.mk Y (n + 1) ⟨z, hz⟩
      = Homology.mk Y (n + 1) ⟨(⇑(singularSdInt Y (n + 1)))^[m] z, hSd⟩ := by
  have hz0 : iterHomotopyInt Y n m (0 : SingularChainInt Y n) = 0 := by
    simp only [iterHomotopyInt, map_zero]
    exact Finset.sum_eq_zero (fun i _ => Function.iterate_fixed (map_zero _) i)
  rw [Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).2 ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  refine ⟨iterHomotopyInt Y (n + 1) m z, ?_⟩
  have hcyc : chainBoundary Y n z = 0 := hz
  have hh := iterHomotopyInt_chainHomotopy Y m n z
  rw [hcyc, hz0, add_zero] at hh
  exact hh

/-- `Sdᵐ` of a cycle is a cycle (`Sd` is a chain map, so `∂(Sdᵐ z) = Sdᵐ(∂z) = Sdᵐ 0 = 0`). -/
theorem singularSd_iterate_mem_cyclesInt (Y : TopCat) (n m : ℕ)
    (r : SingularChainInt Y (n + 1)) (hr : r ∈ cycles Y (n + 1)) :
    (⇑(singularSdInt Y (n + 1)))^[m] r ∈ cycles Y (n + 1) := by
  show chainBoundary Y n ((⇑(singularSdInt Y (n + 1)))^[m] r) = 0
  have hr0 : chainBoundary Y n r = 0 := hr
  rw [singularSdInt_iterate_chainBoundary, hr0]
  exact Function.iterate_fixed (map_zero _) m

/-- **mvUnionChainsInt membership ⟹ cover partition** (integral, abstract `M`, `U'`, `V'`). A chain in
`mvUnionChainsInt U' V' n = C(U') + C(V')` decomposes subordinate to the cover as `chainIncl U' zA +
chainIncl V' zB`. -/
theorem exists_chainIncl_partition_of_mem_mvUnionChainsInt {M : TopCat} (U' V' : Set ↑M) (n : ℕ)
    (c : SingularChainInt M n) (hc : c ∈ mvUnionChainsInt U' V' n) :
    ∃ (zA : SingularChainInt (sub U') n) (zB : SingularChainInt (sub V') n),
      c = chainIncl U' n zA + chainIncl V' n zB := by
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hc
  obtain ⟨zA, hzA⟩ := hu
  obtain ⟨zB, hzB⟩ := hv
  exact ⟨zA, zB, by rw [← huv, ← hzA, ← hzB]⟩

end SKEFTHawking.SingularConnSquareLHSSubdivInt
