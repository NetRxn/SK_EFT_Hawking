import Mathlib
import SKEFTHawking.SingularConnSquareCloseNC
import SKEFTHawking.SingularLocalDualityKBot

/-!
# Phase 5q.G (G1 PD-induction, brick B2/J₀) — the BOTTOM double-support δφ-kill

The bottom (`cap (m := 0)`) mirror of Brick J
(`SingularConnSquareCloseNC.cap_relCochains_pair_double_support_eq_boundary`, whose output
`cap (m := n+1) a c = ∂E` is `(n+1)`-indexed and cannot hit the bottom): for a cocycle `a`
vanishing on both cover legs and a `P`-supported chain `c` (same degree as `a`) that is
rel-`(A∪B)` null-homologous via an ambient bound, the bottom cap `cap (m := 0) a c` is the
boundary of a **`P`-supported `1`-chain**. Internals mirror J 1:1 (small-`D` cover split,
`b`-collection with double support, leg-split kill, homotopy bound) at the degree map
`(m := n+1) → (m := 0)`, `(m := n+1+1) → (m := 1)`, `k+n+1 → q+1`, `k+n → q`; the boundary
membership at the end is the plain `boundaries _ 0 = range (chainBoundary _ 0)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularExcision SKEFTHawking.SingularMayerVietoris
  SKEFTHawking.SingularCapSupport SKEFTHawking.SingularConnSquareCloseNC

namespace SKEFTHawking.SingularConnSquareCloseNCBot

variable {X : TopCat} [T2Space ↑X]

/-- **The bottom double-support δφ-kill** (Brick J₀): `cap (m := 0) a c = ∂E` with
`E ∈ subspaceChains P 1`. -/
theorem cap_relCochains_pair_double_support_eq_boundary₀ {A B P : Set ↑X}
    (hA : IsOpen A) (hB : IsOpen B) (hP : IsOpen P)
    (hcover : P ∪ (A ∪ B) = Set.univ) {q : ℕ}
    (a : SingularCochain X (q + 1)) (hac : coboundary X (q + 1) a = 0)
    (haA : a ∈ relCochains A (q + 1)) (haB : a ∈ relCochains B (q + 1))
    (c : SingularChain X (q + 1)) (hcP : c ∈ subspaceChains P (q + 1))
    (D : SingularChain X (q + 1 + 1)) (ρ : SingularChain X (q + 1))
    (hρ : ρ ∈ subspaceChains (A ∪ B) (q + 1))
    (heq : c = chainBoundary X (q + 1) D + ρ)
    (u' : SingularChain (sub A) q) (w' : SingularChain (sub B) q)
    (hbd : chainBoundary X q c = chainIncl A q u' + chainIncl B q w') :
    ∃ E : SingularChain X (0 + 1), E ∈ subspaceChains P (0 + 1)
      ∧ cap (m := 0) a c = chainBoundary X 0 E := by
  have hadd : ∀ (d : ℕ) (j : ℕ) (x y : SingularChain X d),
      SingularSubdivision.iterHomotopy X d j (x + y)
        = SingularSubdivision.iterHomotopy X d j x + SingularSubdivision.iterHomotopy X d j y := by
    intro d j x y
    simp [SingularSubdivision.iterHomotopy, map_add, Finset.sum_add_distrib]
  -- small D over the total cover (P, A∪B)
  have hDmem : D ∈ subspaceChains (P ∪ (A ∪ B)) (q + 1 + 1) :=
    SingularExcision.mem_subspaceChains_of_support (fun τ _ => by
      rw [hcover]; exact Set.subset_univ _)
  obtain ⟨ν, D₁, D₂, hD₁, hD₂, hDsplit⟩ :=
    exists_iterate_cover_split_amb hP (hA.union hB) D hDmem
  have hhD := SingularSubdivision.iterHomotopy_chainHomotopy X ν (q + 1) D
  have hDbnd : chainBoundary X (q + 1) D
      = chainBoundary X (q + 1) D₁ + chainBoundary X (q + 1) D₂
        + chainBoundary X (q + 1)
            (SingularSubdivision.iterHomotopy X (q + 1) ν
              (chainBoundary X (q + 1) D)) := by
    have h1 := congrArg (chainBoundary X (q + 1)) hhD
    rw [map_add, map_add, chainBoundary_chainBoundary_apply, zero_add, hDsplit, map_add] at h1
    rw [h1]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hTsplit : SingularSubdivision.iterHomotopy X (q + 1) ν
      (chainBoundary X (q + 1) D)
      = SingularSubdivision.iterHomotopy X (q + 1) ν c
        + SingularSubdivision.iterHomotopy X (q + 1) ν ρ := by
    rw [show chainBoundary X (q + 1) D = c + ρ from by
        rw [heq]; abel_nf; simp only [two_smul, ZModModule.add_self, add_zero, zero_add],
      hadd]
  set b : SingularChain X (q + 1) := ρ + chainBoundary X (q + 1) D₂
    + chainBoundary X (q + 1) (SingularSubdivision.iterHomotopy X (q + 1) ν ρ) with hbdef
  have hbeq : c = chainBoundary X (q + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c) + b := by
    conv_lhs => rw [heq]
    rw [hDbnd, hTsplit, hbdef]
    simp only [map_add]
    abel
  have hb2 : b = c + chainBoundary X (q + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c) := by
    have h2 := congrArg (· + chainBoundary X (q + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c)) hbeq
    simp only at h2
    rw [h2]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hbP : b ∈ subspaceChains P (q + 1) := by
    rw [hb2]
    exact Submodule.add_mem _ hcP (chainBoundary_mem_subspaceChains _ (Submodule.add_mem _ hD₁
      (SingularExcision.iterHomotopy_mem_subspaceChains hcP ν)))
  have hbAB : b ∈ subspaceChains (A ∪ B) (q + 1) :=
    Submodule.add_mem _ (Submodule.add_mem _ hρ (chainBoundary_mem_subspaceChains _ hD₂))
      (chainBoundary_mem_subspaceChains _
        (SingularExcision.iterHomotopy_mem_subspaceChains hρ ν))
  have hbInter : b ∈ subspaceChains ((P ∩ A) ∪ (P ∩ B)) (q + 1) := by
    have h := Submodule.mem_inf.mpr ⟨hbP, hbAB⟩
    rw [SingularExcision.subspaceChains_inf, Set.inter_union_distrib_left] at h
    exact h
  obtain ⟨κ, bA, bB, hbA, hbB, hbSplit⟩ :=
    exists_iterate_cover_split_amb (hP.inter hA) (hP.inter hB) b hbInter
  have hhb := SingularSubdivision.iterHomotopy_chainHomotopy X κ q b
  have hkill1 : cap (m := 0) a ((⇑(SingularSubdivision.singularSd X (q + 1)))^[κ] b)
      = 0 := by
    rw [hbSplit, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply,
      cap_relCochains_subspaceChains_eq_zero (m := 0) a haA _
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (q + 1) hbA),
      cap_relCochains_subspaceChains_eq_zero (m := 0) a haB _
        (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (q + 1) hbB),
      add_zero]
  have hkill2 : cap (m := 0) a (SingularSubdivision.iterHomotopy X q κ
      (chainBoundary X q b)) = 0 := by
    have hcbd : chainBoundary X q b = chainBoundary X q c := by
      rw [hb2, map_add, chainBoundary_chainBoundary_apply, add_zero]
    rw [hcbd, hbd, hadd, ← capₗ_apply, map_add, capₗ_apply, capₗ_apply,
      cap_relCochains_subspaceChains_eq_zero (m := 0) a haA _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨u', rfl⟩ κ),
      cap_relCochains_subspaceChains_eq_zero (m := 0) a haB _
        (SingularExcision.iterHomotopy_mem_subspaceChains ⟨w', rfl⟩ κ),
      add_zero]
  have hcb : cap (m := 0) a c
      = cap (m := 0) a (chainBoundary X (q + 1)
          (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c))
        + cap (m := 0) a b := by
    conv_lhs => rw [hbeq]
    rw [← capₗ_apply, map_add, capₗ_apply, capₗ_apply]
  have hb3' : (chainBoundary X (q + 1) (SingularSubdivision.iterHomotopy X (q + 1) κ b)
      + SingularSubdivision.iterHomotopy X q κ (chainBoundary X q b))
      + (⇑(SingularSubdivision.singularSd X (q + 1)))^[κ] b = b := by
    rw [hhb]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hcapb : cap (m := 0) a b = chainBoundary X 0
      (cap (m := 1) a (SingularSubdivision.iterHomotopy X (q + 1) κ b)) := by
    have hcc : cap (m := 0) a b
        = cap (m := 0) a ((chainBoundary X (q + 1)
            (SingularSubdivision.iterHomotopy X (q + 1) κ b)
          + SingularSubdivision.iterHomotopy X q κ (chainBoundary X q b))
          + (⇑(SingularSubdivision.singularSd X (q + 1)))^[κ] b) := by rw [hb3']
    rw [hcc, ← capₗ_apply, map_add, map_add, capₗ_apply, capₗ_apply, capₗ_apply, hkill1,
      hkill2, add_zero, add_zero]
    exact (chainBoundary_cap_cocycle_arg (m := 0) a hac _ (by omega)).symm
  have hE₁ : cap (m := 0) a (chainBoundary X (q + 1)
      (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c))
      = chainBoundary X 0 (cap (m := 1) a
          (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c)) :=
    (chainBoundary_cap_cocycle_arg (m := 0) a hac _ (by omega)).symm
  refine ⟨cap (m := 1) a (D₁ + SingularSubdivision.iterHomotopy X (q + 1) ν c)
      + cap (m := 1) a (SingularSubdivision.iterHomotopy X (q + 1) κ b),
    Submodule.add_mem _
      (SingularCapSupport.cap_mem_subspaceChains (m := 1) P a (Submodule.add_mem _ hD₁
        (SingularExcision.iterHomotopy_mem_subspaceChains hcP ν)))
      (SingularCapSupport.cap_mem_subspaceChains (m := 1) P a
        (SingularMayerVietoris.subspaceChains_mono
          (Set.union_subset Set.inter_subset_left Set.inter_subset_left) (q + 1 + 1)
          (SingularExcision.iterHomotopy_mem_subspaceChains hbInter κ))), ?_⟩
  rw [hcb, hcapb, hE₁]
  simp only [map_add]

end SKEFTHawking.SingularConnSquareCloseNCBot
