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
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCohomologySnake
  SKEFTHawking.SingularOpenDualityCycle

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

/-- **The bottom N2 δφ-kill** (Brick L₀ — `fact_i_n2_kill` re-instantiated at the 0-spellings over
J₀; the F₂-abstraction carries verbatim). -/
theorem fact_i_n2_kill₀ {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + 0 + 1))
    (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (N + 1 + 0 + 1))
    (hf₁ : f₁ ∈ subspaceChains (U ∩ LVᶜ) (N + 1 + 0 + 1))
    (hf₂ : f₂ ∈ subspaceChains (V ∩ LUᶜ) (N + 1 + 0 + 1))
    (hf₃ : f₃ ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1))
    (hIsplit : (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁) = f₁ + f₂ + f₃)
    (F₂ : SingularChain X (N + 1 + 0 + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1))
    (η₂ : SingularChain X (N + 1 + 0 + 1 + 1)) (a₂ : SingularChain X (N + 1 + 0 + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + 0 + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0 + 1))
    (hF₂bd : chainBoundary X (N + 1 + 0) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0))
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (hFsplit : chainBoundary X (N + 1 + 0)
        ((⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
      = chainIncl _ (N + 1 + 0) aF + chainIncl _ (N + 1 + 0) bF) :
    ∃ E : SingularChain X (0 + 1), E ∈ subspaceChains (U ∩ V) (0 + 1)
      ∧ cap (m := 0) (coboundary X (N + 1) (cochainSplit LUᶜ (N + 1) g.1.1))
          (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
        = chainBoundary X 0 E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 :=
    (SingularConnSquareRHSPairing.relCocycle_props g).1
  have hK₁S : ((↑K₁.1 : Set ↑X))ᶜ ⊆ LUᶜ ∪ LVᶜ := by
    rw [hK₁]; exact fun x hx => Or.inl hx.1
  obtain ⟨D, ρ, hρ, heq⟩ :=
    fund_pair_three_set_rel_comparison_free (S := LUᶜ ∪ LVᶜ) (k := N + 1) (m := 0)
      (hU.union hV) z₀ hz₀ K₁ hK₁S μ jF f₁ f₂ f₃
      (SingularMayerVietoris.subspaceChains_mono (fun _ hx => Or.inr hx.2) _ hf₁)
      (SingularMayerVietoris.subspaceChains_mono (fun _ hx => Or.inl hx.2) _ hf₂)
      hIsplit F₂ η₂ a₂ heq₂ ha₂ hF₂bd
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + 0)) hIsplit
  rw [SingularSubdivision.singularSd_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + 0) f₃
      = (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
          (chainBoundary X (N + 1 + 0)
            (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
        + chainBoundary X (N + 1 + 0) f₁ + chainBoundary X (N + 1 + 0) f₂ := by
    rw [hbdIsplit]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hSdmem : (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0)
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChains LUᶜ (N + 1 + 0) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _
      (SingularExcision.singularSd_iterate_mem_subspaceChains
        (hK₁ ▸ SingularOpenDualityCycle.fundCycleW_boundary (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁) μ)
  have hf2bdmem : chainBoundary X (N + 1 + 0) f₂
      ∈ subspaceChains LUᶜ (N + 1 + 0) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChains _ hf₂)
  have haFmem : chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0) aF
      ∈ subspaceChains LUᶜ (N + 1 + 0) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨aF, rfl⟩
  have hf1bdmem : chainBoundary X (N + 1 + 0) f₁
      ∈ subspaceChains LVᶜ (N + 1 + 0) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
      (chainBoundary_mem_subspaceChains _ hf₁)
  have hbFmem' : chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF
      ∈ subspaceChains LVᶜ (N + 1 + 0) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨bF, rfl⟩
  set u : SingularChain X (N + 1 + 0) :=
    (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0)
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
    + chainBoundary X (N + 1 + 0) f₂
    + chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0) aF with hudef
  set w : SingularChain X (N + 1 + 0) :=
    chainBoundary X (N + 1 + 0) f₁
    + chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF with hwdef
  have humem : u ∈ subspaceChains LUᶜ (N + 1 + 0) :=
    Submodule.add_mem _ (Submodule.add_mem _ hSdmem hf2bdmem) haFmem
  have hwmem : w ∈ subspaceChains LVᶜ (N + 1 + 0) :=
    Submodule.add_mem _ hf1bdmem hbFmem'
  have hbd_uncast : chainBoundary X (N + 1 + 0)
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂) = u + w := by
    rw [map_add, hFsplit, hf₃bd, hudef, hwdef]
    abel
  have hcP : (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
      ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1) :=
    Submodule.add_mem _ hf₃
      (SingularExcision.singularSd_iterate_mem_subspaceChains hF₂mem jF)
  have humem' := humem
  have hwmem' := hwmem
  rw [subspaceChains, LinearMap.mem_range] at humem' hwmem'
  obtain ⟨uS, huS⟩ := humem'
  obtain ⟨wS, hwS⟩ := hwmem'
  have hcover : (U ∩ V) ∪ (LUᶜ ∪ LVᶜ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hxU : x ∈ LU
    · by_cases hxV : x ∈ LV
      · exact Or.inl ⟨hLUU hxU, hLVV hxV⟩
      · exact Or.inr (Or.inr hxV)
    · exact Or.inr (Or.inl hxU)
  obtain ⟨E, hE, hcap⟩ :=
    cap_relCochains_pair_double_support_eq_boundary₀ hLUc hLVc (hU.inter hV) hcover
      (q := N + 1)
      (coboundary X (N + 1) (cochainSplit LUᶜ (N + 1) g.1.1))
      (coboundary_comp_coboundary X (N + 1) _)
      (cochainSplit_coboundary_mem_U LUᶜ (N + 1) g.1.1)
      (cochainSplit_coboundary_mem_V LUᶜ LVᶜ (N + 1) g.1.1 g.1.2 hgc)
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
      hcP D ρ hρ heq uS wS (by rw [hbd_uncast, ← huS, ← hwS])
  exact ⟨E, hE, hcap⟩

/-- **The bottom fact-(i) ambient core** (Brick M₀ — `fact_i_ambient_core` re-instantiated at the
0-spellings, cast-free; the σR-cap-engine reuses at `m := 0` with `h := rfl`). -/
theorem fact_i_ambient_core₀ {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + 0 + 1))
    (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V))
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (μ jF : ℕ) (f₁ f₂ f₃ : SingularChain X (N + 1 + 0 + 1))
    (hf₁ : f₁ ∈ subspaceChains (U ∩ LVᶜ) (N + 1 + 0 + 1))
    (hf₂ : f₂ ∈ subspaceChains (V ∩ LUᶜ) (N + 1 + 0 + 1))
    (hf₃ : f₃ ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1))
    (hIsplit : (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁)
      = f₁ + f₂ + f₃)
    (F₂ : SingularChain X (N + 1 + 0 + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1))
    (η₂ : SingularChain X (N + 1 + 0 + 1 + 1)) (a₂ : SingularChain X (N + 1 + 0 + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + 0 + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0 + 1))
    (hF₂bd : chainBoundary X (N + 1 + 0) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0))
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (hFsplit : chainBoundary X (N + 1 + 0)
        ((⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
      = chainIncl _ (N + 1 + 0) aF + chainIncl _ (N + 1 + 0) bF) :
    ∃ E : SingularChain X (0 + 1), E ∈ subspaceChains (U ∩ V) (0 + 1)
      ∧ chainBoundary X 0 (cap (m := 0 + 1) g.1.1 (f₂ + f₃))
          + cap (m := 0) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF)
        = chainBoundary X 0 E := by
  have hgc : coboundary X (N + 1) g.1.1 = 0 :=
    (SingularConnSquareRHSPairing.relCocycle_props g).1
  have hbdIsplit := congrArg (chainBoundary X (N + 1 + 0)) hIsplit
  rw [SingularSubdivision.singularSd_iterate_chainBoundary, map_add, map_add] at hbdIsplit
  have hf₃bd : chainBoundary X (N + 1 + 0) f₃
      = (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
          (chainBoundary X (N + 1 + 0)
            (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
        + chainBoundary X (N + 1 + 0) f₁ + chainBoundary X (N + 1 + 0) f₂ := by
    rw [hbdIsplit]
    abel_nf
    simp only [two_smul, ZModModule.add_self, add_zero, zero_add]
  have hSdKmem : (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0)
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
      ∈ subspaceChains (LUᶜ ∩ LVᶜ) (N + 1 + 0) :=
    SingularExcision.singularSd_iterate_mem_subspaceChains
      (hK₁ ▸ SingularOpenDualityCycle.fundCycleW_boundary (k := N + 1) (m := 0)
        (hU.union hV) z₀ hz₀ K₁) μ
  set u : SingularChain X (N + 1 + 0) :=
    (⇑(SingularSubdivision.singularSd X (N + 1 + 0)))^[μ]
      (chainBoundary X (N + 1 + 0)
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
    + chainBoundary X (N + 1 + 0) f₂
    + chainIncl (LUᶜ ∩ (U ∩ V)) (N + 1 + 0) aF with hudef
  set w : SingularChain X (N + 1 + 0) :=
    chainBoundary X (N + 1 + 0) f₁
    + chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF with hwdef
  have humem : u ∈ subspaceChains LUᶜ (N + 1 + 0) :=
    Submodule.add_mem _ (Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ hSdKmem)
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChains _ hf₂)))
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨aF, rfl⟩)
  have hwmem : w ∈ subspaceChains LVᶜ (N + 1 + 0) :=
    Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right _
        (chainBoundary_mem_subspaceChains _ hf₁))
      (SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left _ ⟨bF, rfl⟩)
  have hbd_uncast : chainBoundary X (N + 1 + 0)
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂) = u + w := by
    rw [map_add, hFsplit, hf₃bd, hudef, hwdef]
    abel
  have hengine := cap_coboundary_cochainSplit_eq (N := N) (m := 0) LUᶜ LVᶜ g
    (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂) u w humem hwmem
    hbd_uncast rfl
  obtain ⟨E₂, hE₂mem, hE₂⟩ := fact_i_n2_kill₀ hU hV hLUc hLVc hLUU hLVV g z₀ hz₀ K₁ hK₁
    μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit
  have hgw : cap (m := 0) g.1.1 w = chainBoundary X 0 E₂
      + chainBoundary X 0 (cap (m := 0 + 1) (cochainSplit LUᶜ (N + 1) g.1.1)
          (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)) := by
    have h0 := hE₂.symm.trans hengine
    rw [h0]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add, add_zero]
  have hsplit' : (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[μ]
      (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁)
      = f₁ + (f₂ + f₃) :=
    hIsplit.trans (add_assoc f₁ f₂ f₃)
  have hcyc0 : chainBoundary X 0 (cap (m := 0 + 1) g.1.1
      ((⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[μ]
        (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁)))
      = 0 := by
    rw [chainBoundary_cap_cocycle_arg (m := 0) g.1.1 hgc _ (by omega),
      SingularSubdivision.singularSd_iterate_chainBoundary]
    exact cap_relCochains_subspaceChains_eq_zero (m := 0) g.1.1 g.1.2 _ hSdKmem
  have hflip : chainBoundary X 0 (cap (m := 0 + 1) g.1.1 (f₂ + f₃))
      = cap (m := 0) g.1.1 (chainBoundary X (N + 1 + 0) f₁) := by
    have h1 : cap (m := 0 + 1) g.1.1
        ((⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[μ]
          (SingularOpenDualityCycle.fundCycleW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁))
        = cap (m := 0 + 1) g.1.1 f₁ + cap (m := 0 + 1) g.1.1 (f₂ + f₃) := by
      rw [hsplit', map_add]
    have h2 := congrArg (chainBoundary X 0) h1
    rw [hcyc0, map_add] at h2
    have h3 : chainBoundary X 0 (cap (m := 0 + 1) g.1.1 (f₂ + f₃))
        = chainBoundary X 0 (cap (m := 0 + 1) g.1.1 f₁) := by
      apply eq_of_sub_eq_zero
      rw [ZModModule.sub_eq_add, h2]
      abel
    exact h3.trans (chainBoundary_cap_cocycle_arg (m := 0) g.1.1 hgc f₁ (by omega))
  refine ⟨E₂ + cap (m := 0 + 1) (cochainSplit LUᶜ (N + 1) g.1.1)
      (f₃ + (⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂),
    Submodule.add_mem _ hE₂mem
      (SingularCapSupport.cap_mem_subspaceChains (m := 0 + 1) (U ∩ V) _
        (Submodule.add_mem _ hf₃
          (SingularExcision.singularSd_iterate_mem_subspaceChains hF₂mem jF))), ?_⟩
  rw [hflip, map_add,
    show cap (m := 0) g.1.1 (chainBoundary X (N + 1 + 0) f₁)
        + cap (m := 0) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF)
      = cap (m := 0) g.1.1 w from by rw [hwdef, map_add]]
  exact hgw

/-- **The BOTTOM SUN FACT (i), discharged** (`fact_i_discharge` re-instantiated at the degree-0
hmatch₀-shape: seams/β at 0, partitions at 0+1, the fund frame at N+1+0+1 — cast-free). -/
theorem fact_i_discharge₀ {U V LU LV : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (hLUc : IsOpen LUᶜ) (hLVc : IsOpen LVᶜ) (hLUU : LU ⊆ U) (hLVV : LV ⊆ V)
    {N : ℕ}
    (g : LinearMap.ker (relCoboundaryₗ (LUᶜ ∩ LVᶜ) (N + 1)))
    (z₀ : SingularChain X (N + 1 + 0 + 1))
    (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K₁ : CompactsIn (U ∪ V))
    (gW : LinearMap.ker (relCoboundaryₗ (((↑K₁.1 : Set ↑X))ᶜ) (N + 1)))
    (hgg : g.1.1 = gW.1.1)
    (hK₁ : ((↑K₁.1 : Set ↑X))ᶜ = LUᶜ ∩ LVᶜ)
    (hcov : (⋃ W ∈ ({(Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))), Subtype.val ⁻¹' V} :
        Set (Set ↑(sub (U ∪ V)))), interior W) = Set.univ)
    (zc0 : ↥(cycles (sub (U ∪ V)) (0 + 1)))
    (hzc0 : Homology.mk (sub (U ∪ V)) (0 + 1) zc0
      = SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K₁
          (Submodule.Quotient.mk gW))
    (zA : SingularChain (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (0 + 1))
    (zB : SingularChain (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (0 + 1))
    (hcyc : chainIncl _ (0 + 1) zA + chainIncl _ (0 + 1) zB
      ∈ cycles (sub (U ∪ V)) (0 + 1))
    (hpart : Homology.mk (sub (U ∪ V)) (0 + 1) zc0
      = Homology.mk (sub (U ∪ V)) (0 + 1) ⟨_, hcyc⟩)
    (hzBmem : zB ∈ SingularPairLES.relCycleLift
      (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0)
    {Y' : TopCat}
    (φin : C(↑(sub (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))
      (Subtype.val ⁻¹' V))), ↑Y'))
    (φout : C(↑Y', ↑(sub (U ∩ V))))
    (hseam : ∀ (w : SingularPairLES.relCycleLift
        (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0),
      chainIncl (U ∩ V) 0 (SingularFunctoriality.mapChain φout 0
          (SingularFunctoriality.mapChain φin 0
            (SingularPairLES.boundaryExtract
              (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0 w)))
        = chainIncl (U ∪ V) 0 (chainBoundary (sub (U ∪ V)) 0
            (chainIncl (Subtype.val ⁻¹' V) (0 + 1) (w : SingularChain _ (0 + 1)))))
    (F₂ : SingularChain X (N + 1 + 0 + 1))
    (hF₂mem : F₂ ∈ subspaceChains (U ∩ V) (N + 1 + 0 + 1))
    (η₂ : SingularChain X (N + 1 + 0 + 1 + 1)) (a₂ : SingularChain X (N + 1 + 0 + 1))
    (heq₂ : F₂ + z₀ = chainBoundary X (N + 1 + 0 + 1) η₂ + a₂)
    (ha₂ : a₂ ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0 + 1))
    (hF₂bd : chainBoundary X (N + 1 + 0) F₂
      ∈ subspaceChains (LUᶜ ∪ LVᶜ) (N + 1 + 0))
    (jF : ℕ)
    (aF : SingularChain (sub (LUᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (bF : SingularChain (sub (LVᶜ ∩ (U ∩ V))) (N + 1 + 0))
    (hFsplit : chainBoundary X (N + 1 + 0)
        ((⇑(SingularSubdivision.singularSd X (N + 1 + 0 + 1)))^[jF] F₂)
      = chainIncl _ (N + 1 + 0) aF + chainIncl _ (N + 1 + 0) bF)
    (hbFmem : chainIncl _ (N + 1 + 0) bF ∈ subspaceChains (U ∩ V) (N + 1 + 0))
    (β : LinearMap.ker (coboundaryₗ (sub (U ∩ V)) 0)) :
    kronecker β.1 (SingularFunctoriality.mapChain φout 0
        (SingularFunctoriality.mapChain φin 0
          (SingularPairLES.boundaryExtract
            (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
            ⟨zB, hzBmem⟩)))
      = kronecker β.1 (cap (m := 0) (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + 0)).symm
            ⟨_, hbFmem⟩)) := by
  obtain ⟨μ, f₁, f₂, f₃, hf₁, hf₂, hf₃, hIsplit, zAc, zBc, hzAc, hzBc, hcycc, hcls⟩ :=
    fact_i_stage1 (k := N + 1) (m := 0) hU hV hLUc hLVc hLUU hLVV z₀ hz₀ K₁ gW
  have hzBcmem : zBc ∈ SingularPairLES.relCycleLift
      (SingularExcisionIso.restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))
      0 :=
    SingularMvDeltaPartition.zB_mem_relCycleLift _ _ 0 zAc zBc hcycc
  have htrans := kronecker_mapChain_boundaryExtract_class_invariant
    (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) 0 hcov φin φout β
    zA zAc zB zBc hcyc hcycc (hpart.symm.trans (hzc0.trans hcls)) hzBmem hzBcmem
  rw [htrans]
  obtain ⟨EM, hEMmem, hEMeq⟩ :=
    fact_i_ambient_core₀ hU hV hLUc hLVc hLUU hLVV g z₀ hz₀ K₁ hK₁
      μ jF f₁ f₂ f₃ hf₁ hf₂ hf₃ hIsplit F₂ hF₂mem η₂ a₂ heq₂ ha₂ hF₂bd aF bF hFsplit
  have hzBcg : chainIncl (U ∪ V) (0 + 1) (chainIncl _ (0 + 1) zBc)
      = cap (m := 0 + 1) g.1.1 (f₂ + f₃) := by rw [hgg]; exact hzBc
  have hambL : chainIncl (U ∩ V) 0
      (SingularFunctoriality.mapChain φout 0 (SingularFunctoriality.mapChain φin 0
        (SingularPairLES.boundaryExtract (SingularExcisionIso.restr
          (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
          ⟨zBc, hzBcmem⟩)))
      = chainBoundary X 0 (cap (m := 0 + 1) g.1.1 (f₂ + f₃)) := by
    rw [hseam ⟨zBc, hzBcmem⟩, SingularRelativeHomologyMod2.chainIncl_chainBoundary, hzBcg]
  have hambR : chainIncl (U ∩ V) 0
      (cap (m := 0) (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + 0)).symm
          ⟨chainIncl _ (N + 1 + 0) bF, hbFmem⟩))
      = cap (m := 0) g.1.1 (chainIncl (LVᶜ ∩ (U ∩ V)) (N + 1 + 0) bF) := by
    rw [← SingularCapChainIncl.cap_chainIncl,
      SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm]
  rw [subspaceChains, LinearMap.mem_range] at hEMmem
  obtain ⟨E', hE'⟩ := hEMmem
  have hsum_mem : SingularFunctoriality.mapChain φout 0
        (SingularFunctoriality.mapChain φin 0
          (SingularPairLES.boundaryExtract (SingularExcisionIso.restr
            (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V)) 0
            ⟨zBc, hzBcmem⟩))
      + cap (m := 0) (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 1) g.1.1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (U ∩ V) (N + 1 + 0)).symm
            ⟨chainIncl _ (N + 1 + 0) bF, hbFmem⟩)
      ∈ boundaries (sub (U ∩ V)) 0 := by
    refine ⟨E', ?_⟩
    apply chainIncl_injective (U ∩ V) 0
    rw [SingularRelativeHomologyMod2.chainIncl_chainBoundary, hE', map_add, hambL, hambR]
    exact hEMeq.symm
  have h0 := kronecker_cocycle_boundary_eq_zero β hsum_mem
  rw [kronecker_add_right] at h0
  exact eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add]; exact h0)

end SKEFTHawking.SingularConnSquareCloseNCBot
