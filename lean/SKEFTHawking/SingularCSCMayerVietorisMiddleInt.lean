/-
# Phase 5q.H (E1 CSC-PD tower) — integral compactly-supported cohomology MV middle exactness

Integral (`ZMod 2 → ℤ`) mirror of `SingularCSCMayerVietorisMiddle`. The substantive middle exactness
`ker (cscMvSumInt U V k) ⊆ range (cscMvDiagInt U V k)` of the integral compactly-supported-cohomology
Mayer–Vietoris sequence
  `Hᵏ_c(U∩V;ℤ) --Δ--> Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ) --Σ--> Hᵏ_c(U∪V;ℤ)`
for opens `U`, `V`. Pair-indexed element-chase reusing the torsion-safe per-pair relative-cohomology MV
(`relCohomMv_exact_middleInt`) directly, with the enlargement trick: given `(α,β) ∈ ker Σ` with
`α = of_U(Kα,a)`, `β = of_V(Kβ,b)`, the collapse `ext_U α = ext_V β` forces (via
`DirectLimit.exists_eq_of_of_eq`) a common compact `K ⊆ U∪V`; `compactsIn_binary_cover` splits
`K = KU' ∪ KV'`; set `LU := Kα ⊔ KU' ⊆ U`, `LV := Kβ ⊔ KV' ⊆ V` so `LU ⊇ Kα`, `LV ⊇ Kβ`, `LU ∪ LV = K`.
The per-pair MV at `(↑LU)ᶜ`, `(↑LV)ᶜ` produces the `U∩V` preimage `γ₀ ∈ Hᵏ(M|LU∩LV)`, and
`γ := of_{U∩V}(LU∩LV, γ₀)` satisfies `cscMvDiagInt γ = (α,β)`. Over ℤ the MV difference is honest
subtraction (`sub_self`), replacing the mod-2 `coprod`/`add_self`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCMayerVietorisInt
import SKEFTHawking.SingularCohomMvMiddleInt
import SKEFTHawking.SingularCompactsInOpen

open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCohomologyMVInt
open SKEFTHawking.SingularCohomMvMiddleInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularCSCMayerVietorisInt

namespace SKEFTHawking.SingularCSCMayerVietorisMiddleInt

variable {M : TopCat}

/-- **Relative-cohomology congruence along a set equality** `S = T` (integral): `Hᵏ(M,S;ℤ) ≃ₗ Hᵏ(M,T;ℤ)`
(a `subst` of the underlying set). -/
noncomputable def relCohomSetCongrInt {S T : Set ↑M} (h : S = T) (n : ℕ) :
    RelativeCohomologyInt S n ≃ₗ[ℤ] RelativeCohomologyInt T n := by
  subst h; exact LinearEquiv.refl _ _

/-- Restriction absorbs a set-congruence on the source (integral): restricting along `S ⊆ T'` after
`relCohomSetCongrInt (T = T')` equals restricting directly along the transported inclusion. -/
theorem relCohomRestrict_relCohomSetCongrInt {S T T' : Set ↑M} (hTT' : T = T') (h : S ⊆ T') (n : ℕ)
    (x : RelativeCohomologyInt T n) :
    relCohomRestrictInt h n (relCohomSetCongrInt hTT' n x)
      = relCohomRestrictInt (hTT' ▸ h) n x := by
  subst hTT'
  rfl

/-- **Computation rule for the integral MV difference** on two `K`-stage classes: `Σ` extends both to
`U∪V` and subtracts. -/
theorem cscMvSumInt_of (U V : Set ↑M) (k : ℕ) (Kα : CompactsIn U) (a : cohomGWInt U k Kα)
    (Kβ : CompactsIn V) (b : cohomGWInt V k Kβ) :
    cscMvSumInt U V k
        (Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U k) (cohomFWInt U k) Kα a,
          Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V k) (cohomFWInt V k) Kβ b)
      = Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) k) (cohomFWInt (U ∪ V) k)
            (compactsInIncl Set.subset_union_left Kα) a
        - Module.DirectLimit.of ℤ (CompactsIn (U ∪ V)) (cohomGWInt (U ∪ V) k) (cohomFWInt (U ∪ V) k)
            (compactsInIncl Set.subset_union_right Kβ) b := by
  rw [cscMvSumInt, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  show cscOpenMonotoneInt Set.subset_union_left k
        (Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U k) (cohomFWInt U k) Kα a)
      - cscOpenMonotoneInt Set.subset_union_right k
        (Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V k) (cohomFWInt V k) Kβ b) = _
  rw [cscOpenMonotoneInt_of, cscOpenMonotoneInt_of]
  rfl

/-- **Two-index colimit collapse** (integral): if `of i x = of j y` in `Hᵏ_c(W;ℤ)` there is a common
compact `K ≥ i, j` at which the two transition images already agree. -/
theorem exists_common_restrictInt {W : Set ↑M} {k : ℕ} {i j : CompactsIn W}
    {x : cohomGWInt W k i} {y : cohomGWInt W k j}
    (h : Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) i x
       = Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) j y) :
    ∃ (K : CompactsIn W) (hiK : i ≤ K) (hjK : j ≤ K),
      cohomFWInt W k i K hiK x = cohomFWInt W k j K hjK y := by
  set s := CompactsIn.sup i j with hs
  have his : i ≤ s := Subtype.coe_le_coe.mp le_sup_left
  have hjs : j ≤ s := Subtype.coe_le_coe.mp le_sup_right
  rw [show Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) i x
        = Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) s
            (cohomFWInt W k i s his x) from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) j y
        = Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W k) (cohomFWInt W k) s
            (cohomFWInt W k j s hjs y) from (Module.DirectLimit.of_f).symm] at h
  obtain ⟨K, hK, hagree⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  refine ⟨K, his.trans hK, hjs.trans hK, ?_⟩
  calc cohomFWInt W k i K (his.trans hK) x
      = cohomFWInt W k s K hK (cohomFWInt W k i s his x) :=
        (DirectedSystem.map_map (f := fun a b h => ⇑(cohomFWInt W k a b h)) his hK x).symm
    _ = cohomFWInt W k s K hK (cohomFWInt W k j s hjs y) := by rw [hagree]
    _ = cohomFWInt W k j K (hjs.trans hK) y :=
        DirectedSystem.map_map (f := fun a b h => ⇑(cohomFWInt W k a b h)) hjs hK y

/-- **`ker Σ ⊆ range Δ`** (integral) — the substantive half of the CSC-MV middle exactness. -/
theorem ker_cscMvSumInt_le_range_cscMvDiagInt [T2Space ↑M] (U V : Set ↑M)
    (hU : IsOpen U) (hV : IsOpen V) {N : ℕ}
    (α : CompactlySupportedCohomologyOpenInt U (N + 1))
    (β : CompactlySupportedCohomologyOpenInt V (N + 1))
    (hαβ : cscMvSumInt U V (N + 1) (α, β) = 0) :
    (α, β) ∈ LinearMap.range (cscMvDiagInt U V (N + 1)) := by
  revert hαβ
  refine Module.DirectLimit.induction_on α (fun Kα a => ?_)
  refine Module.DirectLimit.induction_on β (fun Kβ b => ?_)
  intro hαβ
  rw [cscMvSumInt_of] at hαβ
  have heq := sub_eq_zero.mp hαβ
  obtain ⟨K, hαK, hβK, hagree⟩ := exists_common_restrictInt heq
  obtain ⟨KU', KV', hcover⟩ := compactsIn_binary_cover hU hV K
  set LU : CompactsIn U := CompactsIn.sup Kα KU' with hLU
  set LV : CompactsIn V := CompactsIn.sup Kβ KV' with hLV
  have hKαLU : (↑Kα.1 : Set ↑M) ⊆ ↑LU.1 := by
    rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]; exact Set.subset_union_left
  have hKβLV : (↑Kβ.1 : Set ↑M) ⊆ ↑LV.1 := by
    rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]; exact Set.subset_union_left
  have hAopen : IsOpen ((↑LU.1 : Set ↑M)ᶜ) := LU.1.isCompact'.isClosed.isOpen_compl
  have hBopen : IsOpen ((↑LV.1 : Set ↑M)ᶜ) := LV.1.isCompact'.isClosed.isOpen_compl
  have hLcover : (↑LU.1 : Set ↑M) ∪ ↑LV.1 = ↑K.1 := by
    have hKαK : (↑Kα.1 : Set ↑M) ⊆ ↑K.1 := hαK
    have hKβK : (↑Kβ.1 : Set ↑M) ⊆ ↑K.1 := hβK
    have hKUK : (↑KU'.1 : Set ↑M) ⊆ ↑K.1 := by rw [hcover]; exact Set.subset_union_left
    have hKVK : (↑KV'.1 : Set ↑M) ⊆ ↑K.1 := by rw [hcover]; exact Set.subset_union_right
    have hLUe : (↑LU.1 : Set ↑M) = ↑Kα.1 ∪ ↑KU'.1 := by
      rw [hLU]; exact TopologicalSpace.Compacts.coe_sup _ _
    have hLVe : (↑LV.1 : Set ↑M) = ↑Kβ.1 ∪ ↑KV'.1 := by
      rw [hLV]; exact TopologicalSpace.Compacts.coe_sup _ _
    apply Set.Subset.antisymm
    · rw [hLUe, hLVe]
      exact Set.union_subset (Set.union_subset hKαK hKUK) (Set.union_subset hKβK hKVK)
    · rw [hLUe, hLVe, hcover]
      intro x hx
      rcases hx with hx | hx
      · exact Or.inl (Or.inr hx)
      · exact Or.inr (Or.inr hx)
  set aU : RelativeCohomologyInt ((↑LU.1 : Set ↑M)ᶜ) (N + 1) :=
    relCohomRestrictInt (Set.compl_subset_compl.mpr hKαLU) (N + 1) a with haU
  set bV : RelativeCohomologyInt ((↑LV.1 : Set ↑M)ᶜ) (N + 1) :=
    relCohomRestrictInt (Set.compl_subset_compl.mpr hKβLV) (N + 1) b with hbV
  have hsum0 : relCohomMvSumInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) (N + 1) (aU, bV) = 0 := by
    have hsubeq : ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) = (↑K.1 : Set ↑M)ᶜ := by
      rw [← Set.compl_union, hLcover]
    have key : relCohomRestrictInt
          (Set.inter_subset_left.trans (Set.compl_subset_compl.mpr hKαLU)) (N + 1) a
        = relCohomRestrictInt
          (Set.inter_subset_right.trans (Set.compl_subset_compl.mpr hKβLV)) (N + 1) b := by
      have hka : relCohomRestrictInt
            (Set.inter_subset_left.trans (Set.compl_subset_compl.mpr hKαLU)) (N + 1) a
          = relCohomRestrictInt hsubeq.le (N + 1)
              (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) K hαK a) :=
        (relCohomRestrictInt_trans hsubeq.le
          (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hαK)) (N + 1) a).symm
      have hkb : relCohomRestrictInt
            (Set.inter_subset_right.trans (Set.compl_subset_compl.mpr hKβLV)) (N + 1) b
          = relCohomRestrictInt hsubeq.le (N + 1)
              (cohomFWInt (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) K hβK b) :=
        (relCohomRestrictInt_trans hsubeq.le
          (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hβK)) (N + 1) b).symm
      rw [hka, hkb, hagree]
    rw [relCohomMvSumInt_apply, haU, hbV,
        relCohomRestrictInt_trans Set.inter_subset_left (Set.compl_subset_compl.mpr hKαLU) (N + 1) a,
        relCohomRestrictInt_trans Set.inter_subset_right (Set.compl_subset_compl.mpr hKβLV) (N + 1) b,
        key, sub_self]
  have hexact := relCohomMv_exact_middleInt ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) hAopen hBopen (m := N)
  rw [LinearMap.exact_iff] at hexact
  obtain ⟨γ₀, hγ₀⟩ := hexact ▸ (LinearMap.mem_ker.mpr hsum0)
  rw [relCohomMvDiagInt_apply, Prod.mk.injEq] at hγ₀
  obtain ⟨hγ₀1, hγ₀2⟩ := hγ₀
  have hJsub : (↑(LU.1 ⊓ LV.1) : Set ↑M) ⊆ U ∩ V := by
    rw [TopologicalSpace.Compacts.coe_inf]
    exact Set.inter_subset_inter LU.2 LV.2
  set J : CompactsIn (U ∩ V) := ⟨LU.1 ⊓ LV.1, hJsub⟩ with hJ
  have hUVeq : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ := by
    rw [hJ, TopologicalSpace.Compacts.coe_inf, Set.compl_inter]
  set γ₀' : cohomGWInt (U ∩ V) (N + 1) J := relCohomSetCongrInt hUVeq (N + 1) γ₀ with hγ₀'
  refine ⟨Module.DirectLimit.of ℤ (CompactsIn (U ∩ V)) (cohomGWInt (U ∩ V) (N + 1))
      (cohomFWInt (U ∩ V) (N + 1)) J γ₀', ?_⟩
  rw [cscMvDiagInt_of]
  refine Prod.ext ?_ ?_
  · show Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1))
          (compactsInIncl Set.inter_subset_left J) γ₀'
        = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1)) Kα a
    have h₁ : compactsInIncl Set.inter_subset_left J ≤ LU := Subtype.coe_le_coe.mp inf_le_left
    have h₂ : Kα ≤ LU := Subtype.coe_le_coe.mp le_sup_left
    have hF1 : cohomFWInt U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀'
        = cohomFWInt U (N + 1) Kα LU h₂ a := by
      have hLHS : cohomFWInt U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀' = aU := by
        rw [hγ₀']
        exact (relCohomRestrict_relCohomSetCongrInt hUVeq _ (N + 1) γ₀).trans hγ₀1
      have hRHS : cohomFWInt U (N + 1) Kα LU h₂ a = aU := by rw [haU]; rfl
      rw [hLHS, hRHS]
    calc Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1))
            (compactsInIncl Set.inter_subset_left J) γ₀'
        = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1)) LU
            (cohomFWInt U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀') :=
          (Module.DirectLimit.of_f).symm
      _ = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1)) LU
            (cohomFWInt U (N + 1) Kα LU h₂ a) := by rw [hF1]
      _ = Module.DirectLimit.of ℤ (CompactsIn U) (cohomGWInt U (N + 1)) (cohomFWInt U (N + 1)) Kα a :=
          Module.DirectLimit.of_f
  · show Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1))
          (compactsInIncl Set.inter_subset_right J) γ₀'
        = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1)) Kβ b
    have h₁ : compactsInIncl Set.inter_subset_right J ≤ LV := Subtype.coe_le_coe.mp inf_le_right
    have h₂ : Kβ ≤ LV := Subtype.coe_le_coe.mp le_sup_left
    have hF2 : cohomFWInt V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀'
        = cohomFWInt V (N + 1) Kβ LV h₂ b := by
      have hLHS : cohomFWInt V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀' = bV := by
        rw [hγ₀']
        exact (relCohomRestrict_relCohomSetCongrInt hUVeq _ (N + 1) γ₀).trans hγ₀2
      have hRHS : cohomFWInt V (N + 1) Kβ LV h₂ b = bV := by rw [hbV]; rfl
      rw [hLHS, hRHS]
    calc Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1))
            (compactsInIncl Set.inter_subset_right J) γ₀'
        = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1)) LV
            (cohomFWInt V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀') :=
          (Module.DirectLimit.of_f).symm
      _ = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1)) LV
            (cohomFWInt V (N + 1) Kβ LV h₂ b) := by rw [hF2]
      _ = Module.DirectLimit.of ℤ (CompactsIn V) (cohomGWInt V (N + 1)) (cohomFWInt V (N + 1)) Kβ b :=
          Module.DirectLimit.of_f

/-- **Integral compactly-supported cohomology MV exactness at the middle** `Hᵏ_c(U;ℤ) ⊕ Hᵏ_c(V;ℤ)`:
`Function.Exact (cscMvDiagInt U V k) (cscMvSumInt U V k)`. The `⊇` half is the chain-complex condition
`cscMvSumInt_comp_cscMvDiagInt`; the substantive `⊆` is `ker_cscMvSumInt_le_range_cscMvDiagInt`. The top
row of the integral Poincaré-duality open-cover `5`-lemma ladder. -/
theorem cscMv_exact_middleInt [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (cscMvDiagInt U V (N + 1)) (cscMvSumInt U V (N + 1)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨α, β⟩ := p
    exact ker_cscMvSumInt_le_range_cscMvDiagInt U V hU hV α β (LinearMap.mem_ker.mp hp)
  · obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, cscMvSumInt_comp_cscMvDiagInt, LinearMap.zero_apply]

end SKEFTHawking.SingularCSCMayerVietorisMiddleInt
