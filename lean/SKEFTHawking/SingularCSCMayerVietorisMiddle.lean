import Mathlib
import SKEFTHawking.SingularCSCMayerVietoris
import SKEFTHawking.SingularRelativeCohomologyMVMiddle
import SKEFTHawking.SingularCompactlySupportedTop

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6d-iii) — compactly-supported cohomology MV middle exactness

The substantive middle exactness `ker (cscMvSum U V k) ⊆ range (cscMvDiag U V k)` of the
compactly-supported-cohomology Mayer–Vietoris sequence
  `Hᵏ_c(U∩V) --Δ--> Hᵏ_c(U) ⊕ Hᵏ_c(V) --Σ--> Hᵏ_c(U∪V)`
for opens `U`, `V`. The colimit-of-cohomology argument provably fails (agreement of colimit reps is
colimit-level, invisible at any fixed compact). The correct route is a **pair-indexed element-chase**
reusing the finite-dim-free per-pair relative-cohomology MV (`relCohomMv_exact_middle`) directly, with
the **enlargement trick**: given `(α,β) ∈ ker Σ` with `α = of_U(K_α,a)`, `β = of_V(K_β,b)`, the collapse
`ext_U α = ext_V β` forces (via `DirectLimit.exists_eq_of_of_eq`) a common compact `K ⊆ U∪V` carrying the
agreement; `binary_compact_cover` splits `K = K_U' ∪ K_V'`; set `L_U := K_α ⊔ K_U' ⊆ U`,
`L_V := K_β ⊔ K_V' ⊆ V` so that `L_U ⊇ K_α`, `L_V ⊇ K_β`, and `L_U ∪ L_V = K`. The per-pair MV at the
opens `(↑L_U)ᶜ`, `(↑L_V)ᶜ` then produces the `U∩V` preimage `γ₀ ∈ Hᵏ(M|L_U∩L_V)`, and
`γ := of_{U∩V}(L_U∩L_V, γ₀)` satisfies `cscMvDiag γ = (α,β)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularRelativeCohomologyMV SKEFTHawking.SingularRelativeCohomologyMVMiddle
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCSCOpenMonotone
  SKEFTHawking.SingularCSCMayerVietoris SKEFTHawking.SingularCompactlySupportedTop

namespace SKEFTHawking.SingularCSCMayerVietorisMiddle

variable {M : TopCat}

/-- **Restriction absorbs a set-congruence on the source**: restricting along `S ⊆ T'` after the
set-congruence `relCohomSetCongr (T = T')` equals restricting `x : Hᵏ(M, T)` directly along the
transported inclusion `S ⊆ T`. (A `subst` of the set equality.) -/
theorem relCohomRestrict_relCohomSetCongr {S T T' : Set ↑M} (hTT' : T = T') (h : S ⊆ T') (n : ℕ)
    (x : RelativeCohomology T n) :
    relCohomRestrict h n (relCohomSetCongr hTT' n x)
      = relCohomRestrict (hTT' ▸ h) n x := by
  subst hTT'
  rfl

/-- **Computation rule for the MV difference** on two `K`-stage classes: `Σ` extends both to `U∪V` (the
underlying compacts `K_α`, `K_β` viewed in `CompactsIn (U∪V)`) and subtracts. -/
theorem cscMvSum_of (U V : Set ↑M) (k : ℕ) (Kα : CompactsIn U) (a : cohomGW U k Kα)
    (Kβ : CompactsIn V) (b : cohomGW V k Kβ) :
    cscMvSum U V k
        (Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U k) (cohomFW U k) Kα a,
          Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V k) (cohomFW V k) Kβ b)
      = Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) k) (cohomFW (U ∪ V) k)
            (compactsInIncl Set.subset_union_left Kα) a
        - Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∪ V)) (cohomGW (U ∪ V) k) (cohomFW (U ∪ V) k)
            (compactsInIncl Set.subset_union_right Kβ) b := by
  rw [cscMvSum, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  show cscOpenMonotone Set.subset_union_left k
        (Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U k) (cohomFW U k) Kα a)
      - cscOpenMonotone Set.subset_union_right k
        (Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V k) (cohomFW V k) Kβ b) = _
  rw [cscOpenMonotone_of, cscOpenMonotone_of]
  rfl

/-- **Two-index colimit collapse**: if `of i x = of j y` in `Hᵏ_c(W)` (different stages `i`, `j`), there
is a common compact `K ≥ i, j` at which the two transition images already agree. (Push both to `i ⊔ j`
via `of_f`, then `exists_eq_of_of_eq`; compose the transitions by `DirectedSystem.map_map`.) -/
theorem exists_common_restrict {W : Set ↑M} {k : ℕ} {i j : CompactsIn W}
    {x : cohomGW W k i} {y : cohomGW W k j}
    (h : Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) i x
       = Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) j y) :
    ∃ (K : CompactsIn W) (hiK : i ≤ K) (hjK : j ≤ K),
      cohomFW W k i K hiK x = cohomFW W k j K hjK y := by
  set s := CompactsIn.sup i j with hs
  have his : i ≤ s := Subtype.coe_le_coe.mp le_sup_left
  have hjs : j ≤ s := Subtype.coe_le_coe.mp le_sup_right
  rw [show Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) i x
        = Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) s
            (cohomFW W k i s his x) from (Module.DirectLimit.of_f).symm,
      show Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) j y
        = Module.DirectLimit.of (ZMod 2) (CompactsIn W) (cohomGW W k) (cohomFW W k) s
            (cohomFW W k j s hjs y) from (Module.DirectLimit.of_f).symm] at h
  obtain ⟨K, hK, hagree⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  refine ⟨K, his.trans hK, hjs.trans hK, ?_⟩
  calc cohomFW W k i K (his.trans hK) x
      = cohomFW W k s K hK (cohomFW W k i s his x) :=
        (DirectedSystem.map_map (f := fun a b h => ⇑(cohomFW W k a b h)) his hK x).symm
    _ = cohomFW W k s K hK (cohomFW W k j s hjs y) := by rw [hagree]
    _ = cohomFW W k j K (hjs.trans hK) y :=
        DirectedSystem.map_map (f := fun a b h => ⇑(cohomFW W k a b h)) hjs hK y

theorem ker_cscMvSum_le_range_cscMvDiag [T2Space ↑M] (U V : Set ↑M)
    (hU : IsOpen U) (hV : IsOpen V) {N : ℕ}
    (α : CompactlySupportedCohomologyOpen U (N + 1))
    (β : CompactlySupportedCohomologyOpen V (N + 1))
    (hαβ : cscMvSum U V (N + 1) (α, β) = 0) :
    (α, β) ∈ LinearMap.range (cscMvDiag U V (N + 1)) := by
  revert hαβ
  refine Module.DirectLimit.induction_on α (fun Kα a => ?_)
  refine Module.DirectLimit.induction_on β (fun Kβ b => ?_)
  intro hαβ
  rw [cscMvSum_of] at hαβ
  have heq := sub_eq_zero.mp hαβ
  obtain ⟨K, hαK, hβK, hagree⟩ := exists_common_restrict heq
  -- binary split of the merged compact K across the cover {U, V}
  obtain ⟨KU', KV', hcover⟩ := compactsIn_binary_cover hU hV K
  -- enlargements: LU ⊇ Kα and ⊇ KU' (so LU ⊆ U); LV ⊇ Kβ and ⊇ KV'
  set LU : CompactsIn U := CompactsIn.sup Kα KU' with hLU
  set LV : CompactsIn V := CompactsIn.sup Kβ KV' with hLV
  have hKαLU : (↑Kα.1 : Set ↑M) ⊆ ↑LU.1 := by rw [hLU, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]; exact Set.subset_union_left
  have hKβLV : (↑Kβ.1 : Set ↑M) ⊆ ↑LV.1 := by rw [hLV, CompactsIn.sup, TopologicalSpace.Compacts.coe_sup]; exact Set.subset_union_left
  -- subspaces A := (↑LU.1)ᶜ, B := (↑LV.1)ᶜ are open (compacts are closed in T2)
  have hAopen : IsOpen ((↑LU.1 : Set ↑M)ᶜ) := LU.1.isCompact'.isClosed.isOpen_compl
  have hBopen : IsOpen ((↑LV.1 : Set ↑M)ᶜ) := LV.1.isCompact'.isClosed.isOpen_compl
  -- the cover equation ↑LU.1 ∪ ↑LV.1 = ↑K.1
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
  -- aU, bV: restrictions of a, b to the subspaces A, B
  set aU : RelativeCohomology ((↑LU.1 : Set ↑M)ᶜ) (N + 1) :=
    relCohomRestrict (Set.compl_subset_compl.mpr hKαLU) (N + 1) a with haU
  set bV : RelativeCohomology ((↑LV.1 : Set ↑M)ᶜ) (N + 1) :=
    relCohomRestrict (Set.compl_subset_compl.mpr hKβLV) (N + 1) b with hbV
  -- (T1) the per-pair MV sum of (aU, bV) vanishes (the agreement at K)
  have hsum0 : relCohomMvSum ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) (N + 1) (aU, bV) = 0 := by
    have hsubeq : ((↑LU.1 : Set ↑M)ᶜ ∩ (↑LV.1 : Set ↑M)ᶜ) = (↑K.1 : Set ↑M)ᶜ := by
      rw [← Set.compl_union, hLcover]
    have key : relCohomRestrict
          (Set.inter_subset_left.trans (Set.compl_subset_compl.mpr hKαLU)) (N + 1) a
        = relCohomRestrict
          (Set.inter_subset_right.trans (Set.compl_subset_compl.mpr hKβLV)) (N + 1) b := by
      have hka : relCohomRestrict
            (Set.inter_subset_left.trans (Set.compl_subset_compl.mpr hKαLU)) (N + 1) a
          = relCohomRestrict hsubeq.le (N + 1)
              (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_left Kα) K hαK a) :=
        (relCohomRestrict_trans hsubeq.le
          (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hαK)) (N + 1) a).symm
      have hkb : relCohomRestrict
            (Set.inter_subset_right.trans (Set.compl_subset_compl.mpr hKβLV)) (N + 1) b
          = relCohomRestrict hsubeq.le (N + 1)
              (cohomFW (U ∪ V) (N + 1) (compactsInIncl Set.subset_union_right Kβ) K hβK b) :=
        (relCohomRestrict_trans hsubeq.le
          (Set.compl_subset_compl.mpr (Subtype.coe_le_coe.mpr hβK)) (N + 1) b).symm
      rw [hka, hkb, hagree]
    rw [relCohomMvSum_apply, haU, hbV,
        relCohomRestrict_trans Set.inter_subset_left (Set.compl_subset_compl.mpr hKαLU) (N + 1) a,
        relCohomRestrict_trans Set.inter_subset_right (Set.compl_subset_compl.mpr hKβLV) (N + 1) b,
        key, ZModModule.add_self]
  -- per-pair MV exactness → the U∩V preimage γ₀
  have hexact := relCohomMv_exact_middle ((↑LU.1 : Set ↑M)ᶜ) ((↑LV.1 : Set ↑M)ᶜ) hAopen hBopen (N := N)
  rw [LinearMap.exact_iff] at hexact
  obtain ⟨γ₀, hγ₀⟩ := hexact ▸ (LinearMap.mem_ker.mpr hsum0)
  rw [relCohomMvDiag_apply, Prod.mk.injEq] at hγ₀
  obtain ⟨hγ₀1, hγ₀2⟩ := hγ₀
  -- the U∩V compact J = LU ⊓ LV and the transported preimage γ₀'
  have hJsub : (↑(LU.1 ⊓ LV.1) : Set ↑M) ⊆ U ∩ V := by
    rw [TopologicalSpace.Compacts.coe_inf]
    exact Set.inter_subset_inter LU.2 LV.2
  set J : CompactsIn (U ∩ V) := ⟨LU.1 ⊓ LV.1, hJsub⟩ with hJ
  have hUVeq : ((↑LU.1 : Set ↑M)ᶜ ∪ (↑LV.1 : Set ↑M)ᶜ) = (↑J.1 : Set ↑M)ᶜ := by
    rw [hJ, TopologicalSpace.Compacts.coe_inf, Set.compl_inter]
  set γ₀' : cohomGW (U ∩ V) (N + 1) J := relCohomSetCongr hUVeq (N + 1) γ₀ with hγ₀'
  refine ⟨Module.DirectLimit.of (ZMod 2) (CompactsIn (U ∩ V)) (cohomGW (U ∩ V) (N + 1))
      (cohomFW (U ∩ V) (N + 1)) J γ₀', ?_⟩
  rw [cscMvDiag_of]
  refine Prod.ext ?_ ?_
  · show Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1))
          (compactsInIncl Set.inter_subset_left J) γ₀'
        = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1)) Kα a
    have h₁ : compactsInIncl Set.inter_subset_left J ≤ LU := Subtype.coe_le_coe.mp inf_le_left
    have h₂ : Kα ≤ LU := Subtype.coe_le_coe.mp le_sup_left
    have hF1 : cohomFW U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀'
        = cohomFW U (N + 1) Kα LU h₂ a := by
      have hLHS : cohomFW U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀' = aU := by
        rw [hγ₀']
        exact (relCohomRestrict_relCohomSetCongr hUVeq _ (N + 1) γ₀).trans hγ₀1
      have hRHS : cohomFW U (N + 1) Kα LU h₂ a = aU := by rw [haU]; rfl
      rw [hLHS, hRHS]
    calc Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1))
            (compactsInIncl Set.inter_subset_left J) γ₀'
        = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1)) LU
            (cohomFW U (N + 1) (compactsInIncl Set.inter_subset_left J) LU h₁ γ₀') :=
          (Module.DirectLimit.of_f).symm
      _ = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1)) LU
            (cohomFW U (N + 1) Kα LU h₂ a) := by rw [hF1]
      _ = Module.DirectLimit.of (ZMod 2) (CompactsIn U) (cohomGW U (N + 1)) (cohomFW U (N + 1)) Kα a :=
          Module.DirectLimit.of_f
  · show Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1))
          (compactsInIncl Set.inter_subset_right J) γ₀'
        = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1)) Kβ b
    have h₁ : compactsInIncl Set.inter_subset_right J ≤ LV := Subtype.coe_le_coe.mp inf_le_right
    have h₂ : Kβ ≤ LV := Subtype.coe_le_coe.mp le_sup_left
    have hF2 : cohomFW V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀'
        = cohomFW V (N + 1) Kβ LV h₂ b := by
      have hLHS : cohomFW V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀' = bV := by
        rw [hγ₀']
        exact (relCohomRestrict_relCohomSetCongr hUVeq _ (N + 1) γ₀).trans hγ₀2
      have hRHS : cohomFW V (N + 1) Kβ LV h₂ b = bV := by rw [hbV]; rfl
      rw [hLHS, hRHS]
    calc Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1))
            (compactsInIncl Set.inter_subset_right J) γ₀'
        = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1)) LV
            (cohomFW V (N + 1) (compactsInIncl Set.inter_subset_right J) LV h₁ γ₀') :=
          (Module.DirectLimit.of_f).symm
      _ = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1)) LV
            (cohomFW V (N + 1) Kβ LV h₂ b) := by rw [hF2]
      _ = Module.DirectLimit.of (ZMod 2) (CompactsIn V) (cohomGW V (N + 1)) (cohomFW V (N + 1)) Kβ b :=
          Module.DirectLimit.of_f

/-- **Compactly-supported cohomology MV exactness at the middle** `Hᵏ_c(U) ⊕ Hᵏ_c(V)`:
`Function.Exact (cscMvDiag U V k) (cscMvSum U V k)`, i.e. `range Δ = ker Σ`. The `⊇` half is the
chain-complex condition `cscMvSum_comp_cscMvDiag`; the substantive `⊆` is the pair-indexed
element-chase `ker_cscMvSum_le_range_cscMvDiag`. The top row of the Poincaré-duality open-cover
`5`-lemma ladder. -/
theorem cscMv_exact_middle [T2Space ↑M] (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) {N : ℕ} :
    Function.Exact (cscMvDiag U V (N + 1)) (cscMvSum U V (N + 1)) := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun p hp => ?_) (fun p hp => ?_)
  · obtain ⟨α, β⟩ := p
    exact ker_cscMvSum_le_range_cscMvDiag U V hU hV α β (LinearMap.mem_ker.mp hp)
  · obtain ⟨q, rfl⟩ := hp
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, cscMvSum_comp_cscMvDiag, LinearMap.zero_apply]

end SKEFTHawking.SingularCSCMayerVietorisMiddle
