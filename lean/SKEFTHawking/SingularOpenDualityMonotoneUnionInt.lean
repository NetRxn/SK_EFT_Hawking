/-
# Phase 5q.H (E1 CSC-PD tower) — integral monotone-union stability of the open duality maps (§1–§2)

Integral (`ZMod 2 → ℤ`) mirror of `SingularOpenDualityMonotoneUnion` — the A3 block of the Bott–Tu-style
open-cover induction (Hatcher 3.36 (iii)): for an ℕ-indexed monotone family of opens `W 0 ⊆ W 1 ⊆ ⋯`, the
open PD map `D_{⋃W}` is bijective if every `D_{W n}` is. This module builds the compact-absorption (§1,
coefficient-free) and the compactly-supported cohomology exhaustion (§2). The homology exhaustion (§3) and
the generic payoff (§4) follow, then instantiate at `SingularOpenDualityInt.openDuality`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCOpenMonotoneInt
import SKEFTHawking.SingularChainSupportInt
import SKEFTHawking.SingularSubspaceChainsEquivInt
import SKEFTHawking.SingularLocalDualityKMonoInt
import SKEFTHawking.SingularOpenDualityNatInt

open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularCSCOpenMonotoneInt
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularSubsetHomologyInt
open SKEFTHawking.SingularLocalDualityKMonoInt
open SKEFTHawking.SingularChainSupportInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularOpenDualityNatInt

namespace SKEFTHawking.SingularOpenDualityMonotoneUnionInt

variable {X : TopCat} {W : ℕ → Set ↑X}

/-! ## §1. Compact absorption into a stage of the monotone tower (coefficient-free) -/

/-- Monotone-tower transport: `W a ⊆ W b` for `a ≤ b`. -/
theorem monotone_subset (hmono : ∀ n, W n ⊆ W (n + 1)) {a b : ℕ} (hab : a ≤ b) : W a ⊆ W b :=
  monotone_nat_of_le_succ hmono hab

/-- **Compact absorption**: a compact subset of the monotone union `⋃ i, W i` of opens lies in a single
stage `W n` (`IsCompact.elim_directed_cover`). -/
theorem exists_compact_subset_stage (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    {K : Set ↑X} (hK : IsCompact K) (hKW : K ⊆ ⋃ i, W i) : ∃ n, K ⊆ W n :=
  hK.elim_directed_cover W hopen hKW (monotone_nat_of_le_succ hmono).directed_le

/-- **Compact absorption, packaged for the `Hᵏ_c` index poset**. -/
theorem compactsIn_iUnion_absorb (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (K : CompactsIn (⋃ i, W i)) : ∃ n, (↑K.1 : Set ↑X) ⊆ W n :=
  exists_compact_subset_stage hmono hopen K.1.isCompact' K.2

/-! ## §2. Exhaustion of the integral compactly-supported cohomology `Hᵏ_c(Wu;ℤ)` -/

/-- **CSC exhaustion (surjectivity)**: every class of `Hᵏ_c(⋃ i, W i;ℤ)` is the `cscOpenMonotoneInt`
extension of a stage class — its `K`-stage compact is absorbed into a stage. -/
theorem cscOpen_iUnion_exhaustInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k : ℕ) (ξ : CompactlySupportedCohomologyOpenInt (⋃ i, W i) k) :
    ∃ (n : ℕ) (β : CompactlySupportedCohomologyOpenInt (W n) k),
      cscOpenMonotoneInt (Set.subset_iUnion W n) k β = ξ := by
  refine Module.DirectLimit.induction_on ξ (fun K a => ?_)
  obtain ⟨n, hKn⟩ := compactsIn_iUnion_absorb hmono hopen K
  refine ⟨n, Module.DirectLimit.of ℤ (CompactsIn (W n)) (cohomGWInt (W n) k)
    (cohomFWInt (W n) k) ⟨K.1, hKn⟩ a, ?_⟩
  rw [cscOpenMonotoneInt_of]
  rfl

/-- **CSC vanishing stage (injectivity side)**: a stage class dying in `Hᵏ_c(⋃ i, W i;ℤ)` already dies at
a later stage `W m ⊇ W n` (`Module.DirectLimit.of.zero_exact` + compact absorption). -/
theorem cscOpen_iUnion_vanish_stageInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k n : ℕ) (α : CompactlySupportedCohomologyOpenInt (W n) k)
    (h0 : cscOpenMonotoneInt (Set.subset_iUnion W n) k α = 0) :
    ∃ m, ∃ hnm : n ≤ m, cscOpenMonotoneInt (monotone_subset hmono hnm) k α = 0 := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotoneInt_of] at h0
    obtain ⟨K', hKK', hf0⟩ := Module.DirectLimit.of.zero_exact h0
    obtain ⟨m₀, hK'm⟩ := compactsIn_iUnion_absorb hmono hopen K'
    refine ⟨max n m₀, le_max_left n m₀, ?_⟩
    rw [cscOpenMonotoneInt_of]
    set Km : CompactsIn (W (max n m₀)) :=
      compactsInIncl (monotone_subset hmono (le_max_left n m₀)) K with hKm
    set Km' : CompactsIn (W (max n m₀)) :=
      ⟨K'.1, hK'm.trans (monotone_subset hmono (le_max_right n m₀))⟩ with hKm'
    have hle : Km ≤ Km' := hKK'
    have harg : cohomFWInt (W (max n m₀)) k Km Km' hle a = 0 := hf0
    have h1 : Module.DirectLimit.of ℤ (CompactsIn (W (max n m₀)))
        (cohomGWInt (W (max n m₀)) k) (cohomFWInt (W (max n m₀)) k) Km'
          (cohomFWInt (W (max n m₀)) k Km Km' hle a) = 0 := by
      rw [harg, map_zero]
    exact (Module.DirectLimit.of_f).symm.trans h1

/-! ## §3. Exhaustion of the subspace homology `H_d(sub Wu;ℤ)` -/

/-- **The `chainIncl`–`mapChainInt` tower bridge**: including a `sub V`-chain into the ambient space
through the intermediate subspace `sub V'` (`V ⊆ V'`) is the direct inclusion. -/
theorem chainIncl_mapChain_subInclCMInt {V V' : Set ↑X} (h : V ⊆ V') (n : ℕ)
    (c : SingularChainInt (sub V) n) :
    chainIncl V' n (mapChainInt (subInclCM h) n c) = chainIncl V n c := by
  rw [← mapChainInt_ambIncl V', ← mapChainInt_comp,
    show (ambIncl V').comp (subInclCM h) = ambIncl V from ContinuousMap.ext fun _ => rfl,
    mapChainInt_ambIncl]

/-- The ambient realization of an integral subspace cycle is an ambient cycle. -/
theorem chainIncl_mem_cyclesInt {S : Set ↑X} {d : ℕ} (z : cycles (sub S) d) :
    chainIncl S d (z : SingularChainInt (sub S) d) ∈ cycles X d := by
  have h1 : mapChainInt (ambIncl S) d (z : SingularChainInt (sub S) d) ∈ cycles X d :=
    mapChainInt_mem_cycles (ambIncl S) z.2
  rwa [mapChainInt_ambIncl] at h1

/-- **Homology exhaustion (surjectivity)**: every class of `H_d(sub (⋃ i, W i);ℤ)` is the `homOfSubsetInt`
image of a stage class. -/
theorem homology_iUnion_exhaustInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (d : ℕ) (y : Homology (sub (⋃ i, W i)) d) :
    ∃ (n : ℕ) (yn : Homology (sub (W n)) d), homOfSubsetInt (Set.subset_iUnion W n) d yn = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  set c : SingularChainInt X d := chainIncl (⋃ i, W i) d (z : SingularChainInt (sub (⋃ i, W i)) d)
    with hc_def
  have hc : c ∈ subspaceChainsInt (⋃ i, W i) d := ⟨(z : SingularChainInt (sub (⋃ i, W i)) d), rfl⟩
  obtain ⟨n, hn⟩ := exists_compact_subset_stage hmono hopen (isCompact_chainImageInt c)
    (chainImage_subset_of_mem_subspaceChainsInt hc)
  have hcn : c ∈ subspaceChainsInt (W n) d :=
    mem_subspaceChainsInt_of_support fun τ hτ x hx =>
      hn ((mem_chainImageInt_iff c x).mpr ⟨τ, hτ, hx⟩)
  set zn : SingularChainInt (sub (W n)) d := (inclRangeEquiv (W n) d).symm ⟨c, hcn⟩ with hzn_def
  have hzn_incl : chainIncl (W n) d zn = c := chainIncl_inclRangeEquiv_symm (W n) d ⟨c, hcn⟩
  have hzn_cyc : zn ∈ cycles (sub (W n)) d := by
    cases d with
    | zero => exact Submodule.mem_top
    | succ e =>
      show chainBoundary (sub (W n)) e zn = 0
      apply chainIncl_injective (W n) e
      rw [chainIncl_chainBoundary, map_zero, hzn_incl]
      exact chainIncl_mem_cyclesInt z
  refine ⟨n, Homology.mk (sub (W n)) d ⟨zn, hzn_cyc⟩, ?_⟩
  show Homology.mapInt (subInclCM (Set.subset_iUnion W n)) d
      (Homology.mk (sub (W n)) d ⟨zn, hzn_cyc⟩) = Homology.mk (sub (⋃ i, W i)) d z
  rw [Homology.mapInt_mk]
  refine congrArg (Homology.mk (sub (⋃ i, W i)) d) (Subtype.ext ?_)
  rw [cyclesMapInt_coe]
  apply chainIncl_injective (⋃ i, W i) d
  rw [chainIncl_mapChain_subInclCMInt, hzn_incl]

/-- Vanishing-class extraction (quotient → chain level), generic space. -/
theorem homology_mk_eq_zero_extractInt {Y : TopCat} {dd : ℕ} (w : cycles Y dd)
    (h0 : Homology.mk Y dd w = 0) :
    ∃ b : SingularChainInt Y (dd + 1), chainBoundary Y dd b = (w : SingularChainInt Y dd) := by
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h0
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

/-- Vanishing class from a bounding chain (chain → quotient level), generic space. -/
theorem homology_mk_eq_zero_of_boundaryInt {Y : TopCat} {dd : ℕ} (w : cycles Y dd)
    (b : SingularChainInt Y (dd + 1)) (hb : chainBoundary Y dd b = (w : SingularChainInt Y dd)) :
    Homology.mk Y dd w = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  exact ⟨b, hb⟩

/-- **Boundary transport across an absorbing subset** (chain level). -/
theorem mapChain_bounds_of_absorbInt {A B C : Set ↑X} (hAB : A ⊆ B) (hAC : A ⊆ C) {d : ℕ}
    (zA : SingularChainInt (sub A) d) (b : SingularChainInt (sub B) (d + 1))
    (hb : chainBoundary (sub B) d b = mapChainInt (subInclCM hAB) d zA)
    (hcC : chainIncl B (d + 1) b ∈ subspaceChainsInt C (d + 1)) :
    ∃ bC : SingularChainInt (sub C) (d + 1),
      chainBoundary (sub C) d bC = mapChainInt (subInclCM hAC) d zA := by
  refine ⟨(inclRangeEquiv C (d + 1)).symm ⟨chainIncl B (d + 1) b, hcC⟩, ?_⟩
  apply chainIncl_injective C d
  rw [chainIncl_chainBoundary, chainIncl_inclRangeEquiv_symm, ← chainIncl_chainBoundary, hb,
    chainIncl_mapChain_subInclCMInt, chainIncl_mapChain_subInclCMInt]

/-- **`homOfSubsetInt`-vanishing extraction** (thin glue). -/
theorem homOfSubset_mk_eq_zero_extractInt {A B : Set ↑X} (h : A ⊆ B) {d : ℕ}
    (z : cycles (sub A) d) (h0 : homOfSubsetInt h d (Homology.mk (sub A) d z) = 0) :
    ∃ b : SingularChainInt (sub B) (d + 1),
      chainBoundary (sub B) d b = mapChainInt (subInclCM h) d (z : SingularChainInt (sub A) d) := by
  rw [homOfSubsetInt, Homology.mapInt_mk] at h0
  obtain ⟨b, hb⟩ := homology_mk_eq_zero_extractInt _ h0
  exact ⟨b, hb⟩

/-- **`homOfSubsetInt`-vanishing from a bounding chain** (thin glue). -/
theorem homOfSubset_mk_eq_zero_of_boundaryInt {A B : Set ↑X} (h : A ⊆ B) {d : ℕ}
    (z : cycles (sub A) d) (b : SingularChainInt (sub B) (d + 1))
    (hb : chainBoundary (sub B) d b = mapChainInt (subInclCM h) d (z : SingularChainInt (sub A) d)) :
    homOfSubsetInt h d (Homology.mk (sub A) d z) = 0 := by
  rw [homOfSubsetInt, Homology.mapInt_mk]
  exact homology_mk_eq_zero_of_boundaryInt _ b hb

/-- **Homology vanishing stage (injectivity side)**: a stage class dying in `H_d(sub (⋃ i, W i);ℤ)`
already dies at a later stage. -/
theorem homology_iUnion_vanish_stageInt (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (d n : ℕ) (yn : Homology (sub (W n)) d)
    (h0 : homOfSubsetInt (Set.subset_iUnion W n) d yn = 0) :
    ∃ m, ∃ hnm : n ≤ m, homOfSubsetInt (monotone_subset hmono hnm) d yn = 0 := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ yn
  have hyn : Homology.mk (sub (W n)) d z = yn := hz
  rw [← hyn] at h0
  obtain ⟨b, hb⟩ := homOfSubset_mk_eq_zero_extractInt (Set.subset_iUnion W n) z h0
  have hcb : chainIncl (⋃ i, W i) (d + 1) b ∈ subspaceChainsInt (⋃ i, W i) (d + 1) := ⟨b, rfl⟩
  obtain ⟨m₀, hm₀⟩ := exists_compact_subset_stage hmono hopen
    (isCompact_chainImageInt (chainIncl (⋃ i, W i) (d + 1) b))
    (chainImage_subset_of_mem_subspaceChainsInt hcb)
  refine ⟨max n m₀, le_max_left n m₀, ?_⟩
  have hcbm : chainIncl (⋃ i, W i) (d + 1) b ∈ subspaceChainsInt (W (max n m₀)) (d + 1) :=
    mem_subspaceChainsInt_of_support fun τ hτ x hx =>
      monotone_subset hmono (le_max_right n m₀)
        (hm₀ ((mem_chainImageInt_iff (chainIncl (⋃ i, W i) (d + 1) b) x).mpr ⟨τ, hτ, hx⟩))
  obtain ⟨bC, hbC⟩ := mapChain_bounds_of_absorbInt (Set.subset_iUnion W n)
    (monotone_subset hmono (le_max_left n m₀)) (z : SingularChainInt (sub (W n)) d) b hb hcbm
  rw [← hyn]
  exact homOfSubset_mk_eq_zero_of_boundaryInt (monotone_subset hmono (le_max_left n m₀)) z bC hbC

/-! ## §4. THE PAYOFF — monotone-union stability of the open duality maps -/

/-- **Monotone-union stability, generic form** (integral): a family of duality maps
`D_V : Hᵏ_c(V;ℤ) → H_d(sub V;ℤ)` natural in `V` (w.r.t. `cscOpenMonotoneInt`/`homOfSubsetInt`) and
bijective at every stage of a monotone open tower is bijective on the union. -/
theorem duality_monotone_union_bijectiveInt {k d : ℕ}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (D : ∀ V : Set ↑X, IsOpen V →
      (CompactlySupportedCohomologyOpenInt V k →ₗ[ℤ] Homology (sub V) d))
    (hnat : ∀ (V V' : Set ↑X) (hV : IsOpen V) (hV' : IsOpen V') (hVV' : V ⊆ V')
      (α : CompactlySupportedCohomologyOpenInt V k),
      D V' hV' (cscOpenMonotoneInt hVV' k α) = homOfSubsetInt hVV' d (D V hV α))
    (hbij : ∀ n, Function.Bijective (D (W n) (hopen n))) :
    Function.Bijective (D (⋃ i, W i) (isOpen_iUnion hopen)) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun ξ h0 => ?_
    obtain ⟨n, β, rfl⟩ := cscOpen_iUnion_exhaustInt hmono hopen k ξ
    rw [hnat (W n) (⋃ i, W i) (hopen n) (isOpen_iUnion hopen) (Set.subset_iUnion W n) β] at h0
    obtain ⟨m, hnm, hdie⟩ :=
      homology_iUnion_vanish_stageInt hmono hopen d n (D (W n) (hopen n) β) h0
    have hDm : D (W m) (hopen m) (cscOpenMonotoneInt (monotone_subset hmono hnm) k β) = 0 := by
      rw [hnat (W n) (W m) (hopen n) (hopen m) (monotone_subset hmono hnm) β]
      exact hdie
    have hβm : cscOpenMonotoneInt (monotone_subset hmono hnm) k β = 0 :=
      (hbij m).injective (by rw [hDm, map_zero])
    have hcomp := LinearMap.congr_fun
      (cscOpenMonotoneInt_comp (monotone_subset hmono hnm) (Set.subset_iUnion W m) k) β
    rw [LinearMap.comp_apply, hβm, map_zero] at hcomp
    exact hcomp.symm
  · intro y
    obtain ⟨n, yn, rfl⟩ := homology_iUnion_exhaustInt hmono hopen d y
    obtain ⟨β, hβ⟩ := (hbij n).surjective yn
    exact ⟨cscOpenMonotoneInt (Set.subset_iUnion W n) k β, by
      rw [hnat (W n) (⋃ i, W i) (hopen n) (isOpen_iUnion hopen) (Set.subset_iUnion W n) β, hβ]⟩

/-- **THE PAYOFF — monotone-union stability of the open integral Poincaré-duality map** (Hatcher 3.36
(iii)): if `D_{W n} : Hᵏ_c(W n;ℤ) → H_{m+1}(sub (W n);ℤ)` is bijective for every stage of a monotone tower
of opens, then `D` is bijective on the union `⋃ i, W i`. Instantiates `duality_monotone_union_bijectiveInt`
with the `openDuality` family + its naturality `openDuality_cscOpenMonotoneInt`. -/
theorem openDuality_monotone_union_bijectiveInt [T2Space ↑X] {k m : ℕ}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (z₀ : SingularChainInt X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (hbij : ∀ n, Function.Bijective (openDuality (k := k) (m := m) (hopen n) z₀ hz₀)) :
    Function.Bijective (openDuality (k := k) (m := m) (isOpen_iUnion hopen) z₀ hz₀) :=
  duality_monotone_union_bijectiveInt hmono hopen
    (fun _V hV => openDuality (k := k) (m := m) hV z₀ hz₀)
    (fun _V _V' hV hV' hVV' α =>
      openDuality_cscOpenMonotoneInt (k := k) (m := m) hV hV' hVV' z₀ hz₀ α)
    hbij

end SKEFTHawking.SingularOpenDualityMonotoneUnionInt
