import Mathlib
import SKEFTHawking.SingularOpenDualityNat
import SKEFTHawking.SingularChainSupport
import SKEFTHawking.SingularMayerVietorisLES

/-!
# Phase 5q.G (G1 PD-induction, arc-2) — monotone-union stability of the open duality maps

The A3 block of the Bott–Tu-style open-cover induction (Hatcher 3.36, condition (iii)): for an
ℕ-indexed **monotone** family of opens `W 0 ⊆ W 1 ⊆ ⋯` with union `Wu = ⋃ i, W i`, if the open
Poincaré-duality map `D_{W n}` is bijective for every `n` then `D_{Wu}` is bijective.

Contents:
1. **Compact absorption** (`exists_compact_subset_stage`/`compactsIn_iUnion_absorb`): a compact
   subset of the union lies in a single stage (compactness + directedness of the monotone open
   cover, `IsCompact.elim_directed_cover`).
2. **CSC exhaustion** (`cscOpen_iUnion_exhaust`): every class of `Hᵏ_c(Wu)` is the extension of a
   stage class (its `K`-stage compact is absorbed into some `W n`).
3. **CSC vanishing stage** (`cscOpen_iUnion_vanish_stage`): a stage class dying in `Hᵏ_c(Wu)` dies
   at a later stage (`Module.DirectLimit.of.zero_exact` + absorption of the witness compact).
4. **Homology exhaustion** (`homology_iUnion_exhaust`/`homology_iUnion_vanish_stage`): every class
   of `H_d(sub Wu)` comes from a stage (a cycle has compact image, absorbed into some `W n`, and
   pulls back through `subspaceChainsEquiv`), and a stage class dying in `H_d(sub Wu)` dies at a
   later stage (the bounding chain has compact image, absorbed likewise).
5. **THE PAYOFF** (`duality_monotone_union_bijective`, instantiated as
   `openDuality_monotone_union_bijective`): a family of duality maps `D_V : Hᵏ_c(V) → H_d(sub V)`
   natural in the open `V` (w.r.t. `cscOpenMonotone`/`homOfSubset`) and bijective at every stage of
   a monotone tower is bijective on the union.

The generic payoff `duality_monotone_union_bijective` is stated for an **arbitrary** homology
degree `d` (including `d = 0`) and an arbitrary compatible family, so the `openDuality₀`
bottom-degree instantiation (whose naturality square `openDuality₀_cscOpenMonotone` lives in the
not-yet-merged `SingularOpenDualityBotNat`) becomes a one-line corollary once that module lands —
exactly parallel to the `openDuality` instantiation below.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularExcision
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCSCOpenMonotone SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularChainSupport
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularOpenDualityNat

namespace SKEFTHawking.SingularOpenDualityMonotoneUnion

variable {X : TopCat} {W : ℕ → Set ↑X}

/-! ## §1. Compact absorption into a stage of the monotone tower -/

/-- Monotone-tower transport: `W a ⊆ W b` for `a ≤ b` (the one-step monotonicity iterated). -/
theorem monotone_subset (hmono : ∀ n, W n ⊆ W (n + 1)) {a b : ℕ} (hab : a ≤ b) : W a ⊆ W b :=
  monotone_nat_of_le_succ hmono hab

/-- **Compact absorption**: a compact subset of the monotone union `⋃ i, W i` of opens lies in a
single stage `W n` (the monotone family is a directed open cover; `IsCompact.elim_directed_cover`
collapses the finite subcover to one index). -/
theorem exists_compact_subset_stage (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    {K : Set ↑X} (hK : IsCompact K) (hKW : K ⊆ ⋃ i, W i) : ∃ n, K ⊆ W n :=
  hK.elim_directed_cover W hopen hKW (monotone_nat_of_le_succ hmono).directed_le

/-- **Compact absorption, packaged for the `Hᵏ_c` index poset**: a compact of the union
(`CompactsIn (⋃ i, W i)`) is a compact of a single stage. -/
theorem compactsIn_iUnion_absorb (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (K : CompactsIn (⋃ i, W i)) : ∃ n, (↑K.1 : Set ↑X) ⊆ W n :=
  exists_compact_subset_stage hmono hopen K.1.isCompact' K.2

/-! ## §2. Exhaustion of the compactly-supported cohomology `Hᵏ_c(Wu)` -/

/-- **CSC exhaustion (surjectivity)**: every class of `Hᵏ_c(⋃ i, W i)` is the `cscOpenMonotone`
extension of a class of some stage `Hᵏ_c(W n)` — its `K`-stage compact is absorbed into a stage. -/
theorem cscOpen_iUnion_exhaust (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k : ℕ) (ξ : CompactlySupportedCohomologyOpen (⋃ i, W i) k) :
    ∃ (n : ℕ) (β : CompactlySupportedCohomologyOpen (W n) k),
      cscOpenMonotone (Set.subset_iUnion W n) k β = ξ := by
  refine Module.DirectLimit.induction_on ξ (fun K a => ?_)
  obtain ⟨n, hKn⟩ := compactsIn_iUnion_absorb hmono hopen K
  refine ⟨n, Module.DirectLimit.of (ZMod 2) (CompactsIn (W n)) (cohomGW (W n) k)
    (cohomFW (W n) k) ⟨K.1, hKn⟩ a, ?_⟩
  rw [cscOpenMonotone_of]
  rfl

/-- **CSC vanishing stage (injectivity side)**: a stage class `α : Hᵏ_c(W n)` that dies in
`Hᵏ_c(⋃ i, W i)` already dies at a later stage `W m ⊇ W n` — the direct-limit vanishing witness
(`Module.DirectLimit.of.zero_exact`) is a compact of the union, absorbed into a stage. -/
theorem cscOpen_iUnion_vanish_stage (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (k n : ℕ) (α : CompactlySupportedCohomologyOpen (W n) k)
    (h0 : cscOpenMonotone (Set.subset_iUnion W n) k α = 0) :
    ∃ m, ∃ hnm : n ≤ m, cscOpenMonotone (monotone_subset hmono hnm) k α = 0 := by
  induction α using Module.DirectLimit.induction_on with
  | _ K a =>
    rw [cscOpenMonotone_of] at h0
    obtain ⟨K', hKK', hf0⟩ := Module.DirectLimit.of.zero_exact h0
    obtain ⟨m₀, hK'm⟩ := compactsIn_iUnion_absorb hmono hopen K'
    refine ⟨max n m₀, le_max_left n m₀, ?_⟩
    rw [cscOpenMonotone_of]
    set Km : CompactsIn (W (max n m₀)) :=
      compactsInIncl (monotone_subset hmono (le_max_left n m₀)) K with hKm
    set Km' : CompactsIn (W (max n m₀)) :=
      ⟨K'.1, hK'm.trans (monotone_subset hmono (le_max_right n m₀))⟩ with hKm'
    have hle : Km ≤ Km' := hKK'
    have harg : cohomFW (W (max n m₀)) k Km Km' hle a = 0 := hf0
    have h1 : Module.DirectLimit.of (ZMod 2) (CompactsIn (W (max n m₀)))
        (cohomGW (W (max n m₀)) k) (cohomFW (W (max n m₀)) k) Km'
          (cohomFW (W (max n m₀)) k Km Km' hle a) = 0 := by
      rw [harg, map_zero]
    exact (Module.DirectLimit.of_f).symm.trans h1

/-! ## §3. Exhaustion of the subspace homology `H_d(sub Wu)` -/

/-- **The `chainIncl`–`mapChain` tower bridge**: including a `sub V`-chain into the ambient space
through the intermediate subspace `sub V'` (`V ⊆ V'`) is the direct inclusion
(`mapChain_ambIncl` + functoriality `mapChain_comp`). -/
theorem chainIncl_mapChain_subInclCM {V V' : Set ↑X} (h : V ⊆ V') (n : ℕ)
    (c : SingularChain (sub V) n) :
    chainIncl V' n (mapChain (subInclCM h) n c) = chainIncl V n c := by
  rw [← mapChain_ambIncl V', ← mapChain_comp,
    show (ambIncl V').comp (subInclCM h) = ambIncl V from ContinuousMap.ext fun _ => rfl,
    mapChain_ambIncl]

/-- The ambient realization of a subspace cycle is an ambient cycle (`chainIncl` is a chain map). -/
theorem chainIncl_mem_cycles {S : Set ↑X} {d : ℕ} (z : cycles (sub S) d) :
    chainIncl S d (z : SingularChain (sub S) d) ∈ cycles X d := by
  have h1 : mapChain (ambIncl S) d (z : SingularChain (sub S) d) ∈ cycles X d :=
    mapChain_mem_cycles (ambIncl S) z.2
  rwa [mapChain_ambIncl] at h1

/-- **Homology exhaustion (surjectivity)**: every class of `H_d(sub (⋃ i, W i))` is the
`homOfSubset` image of a class of some stage `H_d(sub (W n))` — a representing cycle has compact
image (`isCompact_chainImage`), absorbed into a stage, and pulls back through
`subspaceChainsEquiv`. -/
theorem homology_iUnion_exhaust (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (d : ℕ) (y : Homology (sub (⋃ i, W i)) d) :
    ∃ (n : ℕ) (yn : Homology (sub (W n)) d), homOfSubset (Set.subset_iUnion W n) d yn = y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  set c : SingularChain X d := chainIncl (⋃ i, W i) d (z : SingularChain (sub (⋃ i, W i)) d)
    with hc_def
  have hc : c ∈ subspaceChains (⋃ i, W i) d := ⟨(z : SingularChain (sub (⋃ i, W i)) d), rfl⟩
  obtain ⟨n, hn⟩ := exists_compact_subset_stage hmono hopen (isCompact_chainImage c)
    (chainImage_subset_of_mem_subspaceChains hc)
  have hcn : c ∈ subspaceChains (W n) d :=
    mem_subspaceChains_of_support fun τ hτ x hx =>
      hn ((mem_chainImage_iff c x).mpr ⟨τ, hτ, hx⟩)
  set zn : SingularChain (sub (W n)) d := (subspaceChainsEquiv (W n) d).symm ⟨c, hcn⟩ with hzn_def
  have hzn_incl : chainIncl (W n) d zn = c := chainIncl_subspaceChainsEquiv_symm (W n) d ⟨c, hcn⟩
  have hzn_cyc : zn ∈ cycles (sub (W n)) d := by
    cases d with
    | zero => exact Submodule.mem_top
    | succ e =>
      show chainBoundary (sub (W n)) e zn = 0
      apply chainIncl_injective (W n) e
      rw [chainIncl_chainBoundary, map_zero, hzn_incl]
      exact chainIncl_mem_cycles z
  refine ⟨n, Homology.mk (sub (W n)) d ⟨zn, hzn_cyc⟩, ?_⟩
  show Homology.map (subInclCM (Set.subset_iUnion W n)) d (Homology.mk (sub (W n)) d ⟨zn, hzn_cyc⟩)
    = Homology.mk (sub (⋃ i, W i)) d z
  rw [Homology.map_mk]
  refine congrArg (Homology.mk (sub (⋃ i, W i)) d) (Subtype.ext ?_)
  rw [cyclesMap_coe]
  apply chainIncl_injective (⋃ i, W i) d
  rw [chainIncl_mapChain_subInclCM, hzn_incl]

/-- **Vanishing-class extraction, generic space** (quotient → chain level): a cycle whose homology
class vanishes is a boundary — the `Homology`-quotient unpacking, done ONCE at an abstract `TopCat`
(cheap elaboration) and reused at the concrete subspace types. -/
theorem homology_mk_eq_zero_extract {Y : TopCat} {dd : ℕ} (w : cycles Y dd)
    (h0 : Homology.mk Y dd w = 0) :
    ∃ b : SingularChain Y (dd + 1), chainBoundary Y dd b = (w : SingularChain Y dd) := by
  have hmem := (Submodule.Quotient.mk_eq_zero _).mp h0
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb⟩

/-- **Vanishing class from a bounding chain, generic space** (chain → quotient level): a cycle that
bounds has vanishing homology class — the `Homology`-quotient repacking, done ONCE at an abstract
`TopCat`. -/
theorem homology_mk_eq_zero_of_boundary {Y : TopCat} {dd : ℕ} (w : cycles Y dd)
    (b : SingularChain Y (dd + 1)) (hb : chainBoundary Y dd b = (w : SingularChain Y dd)) :
    Homology.mk Y dd w = 0 := by
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
  exact ⟨b, hb⟩

/-- **Boundary transport across an absorbing subset** (chain level): if the `sub B`-pushforward of
a `sub A`-chain `zA` bounds in `sub B` (`A ⊆ B`) and the ambient realization of the bounding chain
is supported in `C` (`A ⊆ C`), then the `sub C`-pushforward of `zA` bounds in `sub C` — the
bounding chain pulls back through `subspaceChainsEquiv`. The chain-level engine of the homology
vanishing stage. -/
theorem mapChain_bounds_of_absorb {A B C : Set ↑X} (hAB : A ⊆ B) (hAC : A ⊆ C) {d : ℕ}
    (zA : SingularChain (sub A) d) (b : SingularChain (sub B) (d + 1))
    (hb : chainBoundary (sub B) d b = mapChain (subInclCM hAB) d zA)
    (hcC : chainIncl B (d + 1) b ∈ subspaceChains C (d + 1)) :
    ∃ bC : SingularChain (sub C) (d + 1),
      chainBoundary (sub C) d bC = mapChain (subInclCM hAC) d zA := by
  refine ⟨(subspaceChainsEquiv C (d + 1)).symm ⟨chainIncl B (d + 1) b, hcC⟩, ?_⟩
  apply chainIncl_injective C d
  rw [chainIncl_chainBoundary, chainIncl_subspaceChainsEquiv_symm, ← chainIncl_chainBoundary, hb,
    chainIncl_mapChain_subInclCM, chainIncl_mapChain_subInclCM]

/-- **`homOfSubset`-vanishing extraction** (thin glue over `homology_mk_eq_zero_extract`): a stage
cycle whose `homOfSubset` image vanishes has a bounding chain for its pushforward. -/
theorem homOfSubset_mk_eq_zero_extract {A B : Set ↑X} (h : A ⊆ B) {d : ℕ}
    (z : cycles (sub A) d) (h0 : homOfSubset h d (Homology.mk (sub A) d z) = 0) :
    ∃ b : SingularChain (sub B) (d + 1),
      chainBoundary (sub B) d b = mapChain (subInclCM h) d (z : SingularChain (sub A) d) := by
  rw [homOfSubset, Homology.map_mk] at h0
  obtain ⟨b, hb⟩ := homology_mk_eq_zero_extract _ h0
  exact ⟨b, hb⟩

/-- **`homOfSubset`-vanishing from a bounding chain** (thin glue over
`homology_mk_eq_zero_of_boundary`): if the pushforward of a stage cycle bounds, its `homOfSubset`
image vanishes. -/
theorem homOfSubset_mk_eq_zero_of_boundary {A B : Set ↑X} (h : A ⊆ B) {d : ℕ}
    (z : cycles (sub A) d) (b : SingularChain (sub B) (d + 1))
    (hb : chainBoundary (sub B) d b = mapChain (subInclCM h) d (z : SingularChain (sub A) d)) :
    homOfSubset h d (Homology.mk (sub A) d z) = 0 := by
  rw [homOfSubset, Homology.map_mk]
  exact homology_mk_eq_zero_of_boundary _ b hb

/-- **Homology vanishing stage (injectivity side)**: a stage class of `H_d(sub (W n))` that dies in
`H_d(sub (⋃ i, W i))` already dies at a later stage `W m ⊇ W n` — the bounding chain of the union
has compact image, absorbed into a stage, and pulls back through `subspaceChainsEquiv`. -/
theorem homology_iUnion_vanish_stage (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (d n : ℕ) (yn : Homology (sub (W n)) d)
    (h0 : homOfSubset (Set.subset_iUnion W n) d yn = 0) :
    ∃ m, ∃ hnm : n ≤ m, homOfSubset (monotone_subset hmono hnm) d yn = 0 := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ yn
  have hyn : Homology.mk (sub (W n)) d z = yn := hz
  rw [← hyn] at h0
  obtain ⟨b, hb⟩ := homOfSubset_mk_eq_zero_extract (Set.subset_iUnion W n) z h0
  have hcb : chainIncl (⋃ i, W i) (d + 1) b ∈ subspaceChains (⋃ i, W i) (d + 1) := ⟨b, rfl⟩
  obtain ⟨m₀, hm₀⟩ := exists_compact_subset_stage hmono hopen
    (isCompact_chainImage (chainIncl (⋃ i, W i) (d + 1) b))
    (chainImage_subset_of_mem_subspaceChains hcb)
  refine ⟨max n m₀, le_max_left n m₀, ?_⟩
  have hcbm : chainIncl (⋃ i, W i) (d + 1) b ∈ subspaceChains (W (max n m₀)) (d + 1) :=
    mem_subspaceChains_of_support fun τ hτ x hx =>
      monotone_subset hmono (le_max_right n m₀)
        (hm₀ ((mem_chainImage_iff (chainIncl (⋃ i, W i) (d + 1) b) x).mpr ⟨τ, hτ, hx⟩))
  obtain ⟨bC, hbC⟩ := mapChain_bounds_of_absorb (Set.subset_iUnion W n)
    (monotone_subset hmono (le_max_left n m₀)) (z : SingularChain (sub (W n)) d) b hb hcbm
  rw [← hyn]
  exact homOfSubset_mk_eq_zero_of_boundary (monotone_subset hmono (le_max_left n m₀)) z bC hbC

/-! ## §4. THE PAYOFF — monotone-union stability of the open duality maps -/

/-- **Monotone-union stability, generic form**: a family of duality maps
`D_V : Hᵏ_c(V) → H_d(sub V)` over the opens of `X`, **natural** in `V` with respect to the
compactly-supported extension `cscOpenMonotone` and the subspace inclusion `homOfSubset`, that is
bijective at every stage of a monotone open tower `W 0 ⊆ W 1 ⊆ ⋯`, is bijective on the union
`⋃ i, W i`. Degree-generic (`d` arbitrary, including `d = 0`) and family-generic — the
`openDuality` (and, post-merge, `openDuality₀`) instantiations are one-liners. -/
theorem duality_monotone_union_bijective {k d : ℕ}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (D : ∀ V : Set ↑X, IsOpen V →
      (CompactlySupportedCohomologyOpen V k →ₗ[ZMod 2] Homology (sub V) d))
    (hnat : ∀ (V V' : Set ↑X) (hV : IsOpen V) (hV' : IsOpen V') (hVV' : V ⊆ V')
      (α : CompactlySupportedCohomologyOpen V k),
      D V' hV' (cscOpenMonotone hVV' k α) = homOfSubset hVV' d (D V hV α))
    (hbij : ∀ n, Function.Bijective (D (W n) (hopen n))) :
    Function.Bijective (D (⋃ i, W i) (isOpen_iUnion hopen)) := by
  constructor
  · -- injectivity: a union class killing under `D` comes from a stage (§2); its `D`-image dies in
    -- the union, hence at a later stage (§3); pull back via naturality + stage bijectivity.
    refine (injective_iff_map_eq_zero _).mpr fun ξ h0 => ?_
    obtain ⟨n, β, rfl⟩ := cscOpen_iUnion_exhaust hmono hopen k ξ
    rw [hnat (W n) (⋃ i, W i) (hopen n) (isOpen_iUnion hopen) (Set.subset_iUnion W n) β] at h0
    obtain ⟨m, hnm, hdie⟩ :=
      homology_iUnion_vanish_stage hmono hopen d n (D (W n) (hopen n) β) h0
    have hDm : D (W m) (hopen m) (cscOpenMonotone (monotone_subset hmono hnm) k β) = 0 := by
      rw [hnat (W n) (W m) (hopen n) (hopen m) (monotone_subset hmono hnm) β]
      exact hdie
    have hβm : cscOpenMonotone (monotone_subset hmono hnm) k β = 0 :=
      (hbij m).injective (by rw [hDm, map_zero])
    have hcomp := LinearMap.congr_fun
      (cscOpenMonotone_comp (monotone_subset hmono hnm) (Set.subset_iUnion W m) k) β
    rw [LinearMap.comp_apply, hβm, map_zero] at hcomp
    exact hcomp.symm
  · -- surjectivity: a union homology class comes from a stage (§3); hit it there (stage
    -- bijectivity); push forward and commute via naturality.
    intro y
    obtain ⟨n, yn, rfl⟩ := homology_iUnion_exhaust hmono hopen d y
    obtain ⟨β, hβ⟩ := (hbij n).surjective yn
    exact ⟨cscOpenMonotone (Set.subset_iUnion W n) k β, by
      rw [hnat (W n) (⋃ i, W i) (hopen n) (isOpen_iUnion hopen) (Set.subset_iUnion W n) β, hβ]⟩

/-- **THE PAYOFF — monotone-union stability of the open Poincaré-duality map** (Hatcher 3.36,
condition (iii), for an ℕ-indexed monotone tower): if `D_{W n} : Hᵏ_c(W n) → H_{m+1}(sub (W n))`
is bijective for every stage of a monotone tower of opens, then `D` is bijective on the union
`⋃ i, W i`. Instantiates `duality_monotone_union_bijective` with the `openDuality` family and its
naturality square `openDuality_cscOpenMonotone`. -/
theorem openDuality_monotone_union_bijective [T2Space ↑X] {k m : ℕ}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (z₀ : SingularChain X (k + m + 1)) (hz₀ : chainBoundary X (k + m) z₀ = 0)
    (hbij : ∀ n, Function.Bijective (openDuality (k := k) (m := m) (hopen n) z₀ hz₀)) :
    Function.Bijective (openDuality (k := k) (m := m) (isOpen_iUnion hopen) z₀ hz₀) :=
  duality_monotone_union_bijective hmono hopen
    (fun _V hV => openDuality (k := k) (m := m) hV z₀ hz₀)
    (fun _V _V' hV hV' hVV' α =>
      openDuality_cscOpenMonotone (k := k) (m := m) hV hV' hVV' z₀ hz₀ α)
    hbij

end SKEFTHawking.SingularOpenDualityMonotoneUnion
