import Mathlib
import SKEFTHawking.SingularSubdivisionInt
import SKEFTHawking.SingularExcision

/-!
# The signed **integral** small-chains theorem (toward integral singular excision)

Integral (signed) mirror of the geometric small-chains core of `SingularExcision`. The **geometric**
inputs — diameter `diamLe`, subordination `IsSubordinate`, the Lebesgue-smallness result
`exists_iterate_subordinate`, the range/face lemmas — are all coefficient-AGNOSTIC (about the
`.support` and geometric realizations, not the coefficient module), so are reused directly from the
mod-2 `SingularExcision` / `SingularSubdivisionDiameter`; only the ℤ-linear small-subcomplex
`smallChainsInt` and the SIGNED cycle-homologous-to-subdivision fact are new.

Delivered over ℤ:
* `smallChainsInt` = the ℤ-span of subordinate simplices, a subcomplex (`chainBoundary`-closed);
* `singularSdInt` preserves smallness + `exists_iterate_smallChainsInt` (any chain becomes small);
* the SIGNED homology fact `c − Sdᵐ c = ∂(Dₘ c)` (`sub_singularSdInt_iterate_eq_boundary`, from
  `iterHomotopyInt_chainHomotopy`) + `exists_small_cycle_homologousInt` (the surjective half).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularExcisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularAffineChainInt
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularExcision (IsSubordinate range_pushSimplexM_subset)
open SKEFTHawking.SingularExcisionPushforward (pushSimplexM)
open SKEFTHawking.SingularCohomologyInt (face)

variable {X : TopCat}

/-! ## §0. The integral affine diameter estimate (support-based, signed mirror)

`diamLeInt` and the shrinkage lemmas are about the `.support` of a chain (which basis simplices appear),
so are coefficient-agnostic in content; only the linear operators `coneInt`/`linBoundaryInt`/
`linSubdivInt` differ from mod-2. The geometric BOUND lemmas (`norm_barycenter_sub_convexHull_le`,
`div_succ_le_div_succ_succ`) are reused verbatim from `SingularSubdivisionDiameter`. -/

section Diameter

open SKEFTHawking.SingularSubdivisionDiameter (norm_barycenter_sub_convexHull_le div_succ_le_div_succ_succ)
open SKEFTHawking.SingularExcisionMod2 (barycenter)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The integral diameter invariant**: every basis simplex of `c` has all pairwise vertex distances
`≤ δ`. -/
def diamLeInt (δ : ℝ) {n : ℕ} (c : LinChainInt V n) : Prop :=
  ∀ w ∈ c.support, ∀ i k, ‖w i - w k‖ ≤ δ

omit [NormedSpace ℝ V] in
theorem diamLeInt_zero_chain (δ : ℝ) {n : ℕ} : diamLeInt δ (0 : LinChainInt V n) := by
  intro w hw; simp at hw

omit [NormedSpace ℝ V] in
theorem diamLeInt.mono {δ δ' : ℝ} (hle : δ ≤ δ') {n : ℕ} {c : LinChainInt V n} (h : diamLeInt δ c) :
    diamLeInt δ' c := fun w hw i k => (h w hw i k).trans hle

omit [NormedSpace ℝ V] in
theorem diamLeInt_single {δ : ℝ} {n : ℕ} {v : Fin (n + 1) → V} {a : ℤ}
    (h : ∀ i k, ‖v i - v k‖ ≤ δ) : diamLeInt δ (Finsupp.single v a) := by
  intro w hw i k
  obtain rfl := Finset.mem_singleton.1 (Finset.mem_of_subset Finsupp.support_single_subset hw)
  exact h i k

omit [NormedSpace ℝ V] in
theorem diamLeInt.add {δ : ℝ} {n : ℕ} {c d : LinChainInt V n} (hc : diamLeInt δ c)
    (hd : diamLeInt δ d) : diamLeInt δ (c + d) := by
  classical
  intro w hw i k
  rcases Finset.mem_union.1 (Finsupp.support_add hw) with h | h
  · exact hc w h i k
  · exact hd w h i k

omit [NormedSpace ℝ V] in
theorem diamLeInt.smul {δ : ℝ} {n : ℕ} (a : ℤ) {c : LinChainInt V n} (hc : diamLeInt δ c) :
    diamLeInt δ (a • c) :=
  fun w hw => hc w (Finsupp.support_smul hw)

omit [NormedSpace ℝ V] in
theorem diamLeInt.sum {δ : ℝ} {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → LinChainInt V n)
    (hf : ∀ i ∈ s, diamLeInt δ (f i)) : diamLeInt δ (∑ i ∈ s, f i) :=
  Finset.sum_induction f (diamLeInt δ) (fun _ _ => diamLeInt.add) (diamLeInt_zero_chain δ) hf

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- Membership in `chainsInInt S` forces every vertex of every support simplex into `S`. -/
theorem chainsInInt_support {S : Set V} {n : ℕ} {c : LinChainInt V n}
    (hc : c ∈ chainsInInt S n) : ∀ w ∈ c.support, ∀ i, w i ∈ S := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨u, hu, rfl⟩ w hw i
    obtain rfl := Finset.mem_singleton.1 (Finset.mem_of_subset Finsupp.support_single_subset hw)
    exact hu i
  · intro w hw; simp at hw
  · intro x y _ _ hx hy w hw i
    rcases Finset.mem_union.1 (Finsupp.support_add hw) with h | h
    · exact hx w h i
    · exact hy w h i
  · intro a x _ hx w hw i; exact hx w (Finsupp.support_smul hw) i

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- The integral cone is the relabelling `v ↦ Fin.cons b v`. -/
theorem coneInt_eq_mapDomain (b : V) (n : ℕ) (c : LinChainInt V n) :
    coneInt b n c = Finsupp.mapDomain (Fin.cons b) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.mapDomain_zero]
  | add c d hc hd => rw [map_add, Finsupp.mapDomain_add, hc, hd]
  | single v a => rw [coneInt_single_smul, Finsupp.mapDomain_single, Finsupp.smul_single,
      smul_eq_mul, mul_one]

omit [NormedSpace ℝ V] in
/-- **Cone diameter preservation** (integral). -/
theorem coneInt_diamLeInt {δ : ℝ} {m : ℕ} {b : V} {c : LinChainInt V m}
    (hb : ∀ w ∈ c.support, ∀ i, ‖b - w i‖ ≤ δ) (hc : diamLeInt δ c) :
    diamLeInt δ (coneInt b m c) := by
  classical
  rw [coneInt_eq_mapDomain]
  intro w' hw' i k
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw')
  refine Fin.cases ?_ (fun j => ?_) i
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp only [Fin.cons_zero, sub_self, norm_zero]
      exact (norm_nonneg _).trans (hb w hw 0)
    · simpa only [Fin.cons_zero, Fin.cons_succ] using hb w hw l
  · refine Fin.cases ?_ (fun l => ?_) k
    · simp only [Fin.cons_succ, Fin.cons_zero]
      rw [norm_sub_rev]
      exact hb w hw j
    · simpa only [Fin.cons_succ] using hc w hw j l

/-- **Barycentric subdivision contracts diameter by `n/(n+1)`** (integral). -/
theorem linSubdivInt_diamLeInt {δ : ℝ} : ∀ (n : ℕ) {c : LinChainInt V n}, diamLeInt δ c →
    diamLeInt ((n : ℝ) / ((n : ℝ) + 1) * δ) (linSubdivInt n c)
  | 0, c, _ => by
    rw [linSubdivInt_zero]
    intro w _ i k
    rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero k, sub_self, norm_zero]
    simp
  | n + 1, c, hc => by
    have hrw : linSubdivInt (n + 1) c
        = c.sum (fun v a => linSubdivInt (n + 1) (Finsupp.single v a)) := by
      conv_lhs => rw [← Finsupp.sum_single c]
      simp only [Finsupp.sum, map_sum]
    rw [hrw, Finsupp.sum]
    refine diamLeInt.sum _ _ (fun v hv => ?_)
    have hvd : ∀ i k, ‖v i - v k‖ ≤ δ := hc v hv
    rw [linSubdivInt_single_smul]
    refine diamLeInt.smul _ (coneInt_diamLeInt (fun w hw i => ?_) ?_)
    · have hmem : w i ∈ convexHull ℝ (Set.range v) :=
        chainsInInt_support (linSubdivInt_mem_chainsInInt (convex_convexHull ℝ _) n
          (linBoundaryInt_mem_chainsInInt (single_mem_chainsInInt
            (fun j => subset_convexHull ℝ (Set.range v) (Set.mem_range_self j))))) w hw i
      exact norm_barycenter_sub_convexHull_le v hmem hvd
    · refine (linSubdivInt_diamLeInt n ?_).mono
        (mul_le_mul_of_nonneg_right (div_succ_le_div_succ_succ n)
          ((norm_nonneg _).trans (hvd 0 0)))
      rw [linBoundaryInt_single, linBoundaryBasisInt]
      exact diamLeInt.sum _ _ (fun i _ => diamLeInt.smul _ (diamLeInt_single (fun a b => hvd _ _)))

/-- **Iterated subdivision contracts diameter geometrically** (integral). -/
theorem linSubdivInt_iterate_diamLeInt {δ : ℝ} {n : ℕ} :
    ∀ (m : ℕ) {c : LinChainInt V n}, diamLeInt δ c →
      diamLeInt (((n : ℝ) / ((n : ℝ) + 1)) ^ m * δ) ((linSubdivInt n)^[m] c)
  | 0, c, hc => by simpa using hc
  | m + 1, c, hc => by
    rw [Function.iterate_succ_apply']
    refine (linSubdivInt_diamLeInt n (linSubdivInt_iterate_diamLeInt m hc)).mono (le_of_eq ?_)
    rw [pow_succ]; ring

/-- **Existence of an arbitrarily fine subdivision** (integral). -/
theorem exists_iterate_diamLeInt {δ : ℝ} {n : ℕ} {c : LinChainInt V n} (hc : diamLeInt δ c)
    {ε : ℝ} (hε : 0 < ε) : ∃ m, diamLeInt ε ((linSubdivInt n)^[m] c) := by
  have hr0 : (0 : ℝ) ≤ (n : ℝ) / ((n : ℝ) + 1) := by positivity
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have htend : Filter.Tendsto (fun m => ((n : ℝ) / ((n : ℝ) + 1)) ^ m * δ) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const δ
  obtain ⟨m, hm⟩ := (htend.eventually_lt_const hε).exists
  exact ⟨m, (linSubdivInt_iterate_diamLeInt m hc).mono (le_of_lt hm)⟩

/-- The standard `n`-simplex's identity affine chain `ιₙ` has diameter `≤ 1` (integral). -/
theorem idChainInt_diamLeInt (n : ℕ) : diamLeInt (1 : ℝ) (idChainInt n) := by
  rw [idChainInt]
  refine diamLeInt_single (fun i k => ?_)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro l
  simp only [Pi.sub_apply, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- **Arbitrarily fine subdivision of the model simplex** (integral). -/
theorem exists_iterate_idChainInt_diamLeInt (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, diamLeInt ε ((⇑(linSubdivInt n))^[m] (idChainInt n)) :=
  exists_iterate_diamLeInt (idChainInt_diamLeInt n) hε

end Diameter

/-- **Lebesgue smallness for a singular simplex** (integral): enough subdivisions make every simplex of
`Sdᵐ[σ]` subordinate to `𝒰`. Mirror of `SingularExcision.exists_iterate_subordinate`, reusing the
geometric `linSubdiv`/`idChain`/diameter substrate (mod-2, coefficient-agnostic support) and bridging
through the integral iterate connection `singularSdInt_iterate_single`. Subordination is a pure
range property, so the affine-side `linSubdiv`-diameter (mod-2) suffices. -/
theorem exists_iterate_subordinateInt {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    {𝒰 : Set (Set X)} (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) :
    ∃ m, ∀ τ ∈ ((⇑(singularSdInt X n))^[m] (Finsupp.single σ 1)).support,
      IsSubordinate 𝒰 τ := by
  classical
  set f := X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ with hfdef
  have hopen : ∀ U : ↥𝒰, IsOpen (f ⁻¹' interior (U : Set X)) :=
    fun U => isOpen_interior.preimage f.continuous
  have hcover : (Set.univ : Set ↥(stdSimplex ℝ (Fin (n + 1)))) ⊆
      ⋃ U : ↥𝒰, f ⁻¹' interior (U : Set X) := by
    intro t _
    have ht : (f t : X) ∈ ⋃ U ∈ 𝒰, interior U := by rw [hcov]; trivial
    obtain ⟨U, hU, htU⟩ := Set.mem_iUnion₂.1 ht
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, htU⟩
  obtain ⟨δ, hδ, hlb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  obtain ⟨m, hm⟩ := exists_iterate_idChainInt_diamLeInt n (ε := δ / 2) (by positivity)
  refine ⟨m, fun τ hτ => ?_⟩
  rw [singularSdInt_iterate_single, pushChainMInt, Finsupp.lmapDomain_apply] at hτ
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  have hu : ∀ j, w j ∈ stdSimplex ℝ (Fin (n + 1)) :=
    chainsInInt_support (linSubdivInt_iterate_idChainInt_mem n m) w hw
  obtain ⟨U, hUball⟩ := hlb ⟨w 0, hu 0⟩ (Set.mem_univ _)
  exact ⟨(U : Set X), U.property,
    (range_pushSimplexM_subset σ hu (by linarith) (fun j => hm w hw 0 j) hUball).trans
      interior_subset⟩

/-! ## §1. The integral small subcomplex `smallChainsInt` -/

/-- The subcomplex of `𝒰`-**small** singular integral `n`-chains: the ℤ-span of the subordinate
simplices (`IsSubordinate` is coefficient-agnostic, reused from `SingularExcision`). -/
noncomputable def smallChainsInt (𝒰 : Set (Set X)) (n : ℕ) :
    Submodule ℤ (SingularChainInt X n) :=
  Submodule.span ℤ {c | ∃ τ, IsSubordinate 𝒰 τ ∧ c = Finsupp.single τ 1}

theorem single_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))} (hτ : IsSubordinate 𝒰 τ) :
    Finsupp.single τ 1 ∈ smallChainsInt 𝒰 n :=
  Submodule.subset_span ⟨τ, hτ, rfl⟩

/-- Pushing an in-simplex affine chain along a **subordinate** simplex `τ` lands in the small chains
(integral): every piece's image is inside `τ`'s image (`range_pushSimplexM_subset_range`, geometric). -/
theorem pushChainMInt_mem_smallChainsInt {N n : ℕ} {𝒰 : Set (Set X)}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N))} (hτ : IsSubordinate 𝒰 τ)
    {c : LinChainInt (Fin (N + 1) → ℝ) n} (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (N + 1))) n) :
    pushChainMInt τ c ∈ smallChainsInt 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [pushChainMInt_single]
    obtain ⟨U, hU𝒰, hUrange⟩ := hτ
    exact single_mem_smallChainsInt
      ⟨U, hU𝒰, (SingularExcision.range_pushSimplexM_subset_range τ hw).trans hUrange⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **The singular subdivision preserves smallness** (integral). -/
theorem singularSdInt_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChainInt X n} (hc : c ∈ smallChainsInt 𝒰 n) :
    singularSdInt X n c ∈ smallChainsInt 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [singularSdInt_single]
    exact pushChainMInt_mem_smallChainsInt hτ
      (linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- A chain all of whose support simplices are subordinate is small (integral). -/
theorem mem_smallChainsInt_of_support {n : ℕ} {𝒰 : Set (Set X)} {c : SingularChainInt X n}
    (h : ∀ τ ∈ c.support, IsSubordinate 𝒰 τ) : c ∈ smallChainsInt 𝒰 n := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum]
  refine Submodule.sum_mem _ (fun τ hτ => ?_)
  have hτs : Finsupp.single τ (c τ) = (c τ) • Finsupp.single τ (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hτs]
  exact Submodule.smul_mem _ _ (single_mem_smallChainsInt (h τ hτ))

/-- Iterating `Sd` keeps a small chain small (integral). -/
theorem singularSdInt_iterate_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChainInt X n} (hc : c ∈ smallChainsInt 𝒰 n) (m : ℕ) :
    (⇑(singularSdInt X n))^[m] c ∈ smallChainsInt 𝒰 n := by
  induction m with
  | zero => rwa [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply']; exact singularSdInt_mem_smallChainsInt ih

/-- **Any chain becomes small under enough subdivisions** (integral): reuses the geometric
`exists_iterate_subordinate` (support-based, coefficient-agnostic) + `singularSdInt_iterate_single`. -/
theorem exists_iterate_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) (c : SingularChainInt X n) :
    ∃ m, (⇑(singularSdInt X n))^[m] c ∈ smallChainsInt 𝒰 n := by
  classical
  choose! M hM using fun (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) =>
    exists_iterate_subordinateInt τ hcov
  obtain ⟨m, hm⟩ : ∃ m, ∀ τ ∈ c.support, M τ ≤ m :=
    ⟨c.support.sup M, fun _ hτ => Finset.le_sup hτ⟩
  refine ⟨m, ?_⟩
  rw [← Finsupp.sum_single c, ← Module.End.coe_pow, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ (fun τ hτ => ?_)
  have hτs : Finsupp.single τ (c τ) = (c τ) • Finsupp.single τ (1 : ℤ) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hτs, map_smul, Module.End.coe_pow,
    ← Nat.sub_add_cancel (hm τ hτ), Function.iterate_add_apply]
  exact Submodule.smul_mem _ _
    (singularSdInt_iterate_mem_smallChainsInt (mem_smallChainsInt_of_support (hM τ)) _)

/-- **`smallChainsInt` is a subcomplex**: the boundary of a small chain is small (integral). -/
theorem chainBoundary_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChainInt X (n + 1)} (hc : c ∈ smallChainsInt 𝒰 (n + 1)) :
    chainBoundary X n c ∈ smallChainsInt 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [chainBoundary_single, boundaryBasis]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
      (single_mem_smallChainsInt (hτ.face i)))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-! ## §2. The surjective half of the small-chains theorem (signed) -/

/-- The iterated-subdivision homotopy kills the zero chain (integral). -/
theorem iterHomotopyInt_zero (X : TopCat) (n m : ℕ) : iterHomotopyInt X n m 0 = 0 := by
  rw [iterHomotopyInt, map_zero]
  exact Finset.sum_eq_zero (fun i _ => by rw [← Module.End.coe_pow, map_zero])

/-- **A cycle is homologous to its subdivision** (integral, SIGNED): if `∂c = 0`, then
`c − Sdᵐ c = ∂(Dₘ c)` (the mod-2 file has `c + Sdᵐ c`). From `iterHomotopyInt_chainHomotopy`. -/
theorem sub_singularSdInt_iterate_eq_boundary {n : ℕ} {c : SingularChainInt X (n + 1)}
    (hc : chainBoundary X n c = 0) (m : ℕ) :
    c - (⇑(singularSdInt X (n + 1)))^[m] c
      = chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m c) := by
  have h := iterHomotopyInt_chainHomotopy X m n c
  rw [hc, iterHomotopyInt_zero, add_zero] at h
  exact h.symm

/-- **The surjective half of the small-chains theorem** (integral): every cycle `z` is homologous to a
*small* cycle `Sdᵐ z` for `m` large. So every integral singular homology class has a `𝒰`-small
representative — the surjectivity the excision iso consumes. -/
theorem exists_small_cycle_homologousInt {n : ℕ} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {z : SingularChainInt X (n + 1)}
    (hz : chainBoundary X n z = 0) :
    ∃ m, (⇑(singularSdInt X (n + 1)))^[m] z ∈ smallChainsInt 𝒰 (n + 1) ∧
      chainBoundary X n ((⇑(singularSdInt X (n + 1)))^[m] z) = 0 ∧
      z - (⇑(singularSdInt X (n + 1)))^[m] z ∈ LinearMap.range (chainBoundary X (n + 1)) := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChainsInt hcov z
  refine ⟨m, hm, ?_,
    ⟨iterHomotopyInt X (n + 1) m z, (sub_singularSdInt_iterate_eq_boundary hz m).symm⟩⟩
  rw [singularSdInt_iterate_chainBoundary, hz, ← Module.End.coe_pow, map_zero]

end SKEFTHawking.SingularExcisionInt
