/-
# Phase 5q.F brick 6c — singular excision: Lebesgue smallness → small chains

The capstone of the barycentric-subdivision engine. `SingularSubdivision` built the singular `Sd` as a
chain map with the chain homotopy `∂D+D∂ = 1−Sd` (so `Sdᵐ` is chain-homotopic to the identity), and
`SingularSubdivisionDiameter` proved the affine subdivision contracts diameter by `n/(n+1)`. This file
joins them: via the iterate connection `Sdᵐ[σ] = σ_#((Sd_aff)ᵐ ιₙ)` a piece of `Sdᵐσ` is `σ` composed
with an affine sub-simplex of arbitrarily small diameter, so — by uniform continuity of `σ` on the
compact `Δⁿ` and a Lebesgue number for an open cover — enough subdivisions make every simplex of a chain
"small" (subordinate to the cover). With the chain homotopy this gives **excision**.

This is the engine for the local homology `Hₙ(M, M∖x) ≅ ℤ/2` (brick 6d), hence the ℤ/2 fundamental class
(6e) and the Poincaré-duality datum `PoincareDual4Mid` (6f). Kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularSubdivision
import SKEFTHawking.SingularSubdivisionDiameter
import SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularExcision

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularExcisionPushforward SKEFTHawking.SingularSubdivisionConvex
open SKEFTHawking.SingularSubdivision SKEFTHawking.SingularSubdivisionDiameter

/-- The standard `n`-simplex's vertices `eᵢ = Pi.single i 1` have all pairwise sup-norm distances `≤ 1`
(`(eᵢ − eₖ) l ∈ {−1, 0, 1}`), so the identity affine chain `ιₙ` has diameter `≤ 1`. The seed the
iterated-subdivision shrinkage acts on. -/
theorem idChain_diamLe (n : ℕ) : diamLe (1 : ℝ) (idChain n) := by
  rw [idChain]
  refine diamLe_single (fun i k => ?_)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro l
  simp only [Pi.sub_apply, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- **Arbitrarily fine subdivision of the model simplex**: for any `ε > 0`, enough barycentric
subdivisions make every affine sub-simplex of `ιₙ` have diameter `< ε` (the contraction factor
`(n/(n+1))ᵐ → 0`). The geometric smallness input the Lebesgue-number step consumes. -/
theorem exists_iterate_idChain_diamLe (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, diamLe ε ((⇑(linSubdiv n))^[m] (idChain n)) :=
  exists_iterate_diamLe (idChain_diamLe n) hε

/-- The geometric realization of `pushSimplexM σ u` (for an in-simplex tuple `u`) is `σ̃` post-composed
with the affine simplex on `u` — `(σ_# u)~ = σ̃ ∘ affineSimplexStd ũ`. -/
theorem pushSimplexM_realize {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {u : Fin (n + 1) → (Fin (N + 1) → ℝ)} (hu : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1))) :
    X.toSSetObjEquiv (op (SimplexCategory.mk n)) (pushSimplexM σ u)
      = (X.toSSetObjEquiv (op (SimplexCategory.mk N)) σ).comp
          (affineSimplexStd (fun j => ⟨u j, hu j⟩)) := by
  rw [pushSimplexM_of_mem σ hu]
  exact Equiv.apply_symm_apply _ _

/-- **A small affine simplex pushes to a simplex with small image**: if every vertex of the in-simplex
tuple `u` is within `ε` of `u 0` and `σ̃` carries the metric ball `B(ũ₀, δ)` (with `ε < δ`) into `U`, then
the realization of `pushSimplexM σ u` has range in `U`. (Each affine-combination point `∑ tⱼ uⱼ` is within
`ε` of `u 0` by `norm_sub_affineSimplex_le`, hence in the ball.) -/
theorem range_pushSimplexM_subset {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {u : Fin (n + 1) → (Fin (N + 1) → ℝ)} (hu : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1)))
    {ε δ : ℝ} (hεδ : ε < δ) (hball : ∀ j, ‖(u 0 : Fin (N + 1) → ℝ) - u j‖ ≤ ε) {U : Set X}
    (hU : Metric.ball (⟨u 0, hu 0⟩ : stdSimplex ℝ (Fin (N + 1)))
            δ ⊆ (X.toSSetObjEquiv (op (SimplexCategory.mk N)) σ) ⁻¹' U) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (pushSimplexM σ u)) ⊆ U := by
  rw [pushSimplexM_realize σ hu]
  rintro _ ⟨t, rfl⟩
  apply hU
  rw [Metric.mem_ball]
  calc dist (affineSimplexStd (fun j => ⟨u j, hu j⟩) t) (⟨u 0, hu 0⟩ : stdSimplex ℝ (Fin (N + 1)))
      = ‖u 0 - (affineSimplexStd (fun j => ⟨u j, hu j⟩) t).val‖ := by
        rw [Subtype.dist_eq, dist_eq_norm, norm_sub_rev]
    _ ≤ ε := norm_sub_affineSimplex_le (u 0) u t hball
    _ < δ := hεδ

/-- **Lebesgue smallness for a singular simplex**: if the interiors of a family `𝒰` cover `X`, then enough
barycentric subdivisions make every simplex of `Sdᵐ[σ]` subordinate to `𝒰` (image inside some `U ∈ 𝒰`).
The cover pulls back along `σ̃` to an open cover of the compact `Δⁿ`; a Lebesgue number `δ` and a
subdivision fine enough that the affine pieces have diameter `< δ` put each `σ`-pushed piece inside a
ball that `σ̃` maps into a cover element. The geometric input to the small-chains excision theorem. -/
theorem exists_iterate_subordinate {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
    {𝒰 : Set (Set X)} (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) :
    ∃ m, ∀ τ ∈ ((⇑(singularSd X n))^[m] (Finsupp.single σ 1)).support,
      ∃ U ∈ 𝒰, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ U := by
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
  obtain ⟨m, hm⟩ := exists_iterate_idChain_diamLe n (ε := δ / 2) (by positivity)
  refine ⟨m, fun τ hτ => ?_⟩
  rw [singularSd_iterate_single, pushChainM, Finsupp.lmapDomain_apply] at hτ
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  have hu : ∀ j, w j ∈ stdSimplex ℝ (Fin (n + 1)) :=
    chainsIn_support (linSubdiv_iterate_idChain_mem n m) w hw
  obtain ⟨U, hUball⟩ := hlb ⟨w 0, hu 0⟩ (Set.mem_univ _)
  exact ⟨(U : Set X), U.property,
    (range_pushSimplexM_subset σ hu (by linarith) (fun j => hm w hw 0 j) hUball).trans
      interior_subset⟩

/-- A pushed-forward sub-simplex's image lies inside the original simplex's image: `range(σ_# w)~ ⊆
range σ̃` (the affine piece maps `Δⁿ` into `Δᴺ`, then `σ̃` carries it inside `range σ̃`). The geometric
core of "subdivision preserves smallness". -/
theorem range_pushSimplexM_subset_range {X : TopCat} {N n : ℕ}
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {w : Fin (n + 1) → (Fin (N + 1) → ℝ)} (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin (N + 1))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (pushSimplexM τ w))
      ⊆ Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk N)) τ) := by
  rw [pushSimplexM_realize τ hw]
  rintro _ ⟨t, rfl⟩
  exact ⟨affineSimplexStd (fun j => ⟨w j, hw j⟩) t, rfl⟩

/-- A singular `n`-simplex is **subordinate** to a family `𝒰` when its image lies in some member of `𝒰`. -/
def IsSubordinate {X : TopCat} {n : ℕ} (𝒰 : Set (Set X))
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) : Prop :=
  ∃ U ∈ 𝒰, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ U

/-- The subcomplex of `𝒰`-**small** singular `n`-chains: the `ℤ/2`-span of the subordinate simplices. -/
noncomputable def smallChains {X : TopCat} (𝒰 : Set (Set X)) (n : ℕ) :
    Submodule (ZMod 2) (SingularChain X n) :=
  Submodule.span (ZMod 2) {c | ∃ τ, IsSubordinate 𝒰 τ ∧ c = Finsupp.single τ 1}

theorem single_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))} (hτ : IsSubordinate 𝒰 τ) :
    Finsupp.single τ 1 ∈ smallChains 𝒰 n :=
  Submodule.subset_span ⟨τ, hτ, rfl⟩

/-- Pushing an in-simplex affine chain along a **subordinate** simplex `τ` lands in the small chains:
every piece's image is inside `τ`'s image, hence inside the same cover member. -/
theorem pushChainM_mem_smallChains {X : TopCat} {N n : ℕ} {𝒰 : Set (Set X)}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N))} (hτ : IsSubordinate 𝒰 τ)
    {c : LinChain (Fin (N + 1) → ℝ) n} (hc : c ∈ chainsIn (stdSimplex ℝ (Fin (N + 1))) n) :
    pushChainM τ c ∈ smallChains 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [pushChainM_single]
    obtain ⟨U, hU𝒰, hUrange⟩ := hτ
    exact single_mem_smallChains ⟨U, hU𝒰, (range_pushSimplexM_subset_range τ hw).trans hUrange⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- **The singular subdivision preserves smallness**: `Sd` maps `𝒰`-small chains to `𝒰`-small chains
(each sub-simplex of a subordinate simplex is subordinate to the same cover member). -/
theorem singularSd_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChain X n} (hc : c ∈ smallChains 𝒰 n) :
    singularSd X n c ∈ smallChains 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [singularSd_single]
    exact pushChainM_mem_smallChains hτ
      (linSubdiv_mem_chainsIn (convex_stdSimplex ℝ _) n (idChain_mem n))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

end SKEFTHawking.SingularExcision
