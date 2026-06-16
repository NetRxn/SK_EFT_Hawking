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
open SKEFTHawking.SingularCohomologyMod2

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

/-- A chain all of whose support simplices are subordinate is small. -/
theorem mem_smallChains_of_support {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)} {c : SingularChain X n}
    (h : ∀ τ ∈ c.support, IsSubordinate 𝒰 τ) : c ∈ smallChains 𝒰 n := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum]
  refine Submodule.sum_mem _ (fun τ hτ => ?_)
  have hτs : Finsupp.single τ (c τ) = (c τ) • Finsupp.single τ (1 : ZMod 2) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hτs]
  exact Submodule.smul_mem _ _ (single_mem_smallChains (h τ hτ))

/-- Iterating `Sd` keeps a small chain small. -/
theorem singularSd_iterate_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChain X n} (hc : c ∈ smallChains 𝒰 n) (m : ℕ) :
    (⇑(singularSd X n))^[m] c ∈ smallChains 𝒰 n := by
  induction m with
  | zero => rwa [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply']; exact singularSd_mem_smallChains ih

/-- **Any chain becomes small under enough subdivisions**: if the interiors of `𝒰` cover `X`, then for
any singular `n`-chain `c` there is `m` with `Sdᵐ c` small. (Each support simplex needs `m_τ`
subdivisions — `exists_iterate_subordinate`; take the `Finset.sup`, and `Sd` preserves smallness so the
extra subdivisions do no harm.) The hypothesis the small-chains chain-homotopy-equivalence consumes. -/
theorem exists_iterate_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) (c : SingularChain X n) :
    ∃ m, (⇑(singularSd X n))^[m] c ∈ smallChains 𝒰 n := by
  classical
  choose! M hM using fun (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) =>
    exists_iterate_subordinate τ hcov
  obtain ⟨m, hm⟩ : ∃ m, ∀ τ ∈ c.support, M τ ≤ m :=
    ⟨c.support.sup M, fun _ hτ => Finset.le_sup hτ⟩
  refine ⟨m, ?_⟩
  rw [← Finsupp.sum_single c, ← Module.End.coe_pow, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ (fun τ hτ => ?_)
  have hτs : Finsupp.single τ (c τ) = (c τ) • Finsupp.single τ (1 : ZMod 2) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hτs, map_smul, Module.End.coe_pow,
    ← Nat.sub_add_cancel (hm τ hτ), Function.iterate_add_apply]
  exact Submodule.smul_mem _ _
    (singularSd_iterate_mem_smallChains (mem_smallChains_of_support (hM τ)) _)

/-- A face of a simplex has image inside the simplex's image (`∂ᵢτ`'s realization is `τ̃` precomposed with
the topological coface). -/
theorem range_face_subset_range {X : TopCat} {n : ℕ}
    (τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (face i τ))
      ⊆ Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk (n + 1))) τ) := by
  rw [toSSetObjEquiv_face]
  rintro _ ⟨t, rfl⟩
  exact ⟨_, rfl⟩

/-- A face of a subordinate simplex is subordinate (to the same cover member). -/
theorem IsSubordinate.face {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))} (hτ : IsSubordinate 𝒰 τ)
    (i : Fin (n + 2)) : IsSubordinate 𝒰 (face i τ) := by
  obtain ⟨U, hU, hrange⟩ := hτ
  exact ⟨U, hU, (range_face_subset_range τ i).trans hrange⟩

/-- **`smallChains` is a subcomplex**: the boundary of a small chain is small (every face of a subordinate
simplex is subordinate). So `(smallChains 𝒰)` is a `ℤ/2`-subcomplex of the singular chain complex. -/
theorem chainBoundary_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChain X (n + 1)} (hc : c ∈ smallChains 𝒰 (n + 1)) :
    chainBoundary X n c ∈ smallChains 𝒰 n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [chainBoundary_single, boundaryBasis]
    exact Submodule.sum_mem _ (fun i _ => single_mem_smallChains (hτ.face i))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- The iterated-subdivision homotopy kills the zero chain. -/
theorem iterHomotopy_zero (X : TopCat) (n m : ℕ) : iterHomotopy X n m 0 = 0 := by
  rw [iterHomotopy, map_zero]
  exact Finset.sum_eq_zero (fun i _ => by rw [← Module.End.coe_pow, map_zero])

/-- **A cycle is homologous to its subdivision**: if `∂c = 0`, then `c + Sdᵐ c = ∂(Dₘ c)` — so `c` and
`Sdᵐ c` represent the same homology class. With `exists_iterate_smallChains` (`Sdᵐ c` small for large
`m`) this is the heart of the small-chains theorem: every homology class has a small representative. -/
theorem add_singularSd_iterate_eq_boundary {X : TopCat} {n : ℕ} {c : SingularChain X (n + 1)}
    (hc : chainBoundary X n c = 0) (m : ℕ) :
    c + (⇑(singularSd X (n + 1)))^[m] c
      = chainBoundary X (n + 1) (iterHomotopy X (n + 1) m c) := by
  have h := iterHomotopy_chainHomotopy X m n c
  rw [hc, iterHomotopy_zero, add_zero] at h
  exact h.symm

/-- **The surjective half of the small-chains theorem**: every cycle `z` is homologous to a *small*
cycle, namely `Sdᵐ z` for `m` large enough. (`Sdᵐ z` is small by `exists_iterate_smallChains`; a cycle
because `Sd` is a chain map (`singularSd_iterate_chainBoundary`) and `∂z = 0`; homologous to `z` by
`add_singularSd_iterate_eq_boundary`.) So every singular homology class has a `𝒰`-small representative —
the surjectivity that, with excision's relative version, computes `Hₙ(X,A)` by small chains. -/
theorem exists_small_cycle_homologous {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {z : SingularChain X (n + 1)}
    (hz : chainBoundary X n z = 0) :
    ∃ m, (⇑(singularSd X (n + 1)))^[m] z ∈ smallChains 𝒰 (n + 1) ∧
      chainBoundary X n ((⇑(singularSd X (n + 1)))^[m] z) = 0 ∧
      z + (⇑(singularSd X (n + 1)))^[m] z ∈ LinearMap.range (chainBoundary X (n + 1)) := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChains hcov z
  refine ⟨m, hm, ?_,
    ⟨iterHomotopy X (n + 1) m z, (add_singularSd_iterate_eq_boundary hz m).symm⟩⟩
  rw [singularSd_iterate_chainBoundary, hz, ← Module.End.coe_pow, map_zero]

/-- The degree-raising prism operator `D` preserves smallness (each piece of `D[τ]` is a homotopy
sub-simplex of `τ`, with image inside `τ`'s). -/
theorem singularD_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChain X n} (hc : c ∈ smallChains 𝒰 n) :
    singularD X n c ∈ smallChains 𝒰 (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [singularD_single]
    exact pushChainM_mem_smallChains hτ
      (linHomotopy_mem_chainsIn (convex_stdSimplex ℝ _) n (idChain_mem n))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- The iterated homotopy `Dₘ = ∑_{i<m} Sdⁱ∘D` preserves smallness. -/
theorem iterHomotopy_mem_smallChains {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChain X n} (hc : c ∈ smallChains 𝒰 n) (m : ℕ) :
    iterHomotopy X n m c ∈ smallChains 𝒰 (n + 1) := by
  rw [iterHomotopy]
  exact Submodule.sum_mem _
    (fun i _ => singularSd_iterate_mem_smallChains (singularD_mem_smallChains hc) i)

/-- **The injective half of the small-chains theorem**: a small cycle `z` that bounds in `C` already
bounds in `C^𝒰`. (`z = ∂w`; subdivide `w` enough that `Sdᵐ w` is small; then `z = ∂(Sdᵐ w + Dₘ z)`
— from `∂(Sdᵐ w) = Sdᵐ(∂w) = Sdᵐ z` and the homotopy `z + Sdᵐ z = ∂(Dₘ z)` — with both terms small
(`Dₘ z` small since `D`, `Sd` preserve smallness).) With surjectivity ⟹ `C^𝒰 ↪ C` a homology iso. -/
theorem smallChains_boundary_of_boundary {X : TopCat} {n : ℕ} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {z : SingularChain X (n + 1)}
    (hz_small : z ∈ smallChains 𝒰 (n + 1)) (hz_cyc : chainBoundary X n z = 0)
    {w : SingularChain X (n + 2)} (hw : chainBoundary X (n + 1) w = z) :
    ∃ w' ∈ smallChains 𝒰 (n + 2), chainBoundary X (n + 1) w' = z := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChains hcov w
  refine ⟨(⇑(singularSd X (n + 2)))^[m] w + iterHomotopy X (n + 1) m z,
    Submodule.add_mem _ hm (iterHomotopy_mem_smallChains hz_small m), ?_⟩
  rw [map_add, singularSd_iterate_chainBoundary, hw,
    ← add_singularSd_iterate_eq_boundary hz_cyc m, add_left_comm, ZModModule.add_self, add_zero]

/-! ## Relative excision: lifting subordinate simplices into subspace chains -/

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- **`toSSetObjEquiv` naturality under the subspace inclusion**: the realization of `simplexIncl A σ'`
(post-composing into `X`) is `Subtype.val` composed with `σ'`'s realization. Definitional, like the
coface naturality. -/
theorem toSSetObjEquiv_simplexIncl {X : TopCat} (A : Set X) {n : ℕ}
    (σ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n))) :
    X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl A n σ')
      = (ConcreteCategory.hom (inclMap A)).comp
          ((sub A).toSSetObjEquiv (op (SimplexCategory.mk n)) σ') := rfl

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- **Lifting lemma**: a singular simplex `τ` whose image lies in `A` is the inclusion of a simplex of
`A` — so `[τ] ∈ subspaceChains A`. (Corestrict the realization `τ̃` to `↥A`; the corestricted simplex
includes back to `τ` by the `simplexIncl` naturality + `Subtype.val ∘ corestrict = id`.) The geometric
input letting a chain subordinate to a cover split into the cover's subspace chains. -/
theorem single_mem_subspaceChains_of_subordinate {X : TopCat} {A : Set X} {n : ℕ}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))}
    (hτ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ A) :
    Finsupp.single τ 1 ∈ subspaceChains A n := by
  have hmem : ∀ t, X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ t ∈ A := fun t => hτ ⟨t, rfl⟩
  set g := X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ with hg
  set σ' := ((sub A).toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (⟨fun t => ⟨g t, hmem t⟩, g.continuous.subtype_mk hmem⟩ :
      C(stdSimplex ℝ (Fin (n + 1)), sub A)) with hσ'
  have hincl : simplexIncl A n σ' = τ := by
    apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    rw [toSSetObjEquiv_simplexIncl, hσ', Equiv.apply_symm_apply]
    rfl
  exact ⟨Finsupp.single σ' 1, by rw [chainIncl_single, hincl]⟩

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- **The two-cover decomposition**: a chain small for `{A, B}` splits into the subspace chains of `A`
and `B` (each subordinate simplex lies in one of them, by the lifting lemma). The bridge from the
small-chains theorem to Mayer–Vietoris and excision. -/
theorem smallChains_two_le {X : TopCat} (A B : Set X) (n : ℕ) :
    smallChains {A, B} n ≤ subspaceChains A n ⊔ subspaceChains B n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨τ, ⟨U, hU, hsub⟩, rfl⟩
  rcases hU with rfl | rfl
  · exact Submodule.mem_sup_left (single_mem_subspaceChains_of_subordinate hsub)
  · exact Submodule.mem_sup_right (single_mem_subspaceChains_of_subordinate hsub)

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- An included simplex `simplexIncl A τ'` has image inside `A`. -/
theorem range_simplexIncl_subset {X : TopCat} (A : Set X) {n : ℕ}
    (τ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl A n τ')) ⊆ A := by
  rw [toSSetObjEquiv_simplexIncl]
  rintro _ ⟨t, rfl⟩
  exact ((sub A).toSSetObjEquiv (op (SimplexCategory.mk n)) τ' t).2

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- The subspace chains of a cover member are small (an `A`-simplex has image in `A ∈ 𝒰`). With
`smallChains_two_le` this gives `smallChains {A, B} = subspaceChains A ⊔ subspaceChains B`. -/
theorem subspaceChains_le_smallChains {X : TopCat} {A : Set X} {𝒰 : Set (Set X)} (hA : A ∈ 𝒰)
    (n : ℕ) : subspaceChains A n ≤ smallChains 𝒰 n := by
  classical
  rintro _ ⟨d, rfl⟩
  refine mem_smallChains_of_support (fun τ hτ => ?_)
  rw [chainIncl, Finsupp.lmapDomain_apply] at hτ
  obtain ⟨τ', _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  exact ⟨A, hA, range_simplexIncl_subset A τ'⟩

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- **The two-cover decomposition (equality)** `C^{A,B} = C(A) + C(B)` — the small chains for `{A, B}`
are exactly the sum of the two subspace chains. The algebraic identity underlying Mayer–Vietoris and
excision. -/
theorem smallChains_two_eq {X : TopCat} (A B : Set X) (n : ℕ) :
    smallChains {A, B} n = subspaceChains A n ⊔ subspaceChains B n := by
  have hA : A ∈ ({A, B} : Set (Set X)) := Set.mem_insert _ _
  have hB : B ∈ ({A, B} : Set (Set X)) := Set.mem_insert_of_mem _ rfl
  refine le_antisymm (smallChains_two_le A B n)
    (sup_le (subspaceChains_le_smallChains hA n) (subspaceChains_le_smallChains hB n))

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- **Pushforward commutes with the subspace inclusion**: `(simplexIncl A τ')_# w = simplexIncl A ((τ')_# w)`
— both realizations are `Subtype.val ∘ τ'~ ∘ affineSimplexStd w` (`toSSetObjEquiv` injective). The
naturality letting `Sd` descend to the subspace chains. -/
theorem pushSimplexM_simplexIncl {X : TopCat} (A : Set X) {n k : ℕ}
    (τ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n)))
    {w : Fin (k + 1) → (Fin (n + 1) → ℝ)} (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin (n + 1))) :
    pushSimplexM (simplexIncl A n τ') w = simplexIncl A k (pushSimplexM τ' w) := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk k))).injective
  rw [pushSimplexM_realize (simplexIncl A n τ') hw, toSSetObjEquiv_simplexIncl,
    toSSetObjEquiv_simplexIncl, pushSimplexM_realize τ' hw]
  rfl

open SKEFTHawking.SingularRelativeHomologyMod2 in
/-- Chain-level: pushing an in-simplex affine chain along an included simplex equals including the
pushforward — `(simplexIncl A τ')_# c = chainIncl A ((τ')_# c)`. -/
theorem pushChainM_simplexIncl {X : TopCat} (A : Set X) {n k : ℕ}
    (τ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n)))
    {c : LinChain (Fin (n + 1) → ℝ) k} (hc : c ∈ chainsIn (stdSimplex ℝ (Fin (n + 1))) k) :
    pushChainM (simplexIncl A n τ') c = chainIncl A k (pushChainM τ' c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [pushChainM_single, pushSimplexM_simplexIncl A τ' hw, pushChainM_single, chainIncl_single]
  · rw [map_zero, map_zero, map_zero]
  · intro a b _ _ ha hb; rw [map_add, map_add, map_add, ha, hb]
  · intro r a _ ha; rw [map_smul, map_smul, map_smul, ha]

end SKEFTHawking.SingularExcision
