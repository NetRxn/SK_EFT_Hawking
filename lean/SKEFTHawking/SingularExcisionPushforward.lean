/-
# Phase 5q.F (w₂-foundation, brick 6c-c7) — the pushforward bridge: affine `Sd`/`D` → singular chains

The barycentric subdivision `Sd` and homotopy `D` are fully verified on the **affine** chain complex
`LinChain(Δⁿ)` (`SingularExcisionMod2`: `∂²=0`, `∂Sd=Sd∂`, `∂D+D∂=1−Sd`). To use them for excision they
must be transported to the **singular** chains of an arbitrary space `X`: a singular `n`-simplex
`σ : Δⁿ → X` post-composes an affine simplex `[w]` (vertices in `Δⁿ`) to a singular simplex
`σ ∘ affineSimplex(w)`, and `Sd(σ) := σ_#(Sd(ι_n))`. The chain-map / homotopy identities then transport
from the affine ones via the **naturality of `σ_#`** (it commutes with `∂` — the one place the
`toSSet`/`toTopHomeo` plumbing is needed; built on Mathlib's `toTopHomeo_naturality`).

Sub-brick c7a: the affine simplex with vertices in the standard simplex `Δᴺ`, **landing in `Δᴺ`** (by
convexity, `convex_stdSimplex`) — `C(Δⁿ, Δᴺ)`, ready to post-compose with a singular `N`-simplex.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2

namespace SKEFTHawking.SingularExcisionPushforward

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2

/-- The affine `n`-simplex with vertices `w : Fin (n+1) → Δᴺ` **landing in `Δᴺ`** (the convex
combination of points of the standard simplex stays in it): `C(Δⁿ, Δᴺ)`. The geometric realization of
an affine simplex *of* `Δᴺ`, ready to post-compose with a singular `N`-simplex `σ : Δᴺ → X`. -/
noncomputable def affineSimplexStd {N n : ℕ} (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) :
    C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (N + 1))) where
  toFun t := ⟨affineSimplex (fun i => (w i : Fin (N + 1) → ℝ)) t, by
    rw [affineSimplex_apply]
    exact (convex_stdSimplex ℝ (Fin (N + 1))).sum_mem (fun i _ => t.2.1 i) t.2.2
      (fun i _ => (w i).2)⟩
  continuous_toFun :=
    (affineSimplex (fun i => (w i : Fin (N + 1) → ℝ))).continuous.subtype_mk _

@[simp] theorem affineSimplexStd_coe_apply {N n : ℕ} (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1)))
    (t : stdSimplex ℝ (Fin (n + 1))) :
    ((affineSimplexStd w t : stdSimplex ℝ (Fin (N + 1))) : Fin (N + 1) → ℝ)
      = ∑ i, (t : Fin (n + 1) → ℝ) i • (w i : Fin (N + 1) → ℝ) := by
  show affineSimplex (fun i => (w i : Fin (N + 1) → ℝ)) t = _
  rw [affineSimplex_apply]

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2

/-- **The pushforward of an affine `n`-simplex of `Δᴺ` along a singular `N`-simplex `σ`**: the singular
`n`-simplex `σ̃ ∘ affineSimplexStd(w)` of `X` (post-compose the geometric realization of `σ` with the
affine simplex). The atom of `Sd(σ) := σ_#(Sd(ι_N))`. -/
noncomputable def pushSimplex {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) :=
  (X.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    ((X.toSSetObjEquiv (op (SimplexCategory.mk N)) σ).comp (affineSimplexStd w))

/-- The pushforward as a `ℤ/2`-linear map `LinChain(Δᴺ)_n → SingularChain X n` (the `Finsupp` extension
of `pushSimplex σ`). The transport of affine `n`-chains of `Δᴺ` to singular `n`-chains of `X`. -/
noncomputable def pushChain {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N))) :
    LinChain (stdSimplex ℝ (Fin (N + 1))) n →ₗ[ZMod 2] SingularChain X n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pushSimplex σ)

theorem pushChain_single {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (w : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) (a : ZMod 2) :
    pushChain σ (Finsupp.single w a) = Finsupp.single (pushSimplex σ w) a := by
  rw [pushChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- **The `toSSetObjEquiv` naturality at a coface `δ i`** (the singular-set simplicial structure):
applying `face i` to a simplex `= toSSetObjEquiv.symm g` corresponds, under `toSSetObjEquiv`, to
precomposing `g` with the topological face `stdSimplex.map (δ i) : Δⁿ → Δⁿ⁺¹`. The one `toSSet`-plumbing
lemma (Mathlib gives no direct version; derived via the restricted-Yoneda structure + `toTopHomeo`). -/
theorem toSSetObjEquiv_symm_face {X : TopCat} {n : ℕ} (i : Fin (n + 2))
    (g : C(stdSimplex ℝ (Fin (n + 1 + 1)), X)) :
    X.toSSetObjEquiv (op (SimplexCategory.mk n))
        (face i ((X.toSSetObjEquiv (op (SimplexCategory.mk (n + 1)))).symm g))
      = g.comp ⟨_root_.stdSimplex.map (SimplexCategory.δ i),
          _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩ :=
  rfl

/-- **The `toSSetObjEquiv` naturality, forward form**: the geometric realization of the singular face
`face i σ` is `σ̃` precomposed with the topological face `stdSimplex.map (δ i)`. (The `apply`-direction
companion of `toSSetObjEquiv_symm_face`.) -/
theorem toSSetObjEquiv_face {X : TopCat} {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    X.toSSetObjEquiv (op (SimplexCategory.mk n)) (face i σ)
      = (X.toSSetObjEquiv (op (SimplexCategory.mk (n + 1))) σ).comp
          ⟨_root_.stdSimplex.map (SimplexCategory.δ i),
            _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩ :=
  rfl

/-- The pure finite-sum reindexing underlying the affine face-compatibility: distributing the
fiber-weighted sum over the convex coefficients and collapsing the fibers of `g` (here `g = δ i`)
gives the pulled-back affine combination. Stated over `ℝ` so the proof is coercion-free; the
geometric lemma applies it by defeq. -/
private theorem sum_fiberwise_reindex {n : ℕ} (g : Fin (n + 1) → Fin (n + 2))
    (T : Fin (n + 1) → ℝ) (a : Fin (n + 2) → ℝ) :
    ∑ x, (∑ x_1 ∈ Finset.univ.filter (fun m => g m = x), T x_1) • a x = ∑ m, T m • a (g m) := by
  rw [← Finset.sum_fiberwise Finset.univ g (fun m => T m • a (g m))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [hm.2]

/-- **Post-composing an affine simplex by the (linear) face map `stdSimplex.map (δ i)`** gives the affine
simplex on the image vertices: `stdSimplex.map (δ i) ∘ affineSimplexStd v = affineSimplexStd (stdSimplex.map
(δ i) ∘ v)`. (The face map is affine — the corestriction of the linear `FunOnFinite.linearMap` — so it
commutes with convex combinations.) The companion of `affineSimplexStd_comp_face` for the singular chain
map's functoriality (2b). -/
theorem stdSimplexMap_comp_affineSimplexStd {N n : ℕ} (i : Fin (N + 2))
    (v : Fin (n + 1) → stdSimplex ℝ (Fin (N + 1))) :
    (⟨_root_.stdSimplex.map (SimplexCategory.δ i),
        _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩
        : C(stdSimplex ℝ (Fin (N + 1)), stdSimplex ℝ (Fin (N + 1 + 1)))).comp (affineSimplexStd v)
      = affineSimplexStd (fun j => _root_.stdSimplex.map (SimplexCategory.δ i) (v j)) := by
  ext t k
  -- Reduce both sides to coordinate sums (defeq); LHS = (FunOnFinite.linearMap (δ i) (∑ⱼ tⱼ•vⱼ)) k,
  -- RHS = (∑ⱼ tⱼ • FunOnFinite.linearMap (δ i) vⱼ) k; equal by linearity of `FunOnFinite.linearMap`.
  change (FunOnFinite.linearMap ℝ ℝ (ConcreteCategory.hom (SimplexCategory.δ i))
            (∑ j, (t : Fin (n + 1) → ℝ) j • ⇑(v j))) k
       = (∑ j, (t : Fin (n + 1) → ℝ) j • ⇑(_root_.stdSimplex.map (SimplexCategory.δ i) (v j))) k
  rw [map_sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [stdSimplex.map_coe]
  exact congrFun (map_smul (FunOnFinite.linearMap ℝ ℝ (ConcreteCategory.hom (SimplexCategory.δ i)))
    ((t : Fin (n + 1) → ℝ) j) (v j : Fin (N + 1) → ℝ)) k

/-- **(B) The affine face-compatibility**: precomposing the affine simplex with the topological coface
`stdSimplex.map (δ i)` (which inserts a `0` coordinate at `i`) drops the `i`-th vertex —
`affineSimplexStd w ∘ (δ i) = affineSimplexStd (w ∘ Fin.succAbove i)`. -/
theorem affineSimplexStd_comp_face {N n : ℕ} (w : Fin (n + 1 + 1) → stdSimplex ℝ (Fin (N + 1)))
    (i : Fin (n + 2)) :
    (affineSimplexStd w).comp ⟨_root_.stdSimplex.map (SimplexCategory.δ i),
        _root_.stdSimplex.continuous_map (SimplexCategory.δ i)⟩
      = affineSimplexStd (w ∘ i.succAbove) := by
  ext t k
  -- Reduce both sides to coordinate sums by `change` (defeq: `affineSimplexStd`'s coe is the
  -- `rfl`-unfolding `affineSimplex`). This sidesteps the `⇑`(DFunLike)/`↑`(Subtype.val from `ext`)
  -- coercion-head mismatch that otherwise blocks `rw`/`simp` from expanding the RHS.
  change (∑ j : Fin (n + 1 + 1),
            ⇑(stdSimplex.map (ConcreteCategory.hom (SimplexCategory.δ i)) t) j • ⇑(w j)) k
       = (∑ m : Fin (n + 1), ⇑t m • ⇑(w (i.succAbove m))) k
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [Pi.smul_apply, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  -- The remaining identity is the pure finite-sum reindexing along the injective coface
  -- `δ i = Fin.succAbove i`. `exact` closes it by defeq (`⇑ = ↑`, `δ i m = Fin.succAbove i m`).
  exact sum_fiberwise_reindex (fun m => (ConcreteCategory.hom (SimplexCategory.δ i)) m)
    (fun x => ⇑t x) (fun x => ⇑(w x) k)

/-- **The pushforward boundary-naturality**: `face i (σ_# [w]) = σ_# [w ∘ ∂ᵢ]` — the singular `i`-th
face of a pushforward is the pushforward of the affine `i`-th face. From the (definitional)
`toSSetObjEquiv` naturality + the affine face-compatibility (B). -/
theorem pushSimplex_face {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (w : Fin (n + 1 + 1) → stdSimplex ℝ (Fin (N + 1))) (i : Fin (n + 2)) :
    face i (pushSimplex σ w) = pushSimplex σ (w ∘ i.succAbove) := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  simp only [pushSimplex, toSSetObjEquiv_symm_face, Equiv.apply_symm_apply]
  exact congrArg (((X.toSSetObjEquiv (op (SimplexCategory.mk N))) σ).comp ·)
    (affineSimplexStd_comp_face w i)

/-- **The pushforward is a chain map**: `∂ ∘ σ_# = σ_# ∘ ∂` (`SingularChain`'s `chainBoundary`
intertwines with the affine `linBoundary`). The chain-level upgrade of `pushSimplex_face`; this is the
naturality that transports the affine subdivision identities (`∂Sd=Sd∂`, `∂D+D∂=1−Sd`, all verified on
`LinChain`) to singular chains. Proven by `ℤ/2`-linearity + the per-basis face computation. -/
theorem pushChain_chainBoundary {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (c : LinChain (stdSimplex ℝ (Fin (N + 1))) (n + 1)) :
    chainBoundary X n (pushChain σ c) = pushChain σ (linBoundary n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single w a =>
    rw [pushChain_single, chainBoundary_single_smul, linBoundary_single_smul, map_smul,
      boundaryBasis, linBoundaryBasis, map_sum]
    refine congrArg (a • ·) (Finset.sum_congr rfl fun i _ => ?_)
    rw [pushChain_single, pushSimplex_face]

open Classical in
/-- **The module-valued pushforward of an affine simplex of `Δᴺ`** along `σ`: for a vertex-tuple
`u : Fin (n+1) → (Fin (N+1) → ℝ)` in the *ambient* `ℝ`-module (where the barycentric subdivision lives),
push it along `σ` when all its vertices lie in `Δᴺ` (corestricting to `affineSimplexStd`), with a junk
constant simplex otherwise (never reached on chains in `chainsIn (stdSimplex …)`). This is the bridge
that lets the module-valued `linSubdiv`/`linHomotopy` be pushed to singular chains. -/
noncomputable def pushSimplexM {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (u : Fin (n + 1) → (Fin (N + 1) → ℝ)) :
    (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) :=
  if h : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1))
  then pushSimplex σ (fun j => ⟨u j, h j⟩)
  else pushSimplex σ (fun _ => stdSimplex.vertex 0)

/-- On an in-simplex vertex-tuple, `pushSimplexM` is the corestricted `pushSimplex`. -/
theorem pushSimplexM_of_mem {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {u : Fin (n + 1) → (Fin (N + 1) → ℝ)} (hu : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1))) :
    pushSimplexM σ u = pushSimplex σ (fun j => ⟨u j, hu j⟩) := by
  rw [pushSimplexM, dif_pos hu]

/-- **The module-valued pushforward boundary-naturality** (in-simplex tuples): `face i (σ_# u) =
σ_# (u ∘ ∂ᵢ)`. The faces of an in-simplex tuple are in-simplex, so both `pushSimplexM`s corestrict
and the identity is `pushSimplex_face`. -/
theorem pushSimplexM_face {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {u : Fin (n + 1 + 1) → (Fin (N + 1) → ℝ)} (hu : ∀ j, u j ∈ stdSimplex ℝ (Fin (N + 1)))
    (i : Fin (n + 2)) :
    face i (pushSimplexM σ u) = pushSimplexM σ (u ∘ i.succAbove) := by
  rw [pushSimplexM_of_mem σ hu,
    pushSimplexM_of_mem σ (u := u ∘ i.succAbove) (fun j => hu (i.succAbove j)), pushSimplex_face]
  rfl

/-- **The affine simplex on all the vertices of `Δᴺ` is the identity**: `affineSimplexStd (vertex ·) =
id` (`∑ⱼ tⱼ eⱼ = t` for `t ∈ Δᴺ`). The "leading term" `ι_N` of the subdivision pushes to `σ` itself. -/
theorem affineSimplexStd_vertex_id {N : ℕ} :
    affineSimplexStd (fun j => stdSimplex.vertex j : Fin (N + 1) → stdSimplex ℝ (Fin (N + 1)))
      = ContinuousMap.id _ := by
  ext t k
  change (∑ j, (t : Fin (N + 1) → ℝ) j • ⇑(stdSimplex.vertex j)) k = (t : Fin (N + 1) → ℝ) k
  rw [Finset.sum_apply]
  simp only [stdSimplex.vertex_coe, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq Finset.univ k (fun j => (t : Fin (N + 1) → ℝ) j),
    Finset.mem_univ, if_true]

/-- The module-valued pushforward as a `ℤ/2`-linear map `LinChain (Fin (N+1) → ℝ) n → SingularChain X n`
(the `Finsupp` extension of `pushSimplexM σ`). -/
noncomputable def pushChainM {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N))) :
    LinChain (Fin (N + 1) → ℝ) n →ₗ[ZMod 2] SingularChain X n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (pushSimplexM σ)

theorem pushChainM_single {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (u : Fin (n + 1) → (Fin (N + 1) → ℝ)) (a : ZMod 2) :
    pushChainM σ (Finsupp.single u a) = Finsupp.single (pushSimplexM σ u) a := by
  rw [pushChainM, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end SKEFTHawking.SingularExcisionPushforward
