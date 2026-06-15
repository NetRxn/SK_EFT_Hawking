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

end SKEFTHawking.SingularExcisionPushforward
