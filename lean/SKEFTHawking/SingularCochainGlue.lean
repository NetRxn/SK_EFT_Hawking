import Mathlib
import SKEFTHawking.SingularCohomologyDisjoint
import SKEFTHawking.SingularCohomologyFunctoriality

/-!
# Phase 5q.G (G3 F-ladder, F7a) — the cochain glue over a disjoint union

Every singular simplex of `M ⊕ N` factors through `Sum.inl` or `Sum.inr`
(`continuous_to_sum_factor` — the standard simplex is preconnected), so a pair of cochains
`(a, b)` on the pieces **glues** to a cochain on the sum, evaluating each simplex through its
factor. The glue is a two-sided inverse to the pullback pair `(inl*, inr*)` **at the cochain
level on the nose**, and it is a cochain map — the cochain complex of `M ⊕ N` is the product
of the pieces' complexes. Feeds F7b (the `Hᵏ(M ⊕ N)` decomposition) and the `wuW2` ⊔-split.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality

namespace SKEFTHawking.SingularCochainGlue

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]

/-- The inclusion `M → M ⊕ N` as a continuous map of `TopCat` carriers. -/
noncomputable def inlC (M N : Type) [TopologicalSpace M] [TopologicalSpace N] :
    C(↑(TopCat.of M), ↑(TopCat.of (M ⊕ N))) :=
  ⟨Sum.inl, continuous_inl⟩

/-- The inclusion `N → M ⊕ N` as a continuous map of `TopCat` carriers. -/
noncomputable def inrC (M N : Type) [TopologicalSpace M] [TopologicalSpace N] :
    C(↑(TopCat.of N), ↑(TopCat.of (M ⊕ N))) :=
  ⟨Sum.inr, continuous_inr⟩

/-- The realization of a singular simplex of the sum. -/
noncomputable def rl {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (M ⊕ N))).obj (op (SimplexCategory.mk n))) :
    C(stdSimplex ℝ (Fin (n + 1)), M ⊕ N) :=
  (TopCat.of (M ⊕ N)).toSSetObjEquiv (op (SimplexCategory.mk n)) σ

/-- The `M`-part of a left-factoring simplex of the sum. -/
noncomputable def leftPart {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (M ⊕ N))).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl σ) ⊆ Set.range (Sum.inl : M → M ⊕ N)) :
    (TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n)) :=
  ((TopCat.of M).toSSetObjEquiv (op (SimplexCategory.mk n))).symm (factorLeft (rl σ) h)

/-- The `N`-part of a right-factoring simplex of the sum. -/
noncomputable def rightPart {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (M ⊕ N))).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl σ) ⊆ Set.range (Sum.inr : N → M ⊕ N)) :
    (TopCat.toSSet.obj (TopCat.of N)).obj (op (SimplexCategory.mk n)) :=
  ((TopCat.of N).toSSetObjEquiv (op (SimplexCategory.mk n))).symm (factorRight (rl σ) h)

/-- **A left-factoring simplex is the pushforward of its `M`-part**: `σ = inl₊(leftPart σ)`. -/
theorem mapSimplex_leftPart {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (M ⊕ N))).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl σ) ⊆ Set.range (Sum.inl : M → M ⊕ N)) :
    mapSimplex (inlC M N) (leftPart σ h) = σ := by
  rw [mapSimplex, leftPart, Equiv.apply_symm_apply, Equiv.symm_apply_eq]
  exact ContinuousMap.ext (fun d => inl_factorLeft (rl σ) h d)

/-- **A right-factoring simplex is the pushforward of its `N`-part**: `σ = inr₊(rightPart σ)`. -/
theorem mapSimplex_rightPart {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of (M ⊕ N))).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl σ) ⊆ Set.range (Sum.inr : N → M ⊕ N)) :
    mapSimplex (inrC M N) (rightPart σ h) = σ := by
  rw [mapSimplex, rightPart, Equiv.apply_symm_apply, Equiv.symm_apply_eq]
  exact ContinuousMap.ext (fun d => inr_factorRight (rl σ) h d)

/-- **The cochain glue**: evaluate a left-factoring simplex through `a`, a right-factoring one
through `b`. -/
noncomputable def glueCochain (n : ℕ) (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n) : SingularCochain (TopCat.of (M ⊕ N)) n :=
  fun σ =>
    letI := Classical.dec (Set.range (rl σ) ⊆ Set.range (Sum.inl : M → M ⊕ N))
    if h : Set.range (rl σ) ⊆ Set.range (Sum.inl : M → M ⊕ N) then a (leftPart σ h)
    else b (rightPart σ ((continuous_to_sum_factor (rl σ)).resolve_left h))

/-- `factorLeft` is determined by any pointwise `inl`-factorization. -/
theorem factorLeft_eq {D : Type*} [TopologicalSpace D] {f : C(D, M ⊕ N)}
    {h : Set.range f ⊆ Set.range (Sum.inl : M → M ⊕ N)} {g : C(D, M)}
    (hfg : ∀ d, f d = Sum.inl (g d)) : factorLeft f h = g :=
  ContinuousMap.ext fun d => Sum.inl_injective (by rw [inl_factorLeft, hfg d])

/-- `factorRight` is determined by any pointwise `inr`-factorization. -/
theorem factorRight_eq {D : Type*} [TopologicalSpace D] {f : C(D, M ⊕ N)}
    {h : Set.range f ⊆ Set.range (Sum.inr : N → M ⊕ N)} {g : C(D, N)}
    (hfg : ∀ d, f d = Sum.inr (g d)) : factorRight f h = g :=
  ContinuousMap.ext fun d => Sum.inr_injective (by rw [inr_factorRight, hfg d])

/-- The realization of an `inl`-pushforward is the post-composition. -/
theorem rl_mapSimplex_inl {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n))) :
    rl (mapSimplex (inlC M N) τ)
      = (inlC M N).comp ((TopCat.of M).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  rw [rl, mapSimplex, Equiv.apply_symm_apply]

/-- The realization of an `inr`-pushforward is the post-composition. -/
theorem rl_mapSimplex_inr {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op (SimplexCategory.mk n))) :
    rl (mapSimplex (inrC M N) τ)
      = (inrC M N).comp ((TopCat.of N).toSSetObjEquiv (op (SimplexCategory.mk n)) τ) := by
  rw [rl, mapSimplex, Equiv.apply_symm_apply]

/-- An `inl`-pushforward factors left. -/
theorem range_rl_mapSimplex_inl {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n))) :
    Set.range (rl (mapSimplex (inlC M N) τ)) ⊆ Set.range (Sum.inl : M → M ⊕ N) := by
  rw [rl_mapSimplex_inl]
  rintro x ⟨d, rfl⟩
  exact ⟨_, rfl⟩

/-- An `inr`-pushforward does NOT factor left (ranges of `inl`/`inr` are disjoint, the standard
simplex is nonempty). -/
theorem not_range_inl_of_mapSimplex_inr {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op (SimplexCategory.mk n))) :
    ¬ Set.range (rl (mapSimplex (inrC M N) τ)) ⊆ Set.range (Sum.inl : M → M ⊕ N) := by
  intro hcon
  obtain ⟨x, hx⟩ := Set.range_nonempty (rl (mapSimplex (inrC M N) τ))
  obtain ⟨m, hm⟩ := hcon hx
  obtain ⟨d, hd⟩ := hx
  rw [rl_mapSimplex_inr] at hd
  exact Sum.inl_ne_inr (hm.trans hd.symm)

/-- `leftPart` recovers the pushed-forward `M`-simplex. -/
theorem leftPart_mapSimplex {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl (mapSimplex (inlC M N) τ)) ⊆ Set.range (Sum.inl : M → M ⊕ N)) :
    leftPart (mapSimplex (inlC M N) τ) h = τ := by
  rw [leftPart, Equiv.symm_apply_eq]
  exact factorLeft_eq (fun d => DFunLike.congr_fun (rl_mapSimplex_inl τ) d)

/-- `rightPart` recovers the pushed-forward `N`-simplex. -/
theorem rightPart_mapSimplex {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op (SimplexCategory.mk n)))
    (h : Set.range (rl (mapSimplex (inrC M N) τ)) ⊆ Set.range (Sum.inr : N → M ⊕ N)) :
    rightPart (mapSimplex (inrC M N) τ) h = τ := by
  rw [rightPart, Equiv.symm_apply_eq]
  exact factorRight_eq (fun d => DFunLike.congr_fun (rl_mapSimplex_inr τ) d)

/-- **The glue evaluates `inl`-pushforwards through `a`** (pointwise (A)). -/
theorem glueCochain_mapSimplex_inl {n : ℕ} (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n)
    (τ : (TopCat.toSSet.obj (TopCat.of M)).obj (op (SimplexCategory.mk n))) :
    glueCochain n a b (mapSimplex (inlC M N) τ) = a τ := by
  simp only [glueCochain]
  rw [dif_pos (range_rl_mapSimplex_inl τ)]
  exact congrArg a (leftPart_mapSimplex τ _)

/-- **The glue evaluates `inr`-pushforwards through `b`** (pointwise (B)). -/
theorem glueCochain_mapSimplex_inr {n : ℕ} (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n)
    (τ : (TopCat.toSSet.obj (TopCat.of N)).obj (op (SimplexCategory.mk n))) :
    glueCochain n a b (mapSimplex (inrC M N) τ) = b τ := by
  simp only [glueCochain]
  rw [dif_neg (not_range_inl_of_mapSimplex_inr τ)]
  exact congrArg b (rightPart_mapSimplex τ _)

/-- **(A)**: `inl* ∘ glue = pr₁` on cochains. -/
theorem cochainPullback_inl_glueCochain (n : ℕ) (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n) :
    cochainPullback (inlC M N) n (glueCochain n a b) = a :=
  funext fun τ => glueCochain_mapSimplex_inl a b τ

/-- **(B)**: `inr* ∘ glue = pr₂` on cochains. -/
theorem cochainPullback_inr_glueCochain (n : ℕ) (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n) :
    cochainPullback (inrC M N) n (glueCochain n a b) = b :=
  funext fun τ => glueCochain_mapSimplex_inr a b τ

/-- **The recomposition**: gluing the two pullbacks of a cochain gives it back — on the nose. -/
theorem glueCochain_pullback (n : ℕ) (c : SingularCochain (TopCat.of (M ⊕ N)) n) :
    glueCochain n (cochainPullback (inlC M N) n c) (cochainPullback (inrC M N) n c) = c := by
  funext σ
  simp only [glueCochain]
  split_ifs with h
  · exact congrArg c (mapSimplex_leftPart σ h)
  · exact congrArg c
      (mapSimplex_rightPart σ ((continuous_to_sum_factor (rl σ)).resolve_left h))

/-- **(C) — the glue is a cochain map**: `δ(glue a b) = glue (δa) (δb)` (faces stay in the
factoring component, `face_mapSimplex`). -/
theorem coboundary_glueCochain (n : ℕ) (a : SingularCochain (TopCat.of M) n)
    (b : SingularCochain (TopCat.of N) n) :
    coboundary (TopCat.of (M ⊕ N)) n (glueCochain n a b)
      = glueCochain (n + 1) (coboundary (TopCat.of M) n a) (coboundary (TopCat.of N) n b) := by
  funext σ
  show (∑ i : Fin (n + 2), glueCochain n a b (face i σ)) = _
  simp only [glueCochain]
  split_ifs with h
  · show _ = ∑ i : Fin (n + 2), a (face i (leftPart σ h))
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show face i σ = face i (mapSimplex (inlC M N) (leftPart σ h)) from
        congrArg (face i) (mapSimplex_leftPart σ h).symm,
      face_mapSimplex]
    exact glueCochain_mapSimplex_inl a b (face i (leftPart σ h))
  · set hr := (continuous_to_sum_factor (rl σ)).resolve_left h
    show _ = ∑ i : Fin (n + 2), b (face i (rightPart σ hr))
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show face i σ = face i (mapSimplex (inrC M N) (rightPart σ hr)) from
        congrArg (face i) (mapSimplex_rightPart σ hr).symm,
      face_mapSimplex]
    exact glueCochain_mapSimplex_inr a b (face i (rightPart σ hr))

/-- The glue of zeros is zero. -/
theorem glueCochain_zero (n : ℕ) :
    glueCochain (M := M) (N := N) n 0 0 = 0 := by
  funext σ
  simp only [glueCochain]
  split_ifs <;> rfl

end SKEFTHawking.SingularCochainGlue
