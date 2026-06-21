import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularRelativeHomologyMod2
import SKEFTHawking.SingularMayerVietoris
import SKEFTHawking.SingularRelativeMV

/-!
# Phase 5q.F (L2, route c) — the singular chain complex as a mathlib `ChainComplex`

Route (c) [the `hcross` DR's RANK-1 gap-free path] requires the singular Mayer–Vietoris sequence as a
`CategoryTheory.ShortComplex.ShortExact`, so that `CategoryTheory.ShortComplex.SnakeInput.naturality_δ`
gives the cap-product MV-naturality square (`hcross`) abstractly — the SES *exactness* discharges the
small-simplices/excision content ONCE, sidestepping the per-instance **non-cycle** gap that kills the
direct singular-chain route (a): there `δ(cochainSplit) ∈ relCochains(union)` is unprovable because the
subdivision homotopy `c + Sdᵐc = ∂(Hc) + H(∂c)` leaves an irreducible `⟨δf, H(∂c)⟩` term, zero only for
cycles (`∂c = 0`), so `δ(cochainSplit)` lies in `relCochains U ⊓ V` but not `relCochains(union)`.

This module is the FOUNDATION: it repackages the project's ad-hoc `SingularChain`/`chainBoundary` as a
mathlib `ChainComplex (ModuleCat (ZMod 2)) ℕ`, so the categorical homological-algebra machinery (short
complexes, snake lemma, connecting maps and their naturality) applies. Kernel-pure
(`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularMayerVietoris SKEFTHawking.SingularRelativeMV CategoryTheory Limits

namespace SKEFTHawking.SingularChainComplexCat

/-- **The singular chain complex of `X` as a mathlib `ChainComplex`** (over `ModuleCat (ZMod 2)`):
objects `Cₙ(X) = SingularChain X n`, differential `∂ = chainBoundary`, with `∂ ∘ ∂ = 0` supplied by
`chainBoundary_comp_chainBoundary`. The categorical substrate for route (c)'s MV `ShortComplex.ShortExact`
and the `SnakeInput.naturality_δ` derivation of `hcross`. -/
noncomputable def singularChainCmplx (X : TopCat) : ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (ZMod 2) (SingularChain X n))
    (fun n => ModuleCat.ofHom (chainBoundary X n))
    (fun n => by rw [← ModuleCat.ofHom_comp, chainBoundary_comp_chainBoundary]; rfl)

/-- The degree-`n` object of `singularChainCmplx` is `SingularChain X n` (definitional unfold of
`ChainComplex.of`). -/
@[simp] theorem singularChainCmplx_X (X : TopCat) (n : ℕ) :
    (singularChainCmplx X).X n = ModuleCat.of (ZMod 2) (SingularChain X n) :=
  rfl

/-- **The restricted boundary `∂ : C_{n+1}(S) → C_n(S)`** (`chainBoundary` corestricted to the subspace
chains `C(S) = subspaceChains S`), well-defined by `chainBoundary_mem_subspaceChains`. -/
noncomputable def subDiff (X : TopCat) (S : Set ↑X) (n : ℕ) :
    subspaceChains S (n + 1) →ₗ[ZMod 2] subspaceChains S n :=
  (chainBoundary X n).restrict (fun c hc => chainBoundary_mem_subspaceChains (S := S) n c hc)

/-- `∂ ∘ ∂ = 0` for the subspace-chain differential (corestriction of the ambient `∂∂=0`). -/
theorem subDiff_comp (X : TopCat) (S : Set ↑X) (n : ℕ) :
    (subDiff X S n).comp (subDiff X S (n + 1)) = 0 :=
  LinearMap.ext fun x => Subtype.ext (chainBoundary_chainBoundary_apply X n x.1)

/-- **The subcomplex `C(S)` of subspace chains as a mathlib `ChainComplex`** — objects
`subspaceChains S n`, differential `subDiff`. One of the three legs of the small-chains Mayer–Vietoris
short exact sequence `0 → C(U∩V) → C(U)⊕C(V) → C(U+V) → 0` that route (c) packages as
`ShortComplex.ShortExact`. -/
noncomputable def subspaceChainsCmplx (X : TopCat) (S : Set ↑X) :
    ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (ZMod 2) (subspaceChains S n))
    (fun n => ModuleCat.ofHom (subDiff X S n))
    (fun n => by rw [← ModuleCat.ofHom_comp, subDiff_comp]; rfl)

/-- The degree-`n` object of `subspaceChainsCmplx S` is `subspaceChains S n`. -/
@[simp] theorem subspaceChainsCmplx_X (X : TopCat) (S : Set ↑X) (n : ℕ) :
    (subspaceChainsCmplx X S).X n = ModuleCat.of (ZMod 2) (subspaceChains S n) :=
  rfl

/-- **The inclusion chain map `C(A) → C(B)` for `A ⊆ B`** (degreewise the submodule inclusion
`subspaceChains_mono`, commuting with `∂` since both are corestrictions of the ambient boundary). The
reusable leg builder for the small-chains Mayer–Vietoris short exact sequence. -/
noncomputable def subInclCmplx (X : TopCat) {A B : Set ↑X} (h : A ⊆ B) :
    subspaceChainsCmplx X A ⟶ subspaceChainsCmplx X B :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => ModuleCat.ofHom (Submodule.inclusion (subspaceChains_mono h n)))
    (fun n => by rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]; congr 1)

/-- The degree-`n` component of `subInclCmplx` is the submodule inclusion. -/
@[simp] theorem subInclCmplx_f (X : TopCat) {A B : Set ↑X} (h : A ⊆ B) (n : ℕ) :
    (subInclCmplx X h).f n = ModuleCat.ofHom (Submodule.inclusion (subspaceChains_mono h n)) :=
  rfl

/-- The restricted boundary on the small (cover-subordinate) union chains `C(U+V) = mvUnionChains U V`. -/
noncomputable def mvUnionDiff (X : TopCat) (U V : Set ↑X) (n : ℕ) :
    mvUnionChains U V (n + 1) →ₗ[ZMod 2] mvUnionChains U V n :=
  (chainBoundary X n).restrict (fun c hc => chainBoundary_mem_mvUnionChains U V n c hc)

theorem mvUnionDiff_comp (X : TopCat) (U V : Set ↑X) (n : ℕ) :
    (mvUnionDiff X U V n).comp (mvUnionDiff X U V (n + 1)) = 0 :=
  LinearMap.ext fun x => Subtype.ext (chainBoundary_chainBoundary_apply X n x.1)

/-- **The small-chains complex `C(U+V)` as a mathlib `ChainComplex`** — objects `mvUnionChains U V n
= C(U) + C(V)`, differential `mvUnionDiff`. The third leg of the small-chains Mayer–Vietoris short exact
sequence `0 → C(U∩V) → C(U)⊕C(V) → C(U+V) → 0`. -/
noncomputable def mvUnionChainsCmplx (X : TopCat) (U V : Set ↑X) :
    ChainComplex (ModuleCat (ZMod 2)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (ZMod 2) (mvUnionChains U V n))
    (fun n => ModuleCat.ofHom (mvUnionDiff X U V n))
    (fun n => by rw [← ModuleCat.ofHom_comp, mvUnionDiff_comp]; rfl)

/-- The degree-`n` object of `mvUnionChainsCmplx U V` is `mvUnionChains U V n`. -/
@[simp] theorem mvUnionChainsCmplx_X (X : TopCat) (U V : Set ↑X) (n : ℕ) :
    (mvUnionChainsCmplx X U V).X n = ModuleCat.of (ZMod 2) (mvUnionChains U V n) :=
  rfl

/-- `C(U) ⊆ C(U+V)` (left summand of `mvUnionChains = C(U) ⊔ C(V)`). -/
theorem subspaceChains_le_mvUnion_left (X : TopCat) (U V : Set ↑X) (n : ℕ) :
    subspaceChains U n ≤ mvUnionChains U V n := by unfold mvUnionChains; exact le_sup_left

/-- `C(V) ⊆ C(U+V)`. -/
theorem subspaceChains_le_mvUnion_right (X : TopCat) (U V : Set ↑X) (n : ℕ) :
    subspaceChains V n ≤ mvUnionChains U V n := by unfold mvUnionChains; exact le_sup_right

/-- **The inclusion chain map `C(W) → C(U+V)`** for `C(W) ⊆ C(U+V)` (used with `W = U` via
`subspaceChains_le_mvUnion_left` and `W = V` via `_right` to build the surjection `C(U)⊕C(V) → C(U+V)`
of the Mayer–Vietoris short exact sequence). -/
noncomputable def subToMvUnionInclCmplx (X : TopCat) (U V W : Set ↑X)
    (hW : ∀ n, subspaceChains W n ≤ mvUnionChains U V n) :
    subspaceChainsCmplx X W ⟶ mvUnionChainsCmplx X U V :=
  ChainComplex.ofHom _ _ _ _ _ _
    (fun n => ModuleCat.ofHom (Submodule.inclusion (hW n)))
    (fun n => by rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]; congr 1)

/-- The degree-`n` component of `subToMvUnionInclCmplx`. -/
@[simp] theorem subToMvUnionInclCmplx_f (X : TopCat) (U V W : Set ↑X)
    (hW : ∀ n, subspaceChains W n ≤ mvUnionChains U V n) (n : ℕ) :
    (subToMvUnionInclCmplx X U V W hW).f n = ModuleCat.ofHom (Submodule.inclusion (hW n)) :=
  rfl

/-- **The Mayer–Vietoris incl–difference map `C(U∩V) → C(U)⊕C(V)`** (over ℤ/2; `⊕ = ⊞` biproduct),
degreewise `c ↦ (c, c)` (the project's signs vanish over ℤ/2). -/
noncomputable def mvSesMap1 (X : TopCat) (U V : Set ↑X) :
    subspaceChainsCmplx X (U ∩ V) ⟶ subspaceChainsCmplx X U ⊞ subspaceChainsCmplx X V :=
  biprod.lift (subInclCmplx X Set.inter_subset_left) (subInclCmplx X Set.inter_subset_right)

/-- **The Mayer–Vietoris sum map `C(U)⊕C(V) → C(U+V)`**, degreewise `(a, b) ↦ a + b` (= the small-chains
surjection onto `mvUnionChains = C(U) ⊔ C(V)`). -/
noncomputable def mvSesMap2 (X : TopCat) (U V : Set ↑X) :
    subspaceChainsCmplx X U ⊞ subspaceChainsCmplx X V ⟶ mvUnionChainsCmplx X U V :=
  biprod.desc (subToMvUnionInclCmplx X U V U (subspaceChains_le_mvUnion_left X U V))
    (subToMvUnionInclCmplx X U V V (subspaceChains_le_mvUnion_right X U V))

/-- **The small-chains Mayer–Vietoris short complex** `C(U∩V) → C(U)⊕C(V) → C(U+V)` as a
`ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ)`. The composite vanishes because over ℤ/2 the two
ways `C(U∩V) ↪ C(U+V)` (through `U` vs through `V`) coincide, so their sum is `x + x = x - x = 0`. The
substrate for `ShortExact` (next) → `SnakeInput.naturality_δ` → cap-product MV-naturality (`hcross`). -/
noncomputable def mvSes (X : TopCat) (U V : Set ↑X) :
    ShortComplex (ChainComplex (ModuleCat (ZMod 2)) ℕ) :=
  ShortComplex.mk (mvSesMap1 X U V) (mvSesMap2 X U V) (by
    rw [mvSesMap1, mvSesMap2, biprod.lift_desc]
    have h12 : subInclCmplx X (Set.inter_subset_left (s := U) (t := V)) ≫
          subToMvUnionInclCmplx X U V U (subspaceChains_le_mvUnion_left X U V)
        = subInclCmplx X (Set.inter_subset_right (s := U) (t := V)) ≫
          subToMvUnionInclCmplx X U V V (subspaceChains_le_mvUnion_right X U V) := by
      apply HomologicalComplex.hom_ext; intro n; apply ModuleCat.hom_ext; apply LinearMap.ext
      intro x; apply Subtype.ext; rfl
    rw [h12, ← ZModModule.sub_eq_add, sub_self])

/-- The inclusion chain map `C(A) → C(B)` is a monomorphism (degreewise the injective submodule
inclusion). -/
theorem subInclCmplx_mono (X : TopCat) {A B : Set ↑X} (h : A ⊆ B) : Mono (subInclCmplx X h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [subInclCmplx_f, ModuleCat.mono_iff_injective]
  exact Submodule.inclusion_injective (subspaceChains_mono h n)

/-- **The Mayer–Vietoris incl–difference map `C(U∩V) → C(U)⊕C(V)` is a monomorphism** — the first leg
of `mvSes` is mono (it factors `biprod.fst`-back to the mono inclusion `C(U∩V) → C(U)`). -/
theorem mvSesMap1_mono (X : TopCat) (U V : Set ↑X) : Mono (mvSesMap1 X U V) := by
  rw [mvSesMap1]
  haveI := subInclCmplx_mono X (Set.inter_subset_left (s := U) (t := V))
  exact mono_of_mono_fac (biprod.lift_fst _ _)

/-- **The Mayer–Vietoris sum map `C(U)⊕C(V) → C(U+V)` is an epimorphism** — degreewise surjective:
every `w ∈ mvUnionChains U V n = C(U) ⊔ C(V)` is `a + b` with `a ∈ C(U)`, `b ∈ C(V)`, the image of the
biproduct element `inl⟨a⟩ + inr⟨b⟩` (`biprod.inl_desc`/`inr_desc`). -/
theorem mvSesMap2_epi (X : TopCat) (U V : Set ↑X) : Epi (mvSesMap2 X U V) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  rw [ModuleCat.epi_iff_surjective]
  rintro ⟨w, hw⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  refine ⟨(biprod.inl (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n ⟨a, ha⟩
    + (biprod.inr (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n ⟨b, hb⟩, ?_⟩
  rw [mvSesMap2, map_add, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, biprod.inl_desc, biprod.inr_desc]
  apply Subtype.ext
  rfl

/-- The value of the sum map `g` on a biproduct element `inl a + inr b` is `a + b` (in `C(U+V)`). The
computational core of the Mayer–Vietoris exactness. -/
theorem mvSesMap2_inl_inr (X : TopCat) (U V : Set ↑X) (n : ℕ)
    (a : subspaceChains U n) (b : subspaceChains V n) :
    (((mvSesMap2 X U V).f n).hom)
        ((biprod.inl (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n a
          + (biprod.inr (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n b)
      = ⟨a.1 + b.1, Submodule.add_mem _ (subspaceChains_le_mvUnion_left X U V n a.2)
          (subspaceChains_le_mvUnion_right X U V n b.2)⟩ := by
  rw [map_add, mvSesMap2, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, biprod.inl_desc, biprod.inr_desc]
  rfl

/-- Biproduct decomposition of an element at degree `n`: `inl (fst y) + inr (snd y) = y`. -/
theorem biprod_total_apply (X : TopCat) (U V : Set ↑X) (n : ℕ)
    (y : ↑((subspaceChainsCmplx X U ⊞ subspaceChainsCmplx X V).X n)) :
    (biprod.inl (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n
        (((biprod.fst (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n).hom y)
      + (biprod.inr (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n
        (((biprod.snd (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n).hom y) = y := by
  have h := congrArg (fun (φ : (subspaceChainsCmplx X U ⊞ subspaceChainsCmplx X V) ⟶ _) =>
    ((φ.f n).hom) y) (biprod.total (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V))
  simpa only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    HomologicalComplex.id_f, ModuleCat.id_apply] using h

/-- `fst (f x) = x` viewed in `C(U)` (the first leg of the diagonal `f x = (x, x)`). -/
theorem mvSesMap1_fst (X : TopCat) (U V : Set ↑X) (n : ℕ) (x : subspaceChains (U ∩ V) n) :
    (((biprod.fst (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n).hom)
        (((mvSesMap1 X U V).f n).hom x)
      = ⟨x.1, subspaceChains_mono Set.inter_subset_left n x.2⟩ := by
  rw [mvSesMap1, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, biprod.lift_fst]; rfl

/-- `snd (f x) = x` viewed in `C(V)` (the second leg of the diagonal). -/
theorem mvSesMap1_snd (X : TopCat) (U V : Set ↑X) (n : ℕ) (x : subspaceChains (U ∩ V) n) :
    (((biprod.snd (X := subspaceChainsCmplx X U) (Y := subspaceChainsCmplx X V)).f n).hom)
        (((mvSesMap1 X U V).f n).hom x)
      = ⟨x.1, subspaceChains_mono Set.inter_subset_right n x.2⟩ := by
  rw [mvSesMap1, ← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, biprod.lift_snd]; rfl

end SKEFTHawking.SingularChainComplexCat
