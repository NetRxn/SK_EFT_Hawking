import Mathlib
import SKEFTHawking.SingularAffineChainInt
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.SingularSubdivision

/-!
# The signed **integral** singular barycentric subdivision `Sd : Cₙ(X;ℤ) → Cₙ(X;ℤ)`

Integral (signed) mirror of the mod-2 `SingularSubdivision`. Bridges the signed affine engine
`SingularAffineChainInt` to singular integral chains `SingularChainInt` via the **geometric**
pushforward maps `pushSimplexM` / `pushSimplexM_face` / `pushSimplexM_facetIncl` (from
`SingularExcisionPushforward`), which are coefficient-AGNOSTIC (they operate on the simplex-valued
function, not the coefficient), so are reused directly; only the ℤ-linear extension `pushChainMInt`
and the signed boundary bookkeeping are new.

Delivers, all over ℤ with the true alternating signs:
* `mapVertsInt` naturality (`∂`, `cone`, `Sd`, `D`);
* `pushChainMInt` + chain-map `∂ ∘ σ_# = σ_# ∘ ∂` + facet functoriality;
* `singularSdInt` with `∂ ∘ Sd = Sd ∘ ∂`;
* `singularDInt` with `∂D + D∂ = 1 − Sd` (SIGNED — the mod-2 file collapses `1 − Sd = 1 + Sd`);
* the `LinearMap` forms + the iterated `Sdᵐ` chain map + `Dₘ` with `∂Dₘ + Dₘ∂ = 1 − Sdᵐ`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

namespace SKEFTHawking.SingularSubdivisionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularAffineChainInt
open SKEFTHawking.SingularExcisionPushforward
open SKEFTHawking.SingularSubdivisionConvex (chainsIn single_mem_chainsIn)
open SKEFTHawking.SingularExcisionMod2 (barycenter)

/-! ## §1. Vertex relabelling `mapVertsInt` and its naturality -/

section MapVerts

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- **Vertex relabelling along a linear map** `L : V →ₗ[ℝ] W` (integral): `[v₀,…,vₙ] ↦ [Lv₀,…,Lvₙ]`. -/
noncomputable def mapVertsInt (L : V →ₗ[ℝ] W) (n : ℕ) :
    LinChainInt V n →ₗ[ℤ] LinChainInt W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => (L : V → W) ∘ v)

theorem mapVertsInt_single (L : V →ₗ[ℝ] W) (n : ℕ) (v : Fin (n + 1) → V) (a : ℤ) :
    mapVertsInt L n (Finsupp.single v a) = Finsupp.single ((L : V → W) ∘ v) a := by
  rw [mapVertsInt, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- A linear map carries a barycenter to the barycenter of the images. -/
theorem map_barycenter (L : V →ₗ[ℝ] W) {n : ℕ} (v : Fin (n + 1) → V) :
    L (barycenter v) = barycenter ((L : V → W) ∘ v) := by
  rw [barycenter, barycenter, map_smul, map_sum]; rfl

/-- `mapVertsInt` commutes with `coneInt` (apex `b ↦ L b`). -/
theorem mapVertsInt_coneInt (L : V →ₗ[ℝ] W) (b : V) (n : ℕ) (c : LinChainInt V n) :
    mapVertsInt L (n + 1) (coneInt b n c) = coneInt (L b) n (mapVertsInt L n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [coneInt_single_smul, map_smul, mapVertsInt_single, Fin.comp_cons]

/-- `mapVertsInt` commutes with the signed affine boundary `∂`. -/
theorem mapVertsInt_linBoundaryInt (L : V →ₗ[ℝ] W) (n : ℕ) (c : LinChainInt V (n + 1)) :
    mapVertsInt L n (linBoundaryInt n c) = linBoundaryInt n (mapVertsInt L (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [linBoundaryInt_single_smul, map_smul, mapVertsInt_single, linBoundaryInt_single_smul,
      mapVertsInt, Finsupp.lmapDomain_apply, linBoundaryBasisInt, linBoundaryBasisInt,
      Finsupp.mapDomain_finset_sum]
    refine congrArg (a • ·) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
    rfl

/-- **The subdivision is natural under linear maps**: `Sd ∘ L_* = L_* ∘ Sd` (integral). -/
theorem mapVertsInt_linSubdivInt (L : V →ₗ[ℝ] W) :
    ∀ (n : ℕ) (c : LinChainInt V n), mapVertsInt L n (linSubdivInt n c) = linSubdivInt n (mapVertsInt L n c)
  | 0, c => by rw [linSubdivInt_zero, linSubdivInt_zero]
  | n + 1, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [linSubdivInt_single_smul, map_smul, mapVertsInt_coneInt, map_barycenter,
        mapVertsInt_linSubdivInt L n, mapVertsInt_linBoundaryInt, mapVertsInt_single,
        ← linSubdivInt_single_smul, mapVertsInt_single]

/-- **The homotopy `D` is natural under linear maps**: `D ∘ L_* = L_* ∘ D` (integral). -/
theorem mapVertsInt_linHomotopyInt (L : V →ₗ[ℝ] W) :
    ∀ (n : ℕ) (c : LinChainInt V n),
      mapVertsInt L (n + 1) (linHomotopyInt n c) = linHomotopyInt n (mapVertsInt L n c)
  | 0, c => by rw [linHomotopyInt_zero_map, linHomotopyInt_zero_map, map_zero]
  | n + 1, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [linHomotopyInt_single_smul, map_smul, mapVertsInt_coneInt, map_barycenter, map_sub,
        mapVertsInt_single, mapVertsInt_linHomotopyInt L n, mapVertsInt_linBoundaryInt,
        mapVertsInt_single, ← linHomotopyInt_single_smul, mapVertsInt_single]

end MapVerts

/-! ## §2. The integral pushforward `pushChainMInt` and its chain-map property

Reuses the coefficient-agnostic geometric maps `pushSimplexM`, `pushSimplexM_face`,
`pushSimplexM_facetIncl` from `SingularExcisionPushforward` (they operate on the simplex-valued
function, not on coefficients), building only the ℤ-linear extension. -/

open SKEFTHawking.SingularSubdivision (pushSimplexM_facetIncl)

/-- The module-valued pushforward as a ℤ-linear map `LinChainInt (Fin (N+1) → ℝ) n → SingularChainInt X n`
(the `Finsupp` extension of the shared geometric `pushSimplexM σ`). -/
noncomputable def pushChainMInt {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N))) :
    LinChainInt (Fin (N + 1) → ℝ) n →ₗ[ℤ] SingularChainInt X n :=
  Finsupp.lmapDomain ℤ ℤ (pushSimplexM σ)

theorem pushChainMInt_single {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    (u : Fin (n + 1) → (Fin (N + 1) → ℝ)) (a : ℤ) :
    pushChainMInt σ (Finsupp.single u a) = Finsupp.single (pushSimplexM σ u) a := by
  rw [pushChainMInt, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- **The pushforward is a chain map on in-`Δᴺ` chains**: `∂ (σ_# c) = σ_# (∂ c)` over ℤ (with the
signs). Reuses the geometric `pushSimplexM_face`; the sign `(-1)ⁱ` threads through via `map_smul`. -/
theorem pushChainMInt_chainBoundary {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {c : LinChainInt (Fin (N + 1) → ℝ) (n + 1)}
    (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (N + 1))) (n + 1)) :
    chainBoundary X n (pushChainMInt σ c) = pushChainMInt σ (linBoundaryInt n c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨u, hu, rfl⟩
    rw [pushChainMInt_single, chainBoundary_single, boundaryBasis, linBoundaryInt_single,
      linBoundaryBasisInt, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, pushChainMInt_single]
    congr 2
    exact pushSimplexM_face σ hu i
  · simp only [map_zero]
  · intro x y _ _ hx hy; simp only [map_add]; rw [hx, hy]
  · intro a x _ hx; simp only [map_smul]; rw [hx]

/-- **Chain-level facet functoriality**: `σ_# ∘ (Lᵢ)_* = (∂ᵢσ)_#` on in-`Δᴺ` chains (integral). -/
theorem pushChainMInt_mapVertsInt {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (N + 1)))) (i : Fin (N + 2))
    {c : LinChainInt (Fin (N + 1) → ℝ) n}
    (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (N + 1))) n) :
    pushChainMInt σ (mapVertsInt (FunOnFinite.linearMap ℝ ℝ i.succAbove) n c)
      = pushChainMInt (SingularCohomologyInt.face i σ) c := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [mapVertsInt_single, pushChainMInt_single, pushChainMInt_single]
    exact congrArg (Finsupp.single · 1) (pushSimplexM_facetIncl σ i hw)
  · simp only [map_zero]
  · intro x y _ _ hx hy; simp only [map_add]; rw [hx, hy]
  · intro a x _ hx; simp only [map_smul]; rw [hx]

/-! ## §3. The signed singular subdivision `singularSdInt` and its chain-map -/

/-- The **identity affine `n`-simplex** of `Δⁿ` (integral): the single simplex on the `n+1` standard
basis vertices `eⱼ = Pi.single j 1`. -/
noncomputable def idChainInt (n : ℕ) : LinChainInt (Fin (n + 1) → ℝ) n :=
  Finsupp.single (fun j => Pi.single j 1) 1

theorem idChainInt_mem (n : ℕ) : idChainInt n ∈ chainsInInt (stdSimplex ℝ (Fin (n + 1))) n :=
  single_mem_chainsInInt (fun j => single_mem_stdSimplex ℝ j)

/-- **The signed singular barycentric subdivision** `Sd : Cₙ(X;ℤ) → Cₙ(X;ℤ)`: `Sd σ := σ_# (Sd ι_n)`. -/
noncomputable def singularSdInt (X : TopCat) (n : ℕ) :
    SingularChainInt X n →ₗ[ℤ] SingularChainInt X n :=
  Finsupp.linearCombination ℤ (fun σ => pushChainMInt σ (linSubdivInt n (idChainInt n)))

theorem singularSdInt_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    singularSdInt X n (Finsupp.single σ 1) = pushChainMInt σ (linSubdivInt n (idChainInt n)) := by
  rw [singularSdInt, Finsupp.linearCombination_single, one_smul]

/-- The `i`-th facet of the identity `(n+1)`-simplex is the linear image of the identity `n`-simplex:
`∂ᵢ ι_{n+1} = (Lᵢ)_* ι_n` (integral). -/
theorem facet_idChainInt (n : ℕ) (i : Fin (n + 2)) :
    Finsupp.single ((fun j => (Pi.single j 1 : Fin (n + 1 + 1) → ℝ)) ∘ i.succAbove) (1 : ℤ)
      = mapVertsInt (FunOnFinite.linearMap ℝ ℝ i.succAbove) n (idChainInt n) := by
  rw [idChainInt, mapVertsInt_single]
  congr 1
  funext j
  rw [Function.comp_apply, Function.comp_apply, FunOnFinite.linearMap_piSingle]

/-- **The singular subdivision is a chain map**: `∂ ∘ Sd = Sd ∘ ∂` on a basis simplex (integral). -/
theorem chainBoundary_singularSdInt (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary X n (singularSdInt X (n + 1) (Finsupp.single σ 1))
      = singularSdInt X n (chainBoundary X n (Finsupp.single σ 1)) := by
  rw [singularSdInt_single,
    pushChainMInt_chainBoundary σ
      (linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) (n + 1) (idChainInt_mem (n + 1))),
    linBoundaryInt_linSubdivInt, idChainInt, linBoundaryInt_single, linBoundaryBasisInt, map_sum,
    map_sum, chainBoundary_single, boundaryBasis, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_smul]
  refine congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
  rw [singularSdInt_single, facet_idChainInt, ← mapVertsInt_linSubdivInt,
    pushChainMInt_mapVertsInt σ i
      (linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))]

/-- **`∂ ∘ Sd = Sd ∘ ∂` as a `LinearMap` identity** (integral). -/
theorem singularSdInt_comp_chainBoundary (X : TopCat) (n : ℕ) :
    (chainBoundary X n).comp (singularSdInt X (n + 1))
      = (singularSdInt X n).comp (chainBoundary X n) := by
  refine LinearMap.ext fun c => ?_
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [LinearMap.comp_apply, map_add] at hc hd ⊢; rw [hc, hd]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ 1 from by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    simp only [LinearMap.comp_apply, map_smul]
    rw [chainBoundary_singularSdInt]

/-! ## §4. The signed singular homotopy `singularDInt` and `∂D + D∂ = 1 − Sd` -/

/-- The top affine simplex of the subdivision (the identity `ι_{N+1}`) pushes to `σ`:
`σ_# ι_{N+1} = σ` (integral). The leading `1` of the homotopy identity. -/
theorem pushChainMInt_idChainInt {X : TopCat} {N : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (N + 1)))) :
    pushChainMInt σ (idChainInt (N + 1)) = Finsupp.single σ 1 := by
  rw [idChainInt, pushChainMInt_single, pushSimplexM_vertices]

/-- **The signed singular subdivision chain homotopy** `D : Cₙ(X;ℤ) → Cₙ₊₁(X;ℤ)`: `D σ := σ_# (D ι_n)`. -/
noncomputable def singularDInt (X : TopCat) (n : ℕ) :
    SingularChainInt X n →ₗ[ℤ] SingularChainInt X (n + 1) :=
  Finsupp.linearCombination ℤ (fun σ => pushChainMInt σ (linHomotopyInt n (idChainInt n)))

theorem singularDInt_single (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    singularDInt X n (Finsupp.single σ 1) = pushChainMInt σ (linHomotopyInt n (idChainInt n)) := by
  rw [singularDInt, Finsupp.linearCombination_single, one_smul]

/-- **The singular subdivision is chain-homotopic to the identity** via `D`: `∂D + D∂ = 1 − Sd`
(integral, SIGNED — the mod-2 file collapses `1 − Sd = 1 + Sd`) on a basis simplex. -/
theorem chainBoundary_singularDInt (X : TopCat) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) :
    chainBoundary X (n + 1) (singularDInt X (n + 1) (Finsupp.single σ 1))
        + singularDInt X n (chainBoundary X n (Finsupp.single σ 1))
      = Finsupp.single σ 1 - singularSdInt X (n + 1) (Finsupp.single σ 1) := by
  have hB : singularDInt X n (chainBoundary X n (Finsupp.single σ 1))
      = pushChainMInt σ (linHomotopyInt n (linBoundaryInt n (idChainInt (n + 1)))) := by
    rw [chainBoundary_single, boundaryBasis, map_sum, idChainInt, linBoundaryInt_single,
      linBoundaryBasisInt, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_smul]
    refine congrArg ((-1 : ℤ) ^ (i : ℕ) • ·) ?_
    rw [singularDInt_single, facet_idChainInt, ← mapVertsInt_linHomotopyInt,
      pushChainMInt_mapVertsInt σ i
        (linHomotopyInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))]
  rw [hB, singularDInt_single,
    pushChainMInt_chainBoundary σ
      (linHomotopyInt_mem_chainsInInt (convex_stdSimplex ℝ _) (n + 1) (idChainInt_mem (n + 1))),
    ← map_add, linBoundaryInt_linHomotopyInt, map_sub, pushChainMInt_idChainInt, singularSdInt_single]

/-- **`∂D + D∂ = 1 − Sd` as a `LinearMap` identity** (integral). -/
theorem singularDInt_chainHomotopy (X : TopCat) (n : ℕ) :
    (chainBoundary X (n + 1)).comp (singularDInt X (n + 1))
        + (singularDInt X n).comp (chainBoundary X n)
      = LinearMap.id - singularSdInt X (n + 1) := by
  refine LinearMap.ext fun c => ?_
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd =>
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add] at hc hd ⊢
    rw [hc, hd]
  | single σ a =>
    rw [show Finsupp.single σ a = a • Finsupp.single σ 1 from by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
    simp only [map_smul]
    refine congrArg (a • ·) ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    exact chainBoundary_singularDInt X n σ

/-! ## §5. Iterated subdivision `Sdᵐ`, the iterated homotopy `Dₘ`, and the pushforward naturality -/

/-- **`∂ ∘ Sdᵐ = Sdᵐ ∘ ∂`** — the iterated subdivision is a chain map (integral). -/
theorem singularSdInt_iterate_chainBoundary (X : TopCat) (n m : ℕ) (c : SingularChainInt X (n + 1)) :
    chainBoundary X n ((⇑(singularSdInt X (n + 1)))^[m] c)
      = (⇑(singularSdInt X n))^[m] (chainBoundary X n c) := by
  have hcomm : ∀ x, chainBoundary X n (singularSdInt X (n + 1) x)
      = singularSdInt X n (chainBoundary X n x) :=
    fun x => LinearMap.congr_fun (singularSdInt_comp_chainBoundary X n) x
  induction m generalizing c with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply, hcomm, ih, Function.iterate_succ',
      Function.comp_apply]

/-- The **iterated subdivision homotopy** `Dₘ := ∑_{i<m} Sdⁱ ∘ D : Cₙ → Cₙ₊₁` (integral). -/
noncomputable def iterHomotopyInt (X : TopCat) (n m : ℕ) (c : SingularChainInt X n) :
    SingularChainInt X (n + 1) :=
  ∑ i ∈ Finset.range m, (⇑(singularSdInt X (n + 1)))^[i] (singularDInt X n c)

theorem iterHomotopyInt_succ (X : TopCat) (n m : ℕ) (c : SingularChainInt X n) :
    iterHomotopyInt X n (m + 1) c
      = iterHomotopyInt X n m c + (⇑(singularSdInt X (n + 1)))^[m] (singularDInt X n c) := by
  rw [iterHomotopyInt, iterHomotopyInt, Finset.sum_range_succ]

/-- **The iterated subdivision is chain-homotopic to the identity**: `∂Dₘ + Dₘ∂ = 1 − Sdᵐ`
(integral, signed). Telescoping induction on `m`: the base is `c − c = 0`; the step adds
`Sdᵐ(∂D+D∂) = Sdᵐ − Sd^{m+1}`. -/
theorem iterHomotopyInt_chainHomotopy (X : TopCat) (m : ℕ) :
    ∀ (n : ℕ) (c : SingularChainInt X (n + 1)),
      chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m c)
          + iterHomotopyInt X n m (chainBoundary X n c)
        = c - (⇑(singularSdInt X (n + 1)))^[m] c := by
  induction m with
  | zero =>
    intro n c
    simp only [iterHomotopyInt, Finset.range_zero, Finset.sum_empty, map_zero, add_zero,
      Function.iterate_zero, id_eq, sub_self]
  | succ m ih =>
    intro n c
    have hadd : ∀ a b : SingularChainInt X (n + 1),
        (⇑(singularSdInt X (n + 1)))^[m] (a + b)
          = (⇑(singularSdInt X (n + 1)))^[m] a + (⇑(singularSdInt X (n + 1)))^[m] b :=
      fun a b => by simp only [← Module.End.coe_pow, map_add]
    have hsub : ∀ a b : SingularChainInt X (n + 1),
        (⇑(singularSdInt X (n + 1)))^[m] (a - b)
          = (⇑(singularSdInt X (n + 1)))^[m] a - (⇑(singularSdInt X (n + 1)))^[m] b :=
      fun a b => by simp only [← Module.End.coe_pow, map_sub]
    have hstep : ∀ x : SingularChainInt X (n + 1),
        chainBoundary X (n + 1) (singularDInt X (n + 1) x) + singularDInt X n (chainBoundary X n x)
          = x - singularSdInt X (n + 1) x :=
      fun x => LinearMap.congr_fun (singularDInt_chainHomotopy X n) x
    rw [iterHomotopyInt_succ, iterHomotopyInt_succ, map_add,
      singularSdInt_iterate_chainBoundary X (n + 1) m, add_add_add_comm, ih n c, ← hadd, hstep,
      hsub, ← Function.iterate_succ_apply]
    abel

-- The affine-image linear map `Δᴹ → Δᴺ`, `x ↦ ∑ₖ xₖ • uₖ` (shared, coefficient-agnostic).
open SKEFTHawking.SingularSubdivision (vertsMap vertsMap_apply vertsMap_basis)

/-- **The pushforward is functorial in the simplex (chain level)** (integral): for an affine chain `c`
on `Δᴹ`, pushing along `σ_# u` equals pushing its `vertsMap u`-relabelling along `σ`. -/
theorem pushChainMInt_pushSimplexM {X : TopCat} {N M n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {u : Fin (M + 1) → (Fin (N + 1) → ℝ)} (hu : ∀ k, u k ∈ stdSimplex ℝ (Fin (N + 1)))
    {c : LinChainInt (Fin (M + 1) → ℝ) n} (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (M + 1))) n) :
    pushChainMInt (pushSimplexM σ u) c = pushChainMInt σ (mapVertsInt (vertsMap u) n c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨x, hx, rfl⟩
    have hv : (fun j => ∑ k, x j k • u k) = ⇑(vertsMap u) ∘ x := by
      funext j; rw [Function.comp_apply, vertsMap_apply]
    rw [pushChainMInt_single, pushSimplexM_pushSimplexM σ hu hx, mapVertsInt_single,
      pushChainMInt_single, hv]
  · simp only [map_zero]
  · intro a b _ _ ha hb; simp only [map_add, ha, hb]
  · intro r a _ ha; simp only [map_smul, ha]

/-- **The singular subdivision is natural under the pushforward**: `Sd(σ_# c) = σ_#(Sd c)` (integral). -/
theorem singularSdInt_pushChainMInt {X : TopCat} {N n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk N)))
    {c : LinChainInt (Fin (N + 1) → ℝ) n} (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (N + 1))) n) :
    singularSdInt X n (pushChainMInt σ c) = pushChainMInt σ (linSubdivInt n c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨u, hu, rfl⟩
    have hbase : mapVertsInt (vertsMap u) n (idChainInt n) = Finsupp.single u 1 := by
      rw [idChainInt, mapVertsInt_single]
      have hcoe : (⇑(vertsMap u) ∘ fun j => (Pi.single j 1 : Fin (n + 1) → ℝ)) = u := by
        funext j; rw [Function.comp_apply, vertsMap_basis]
      rw [hcoe]
    rw [pushChainMInt_single, singularSdInt_single,
      pushChainMInt_pushSimplexM σ hu
        (linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n)),
      mapVertsInt_linSubdivInt, hbase]
  · simp only [map_zero]
  · intro a b _ _ ha hb; simp only [map_add, ha, hb]
  · intro r a _ ha; simp only [map_smul, ha]

/-- The iterated subdivision of the identity chain stays in `Δⁿ`'s in-simplex chains (integral). -/
theorem linSubdivInt_iterate_idChainInt_mem (n m : ℕ) :
    (⇑(linSubdivInt n))^[m] (idChainInt n) ∈ chainsInInt (stdSimplex ℝ (Fin (n + 1))) n := by
  induction m with
  | zero => rw [Function.iterate_zero_apply]; exact idChainInt_mem n
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) n ih

/-- **The iterate connection**: `Sdᵐ[σ] = σ_#((Sd_aff)ᵐ ιₙ)` (integral). The bridge that hands the
affine diameter estimate to the singular excision argument. -/
theorem singularSdInt_iterate_single {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (m : ℕ) :
    (⇑(singularSdInt X n))^[m] (Finsupp.single σ 1)
      = pushChainMInt σ ((⇑(linSubdivInt n))^[m] (idChainInt n)) := by
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply, Function.iterate_zero_apply, idChainInt, pushChainMInt_single,
      pushSimplexM_vertices]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      singularSdInt_pushChainMInt σ (linSubdivInt_iterate_idChainInt_mem n k),
      Function.iterate_succ_apply']

end SKEFTHawking.SingularSubdivisionInt
