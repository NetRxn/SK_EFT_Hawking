import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularRelativeCap
import SKEFTHawking.SingularLocalHomologyIsoInt

/-!
# Phase 5q.H (E1 integral topology) — the Euclidean local Poincaré-duality cap-iso (PD base case)

The **base case** of the Mayer–Vietoris five-lemma proof of integral Poincaré duality on an open
4-manifold (Hatcher 3.35): for the open Euclidean model `ℝ⁴` (a chart ball), the cap-duality map from
compactly-supported cohomology to homology is an **isomorphism**. Concretely the load-bearing case is
`H⁴_c(ℝ⁴; ℤ) ⌢ [ℝ⁴]_loc ≅ H₀(ℝ⁴; ℤ)`, both `≅ ℤ`.

This is the self-contained leaf consumed by the lead's MV five-lemma. It does **not** depend on the
general MV/CSC colimit — the `ℝ⁴` case is built standalone, computing the compactly-supported cohomology
directly (it is `ℤ` at `k = 4` and `0` else).

## Structure

* §A — the **integral relative cap chain-heart**: a cochain vanishing on the subspace `S` caps a
  subspace chain to `0` (`capInt_subspaceChainInt_eq_zero`), so `a ⌢ (relative cycle)` is an absolute
  cycle (`capInt_relCycle_isCycleInt`). Integral mirror of `SingularRelativeCap`, reusing the built
  `capInt` primitives.
* §B — **integral relative cohomology** `Hⁿ(X, S; ℤ)` (`RelativeCohomologyInt`), the annihilator of the
  subspace subcomplex under the integral Kronecker pairing. Integral mirror of
  `SingularRelativeCohomologyMod2`.
* §C — the **integral relative Poincaré–Lefschetz duality map** `relativeDualityInt : Hᵏ(X,S;ℤ) →
  Hₘ₊₁(X;ℤ)`, `[a] ↦ [a ⌢ z]`. Integral mirror of `SingularRelativeDuality.relativeDuality`.
* §D — the **degree-0 output** duality map `relativeDualityInt0 : Hᵏ⁺¹(X,S;ℤ) → H₀(X;ℤ)` — the
  top-degree / load-bearing shape `H⁴_c(ℝ⁴) ⌢ [ℝ⁴]_loc → H₀`.
* §E — the concrete Euclidean-model target-side isos: `H₀(ℝ⁴;ℤ) ≅ ℤ` (`euclH0IsoInt`), off-degree
  homology vanishing (`euclHomologyOffDegree_eq_zero`), and the source-side local homology
  `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ` re-exported (`euclLocalHomologyIsoInt'`).
* §F — the **local cap-iso packaging** `EuclLocalCapIsoData`: the base-case iso as a `LinearEquiv`
  disclosed as datum (the source-side `H⁴_c(ℝ⁴;ℤ) ≅ ℤ` + generator match = the integral-relative-UCT
  input the mod-2 base case gets from field-UC), with the reduction to `IsIso` / bijectivity that the
  MV five-lemma consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularLineMinusPointInt (augHInt eucl_augHInt_injective augHInt_surjective)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularLocalHomologyInt (eucl_homology_trivialInt)
open SKEFTHawking.SingularLocalHomologyIsoInt (euclLocalHomologyIsoInt)

namespace SKEFTHawking.SingularEuclideanCapIsoInt

variable {X : TopCat} (S : Set X)

/-! ## §A. The integral relative cap chain-heart -/

/-- **`frontFace` commutes with the subspace inclusion** (integral cup faces) — naturality of
`simplexIncl` against the front-face inclusion `frontIncl`. Integral analogue of
`SingularRelativeCap.frontFace_simplexIncl`, for the `SingularCupInt.frontFace` used by `capBasisInt`. -/
theorem frontFace_simplexIncl {p q : ℕ}
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (p + q)))) :
    frontFace (simplexIncl S (p + q) τ) = simplexIncl S p (frontFace τ) := by
  simpa only [simplexIncl, frontFace] using
    -- v4.32: `FunctorToTypes.naturality` is deprecated in favour of `NatTrans.naturality_apply`,
    -- which takes F/G implicitly, so the two `_`s go. Orientation is unchanged — the `.symm`
    -- stays. (A sibling site elsewhere DID need the orientation flipped; check, do not assume.)
    (NatTrans.naturality_apply (TopCat.toSSet.map (SingularRelativeHomologyMod2.inclMap S))
      (frontIncl p q).op τ).symm

/-- **A cochain vanishing on `S` caps a subspace chain to `0`** (integral): if `a σ = 0` for every
`S`-simplex `σ` (i.e. `a` is a relative cochain), then `a ⌢ c = 0` for every `c ∈ subspaceChainsInt S`.
Integral mirror of `SingularRelativeCap.cap_subspaceChain_eq_zero`, reusing the topological
front-face naturality lemma (`ZMod 2`-independent). -/
theorem capInt_subspaceChainInt_eq_zero {k m : ℕ} (a : SingularCochainInt X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    {c : SingularChainInt X (k + m)} (hc : c ∈ subspaceChainsInt S (k + m)) :
    capInt (m := m) a c = 0 := by
  rw [subspaceChainsInt, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]
  | add d e hd he => rw [map_add, map_add, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, capInt_single_smul, capBasisInt,
        frontFace_simplexIncl S τ, ha (frontFace τ), zero_smul, smul_zero]

/-- **The integral relative cap lands cycles**: for a **relative cocycle** `a` (vanishing on `S`,
`δa = 0`) and a **relative cycle** `z` (its boundary `∂z` is a subspace chain), the cap `a ⌢ z` is an
**absolute** cycle. Integral mirror of `SingularRelativeCap.cap_relCycle_isCycle`; the chain-level heart
of the integral relative duality map `Hᵏ(M, S; ℤ) → Hₙ₋ₖ(M; ℤ)`. -/
theorem capInt_relCycle_isCycleInt {k m : ℕ} (a : SingularCochainInt X k)
    (ha : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      a (simplexIncl S k τ) = 0)
    (hδa : coboundaryₗ X k a = 0) {z : SingularChainInt X (k + m + 1)}
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    chainBoundary X m (capInt (m := m + 1) a z) = 0 := by
  rw [capInt_cocycle_chainMap a hδa z]
  rw [capInt_subspaceChainInt_eq_zero S a ha hz, smul_zero]

/-! ## §B. Integral relative cohomology `Hⁿ(X, S; ℤ) = ker δⁿ / im δⁿ⁻¹`

Direct integral mirror of `SingularRelativeCohomologyMod2` (`ZMod 2 → ℤ`): relative `n`-cochains are
the singular integral `n`-cochains that vanish on the subspace chains `subspaceChainsInt S n` (the
annihilator of `C_•(S;ℤ) ↪ C_•(X;ℤ)` under the integral Kronecker pairing). The integral coboundary
preserves this annihilator (adjunction `⟨δf, c⟩ = ⟨f, ∂c⟩` + `∂` mapping subspace chains to subspace
chains), giving the relative cochain complex and its cohomology. -/

/-- **Relative `n`-cochains** `Cⁿ(X, S; ℤ)`: the integral `n`-cochains `f` vanishing on the subspace
chains, `⟨f, c⟩ = 0` for every `c ∈ subspaceChainsInt S n`. The integer-coefficient annihilator of the
subcomplex `C_•(S;ℤ) ↪ C_•(X;ℤ)`. -/
def relCochainsInt (n : ℕ) : Submodule ℤ (SingularCochainInt X n) where
  carrier := { f | ∀ c ∈ subspaceChainsInt S n, kronecker f c = 0 }
  zero_mem' := by
    intro c _
    simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
  add_mem' {f g} hf hg := by
    intro c hc
    rw [kronecker_add_left, hf c hc, hg c hc, add_zero]
  smul_mem' s f hf := by
    intro c hc
    rw [kronecker_smul_left, hf c hc, smul_zero]

theorem mem_relCochainsInt (n : ℕ) (f : SingularCochainInt X n) :
    f ∈ relCochainsInt S n ↔ ∀ c ∈ subspaceChainsInt S n, kronecker f c = 0 :=
  Iff.rfl

/-- **The integral coboundary preserves relative cochains** (adjunction + `∂` on subspace chains). -/
theorem coboundary_mem_relCochainsInt (n : ℕ) (f : SingularCochainInt X n)
    (hf : f ∈ relCochainsInt S n) : coboundary X n f ∈ relCochainsInt S (n + 1) := by
  intro c hc
  rw [kronecker_coboundary_chainBoundary]
  exact hf _ (chainBoundary_mem_subspaceChainsInt S n c hc)

/-- The **integral relative coboundary** `δⁿ : Cⁿ(X,S;ℤ) →ₗ Cⁿ⁺¹(X,S;ℤ)`. -/
noncomputable def relCoboundaryIntₗ (n : ℕ) :
    relCochainsInt S n →ₗ[ℤ] relCochainsInt S (n + 1) :=
  ((coboundaryₗ X n).domRestrict (relCochainsInt S n)).codRestrict (relCochainsInt S (n + 1))
    (fun f => coboundary_mem_relCochainsInt S n f.1 f.2)

@[simp] theorem relCoboundaryIntₗ_coe (n : ℕ) (f : relCochainsInt S n) :
    (relCoboundaryIntₗ S n f : SingularCochainInt X (n + 1)) = coboundary X n f.1 := rfl

/-- The submodule of integral relative `n`-coboundaries, `⊥` in degree `0`. -/
noncomputable def relCoboundaryRangeInt (n : ℕ) : Submodule ℤ (relCochainsInt S n) :=
  match n with
  | 0 => ⊥
  | m + 1 => LinearMap.range (relCoboundaryIntₗ S m)

/-- Integral relative coboundaries are relative cocycles, `im δⁿ⁻¹ ≤ ker δⁿ`. -/
theorem relCoboundaryRangeInt_le_ker (n : ℕ) :
    relCoboundaryRangeInt S n ≤ LinearMap.ker (relCoboundaryIntₗ S n) := by
  cases n with
  | zero => exact bot_le
  | succ m =>
    show LinearMap.range (relCoboundaryIntₗ S m) ≤ LinearMap.ker (relCoboundaryIntₗ S (m + 1))
    rw [LinearMap.range_le_ker_iff]
    apply LinearMap.ext
    intro g
    apply Subtype.ext
    show coboundary X (m + 1) (coboundary X m g.1) = 0
    exact coboundary_comp_coboundary X m g.1

/-- **Integral relative singular cohomology** `Hⁿ(X, S; ℤ) = ker δⁿ / im δⁿ⁻¹`. -/
def RelativeCohomologyInt (n : ℕ) : Type :=
  (LinearMap.ker (relCoboundaryIntₗ S n)) ⧸
    (relCoboundaryRangeInt S n).submoduleOf (LinearMap.ker (relCoboundaryIntₗ S n))

noncomputable instance (n : ℕ) : AddCommGroup (RelativeCohomologyInt S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module ℤ (RelativeCohomologyInt S n) :=
  inferInstanceAs (Module ℤ (_ ⧸ _))

/-- The integral relative cohomology class of a relative cocycle. -/
noncomputable def RelativeCohomologyInt.mk (n : ℕ) (z : LinearMap.ker (relCoboundaryIntₗ S n)) :
    RelativeCohomologyInt S n :=
  Submodule.Quotient.mk z

theorem RelativeCohomologyInt.mk_surjective (n : ℕ) :
    Function.Surjective (RelativeCohomologyInt.mk S n) :=
  Submodule.Quotient.mk_surjective _

/-- An integral relative cohomology class `[z]` vanishes iff its cocycle is a relative coboundary. -/
theorem RelativeCohomologyInt.mk_eq_zero_iff (n : ℕ) (z : LinearMap.ker (relCoboundaryIntₗ S n)) :
    RelativeCohomologyInt.mk S n z = 0 ↔
      (z : relCochainsInt S n) ∈ relCoboundaryRangeInt S n := by
  constructor
  · intro h
    have h2 : z ∈ (relCoboundaryRangeInt S n).submoduleOf (LinearMap.ker (relCoboundaryIntₗ S n)) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

/-! ## §C. The integral relative Poincaré–Lefschetz duality map `D_z : Hᵏ(X, S; ℤ) → Hₙ₋ₖ(X; ℤ)`

For a fixed relative fundamental cycle `z` (an integral `(k+m+1)`-chain whose boundary `∂z` is a
subspace chain), `[a] ↦ [a ⌢ z]`. Integral mirror of `SingularRelativeDuality.relativeDuality`. -/

/-- A **relative cochain vanishes on `S`-simplices**: `⟨f, c⟩ = 0` for every subspace chain forces
`f (simplexIncl S k τ) = 0` on each single `S`-simplex `τ` (a single `S`-simplex is a subspace chain,
`kronecker f (single (simplexIncl τ) 1) = f (simplexIncl τ)`). -/
theorem relCochainInt_vanish {k : ℕ} (a : relCochainsInt S k)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))) :
    (a : SingularCochainInt X k) (simplexIncl S k τ) = 0 := by
  have hmem : (Finsupp.single (simplexIncl S k τ) (1 : ℤ)) ∈ subspaceChainsInt S k := by
    rw [subspaceChainsInt, LinearMap.mem_range]
    exact ⟨Finsupp.single τ 1, by rw [chainIncl_single]⟩
  have := a.2 _ hmem
  rwa [kronecker_single, one_mul] at this

/-- A **relative cocycle has zero absolute coboundary**: the relative-coboundary kernel condition
`relCoboundaryIntₗ S k a = 0` unfolds (via `relCoboundaryIntₗ_coe`) to `coboundary X k a.1 = 0`. -/
theorem relCocycleInt_coboundary_zero {k : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    coboundaryₗ X k (a : relCochainsInt S k) = 0 := by
  have h : relCoboundaryIntₗ S k a = 0 := a.2
  have h2 := Subtype.ext_iff.mp h
  rwa [relCoboundaryIntₗ_coe, ZeroMemClass.coe_zero] at h2

/-- For a relative cocycle `a` and a relative cycle `z`, `capInt a.1.1 z` is an absolute `(m+1)`-cycle. -/
theorem capInt_relCocycle_isCycleInt {k m : ℕ} (a : LinearMap.ker (relCoboundaryIntₗ S k))
    (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    capInt (m := m + 1) (a : relCochainsInt S k) z ∈ cycles X (m + 1) := by
  show chainBoundary X m (capInt (m := m + 1) (a : relCochainsInt S k) z) = 0
  exact capInt_relCycle_isCycleInt S _ (relCochainInt_vanish S a.1)
    (relCocycleInt_coboundary_zero S a) hz

/-- The underlying map `f ↦ capInt f z` on absolute `k`-cochains, restricted to the relative cocycles. -/
noncomputable def capCochainIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] SingularChainInt X (m + 1) :=
  ((capIntₗ k (m + 1)).flip z).comp
    ((relCochainsInt S k).subtype.comp (LinearMap.ker (relCoboundaryIntₗ S k)).subtype)

@[simp] theorem capCochainIntₗ_apply {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    capCochainIntₗ S z a = capInt (m := m + 1) (a : relCochainsInt S k) z := rfl

/-- The map `a ↦ a ⌢ z` landing in the absolute `(m+1)`-cycles (cod-restriction of `capCochainIntₗ`). -/
noncomputable def capRelCocycleIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] cycles X (m + 1) :=
  (capCochainIntₗ S z).codRestrict (cycles X (m + 1))
    (fun a => capInt_relCocycle_isCycleInt S a z hz)

@[simp] theorem capRelCocycleIntₗ_coe {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    (capRelCocycleIntₗ S z hz a : SingularChainInt X (m + 1))
      = capInt (m := m + 1) (a : relCochainsInt S k) z := rfl

/-- The cycle-level map `a ↦ [a ⌢ z]` on relative cocycles, `ker (relCoboundaryIntₗ S k) → Hₘ₊₁`. -/
noncomputable def relDualityIntₗ {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    LinearMap.ker (relCoboundaryIntₗ S k) →ₗ[ℤ] Homology X (m + 1) :=
  ((boundaries X (m + 1)).submoduleOf (cycles X (m + 1))).mkQ.comp (capRelCocycleIntₗ S z hz)

@[simp] theorem relDualityIntₗ_apply {k m : ℕ} (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    relDualityIntₗ S z hz a = Homology.mk X (m + 1) (capRelCocycleIntₗ S z hz a) := rfl

/-- `chainBoundary` commutes with a degree cast (integral re-indexing helper). -/
private theorem chainBoundaryInt_cast {a b : ℕ} (z : SingularChainInt X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) :
    chainBoundary X b (e ▸ z) = eb ▸ chainBoundary X a z := by
  subst eb; rw [show e = rfl from rfl]

/-- A cast of a subspace chain is a subspace chain (integral). -/
private theorem subspaceChainsInt_cast {a b : ℕ} (c : SingularChainInt X a) (eb : a = b)
    (hc : c ∈ subspaceChainsInt S a) : (eb ▸ c) ∈ subspaceChainsInt S b := by
  subst eb; exact hc

/-- **The integral relative-cohomology descent fact**: for a `j`-cochain `g` vanishing on `S` and a
relative cycle `z`, the coboundary `δg` caps `z` to an absolute `(m+1)`-**boundary**. `capInt_leibniz`
gives `∂(g ⌢ z) = (-1)ⁿ⁺¹ (δg) ⌢ z + (-1)ⁿ g ⌢ (∂z)`; the last term dies (`g` kills subspace chains,
`∂z ∈ subspaceChains`), so `(δg) ⌢ z` is `(-1)ⁿ⁺¹ · ∂(g ⌢ z)`, a boundary (unit sign). Integral mirror
of `SingularRelativeDuality.cap_relCoboundary_mem_boundaries`. -/
theorem capInt_relCoboundary_mem_boundariesInt {j m : ℕ} (g : SingularCochainInt X j)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk j))),
      g (simplexIncl S j τ) = 0)
    (z : SingularChainInt X (j + 1 + m + 1))
    (hz : chainBoundary X (j + 1 + m) z ∈ subspaceChainsInt S (j + 1 + m)) :
    capInt (m := m + 1) (coboundary X j g) z ∈ boundaries X (m + 1) := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  have hleib := capInt_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  have ed : j + 1 + m = j + (m + 1) := by omega
  have hmid : capInt (m := m + 1) g (chainBoundary X (j + (m + 1)) (e ▸ z)) = 0 := by
    apply capInt_subspaceChainInt_eq_zero S g hg
    rw [chainBoundaryInt_cast z e ed]
    exact subspaceChainsInt_cast S _ ed hz
  rw [hmid, smul_zero, add_zero] at hleib
  have hcancel : (h ▸ (e ▸ z) : SingularChainInt X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rw [hcancel] at hleib
  -- hleib : ∂(capInt g (e▸z)) = (-1)^(j+1) • (δg ⌢ z).  The RHS is `(-1)^(j+1)` times a boundary.
  have hbdry : (-1 : ℤ) ^ (j + 1) • capInt (m := m + 1) (coboundary X j g) z ∈ boundaries X (m + 1) := by
    rw [← hleib]
    exact LinearMap.mem_range_self _ _
  have hunit : ((-1 : ℤ) ^ (j + 1)) * ((-1 : ℤ) ^ (j + 1)) = 1 := by
    rw [← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by ring, pow_mul, neg_one_sq, one_pow]
  have := (boundaries X (m + 1)).smul_mem ((-1 : ℤ) ^ (j + 1)) hbdry
  rwa [smul_smul, hunit, one_smul] at this

/-- **The integral relative Poincaré–Lefschetz duality map** `D_z : Hᵏ(X, S; ℤ) → Hₘ₊₁(X; ℤ)`,
`[a] ↦ [a ⌢ z]`, for a fixed relative fundamental cycle `z` (an integral `(k+m+1)`-chain whose boundary
`∂z` is a subspace chain). Well-defined: a relative cocycle caps `z` to an absolute cycle
(`capInt_relCocycle_isCycleInt`), a relative coboundary to an absolute boundary
(`capInt_relCoboundary_mem_boundariesInt`). Integral mirror of `SingularRelativeDuality.relativeDuality`. -/
noncomputable def relativeDualityInt (k m : ℕ) (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m)) :
    RelativeCohomologyInt S k →ₗ[ℤ] Homology X (m + 1) :=
  Submodule.liftQ _ (relDualityIntₗ S z hz) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityIntₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
      capRelCocycleIntₗ_coe]
    cases k with
    | zero =>
        rw [show relCoboundaryRangeInt S 0 = (⊥ : Submodule ℤ (relCochainsInt S 0)) from rfl,
          Submodule.mem_bot] at ha
        have h0 : ((a : relCochainsInt S 0) : SingularCochainInt X 0) = 0 := by rw [ha]; rfl
        rw [h0]
        have hz0 : capInt (m := m + 1) (0 : SingularCochainInt X 0) z = (0 : SingularChainInt X (m + 1)) := by
          rw [← capIntₗ_apply, map_zero]; rfl
        rw [hz0]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show relCoboundaryRangeInt S (j + 1) = LinearMap.range (relCoboundaryIntₗ S j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        have hcob : ((a : relCochainsInt S (j + 1)) : SingularCochainInt X (j + 1)) = coboundary X j g.1 := by
          rw [← hg, relCoboundaryIntₗ_coe]
        rw [hcob]
        exact capInt_relCoboundary_mem_boundariesInt S g.1 (relCochainInt_vanish S g) z hz)

/-- **Computation rule for `D_z`** on a relative cocycle: `D_z [a] = [a ⌢ z]` (the `liftQ`
β-reduction, packaged through the cycle-level `relDualityIntₗ`). -/
@[simp] theorem relativeDualityInt_mk (k m : ℕ) (z : SingularChainInt X (k + m + 1))
    (hz : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (a : LinearMap.ker (relCoboundaryIntₗ S k)) :
    relativeDualityInt S k m z hz (RelativeCohomologyInt.mk S k a) = relDualityIntₗ S z hz a :=
  rfl

/-! ## §D. The degree-0 output duality map `D_z : Hᵏ⁺¹(X, S; ℤ) → H₀(X; ℤ)`

The load-bearing (top-degree) case caps `Hᵏ⁺¹(X, S; ℤ)` against a relative fundamental cycle
`z ∈ C_{k+1}(X)` (`∂z ∈ subspace chains`) landing in `H₀(X; ℤ)` — the case `H⁴_c(ℝ⁴) ⌢ [ℝ⁴]_loc → H₀`.
In degree `0` every chain is a cycle (`cycles X 0 = ⊤`), so cycle-membership is free; the well-definedness
input is only that a relative coboundary caps to an absolute `0`-boundary
(`capInt_relCoboundary_mem_boundariesInt` at `m = 0` gives the degree-1 case; degree-0 uses that
`a ⌢ z ∈ C₀` and the relative-coboundary case reduces to `k = j + 1`). -/

/-- **The degree-0 integral relative-cohomology descent fact**: for a `k`-cochain `g` vanishing on `S`
and a relative cycle `z : C_{k+1}`, the coboundary `δg` caps `z` to an absolute `0`-**boundary**.
`capInt_leibniz` (at output degree `0`) gives `∂(g ⌢ z) = (-1)ᵏ⁺¹ (δg) ⌢ z + (-1)ᵏ g ⌢ (∂z)`; the last
term dies (`g` kills subspace chains, `∂z ∈ subspace chains`), so `(δg) ⌢ z` is `(-1)ᵏ⁺¹ · ∂(g ⌢ z)`,
a `0`-boundary (unit sign). The degree-0 companion of `capInt_relCoboundary_mem_boundariesInt`. -/
theorem capInt_relCoboundary_mem_boundaries0Int {k : ℕ} (g : SingularCochainInt X k)
    (hg : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      g (simplexIncl S k τ) = 0)
    (z : SingularChainInt X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChainsInt S k) :
    capInt (m := 0) (coboundary X k g) z ∈ boundaries X 0 := by
  have h : k + 0 + 1 = k + 1 + 0 := by omega
  have hleib := capInt_leibniz (a := g) (c := z) (m := 0) h
  have hmid : capInt (m := 0) g (chainBoundary X (k + 0) z) = 0 :=
    capInt_subspaceChainInt_eq_zero S g hg hz
  rw [hmid, smul_zero, add_zero] at hleib
  -- hleib : ∂(capInt g z) = (-1)^(k+1) • (δg ⌢ (h ▸ z));  h ▸ z = z defeq (k+0+1 = k+1+0 both = k+1).
  have hcast : (h ▸ z : SingularChainInt X (k + 1 + 0)) = z := rfl
  rw [hcast] at hleib
  have hbdry : (-1 : ℤ) ^ (k + 1) • capInt (m := 0) (coboundary X k g) z ∈ boundaries X 0 := by
    rw [← hleib]
    exact LinearMap.mem_range_self _ _
  have hunit : ((-1 : ℤ) ^ (k + 1)) * ((-1 : ℤ) ^ (k + 1)) = 1 := by
    rw [← pow_add, show (k + 1) + (k + 1) = 2 * (k + 1) by ring, pow_mul, neg_one_sq, one_pow]
  have := (boundaries X 0).smul_mem ((-1 : ℤ) ^ (k + 1)) hbdry
  rwa [smul_smul, hunit, one_smul] at this

/-- The degree-0 cycle-level duality: `a ↦ [a ⌢ z] ∈ H₀(X)` for a relative cocycle `a : Cᵏ⁺¹(X,S)` and
a relative cycle `z : C_{k+1}` (`∂z ∈ subspace chains`); `a ⌢ z ∈ C₀` is automatically a cycle. -/
noncomputable def relDualityInt0ₗ {k : ℕ} (z : SingularChainInt X (k + 1))
    (_hz : chainBoundary X k z ∈ subspaceChainsInt S k) :
    LinearMap.ker (relCoboundaryIntₗ S (k + 1)) →ₗ[ℤ] Homology X 0 :=
  ((boundaries X 0).submoduleOf (cycles X 0)).mkQ.comp
    (((capIntₗ (k + 1) 0).flip z).comp
      ((relCochainsInt S (k + 1)).subtype.comp (LinearMap.ker (relCoboundaryIntₗ S (k + 1))).subtype)
      |>.codRestrict (cycles X 0) (fun _ => Submodule.mem_top))

@[simp] theorem relDualityInt0ₗ_apply {k : ℕ} (z : SingularChainInt X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChainsInt S k)
    (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    relDualityInt0ₗ S z hz a
      = Homology.mk X 0 ⟨capInt (m := 0) (a : relCochainsInt S (k + 1)) z, Submodule.mem_top⟩ :=
  rfl

/-- **The degree-0 integral relative Poincaré–Lefschetz duality map** `D_z : Hᵏ⁺¹(X, S; ℤ) → H₀(X; ℤ)`,
`[a] ↦ [a ⌢ z]`. Well-defined: relative coboundaries cap `z` to absolute `0`-boundaries
(`capInt_relCoboundary_mem_boundariesInt`, the `k = j + 1` branch; the `k = 0` case is empty here since
the cochain degree is `k + 1 ≥ 1`). The top-degree companion of `relativeDualityInt`. -/
noncomputable def relativeDualityInt0 (k : ℕ) (z : SingularChainInt X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChainsInt S k) :
    RelativeCohomologyInt S (k + 1) →ₗ[ℤ] Homology X 0 :=
  Submodule.liftQ _ (relDualityInt0ₗ S z hz) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker, relDualityInt0ₗ_apply]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    rw [show relCoboundaryRangeInt S (k + 1) = LinearMap.range (relCoboundaryIntₗ S k) from rfl] at ha
    obtain ⟨g, hg⟩ := ha
    have hcob : ((a : relCochainsInt S (k + 1)) : SingularCochainInt X (k + 1)) = coboundary X k g.1 := by
      rw [← hg, relCoboundaryIntₗ_coe]
    rw [hcob]
    exact capInt_relCoboundary_mem_boundaries0Int S g.1 (relCochainInt_vanish S g) z hz)

/-- **Computation rule for the degree-0 `D_z`**: `D_z [a] = [a ⌢ z] ∈ H₀`. -/
@[simp] theorem relativeDualityInt0_mk (k : ℕ) (z : SingularChainInt X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChainsInt S k)
    (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) :
    relativeDualityInt0 S k z hz (RelativeCohomologyInt.mk S (k + 1) a) = relDualityInt0ₗ S z hz a :=
  rfl

/-! ## §E. The concrete Euclidean-model target-side isomorphisms `H₀(ℝ⁴;ℤ) ≅ ℤ` + off-degree vanishing

The two target-side facts the PD base case needs: `H₀(ℝ⁴;ℤ) ≅ ℤ` (the codomain of the load-bearing
degree-0 cap `H⁴_c(ℝ⁴) ⌢ [ℝ⁴]_loc → H₀`), and the vanishing of the off-degree homology
`Hᵢ(ℝ⁴;ℤ) = 0` for `i ≥ 1` (the off-degree pieces of the local duality — both sides `0`, so the cap is
trivially iso off the top degree). `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ` is already `euclLocalHomologyIsoInt`. -/

/-- **`H₀(ℝ⁴; ℤ) ≅ ℤ`** — the codomain of the load-bearing Euclidean local cap. The integral
augmentation `ε̄ : H₀(ℝ⁴;ℤ) → ℤ` is bijective: injective because `ℝ⁴` is reduced-acyclic
(`eucl_augHInt_injective`, the straight-line contraction), surjective on any `0`-simplex
(`augHInt_surjective`). This is the target `≅ ℤ` matching `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ`
(`euclLocalHomologyIsoInt`) under the local cap-duality. -/
noncomputable def euclH0IsoInt : Homology (Eucl 4) 0 ≃ₗ[ℤ] ℤ :=
  LinearEquiv.ofBijective (augHInt (Eucl 4))
    ⟨eucl_augHInt_injective 4,
      augHInt_surjective (Eucl 4)
        (SKEFTHawking.SingularHomotopyInvariance.constSimplex
          (0 : (Eucl 4 : TopCat)) 0)⟩

@[simp] theorem euclH0IsoInt_apply (x : Homology (Eucl 4) 0) :
    euclH0IsoInt x = augHInt (Eucl 4) x := rfl

/-- **Off-degree homology vanishing `Hᵢ₊₁(ℝ⁴; ℤ) = 0`** — the off-degree pieces of the Euclidean local
duality: `ℝ⁴` is contractible, so `Hᵢ(ℝ⁴;ℤ) = 0` for `i ≥ 1` (`eucl_homology_trivialInt`). Off the top
degree both the compactly-supported cohomology and the homology vanish, so the local cap is trivially an
iso there; the only non-trivial degree is the top one (`H⁴_c ⌢ [ℝ⁴]_loc → H₀`). -/
theorem euclHomologyOffDegree_eq_zero (i : ℕ) (x : Homology (Eucl 4) (i + 1)) : x = 0 :=
  eucl_homology_trivialInt 4 i x

/-- **The Euclidean local homology `H₄(ℝ⁴, ℝ⁴∖0; ℤ) ≅ ℤ`** re-exported as the source-side generator model
of the local cap-duality (`euclLocalHomologyIsoInt`, already built). Paired with `euclH0IsoInt`
(`H₀ ≅ ℤ`), these are the two `≅ ℤ` ends the load-bearing cap `H⁴_c(ℝ⁴) ⌢ [ℝ⁴]_loc ≅ H₀(ℝ⁴)` connects. -/
noncomputable def euclLocalHomologyIsoInt' :
    RelHomologyInt (X := Eucl 4) {x | x ≠ 0} 4 ≃ₗ[ℤ] ℤ :=
  euclLocalHomologyIsoInt

/-! ## §F. The Euclidean local cap-iso packaging (the PD base case the MV five-lemma consumes)

The base-case headline: the load-bearing Euclidean local cap-duality map
`D_z : H⁴_c(ℝ⁴; ℤ) → H₀(ℝ⁴; ℤ)` (`relativeDualityInt0 {x|x≠0} 3 z hz`, `H⁴_c` computed directly as the
relative cohomology `H⁴(ℝ⁴, ℝ⁴∖0; ℤ)`) is an **isomorphism**.

The `H₀`-side end is already `≅ ℤ` (`euclH0IsoInt`) and off-degree pieces vanish (§E). The remaining
input is the **source-side** `H⁴_c(ℝ⁴; ℤ) ≅ ℤ` together with the generator match `D_z(gen) = ±gen` — this
is exactly the integral-relative-UCT fact `H⁴(ℝ⁴, ℝ⁴∖0; ℤ) ≅ Hom(H₄(ℝ⁴, ℝ⁴∖0; ℤ), ℤ) ≅ ℤ` (free, no Tor,
since `H₃ = 0`) that over `ZMod 2` the mod-2 base case gets for free from field universal coefficients
(`SingularRelativeUC`), but which over ℤ is a genuine free-UCT computation. It is disclosed here as the
concrete datum `EuclLocalCapIsoData`; from it the base-case iso is REDUCED to a `LinearEquiv` /
bijectivity — the exact form the MV five-lemma consumes. -/

/-- **The Euclidean local cap-iso datum** — the sharpened, checkable input to the PD base case.

Discloses only:
* `z`, `hz` — a relative fundamental cycle for `[ℝ⁴]_loc` (an integral `4`-chain with `∂z` a subspace
  chain of `ℝ⁴∖0`), the class the cap is taken against;
* `sourceIso` — the source-side compactly-supported cohomology iso `H⁴_c(ℝ⁴; ℤ) ≅ ℤ` (the free
  integral-relative-UCT fact `H⁴(ℝ⁴, ℝ⁴∖0) ≅ Hom(H₄, ℤ) ≅ ℤ`; the field-UC the mod-2 base case gets free);
* `genMatch` — the generator match `ε̄(D_z(sourceIso.symm 1)) = ±1`, i.e. the cap sends the `H⁴_c`
  generator to a generator of `H₀(ℝ⁴;ℤ) ≅ ℤ` (equivalently `D_z` is compatible with the two `≅ ℤ` ends).

From this datum the base-case cap `D_z` is bijective (`EuclLocalCapIsoData.capBijective`), i.e. a
`LinearEquiv` `H⁴_c(ℝ⁴;ℤ) ≃ₗ H₀(ℝ⁴;ℤ)` (`EuclLocalCapIsoData.capEquiv`). The `H₀ ≅ ℤ` end is BUILT
(`euclH0IsoInt`, §E); only the source-side iso + generator match are disclosed — the exact residual
integral-UCT input, isolated cleanly. -/
structure EuclLocalCapIsoData where
  /-- A relative fundamental cycle for `[ℝ⁴]_loc`: an integral `4`-chain whose boundary is a subspace
  chain of `ℝ⁴∖0`. -/
  z : SingularChainInt (Eucl 4) 4
  /-- `∂z` lies in the subspace chains of `ℝ⁴∖0` (so `z` represents a relative class). -/
  hz : chainBoundary (Eucl 4) 3 z ∈ subspaceChainsInt {x | x ≠ 0} 3
  /-- The source-side compactly-supported cohomology iso `H⁴_c(ℝ⁴; ℤ) ≅ ℤ` (free integral-relative-UCT). -/
  sourceIso : RelativeCohomologyInt (X := Eucl 4) {x | x ≠ 0} 4 ≃ₗ[ℤ] ℤ
  /-- The generator match: the cap sends the `H⁴_c` generator to a generator of `H₀(ℝ⁴;ℤ) ≅ ℤ`
  (`ε̄(D_z gen) = ±1`), i.e. `IsUnit` in ℤ. -/
  genMatch : IsUnit (augHInt (Eucl 4)
    (relativeDualityInt0 {x | x ≠ 0} 3 z hz (sourceIso.symm 1)))

/-- **The Euclidean local cap map, as a plain ℤ-linear map** `H⁴_c(ℝ⁴; ℤ) →ₗ H₀(ℝ⁴; ℤ)`, from a datum's
fundamental cycle. This is `relativeDualityInt0 {x|x≠0} 3 z hz` — the load-bearing degree-0 cap
`H⁴(ℝ⁴, ℝ⁴∖0; ℤ) ⌢ [ℝ⁴]_loc → H₀(ℝ⁴; ℤ)`. -/
noncomputable def EuclLocalCapIsoData.capMap (D : EuclLocalCapIsoData) :
    RelativeCohomologyInt (X := Eucl 4) {x | x ≠ 0} 4 →ₗ[ℤ] Homology (Eucl 4) 0 :=
  relativeDualityInt0 {x | x ≠ 0} 3 D.z D.hz

/-- **The base-case cap is bijective** — from the datum. The composite
`ℤ --sourceIso.symm--> H⁴_c --capMap--> H₀ --ε̄--> ℤ` sends `1 ↦ ±1` (a `ℤ`-unit, `genMatch`), so it is
a bijective ℤ-linear endomorphism of `ℤ`; since `sourceIso` and `ε̄` (`euclH0IsoInt`) are already
bijective, `capMap` is bijective. The exact base-case iso the MV five-lemma consumes, reduced to the
disclosed source-iso + generator-match datum. -/
theorem EuclLocalCapIsoData.capBijective (D : EuclLocalCapIsoData) :
    Function.Bijective D.capMap := by
  -- The endomorphism `φ = ε̄ ∘ capMap ∘ sourceIso.symm : ℤ →ₗ ℤ` sends `1 ↦ ε̄(D_z gen)`, a unit.
  set φ : ℤ →ₗ[ℤ] ℤ :=
    (euclH0IsoInt.toLinearMap.comp D.capMap).comp D.sourceIso.symm.toLinearMap with hφ
  have hφ1 : φ 1 = augHInt (Eucl 4)
      (relativeDualityInt0 {x | x ≠ 0} 3 D.z D.hz (D.sourceIso.symm 1)) := rfl
  -- `φ` is `n ↦ n * u` for the unit `u = φ 1`; multiplication by a unit is bijective on ℤ.
  obtain ⟨u, hu⟩ := hφ1 ▸ D.genMatch
  have hφ1u : φ 1 = (u : ℤ) := by rw [hφ1, hu]
  have hmulmap : ∀ n : ℤ, φ n = n * (u : ℤ) := by
    intro n
    have hn : φ n = n • φ 1 := by rw [← map_smul]; congr 1; rw [smul_eq_mul, mul_one]
    rw [hn, hφ1u, smul_eq_mul]
  have hφbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      rw [hmulmap a, hmulmap b] at hab
      exact mul_right_cancel₀ u.ne_zero hab
    · intro y
      refine ⟨y * (u⁻¹ : ℤˣ), ?_⟩
      rw [hmulmap, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  -- `φ = ε̄ ∘ capMap ∘ sourceIso.symm` bijective, with `ε̄` and `sourceIso.symm` bijective ⟹ capMap bijective.
  have hcomp : (⇑euclH0IsoInt ∘ ⇑D.capMap) ∘ ⇑D.sourceIso.symm = ⇑φ := rfl
  have h1 : Function.Bijective (⇑euclH0IsoInt ∘ ⇑D.capMap) := by
    have := hφbij
    rw [← hcomp] at this
    exact (Function.Bijective.of_comp_iff _ D.sourceIso.symm.bijective).mp this
  exact (Function.Bijective.of_comp_iff' euclH0IsoInt.bijective _).mp h1

/-- **The base-case cap as a `LinearEquiv`** `H⁴_c(ℝ⁴; ℤ) ≃ₗ H₀(ℝ⁴; ℤ)` — the Euclidean local
Poincaré-duality cap-iso the MV five-lemma consumes, built from the datum via `capBijective`. -/
noncomputable def EuclLocalCapIsoData.capEquiv (D : EuclLocalCapIsoData) :
    RelativeCohomologyInt (X := Eucl 4) {x | x ≠ 0} 4 ≃ₗ[ℤ] Homology (Eucl 4) 0 :=
  LinearEquiv.ofBijective D.capMap D.capBijective

end SKEFTHawking.SingularEuclideanCapIsoInt
