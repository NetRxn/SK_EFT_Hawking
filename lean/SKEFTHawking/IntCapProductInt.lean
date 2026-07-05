/-
# Phase 5q.H · E1 — the singular **integral** cap product `⌢ : Cᵏ × Cₖ₊ₘ → Cₘ`, its descent to
# `Hᵏ × H_{k+m+1} → H_{m+1}`, the integral cap–cup adjunction, and the reduction of `IntPoincareDuality`
# to the integral cap-iso.

Substrate-G foundation brick (Option-A from-scratch). The **integral** analogue of the mod-2 cap
tower (`SingularCapHomology.capH`, `SingularCapChainIncl.kronecker_cup_cap`,
`PoincareDualityConstruct.fundamentalFunctional_cupH24`). Built directly on the integral chains/cochains
of `SingularHomologyInt` / `SingularCohomologyInt`.

Structurally mirrors the mod-2 cap `SingularHomologyMod2.{capBasis, cap, cap_leibniz, cap_cocycle_chainMap}`
and its cohomology descent `SingularCapHomology.capH` — the SAME Alexander–Whitney front-`k`-face ∪
back-`m`-face split — but over the base ring **ℤ** with the genuine **graded signs** in the boundary. The
load-bearing difference from the mod-2 file is the *signed* cap-Leibniz rule

  `∂(a ⌢ c) = (δa) ⌢ c + (-1)ᵏ · (a ⌢ ∂c)`   (`capInt_leibniz`)

whose `(-1)ᵏ` the mod-2 file could drop (`+1 = -1` in char 2). It is what makes a cocycle `a` cap to a
CHAIN MAP (up to the unit `(-1)ᵏ`), so `a ⌢ ·` descends to a well-defined ℤ-linear map on homology, and a
COBOUNDARY cap a cycle to a boundary — the two descent facts behind `capHInt`.

The **cap–cup adjunction** `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (`kroneckerInt_cup_capInt`) is, remarkably,
**sign-free at the chain level**: neither `cup` nor `capInt` carries a sign (the sign lives only in `δ`/`∂`),
so both sides equal `a(frontₖσ) · b(backₗσ)` on a basis simplex — verbatim the mod-2 argument over ℤ.

Headlines:
* `capHInt : Cohomology X k →ₗ[ℤ] Homology X (k+m+1) →ₗ[ℤ] Homology X (m+1)` — the integral cap on
  (co)homology (the char-0 upgrade of the mod-2 `capH`);
* `interFormInt_eq_kroneckerHInt_capHInt` — the descended adjunction
  `interFormInt fc a b = ⟨b, a ⌢ [M]⟩` for `fc = intFundamentalClassOfHomology [M]` (the integral mirror
  of `fundamentalFunctional_cupH24`);
* `intPoincareDualityOfCapIso` — **`IntPoincareDuality` inhabited from the integral cap-iso** plus the
  perfect-pairing of the integral Kronecker `H₂ ≃ Dual H²`; this REDUCES the disclosed `IntPoincareDuality`
  (a `H² ≃ Dual H²` iso) to the cleaner geometric datum "the integral cap `· ⌢ [M] : H² → H₂` is an iso"
  — the exact char-0 upgrade of the on-main mod-2 injective `SingularPD4Instances.nondeg_of_closed`.

All proofs kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom. The disclosed geometric inputs are structure fields, not axioms.
-/
import Mathlib
import SKEFTHawking.SingularHomologyInt
import SKEFTHawking.IntersectionFormUnimodularInt

namespace SKEFTHawking.SingularCohomologyInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt

variable {X : TopCat}

/-! ## §0. Integral homology-class arithmetic (`rfl`-lemmas for cheap rewrites) -/

/-- `Homology.mk` is additive. A `rfl`-lemma (`Homology.mk` is `Submodule.Quotient.mk`). -/
theorem Homology.mk_add (n : ℕ) (u v : cycles X n) :
    Homology.mk X n (u + v) = Homology.mk X n u + Homology.mk X n v := rfl

/-- `Homology.mk` commutes with the ℤ-action. A `rfl`-lemma. -/
theorem Homology.mk_smul (n : ℕ) (s : ℤ) (u : cycles X n) :
    Homology.mk X n (s • u) = s • Homology.mk X n u := rfl

/-- A homology class vanishes iff its representative cycle is a boundary. -/
theorem Homology.mk_eq_zero (n : ℕ) (u : cycles X n) :
    Homology.mk X n u = 0 ↔ u ∈ (boundaries X n).submoduleOf (cycles X n) :=
  Submodule.Quotient.mk_eq_zero _

/-! ## §1. The integral cap product `⌢ : Cᵏ × Cₖ₊ₘ → Cₘ` (sign-free at the chain level) -/

/-- The integral cap product of a `k`-cochain with a *single basis* `(k+m)`-simplex `σ`:
`a ⌢ σ = a(frontₖ σ) • [backₘ σ]`. A ℤ-chain in `Cₘ`. Mirror of `SingularHomologyMod2.capBasis`, over ℤ. -/
noncomputable def capBasisInt {k m : ℕ} (a : SingularCochainInt X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) : SingularChainInt X m :=
  a (frontFace σ) • Finsupp.single (backFace σ) 1

/-- The **integral cap product** `⌢ : Cᵏ × Cₖ₊ₘ → Cₘ` (with `n = k + m`), the ℤ-linear extension of
`σ ↦ a(frontₖ σ) • [backₘ σ]` off the basis simplices (`Finsupp.linearCombination`). Connects integral
cohomology and homology — the substrate for the integral Poincaré-duality map `· ⌢ [M]`. -/
noncomputable def capInt {k m : ℕ} (a : SingularCochainInt X k) :
    SingularChainInt X (k + m) →ₗ[ℤ] SingularChainInt X m :=
  Finsupp.linearCombination ℤ (capBasisInt a)

/-- The cap product on a basis simplex: `a ⌢ [σ] = a(frontₖ σ) • [backₘ σ]`. -/
theorem capInt_single {k m : ℕ} (a : SingularCochainInt X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) :
    capInt (m := m) a (Finsupp.single σ 1) = capBasisInt a σ := by
  rw [capInt, Finsupp.linearCombination_single, one_smul]

/-- The cap product on a scaled basis simplex. -/
theorem capInt_single_smul {k m : ℕ} (a : SingularCochainInt X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m)))) (s : ℤ) :
    capInt (m := m) a (Finsupp.single σ s) = s • capBasisInt a σ := by
  rw [capInt, Finsupp.linearCombination_single]

/-- The cap product is ℤ-linear in the cochain argument (additivity). -/
theorem capInt_add_cochain {k m : ℕ} (a b : SingularCochainInt X k)
    (c : SingularChainInt X (k + m)) : capInt (m := m) (a + b) c = capInt a c + capInt b c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd]; abel
  | single σ s =>
      rw [capInt_single_smul, capInt_single_smul, capInt_single_smul, ← smul_add]
      congr 1
      simp only [capBasisInt, Pi.add_apply, add_smul]

/-- The cap product is ℤ-linear in the cochain argument (homogeneity). -/
theorem capInt_smul_cochain {k m : ℕ} (s : ℤ) (a : SingularCochainInt X k)
    (c : SingularChainInt X (k + m)) : capInt (m := m) (s • a) c = s • capInt a c := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd => rw [map_add, map_add, hc, hd, smul_add]
  | single σ t =>
      rw [capInt_single_smul, capInt_single_smul, smul_comm]
      congr 1
      simp only [capBasisInt, Pi.smul_apply, smul_eq_mul, mul_smul]

/-- The **integral cap product packaged as a ℤ-bilinear map** `Cᵏ →ₗ (Cₖ₊ₘ →ₗ Cₘ)`. -/
noncomputable def capIntₗ (k m : ℕ) :
    SingularCochainInt X k →ₗ[ℤ] SingularChainInt X (k + m) →ₗ[ℤ] SingularChainInt X m where
  toFun := capInt
  map_add' a b := LinearMap.ext fun c => by rw [LinearMap.add_apply]; exact capInt_add_cochain a b c
  map_smul' s a := LinearMap.ext fun c => by
    rw [LinearMap.smul_apply, RingHom.id_apply]; exact capInt_smul_cochain s a c

@[simp] theorem capIntₗ_apply {k m : ℕ} (a : SingularCochainInt X k)
    (c : SingularChainInt X (k + m)) : capIntₗ k m a c = capInt a c := rfl

/-! ## §2. The cap–cup adjunction `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (chain level, sign-free) -/

/-- **Integral cap–cup adjunction** `⟨a ∪ b, c⟩ = ⟨b, a ⌢ c⟩` (chain level): the integral Kronecker
pairing of a cup product against a chain equals the pairing of the right factor against the cap product.
Both sides use the SAME Alexander–Whitney front/back split, so on a basis simplex both equal
`a(frontₖσ) · b(backₗσ)`. Sign-free (`cup`/`capInt` carry no sign; the sign lives only in `δ`/`∂`) — the
verbatim integral mirror of the mod-2 `SingularCapChainIncl.kronecker_cup_cap`. -/
theorem kroneckerInt_cup_capInt {k l : ℕ} (a : SingularCochainInt X k) (b : SingularCochainInt X l)
    (c : SingularChainInt X (k + l)) :
    kronecker (cup a b) c = kronecker b (capInt a c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [map_zero]
  | add c d hc hd => rw [kronecker_add_right, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [capInt_single_smul, capBasisInt, kronecker_single, kronecker_smul_right,
        kronecker_smul_right, kronecker_single, cup_apply]
      simp only [smul_eq_mul]; ring

/-! ## §3. The signed cap-Leibniz rule `∂(a ⌢ c) = (-1)ᵏ⁺¹ · (δa ⌢ c) + (-1)ᵏ · (a ⌢ ∂c)` -/

/-- **Signed cap Leibniz on a basis simplex** (over ℤ):
`∂(a ⌢ σ) = (-1)ᵏ⁺¹ · (δa ⌢ σ) + (-1)ᵏ · (a ⌢ ∂σ)`, cast-free at a basis `(k+m+1)`-simplex `σ`.
The homological analogue of the signed cup Leibniz `coboundary_cup`. The two front-face sums (from
`δa`'s faces and `∂σ`'s `i ≤ k` faces) carry the SAME `(-1)ⁱ`; the overall `(-1)ᵏ⁺¹` / `(-1)ᵏ` signs
(opposite by a factor `-1`) are exactly what makes them CANCEL over ℤ — where the mod-2 file used
`+1 = -1`. Solving the three coefficient constraints (front-sum cancellation, back diagonal, back sum)
pins these signs uniquely. -/
theorem capInt_leibniz_single {k m : ℕ} (a : SingularCochainInt X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) :
    chainBoundary X m (capInt (m := m + 1) a (Finsupp.single σ 1))
      = (-1 : ℤ) ^ (k + 1) • (coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) 1)
        + (-1 : ℤ) ^ k • capInt (m := m) a (boundaryBasis X (k + m) σ) := by
  have hL : chainBoundary X m (capInt (m := m + 1) a (Finsupp.single σ 1))
      = a (frontSmall σ) • Finsupp.single (backBig σ) 1
        + a (frontSmall σ) • ∑ l : Fin (m + 1),
            ((-1 : ℤ) ^ (l.succ : ℕ)) • Finsupp.single (face l.succ (backSmall σ)) (1 : ℤ) := by
    rw [capInt_single, capBasisInt, map_smul, chainBoundary_single]
    show a (frontSmall σ) • boundaryBasis X m (backSmall σ) = _
    rw [boundaryBasis, Fin.sum_univ_succ, face_zero_backSmall, smul_add]
    simp only [Fin.val_zero, pow_zero, one_smul]
  have h : k + 1 + (m + 1) = k + m + 2 := by omega
  have hcap : capInt (m := m) a (boundaryBasis X (k + m) σ)
      = (∑ j : Fin (k + 1), ((-1 : ℤ) ^ (j.castSucc : ℕ)) •
            (a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ℤ)))
        + (∑ l : Fin (m + 1), ((-1 : ℤ) ^ (k + (l.succ : ℕ))) •
            (a (frontSmall σ) • Finsupp.single (face l.succ (backSmall σ)) (1 : ℤ))) := by
    have hsum : capInt (m := m) a (boundaryBasis X (k + m) σ)
        = ∑ i : Fin (k + m + 2), ((-1 : ℤ) ^ (i : ℕ)) • capBasisInt a (face i σ) := by
      rw [boundaryBasis, map_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [map_smul, capInt_single])
    rw [hsum, ← Equiv.sum_comp (finCongr h)
        (fun i => ((-1 : ℤ) ^ (i : ℕ)) • capBasisInt a (face i σ)), Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      have hle : (finCongr h (Fin.castAdd (m + 1) j)).val ≤ k := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd]; omega
      rw [capBasisInt, frontFace_face_of_le σ _ hle, backFace_face_of_le σ _ hle]
      have hidx : (⟨(finCongr h (Fin.castAdd (m + 1) j)).val, by omega⟩ : Fin (k + 2))
          = j.castSucc := by apply Fin.ext; simp [Fin.val_castSucc]
      rw [hidx]
      congr 2
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      have hgt : k < (finCongr h (Fin.natAdd (k + 1) l)).val := by
        simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [capBasisInt, frontFace_face_of_gt σ _ hgt, backFace_face_of_gt σ _ hgt]
      have hidx : (⟨(finCongr h (Fin.natAdd (k + 1) l)).val - k, by have := l.isLt; omega⟩ :
          Fin (m + 2)) = l.succ := by
        apply Fin.ext; simp only [Fin.val_succ, finCongr_apply, Fin.val_cast, Fin.val_natAdd]; omega
      rw [hidx]; congr 2
      simp only [finCongr_apply, Fin.val_cast, Fin.val_natAdd, Fin.val_succ]; omega
  have hcobound : coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) (1 : ℤ)
      = (∑ j : Fin (k + 1), ((-1 : ℤ) ^ (j.castSucc : ℕ)) •
            (a (face j.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ℤ)))
        + ((-1 : ℤ) ^ (k + 1)) • (a (frontSmall σ) • Finsupp.single (backBig σ) (1 : ℤ)) := by
    rw [coboundary_apply, Fin.sum_univ_castSucc, face_last_frontBig, add_smul, Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_); rw [smul_smul, mul_smul]
    · simp only [Fin.val_last]; rw [mul_smul]
  -- Assemble: the two front-face sums (from `δa` and the `i ≤ k` faces of `∂σ`) cancel over ℤ
  -- via the opposite signs `(-1)ᵏ⁺¹` / `(-1)ᵏ`; the back diagonal and back sum then match.
  rw [hL, hcap, hcobound]
  rw [smul_add, smul_add, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum]
  rw [show (∑ x : Fin (k + 1), (-1 : ℤ) ^ (k + 1) •
        ((-1 : ℤ) ^ (x.castSucc : ℕ) •
          (a (face x.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ℤ))))
      = - ∑ x : Fin (k + 1), (-1 : ℤ) ^ k •
          ((-1 : ℤ) ^ (x.castSucc : ℕ) •
            (a (face x.castSucc (frontBig σ)) • Finsupp.single (backBig σ) (1 : ℤ))) from by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← neg_smul]; congr 1; rw [pow_succ]; ring]
  abel_nf
  congr 1
  · rw [show (-1 • (1 : ℤ)) = -1 from by norm_num, smul_smul, ← pow_add]; norm_num
  · rw [show (-1 • (1 : ℤ)) = -1 from by norm_num, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [smul_comm (a (frontSmall σ)), smul_smul, smul_smul, ← pow_add,
      show k + (k + (x.succ : ℕ)) = 2 * k + (x.succ : ℕ) by ring, pow_add, pow_mul]
    norm_num

/-- **A cocycle caps to a chain map up to the unit sign `(-1)ᵏ`** (over ℤ): if `a` is a cocycle
(`δa = 0`) then `∂(a ⌢ c) = (-1)ᵏ · (a ⌢ ∂c)` for every `(k+m+1)`-chain `c`. From `capInt_leibniz_single`,
the `δa ⌢ c` term drops (`δa = 0`). Since `(-1)ᵏ` is a unit, `a ⌢ ·` still sends cycles to cycles and
boundaries to boundaries — the descent fact making `a ⌢ ·` well-defined on homology for a cocycle `a`.
Cast-free (proved by `Finsupp.induction_linear` reducing to `capInt_leibniz_single`). -/
theorem capInt_cocycle_chainMap {k m : ℕ} (a : SingularCochainInt X k)
    (ha : coboundaryₗ X k a = 0) (c : SingularChainInt X (k + m + 1)) :
    chainBoundary X m (capInt (m := m + 1) a c)
      = (-1 : ℤ) ^ k • capInt (m := m) a (chainBoundary X (k + m) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, map_add, map_add, hc, hd, map_add, smul_add]
  | single σ s =>
      rw [capInt_single_smul, map_smul, chainBoundary_single_smul, map_smul,
        show chainBoundary X m (capBasisInt a σ)
          = chainBoundary X m (capInt (m := m + 1) a (Finsupp.single σ 1)) by rw [capInt_single],
        capInt_leibniz_single]
      have hδ : coboundary X k a (frontBig σ) = 0 := congrFun ha (frontBig σ)
      rw [hδ, zero_smul, smul_zero, zero_add, smul_comm]

/-! ## §4. Degree-cast helpers and the general cast-carrying cap-Leibniz `capInt_leibniz` -/

/-- A degree cast of a singular simplex is the functorial image of the `eqToHom` of the degree equality.
The bridge letting the cap-Leibniz middle term `(δa) ⌢ c` be evaluated cast-free (integral mirror of
`SingularHomologyMod2.singularSimplex_cast_eq`). -/
theorem singularSimplex_cast_eqInt {d n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk d))) (h : d = n) :
    (h ▸ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)))
      = (TopCat.toSSet.obj X).map (eqToHom (by rw [h])).op σ := by
  subst h; simp

/-- Under the cast `k+m+1 → (k+1)+m`, the split-`(k+1, m)` front face of `σ` is the split-`(k, m)`
`frontBig σ`. Integral mirror of `SingularHomologyMod2.frontFace_cast`. -/
theorem frontFace_castInt {k m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (h : k + m + 1 = k + 1 + m) :
    (frontFace (h ▸ σ) : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + 1)))) = frontBig σ := by
  unfold frontFace frontBig
  rw [singularSimplex_cast_eqInt σ h, ← FunctorToTypes.map_comp_apply, ← op_comp]
  have hmor : (frontIncl (k + 1) m
      ≫ eqToHom (show SimplexCategory.mk (k + 1 + m) = SimplexCategory.mk (k + m + 1) by rw [h]))
      = frontBigIncl k m := by
    apply SimplexCategory.Hom.ext; ext x : 2; apply Fin.ext
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, frontIncl,
      frontBigIncl, toOrderHom_mkHom, OrderHom.coe_mk, Fin.val_castLE]
    rw [SimplexCategory.eqToHom_toOrderHom]
    simp only [OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_castLE]
  rw [hmor]

/-- Under the cast `k+m+1 → (k+1)+m`, the split-`(k+1, m)` back face of `σ` is the split-`(k, m)`
`backBig σ`. Integral mirror of `SingularHomologyMod2.backFace_cast`. -/
theorem backFace_castInt {k m : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (h : k + m + 1 = k + 1 + m) :
    (backFace (h ▸ σ) : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk m))) = backBig σ := by
  unfold backFace backBig
  rw [singularSimplex_cast_eqInt σ h, ← FunctorToTypes.map_comp_apply, ← op_comp]
  have hmor : (backIncl (k + 1) m
      ≫ eqToHom (show SimplexCategory.mk (k + 1 + m) = SimplexCategory.mk (k + m + 1) by rw [h]))
      = backBigIncl k m := by
    apply SimplexCategory.Hom.ext; ext x : 2; apply Fin.ext
    simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, backIncl,
      backBigIncl, toOrderHom_mkHom, OrderHom.coe_mk]
    rw [SimplexCategory.eqToHom_toOrderHom]
    simp only [OrderEmbedding.toOrderHom_coe, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk, Fin.val_cast, Fin.val_natAdd]
  rw [hmor]

/-- A degree cast of a `Finsupp.single` of a simplex is the `single` of the cast simplex. -/
theorem singularChainInt_single_cast {d n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk d))) (s : ℤ) (h : d = n) :
    (h ▸ Finsupp.single σ s : SingularChainInt X n)
      = Finsupp.single (h ▸ σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) s := by
  subst h; rfl

/-- The middle term `(δa) ⌢ σ` of the cap-Leibniz rule, evaluated at the cast basis simplex `h ▸ σ`
(at the `capInt (δa)` degree `(k+1)+m`), recovers the cast-free `(δa)(frontBig σ) • [backBig σ]`. -/
theorem capInt_coboundary_single_cast {k m : ℕ} (a : SingularCochainInt X k)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + m + 1)))) (s : ℤ)
    (h : k + m + 1 = k + 1 + m) :
    capInt (m := m) (coboundary X k a) (h ▸ Finsupp.single σ s)
      = s • (coboundary X k a (frontBig σ) • Finsupp.single (backBig σ) (1 : ℤ)) := by
  rw [singularChainInt_single_cast σ s h, capInt_single_smul, capBasisInt, frontFace_castInt σ h,
    backFace_castInt σ h]

/-- A degree cast of singular ℤ-chains is additive. -/
theorem singularChainInt_cast_add {d n : ℕ} (c d' : SingularChainInt X d) (h : d = n) :
    (h ▸ (c + d') : SingularChainInt X n) = (h ▸ c) + (h ▸ d') := by
  subst h; rfl

/-- A degree cast sends the zero chain to the zero chain. -/
theorem singularChainInt_cast_zero {d n : ℕ} (h : d = n) :
    (h ▸ (0 : SingularChainInt X d) : SingularChainInt X n) = 0 := by
  subst h; rfl

/-- **The general signed cap-Leibniz rule** (over ℤ):
`∂(a ⌢ c) = (-1)ᵏ⁺¹ · ((δa) ⌢ c) + (-1)ᵏ · (a ⌢ ∂c)` for a `k`-cochain `a` and an arbitrary
`(k+m+1)`-chain `c`. The middle term `(δa) ⌢ c` caps the `(k+1)`-coboundary `δa` against `c` re-indexed
to degree `(k+1)+m` (propositionally `= k+m+1`; the `cast` is the homological counterpart of the degree
shift). Proved by `Finsupp.induction_linear` reducing to `capInt_leibniz_single`, with the cast
discharged by `capInt_coboundary_single_cast`. The integral mirror of `SingularHomologyMod2.cap_leibniz`. -/
theorem capInt_leibniz {k m : ℕ} (a : SingularCochainInt X k)
    (c : SingularChainInt X (k + m + 1)) (h : k + m + 1 = k + 1 + m) :
    chainBoundary X m (capInt (m := m + 1) a c)
      = (-1 : ℤ) ^ (k + 1) • capInt (m := m) (coboundary X k a) (h ▸ c)
        + (-1 : ℤ) ^ k • capInt (m := m) a (chainBoundary X (k + m) c) := by
  induction c using Finsupp.induction_linear with
  | zero => rw [singularChainInt_cast_zero h]; simp
  | add c d hc hd =>
      rw [map_add, map_add, map_add, hc, hd, singularChainInt_cast_add c d h, map_add, map_add,
        smul_add, smul_add, add_add_add_comm]
  | single σ s =>
      rw [capInt_single_smul, map_smul, chainBoundary_single_smul, map_smul,
        show chainBoundary X m (capBasisInt a σ)
          = chainBoundary X m (capInt (m := m + 1) a (Finsupp.single σ 1)) by rw [capInt_single],
        capInt_leibniz_single, smul_add, capInt_coboundary_single_cast a σ s h]
      rw [smul_smul, mul_smul, smul_comm s ((-1 : ℤ) ^ (k + 1)), smul_comm s ((-1 : ℤ) ^ k)]

/-! ## §5. The integral cap on (co)homology `capHInt : Hᵏ × H_{k+m+1} → H_{m+1}` -/

/-- For a fixed `k`-**cocycle** `a` (`δa = 0`), `capInt a` restricted to the `(k+m+1)`-cycles lands in
the `(m+1)`-cycles: `∂(a ⌢ z) = (-1)ᵏ · (a ⌢ ∂z) = (-1)ᵏ · (a ⌢ 0) = 0` (`capInt_cocycle_chainMap`).
Packaged as a ℤ-linear map `Z_{k+m+1} → Z_{m+1}` (descent fact 1i). Integral mirror of
`SingularCapHomology.capCyclesₗ`. -/
noncomputable def capCyclesIntₗ {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) :
    cycles X (k + m + 1) →ₗ[ℤ] cycles X (m + 1) :=
  LinearMap.restrict (capInt (m := m + 1) a.1) (p := cycles X (k + m + 1)) (q := cycles X (m + 1))
    fun z hz => by
      show chainBoundary X m (capInt a.1 z) = 0
      have hz' : chainBoundary X (k + m) z = 0 := hz
      rw [capInt_cocycle_chainMap a.1 (LinearMap.mem_ker.mp a.2) z, hz', map_zero, smul_zero]

@[simp] theorem capCyclesIntₗ_coe {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (z : cycles X (k + m + 1)) :
    (capCyclesIntₗ (m := m) a z : SingularChainInt X (m + 1))
      = capInt a.1 (z : SingularChainInt X (k + m + 1)) :=
  LinearMap.restrict_coe_apply _ _ _

/-- For a fixed `k`-cocycle `a`, `capInt a` descends to a ℤ-linear map on homology
`H_{k+m+1} → H_{m+1}`: it sends boundaries to boundaries, since `a ⌢ ∂w = (-1)ᵏ · ∂(a ⌢ w)` is a boundary
(`(-1)ᵏ` a unit; `capInt_cocycle_chainMap`). The homology-argument descent for a fixed cocycle. Integral
mirror of `SingularCapHomology.capHomology`. -/
noncomputable def capHomologyInt {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k)) :
    Homology X (k + m + 1) →ₗ[ℤ] Homology X (m + 1) :=
  Submodule.mapQ _ _ (capCyclesIntₗ a) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hzb
    obtain ⟨w, hw⟩ := hzb
    refine ⟨(-1 : ℤ) ^ k • capInt (m := m + 2) a.1 w, ?_⟩
    show chainBoundary X (m + 1) ((-1 : ℤ) ^ k • capInt a.1 w) = capInt a.1 z
    rw [map_smul, capInt_cocycle_chainMap (m := m + 1) a.1 (LinearMap.mem_ker.mp a.2) w, smul_smul,
      ← pow_add, show k + k = 2 * k by ring, pow_mul]
    simp only [neg_one_sq, one_pow, one_smul]
    exact congrArg (capInt a.1) hw)

@[simp] theorem capHomologyInt_mk {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (z : cycles X (k + m + 1)) :
    capHomologyInt (m := m) a (Homology.mk X (k + m + 1) z)
      = Homology.mk X (m + 1) (capCyclesIntₗ a z) :=
  Submodule.mapQ_apply _ _ _ _

/-- `capCyclesIntₗ` is additive in the cochain (at the cycle level). -/
theorem capCyclesIntₗ_add {k m : ℕ} (a a' : LinearMap.ker (coboundaryₗ X k)) (z : cycles X (k + m + 1)) :
    capCyclesIntₗ (m := m) (a + a') z = capCyclesIntₗ a z + capCyclesIntₗ a' z := by
  apply Subtype.ext
  simp only [capCyclesIntₗ_coe, Submodule.coe_add]
  exact capInt_add_cochain (k := k) (m := m + 1) a.1 a'.1 z.1

/-- `capCyclesIntₗ` commutes with the ℤ-action in the cochain (at the cycle level). -/
theorem capCyclesIntₗ_smul {k m : ℕ} (s : ℤ) (a : LinearMap.ker (coboundaryₗ X k))
    (z : cycles X (k + m + 1)) :
    capCyclesIntₗ (m := m) (s • a) z = s • capCyclesIntₗ a z := by
  apply Subtype.ext
  simp only [capCyclesIntₗ_coe, SetLike.val_smul]
  exact capInt_smul_cochain (k := k) (m := m + 1) s a.1 z.1

/-- `capHomologyInt` is additive in the cochain. -/
theorem capHomologyInt_add {k m : ℕ} (a a' : LinearMap.ker (coboundaryₗ X k)) :
    capHomologyInt (m := m) (a + a') = capHomologyInt a + capHomologyInt a' := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capHomologyInt (a + a') (Homology.mk X (k + m + 1) z)
    = capHomologyInt a (Homology.mk X (k + m + 1) z) + capHomologyInt a' (Homology.mk X (k + m + 1) z)
  rw [capHomologyInt_mk, capHomologyInt_mk, capHomologyInt_mk, ← Homology.mk_add, capCyclesIntₗ_add]

/-- `capHomologyInt` commutes with the ℤ-action in the cochain. -/
theorem capHomologyInt_smul {k m : ℕ} (s : ℤ) (a : LinearMap.ker (coboundaryₗ X k)) :
    capHomologyInt (m := m) (s • a) = s • capHomologyInt a := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show capHomologyInt (s • a) (Homology.mk X (k + m + 1) z)
    = s • capHomologyInt a (Homology.mk X (k + m + 1) z)
  rw [capHomologyInt_mk, capHomologyInt_mk, ← Homology.mk_smul, capCyclesIntₗ_smul]

/-- The map `a ↦ capHomologyInt a`, packaged as ℤ-linear in the cochain (before descending the
cohomology quotient). -/
noncomputable def capHomologyIntₗ {k m : ℕ} :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ℤ]
      (Homology X (k + m + 1) →ₗ[ℤ] Homology X (m + 1)) where
  toFun := capHomologyInt
  map_add' := capHomologyInt_add
  map_smul' := capHomologyInt_smul

/-- The cap of the zero `0`-cochain: `(0 : C⁰) ⌢ z = 0`. -/
theorem capInt_zero_cochain {m : ℕ} (z : SingularChainInt X (0 + (m + 1))) :
    capInt (0 : SingularCochainInt X 0) z = (0 : SingularChainInt X (m + 1)) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => rw [map_add, hc, hd, add_zero]
  | single σ s => rw [capInt_single_smul]; simp [capBasisInt]

/-- `chainBoundary` commutes with a degree cast on the chain: a cast cycle is a cycle. (Generic
re-indexing helper, proved by `subst`.) Integral mirror of the mod-2 `chainBoundary_cast_eq_zero`. -/
private theorem chainBoundaryInt_cast_eq_zero {a b : ℕ} (z : SingularChainInt X (a + 1))
    (e : a + 1 = b + 1) (eb : a = b) (hz : chainBoundary X a z = 0) :
    chainBoundary X b (e ▸ z) = 0 := by
  subst eb
  rw [show e = rfl from rfl]
  simpa using hz

/-- **The cohomology-argument descent fact** (coboundary in degree `j+1`): for a `j`-cochain `g`, its
coboundary `δg` caps a `(j+1+m+1)`-**cycle** `z` (`∂z = 0`) to a `(m+1)`-**boundary**. `capInt_leibniz`
gives `∂(g ⌢ z) = (-1)ʲ⁺¹ (δg ⌢ z) + (-1)ʲ (g ⌢ ∂z)`; the last term dies (`∂z = 0`), so
`δg ⌢ z = (-1)ʲ⁺¹ ∂(g ⌢ z)` is a boundary (`(-1)ʲ⁺¹` a unit). This makes `capHInt` well-defined modulo
coboundaries. Integral mirror of `SingularCapHomology.cap_coboundary_cycle_mem_boundaries`. -/
theorem capInt_coboundary_cycle_mem_boundaries {j m : ℕ} (g : SingularCochainInt X j)
    (z : SingularChainInt X (j + 1 + m + 1)) (hz : chainBoundary X (j + 1 + m) z = 0) :
    capInt (m := m + 1) (coboundary X j g) z ∈ boundaries X (m + 1) := by
  have e : j + 1 + m + 1 = j + (m + 1) + 1 := by omega
  have h : j + (m + 1) + 1 = j + 1 + (m + 1) := by omega
  have hz' : chainBoundary X (j + (m + 1)) (e ▸ z) = 0 :=
    chainBoundaryInt_cast_eq_zero z e (by omega) hz
  refine ⟨(-1 : ℤ) ^ (j + 1) • capInt (m := m + 2) g (e ▸ z), ?_⟩
  have hleib := capInt_leibniz (a := g) (c := e ▸ z) (m := m + 1) h
  rw [hz', map_zero, smul_zero, add_zero] at hleib
  have hcancel : (h ▸ (e ▸ z) : SingularChainInt X (j + 1 + (m + 1))) = z := by
    rw [eqRec_eq_cast, eqRec_eq_cast, cast_cast, cast_eq]
  rw [hcancel] at hleib
  rw [map_smul, hleib, smul_smul, ← pow_add, show (j + 1) + (j + 1) = 2 * (j + 1) by ring, pow_mul]
  simp only [neg_one_sq, one_pow, one_smul]

/-- **The integral cap product on (co)homology** `⌢ : Hᵏ × H_{k+m+1} → H_{m+1}` — a genuine ℤ-bilinear
map (the char-0 upgrade of the mod-2 `SingularCapHomology.capH`; the homological analogue of
`kroneckerHInt` / `cupH24`). Well-defined: a cocycle caps a cycle to a cycle and a boundary to a boundary
(`capInt_cocycle_chainMap`, descending the homology quotient via `capHomologyInt`), and a *coboundary*
caps a cycle to a boundary (`capInt_coboundary_cycle_mem_boundaries`, descending the cohomology quotient).
The substrate for the integral Poincaré-duality map `· ⌢ [M]`. -/
noncomputable def capHInt (k m : ℕ) :
    Cohomology X k →ₗ[ℤ]
      Homology X (k + m + 1) →ₗ[ℤ] Homology X (m + 1) :=
  Submodule.liftQ _ capHomologyIntₗ (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.zero_apply]
    show capHomologyInt a (Homology.mk X (k + m + 1) z) = 0
    rw [capHomologyInt_mk, Homology.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, capCyclesIntₗ_coe]
    have hzc : chainBoundary X (k + m) z.1 = 0 :=
      LinearMap.mem_ker.mp (z.2 : z.1 ∈ LinearMap.ker (chainBoundary X (k + m)))
    cases k with
    | zero =>
        rw [show coboundaryRange X 0 = (⊥ : Submodule ℤ (SingularCochainInt X 0)) from rfl,
          Submodule.mem_bot] at ha
        rw [show (a.1 : SingularCochainInt X 0) = 0 from ha, capInt_zero_cochain]
        exact Submodule.zero_mem _
    | succ j =>
        rw [show coboundaryRange X (j + 1) = LinearMap.range (coboundaryₗ X j) from rfl] at ha
        obtain ⟨g, hg⟩ := ha
        rw [← hg]
        exact capInt_coboundary_cycle_mem_boundaries g z.1 hzc)

@[simp] theorem capHInt_mk_mk {k m : ℕ} (a : LinearMap.ker (coboundaryₗ X k))
    (z : cycles X (k + m + 1)) :
    capHInt k m (Cohomology.mk X k a) (Homology.mk X (k + m + 1) z)
      = Homology.mk X (m + 1) (capCyclesIntₗ a z) :=
  rfl

/-! ## §6. The descended integral cap–cup adjunction with the fundamental class `[M]` -/

open SKEFTHawking.SingularHomologyInt

/-- **`cupH24` on representatives** `[fa] ∪ [gc] = [fa ⌣ gc]` (over ℤ). -/
theorem cupH24_mk_mk_repr {fc gc : LinearMap.ker (coboundaryₗ X 2)} :
    cupH24 (Submodule.Quotient.mk fc) (Submodule.Quotient.mk gc)
      = Submodule.Quotient.mk (⟨cup fc.1 gc.1, cup_cocycle fc.1 gc.1
          (LinearMap.mem_ker.mp fc.2) (LinearMap.mem_ker.mp gc.2)⟩ :
          LinearMap.ker (coboundaryₗ X 4)) :=
  cupH24_mk_mk fc gc

/-- **The descended integral cap–cup adjunction with `[M]`** (`k = m = 2`, 4-manifold):
`⟨a ∪ b, [M]⟩ = ⟨b, a ⌢ [M]⟩` at the level of integral (co)homology classes. The cohomology-level form
of the chain adjunction `kroneckerInt_cup_capInt` evaluated against the integral fundamental class
`[M] : Homology X 4`. The bridge from the integral cup pairing `(a,b) ↦ ⟨a∪b, [M]⟩` to the duality map
`a ⌢ [M]`. Integral mirror of `PoincareDualityConstruct.fundamentalFunctional_cupH24`. -/
theorem kroneckerHInt_cupH24 (zM : Homology X 4) (a b : Cohomology X 2) :
    kroneckerHInt 4 (cupH24 a b) zM
      = kroneckerHInt 2 b (capHInt 2 1 a zM) := by
  obtain ⟨fa, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨fb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ zM
  rw [cupH24_mk_mk_repr]
  show kroneckerHInt 4 (Submodule.Quotient.mk _) (Submodule.Quotient.mk zc)
    = kroneckerHInt 2 (Submodule.Quotient.mk fb) (capHInt 2 1 (Submodule.Quotient.mk fa)
        (Submodule.Quotient.mk zc))
  rw [kroneckerHInt_mk_mk]
  show kronecker (cup fa.1 fb.1) zc.1
    = kroneckerHInt 2 (Submodule.Quotient.mk fb) (Homology.mk X 2 (capCyclesIntₗ fa zc))
  rw [Homology.mk, kroneckerHInt_mk_mk, capCyclesIntₗ_coe]
  exact kroneckerInt_cup_capInt fa.1 fb.1 zc.1

/-- **The intersection form as `⟨b, a ⌢ [M]⟩`** — `interFormInt (intFundamentalClassOfHomology [M]) a b
= ⟨b, a ⌢ [M]⟩`, the descended adjunction packaged for the intersection form built from an actual
fundamental class `[M] : Homology X 4`. Combines `interFormInt_apply`, the eval-bridge
`intFundamentalClassOfHomology_eval`, and `kroneckerHInt_cupH24`. This connects the disclosed
`IntPoincareDuality` form-view to the geometric cap-with-`[M]` map. -/
theorem interFormInt_eq_kroneckerHInt_capHInt (zM : Homology X 4) (a b : Cohomology X 2) :
    interFormInt (intFundamentalClassOfHomology zM) a b
      = kroneckerHInt 2 b (capHInt 2 1 a zM) := by
  rw [interFormInt_apply, intFundamentalClassOfHomology_eval, kroneckerHInt_cupH24]

/-! ## §7. Reducing `IntPoincareDuality` to the integral cap-iso -/

/-- **The integral Poincaré-duality datum as the integral cap-iso** — the cleaner geometric datum that
`IntPoincareDuality` reduces to (a disclosed datum, NOT an axiom).

Carries the two geometric facts a closed oriented 4-manifold's integral Poincaré duality decomposes into,
each an *isomorphism*:

* `capEquiv` — the integral **cap map** `· ⌢ [M] : H²(M;ℤ) ≃ₗ[ℤ] H₂(M;ℤ)` is an isomorphism (with
  `capEquiv_apply` fixing its underlying map to be `capHInt 2 1 · [M]`). This is the exact **char-0
  upgrade** of the on-main mod-2 injective non-degeneracy `SingularPD4Instances.nondeg_of_closed` — where
  mod-2 has injectivity of `· ⌢ [M]` over `ZMod 2`, the integral statement is the full iso.

* `kronEquiv` — the integral **Kronecker pairing** `H₂(M;ℤ) ≃ₗ[ℤ] Dual ℤ (H²(M;ℤ))` is a perfect pairing
  (with `kronEquiv_apply` fixing it to `⟨b, ·⟩ = kroneckerHInt 2 b ·`). Over a field this is universal
  coefficients (`homology_eq_zero_of_kroneckerH` is its mod-2 shadow); over ℤ (with free finitely-generated
  (co)homology) it is the free-part perfect pairing.

The COMPOSITE `H² --capEquiv--> H₂ --kronEquiv--> Dual H²` is exactly `interFormInt`-curried, so it inhabits
`IntPoincareDuality (intFundamentalClassOfHomology [M])` (`intPoincareDualityOfCapIso`). This turns the
disclosed `IntPoincareDuality` (a `H² ≃ Dual H²` iso) into the cleaner geometric statement "the integral cap
`· ⌢ [M]` is an iso" — the community-scale integral-PD core, cleanly isolated. -/
structure IntCapIso (zM : Homology X 4) where
  /-- The integral cap map `· ⌢ [M] : H²(M;ℤ) → H₂(M;ℤ)` as an isomorphism. -/
  capEquiv : Cohomology X 2 ≃ₗ[ℤ] Homology X 2
  /-- The cap equivalence's underlying map is `capHInt 2 1 · [M]`. -/
  capEquiv_apply : ∀ a : Cohomology X 2, capEquiv a = capHInt 2 1 a zM
  /-- The integral Kronecker pairing `H₂(M;ℤ) → Dual ℤ (H²(M;ℤ))` as a perfect-pairing isomorphism. -/
  kronEquiv : Homology X 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology X 2)
  /-- The Kronecker equivalence is `h ↦ ⟨·, h⟩ = kroneckerHInt 2 · h`. -/
  kronEquiv_apply : ∀ (h : Homology X 2) (b : Cohomology X 2), kronEquiv h b = kroneckerHInt 2 b h

/-- **`IntPoincareDuality` from the integral cap-iso.** Given the cleaner geometric datum `IntCapIso [M]`
(the integral cap `· ⌢ [M]` is an iso + the integral Kronecker `H₂ ≃ Dual H²` is a perfect pairing), the
disclosed `IntPoincareDuality (intFundamentalClassOfHomology [M])` is inhabited: its perfect-pairing iso is
the composite `capEquiv.trans kronEquiv`, whose underlying map is `interFormInt`-curried by the descended
adjunction `interFormInt_eq_kroneckerHInt_capHInt`. This is the REDUCTION: `IntPoincareDuality` (a
`H² ≃ Dual H²` iso) ⟸ "integral cap `· ⌢ [M]` is an iso" — the char-0 upgrade of the on-main mod-2
injective `nondeg_of_closed`, with the residual community-scale core now precisely the cap-iso proof. -/
noncomputable def intPoincareDualityOfCapIso {zM : Homology X 4} (C : IntCapIso zM) :
    IntPoincareDuality (intFundamentalClassOfHomology zM) where
  toDualEquiv := C.capEquiv.trans C.kronEquiv
  toDualEquiv_apply a b := by
    rw [interFormInt_eq_kroneckerHInt_capHInt, LinearEquiv.trans_apply, C.kronEquiv_apply,
      C.capEquiv_apply]

/-- **Unimodularity of the intersection matrix from the integral cap-iso** — the end-to-end reduction:
given the integral cap-iso datum `IntCapIso [M]` and a free basis `B` of `H²(M;ℤ)`, the integer
intersection matrix `interMatrix (intFundamentalClassOfHomology [M]) B` is unimodular. Composes
`intPoincareDualityOfCapIso` with the DONE `interMatrix_isUnimodular_of_intPD`. Confirms the cap-iso datum
feeds the whole `IsEvenUnimodular` → `σ ÷ 16` leg, now anchored on the cleaner geometric input. -/
theorem interMatrix_isUnimodular_of_capIso {zM : Homology X 4}
    (B : IntH2Basis X) (C : IntCapIso zM) :
    IsUnimodular (interMatrix (intFundamentalClassOfHomology zM) B) :=
  interMatrix_isUnimodular_of_intPD _ B (intPoincareDualityOfCapIso C)

end SKEFTHawking.SingularCohomologyInt
