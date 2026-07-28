/-
# Phase 5q.H — supplying `hfam`: the welded `K3`'s 22-class family, BLOCK BY BLOCK

`KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` reduced the welded Kummer
`K3`'s entire E1 residual ledger to three geometric inputs, of which the one this module attacks is

    hfam : ∀ o, ∃ v : Fin 22 → H²(K3;ℤ), ∀ i j, ⟨vᵢ ∪ vⱼ, [K3]_o⟩ = kummerSubForm i j

with `kummerSubForm = ⟨−2⟩¹⁶ ⊕ 3H`. That single statement bundles three *independent* geometric
tabulations, and as long as they stay bundled they cannot be worked in parallel. This module splits
them, and generalises the consumer so that the split is not a cul-de-sac.

## §1–§3 — the split

`gram_append_blockDiag` is the general fact: a `Fin na`-family `x` and a `Fin nb`-family `y` whose
own Grams are `A` and `B` and which are **mutually orthogonal** assemble (via `Fin.append`) into a
`Fin (na+nb)`-family whose Gram is `blockDiag A B`. Specialised at `na = 16`, `nb = 6`,
`A = ⟨−2⟩¹⁶`, `B = 3H` it turns `hfam` into exactly three obligations:

| block | obligation | geometric content |
|---|---|---|
| `⟨−2⟩¹⁶` | 16 classes, `⟨xᵢ∪xᵢ⟩ = −2`, `⟨xᵢ∪xⱼ⟩ = 0` (`i ≠ j`) | the exceptional `(−2)`-spheres of the 16 `E`-pieces, pairwise disjoint |
| `3H` | 6 classes with Gram `torusFourForm` | the `T⁴` classes descended through `Q = T⁴°/τ` |
| cross | `⟨xᵢ∪yⱼ⟩ = 0` | `E`-supported vs `Q`-supported |

`§3` re-indexes the 16-block by the *geometric* index `KummerWeld.EIndex` (the 16 fixed points of
`τ`), which is how the exceptional classes actually arrive, so the E-lane never has to choose a
numbering.

## §4 — the consumer, generalised (a strictly weaker hypothesis)

`kummerSubForm` is not sacred: the only thing the lattice route consumes is
`latticeSig (kummerK3Gram o) = −16`, and `IntersectionSigFullRankFamily` delivers that from **any**
family whose Gram `G` merely satisfies `det G ≠ 0` and `latticeSig G = −16`.
`nonempty_kummerK3E1Atoms_of_stable_of_geometric_nondegenerate` is the headline with `hfam` replaced
by that weaker input, and `hfamGen_of_hfam` proves the original `hfam` implies it — so the
generalisation is a genuine widening of the supply side and still plugs into the exact obligation.

## §5 — the non-vacuity certificate

`hfam` is not satisfiable without geometry: `linearIndependent_of_gram_nondegenerate` shows any
family with nondegenerate Gram is `ℤ`-linearly independent, so `hfam` forces **22 independent
classes** in `H²(K3;ℤ)` — it cannot be discharged by `v = 0`, by repeats, or by any degenerate
choice. (`kummerSubForm_det_ne_zero` supplies the nondegeneracy for the `⟨−2⟩¹⁶ ⊕ 3H` shape.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3GramFromLattice

namespace SKEFTHawking.KummerK3GeometricFamily

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3 EIndex eIndex_card)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (blockDiag blockDiag_def)
open SKEFTHawking.KummerInvolution (torusFourForm)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.IntersectionSigFullRankFamily
open SKEFTHawking.KummerK3GramFromLattice

noncomputable section

variable {X : TopCat}

/-! ## §1. `blockDiag` entrywise, on the `Fin.castAdd` / `Fin.natAdd` split -/

theorem blockDiag_castAdd_castAdd {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (i j : Fin na) :
    blockDiag A B (Fin.castAdd nb i) (Fin.castAdd nb j) = A i j := by
  simp [blockDiag_def]

theorem blockDiag_castAdd_natAdd {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (i : Fin na) (j : Fin nb) :
    blockDiag A B (Fin.castAdd nb i) (Fin.natAdd na j) = 0 := by
  simp [blockDiag_def]

theorem blockDiag_natAdd_castAdd {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (i : Fin nb) (j : Fin na) :
    blockDiag A B (Fin.natAdd na i) (Fin.castAdd nb j) = 0 := by
  simp [blockDiag_def]

theorem blockDiag_natAdd_natAdd {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (i j : Fin nb) :
    blockDiag A B (Fin.natAdd na i) (Fin.natAdd na j) = B i j := by
  simp [blockDiag_def]

/-! ## §2. The block-assembly of a geometric family -/

/-- **Two mutually orthogonal families assemble into one with block-diagonal Gram.**

If `x : Fin na → H²(X;ℤ)` has Gram `A`, `y : Fin nb → H²(X;ℤ)` has Gram `B`, and every `xᵢ` is
orthogonal to every `yⱼ`, then `Fin.append x y : Fin (na+nb) → H²(X;ℤ)` has Gram `blockDiag A B`.
Symmetry of the intersection form (`interFormInt_symm`) supplies the second off-diagonal block, so
only one direction of orthogonality has to be tabulated. -/
theorem gram_append_blockDiag (fc : IntFundamentalClass X) {na nb : ℕ}
    (x : Fin na → Cohomology X 2) (y : Fin nb → Cohomology X 2)
    (A : Matrix (Fin na) (Fin na) ℤ) (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : ∀ i j, interFormInt fc (x i) (x j) = A i j)
    (hB : ∀ i j, interFormInt fc (y i) (y j) = B i j)
    (hcross : ∀ i j, interFormInt fc (x i) (y j) = 0) :
    ∀ i j : Fin (na + nb),
      interFormInt fc (Fin.append x y i) (Fin.append x y j) = blockDiag A B i j := by
  intro i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.append_left, blockDiag_castAdd_castAdd]
      exact hA i j
    | right j =>
      rw [Fin.append_left, Fin.append_right, blockDiag_castAdd_natAdd]
      exact hcross i j
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.append_right, Fin.append_left, blockDiag_natAdd_castAdd,
        interFormInt_symm fc (y i) (x j)]
      exact hcross j i
    | right j =>
      rw [Fin.append_right, Fin.append_right, blockDiag_natAdd_natAdd]
      exact hB i j

/-! ## §3. The Kummer specialisation: `⟨−2⟩¹⁶ ⊕ 3H` from three tabulations -/

/-- **`hfam`'s family, from the 16-block, the 6-block and the cross-block.**

The three hypotheses are exactly the three geometric tabulations listed in the module docstring, and
none of them mentions the other two — so the E-lane, the Q-lane and the cross-lane are independent.
`Fin.append` supplies the family, `gram_append_blockDiag` its Gram. -/
theorem exists_kummerSubForm_family_of_blocks (fc : IntFundamentalClass X)
    (x : Fin 16 → Cohomology X 2) (y : Fin 6 → Cohomology X 2)
    (hself : ∀ i, interFormInt fc (x i) (x i) = -2)
    (hoff : ∀ i j, i ≠ j → interFormInt fc (x i) (x j) = 0)
    (hy : ∀ i j, interFormInt fc (y i) (y j) = torusFourForm i j)
    (hcross : ∀ i j, interFormInt fc (x i) (y j) = 0) :
    ∃ v : Fin 22 → Cohomology X 2,
      ∀ i j, interFormInt fc (v i) (v j) = kummerSubForm i j := by
  refine ⟨Fin.append x y, ?_⟩
  have hA : ∀ i j, interFormInt fc (x i) (x j) = negTwoDiag 16 i j := by
    intro i j
    rw [negTwoDiag_apply]
    by_cases h : i = j
    · subst h; simpa using hself i
    · simpa [h] using hoff i j h
  exact gram_append_blockDiag fc x y (negTwoDiag 16) torusFourForm hA hy hcross

/-- **The same, with the 16-block indexed by the geometric index `EIndex`** — the 16 fixed points of
`τ`, one per `E`-piece of the weld (`KummerWeld.eIndex_card : Fintype.card EIndex = 16`). This is the
shape in which the exceptional `(−2)`-classes actually arrive, so the E-lane never has to pick a
numbering of the fixed points. -/
theorem exists_kummerSubForm_family_of_eIndex_blocks (fc : IntFundamentalClass X)
    (x : EIndex → Cohomology X 2) (y : Fin 6 → Cohomology X 2)
    (hself : ∀ c, interFormInt fc (x c) (x c) = -2)
    (hoff : ∀ c d, c ≠ d → interFormInt fc (x c) (x d) = 0)
    (hy : ∀ i j, interFormInt fc (y i) (y j) = torusFourForm i j)
    (hcross : ∀ c j, interFormInt fc (x c) (y j) = 0) :
    ∃ v : Fin 22 → Cohomology X 2,
      ∀ i j, interFormInt fc (v i) (v j) = kummerSubForm i j := by
  let e : EIndex ≃ Fin 16 := Fintype.equivFinOfCardEq eIndex_card
  refine exists_kummerSubForm_family_of_blocks fc (fun i => x (e.symm i)) y
    (fun i => hself _) (fun i j hij => hoff _ _ ?_) hy (fun i j => hcross _ _)
  exact fun h => hij (e.symm.injective h)

/-! ## §4. The consumer, generalised: any nondegenerate Gram of signature `−16` -/

/-- **`latticeSig (kummerK3Gram o) = −16` from ANY nondegenerate family of signature `−16`.**

`IntersectionSigFullRankFamily.latticeSig_interMatrix_eq_of_fullRank_family` never asked for the
Gram to be `kummerSubForm`; it asked for `det G ≠ 0` (so the family spans a finite-index sublattice)
and `latticeSig G = −16`. Stating it at that strength means the geometric lane may return *any*
computable nondegenerate Gram — a different normalisation of the exceptional classes, a different
`T⁴` frame, a family of 22 classes that is not even block-decomposed — without renegotiating the
interface. -/
theorem kummerK3Gram_latticeSig_of_nondegenerate_family (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2) (G : Matrix (Fin 22) (Fin 22) ℤ)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
    (hdet : G.det ≠ 0) (hsig : latticeSig G = -16) :
    latticeSig (kummerK3Gram o) = -16 :=
  latticeSig_interMatrix_eq_of_fullRank_family _ kummerK3IntH2Basis kummerK3IntH2Basis_rank v G hv
    hdet hsig

/-- **THE HEADLINE, with `hfam` weakened to a nondegenerate family of signature `−16`.**

Identical to `KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable_of_geometric` except in its
last hypothesis, which is strictly weaker (`hfamGen_of_hfam` below). `hpd` and `heven` are passed
through verbatim. -/
theorem nonempty_kummerK3E1Atoms_of_stable_of_geometric_nondegenerate
    (hstable : StableNegRank16Two)
    (hpd : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfamGen : ∀ o : IntOrientation KummerK3, ∃ (G : Matrix (Fin 22) (Fin 22) ℤ)
        (v : Fin 22 → Cohomology KummerK3top 2),
        (∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
          ∧ G.det ≠ 0 ∧ latticeSig G = -16) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable hstable
    (fun o => kummerK3Gram_isEvenUnimodular o (hpd o) (heven o))
    (fun o => by
      obtain ⟨G, v, hv, hdet, hsig⟩ := hfamGen o
      exact kummerK3Gram_latticeSig_of_nondegenerate_family o v G hv hdet hsig)

/-- **The original `hfam` implies the generalised one** — `det kummerSubForm = ±2¹⁶ ≠ 0` and
`latticeSig kummerSubForm = −16`. Proved so that §4 is visibly a *widening* of the supply side and
not a different obligation: anything that discharges `hfam` discharges `hfamGen`. -/
theorem hfamGen_of_hfam
    (hfam : ∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = kummerSubForm i j) :
    ∀ o : IntOrientation KummerK3, ∃ (G : Matrix (Fin 22) (Fin 22) ℤ)
      (v : Fin 22 → Cohomology KummerK3top 2),
      (∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
        ∧ G.det ≠ 0 ∧ latticeSig G = -16 := by
  intro o
  obtain ⟨v, hv⟩ := hfam o
  exact ⟨kummerSubForm, v, hv, kummerSubForm_det_ne_zero, kummerSubForm_latticeSig⟩

/-! ## §5. Non-vacuity: a family with nondegenerate Gram is linearly independent -/

/-- **A family whose intersection Gram is nondegenerate is `ℤ`-linearly independent.**

The zero-geometric-input attack on `hfam` (and on the weakened `hfamGen`): could either be satisfied
without exhibiting genuine cohomology? No. `det G ≠ 0` forces the `n` classes to be independent over
`ℤ`, so `hfam` demands 22 independent classes in `H²(K3;ℤ)` — `v = 0`, a repeated class, or any
family spanning a rank-`< 22` subgroup all fail. The proof is the adjugate identity: a relation
`∑ gᵢ vᵢ = 0` pairs against each `vⱼ` to give `g ᵥ* G = 0`, hence `(det G) • g = 0`, hence `g = 0`
in the domain `ℤ`. -/
theorem linearIndependent_of_gram_nondegenerate (fc : IntFundamentalClass X) {n : ℕ}
    (v : Fin n → Cohomology X 2) (G : Matrix (Fin n) (Fin n) ℤ)
    (hv : ∀ i j, interFormInt fc (v i) (v j) = G i j) (hdet : G.det ≠ 0) :
    LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hvec : Matrix.vecMul g G = 0 := by
    funext j
    have : interFormInt fc (∑ i, g i • v i) (v j) = 0 := by rw [hg]; simp
    rw [map_sum] at this
    simpa [Matrix.vecMul, dotProduct, hv] using this
  have hadj : G.det • g = 0 := by
    have := congrArg (fun w => Matrix.vecMul w G.adjugate) hvec
    simpa [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul,
      Matrix.vecMul_one] using this
  intro i
  have := congrFun hadj i
  simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
  exact (mul_eq_zero.mp this).resolve_left hdet

/-- **The non-vacuity certificate at the actual `hfam` shape.** Any family realising
`kummerSubForm` as its intersection Gram consists of 22 `ℤ`-linearly independent classes of
`H²(K3;ℤ)`. -/
theorem linearIndependent_of_gram_kummerSubForm (fc : IntFundamentalClass X)
    (v : Fin 22 → Cohomology X 2)
    (hv : ∀ i j, interFormInt fc (v i) (v j) = kummerSubForm i j) :
    LinearIndependent ℤ v :=
  linearIndependent_of_gram_nondegenerate fc v kummerSubForm hv kummerSubForm_det_ne_zero

/-! ## §6. Gram transport along an integer congruence — the `IntCongr`-to-equality adapter -/

/-- **A family's Gram can be moved along an integer congruence by recombining the family.**

If `y` has Gram `M` and `IntCongr M N` (witness `P`, `Pᵀ M P = N`), then the recombined family
`y'ⱼ = ∑ᵢ Pᵢⱼ · yᵢ` has Gram `N` on the nose. Pure bilinear algebra
(`SphereProdBasisIdInt.gram_congr_of_basis_change`, which never asked `P` to be unimodular — the
`IsUnit` half of `IntCongr` is not used).

**Why the block interface needs this.** §3's 6-block hypothesis asks for `⟨yᵢ ∪ yⱼ⟩ = torusFourForm i j`
*literally*, while the banked `T⁴` result
`KummerT4GramCross.interMatrix_t4_intCongr_torusFourForm` is an `IntCongr` to `torusFourForm`
(its Gram in the pair basis is `t4m • XMat`). This adapter closes that gap without renegotiating
either statement. -/
theorem exists_family_gram_of_intCongr (fc : IntFundamentalClass X) {n : ℕ}
    (y : Fin n → Cohomology X 2) (M N : Matrix (Fin n) (Fin n) ℤ)
    (hy : ∀ i j, interFormInt fc (y i) (y j) = M i j) (hcong : IntCongr M N) :
    ∃ y' : Fin n → Cohomology X 2, ∀ i j, interFormInt fc (y' i) (y' j) = N i j := by
  obtain ⟨P, -, hP⟩ := hcong
  refine ⟨fun j => ∑ i, P i j • y i, fun i j => ?_⟩
  have hgram := SKEFTHawking.SphereProdBasisIdInt.gram_congr_of_basis_change (interFormInt fc) y
    (fun j => ∑ i, P i j • y i) P (fun _ => rfl)
  have hM : (Matrix.of fun i j => interFormInt fc (y i) (y j)) = M := by
    ext a b; exact hy a b
  rw [hM, hP] at hgram
  exact (congrFun (congrFun hgram i) j).symm

/-- **The 6-block hypothesis of §3 from an `IntCongr` to `3H`.** The `IntCongr`-shaped form of the
`hy` input, so the `Q`-lane may deliver its `T⁴`-descended classes with any Gram congruent to
`torusFourForm` rather than equal to it. -/
theorem exists_torusBlock_of_intCongr (fc : IntFundamentalClass X)
    (y : Fin 6 → Cohomology X 2) (M : Matrix (Fin 6) (Fin 6) ℤ)
    (hy : ∀ i j, interFormInt fc (y i) (y j) = M i j) (hcong : IntCongr M torusFourForm) :
    ∃ y' : Fin 6 → Cohomology X 2, ∀ i j, interFormInt fc (y' i) (y' j) = torusFourForm i j :=
  exists_family_gram_of_intCongr fc y M torusFourForm hy hcong

end

end SKEFTHawking.KummerK3GeometricFamily
