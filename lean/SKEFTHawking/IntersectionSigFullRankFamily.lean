/-
# Phase 5q.H — the intersection form's SIGNATURE from a full-rank family, with no basis

`LatticeSigFullRankSublattice` says a signature only sees the form over `ℝ`, so a finite-index
sublattice computes it. This module transports that to the manifold side:

    latticeSig_interMatrix_of_fullRank_family :
      (v : Fin n → H²(X;ℤ))  with  ⟨vᵢ ∪ vⱼ, [X]⟩ = G i j  and  det G ≠ 0
        ⟹  latticeSig (reindex (interMatrix fc B)) = latticeSig G

for **any** `IntH2Basis` datum `B` of rank `n`. The family `v` is arbitrary: not a basis, not
required to generate, not required to be linearly independent (nondegeneracy of its own Gram forces
that). This is the exact escape from `SETTLED_FORKS:
kummer-16-plus-6-geometric-block-is-not-a-basis` — for the *Gram congruence* the 16 exceptional plus
6 descended classes are genuinely insufficient (they span an index-`2⁸` proper sublattice, and the
Kummer half-sums are mandatory), but for the *signature* they are exactly enough.

## Route note — why not Novikov additivity

The obvious alternative for `σ(K3) = −16` is Novikov additivity across the 16 `ℝP³` seams
(`σ(K3) = σ(Q) + 16·σ(E)`). That needs signature-additivity-under-gluing-along-a-3-manifold, which
exists **nowhere** in Mathlib or in this tree: it would require relative intersection forms on
manifolds-with-boundary, the Maslov/Wall non-additivity correction term to be shown to vanish, and a
relative fundamental class for each piece. The full-rank-family route needs none of that — only a
tabulation of `⟨vᵢ ∪ vⱼ, [K3]⟩` for 22 explicit classes, which is the same kind of computation the
arc already performs (`IntersectionMatrixBasisChange.interMatrix_capDual`). The sublattice route also
degrades gracefully: any *other* full-rank family with a computable nondegenerate Gram works.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionMatrixBasisChange
import SKEFTHawking.LatticeSigFullRankSublattice

namespace SKEFTHawking.IntersectionSigFullRankFamily

open Matrix
open SKEFTHawking SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SphereProdBasisIdInt (gram_congr_of_basis_change)
open SKEFTHawking.IntersectionMatrixBasisChange (reindex_interMatrix)
open SKEFTHawking.LatticeSigFullRank

variable {X : TopCat}

/-! ## §1. The Gram of an arbitrary family is a congruence of the basis Gram -/

/-- **`Gram(v) = Pᵀ · Gram(basis) · P` where `P` is the coordinate matrix of the family.**

Pure bilinear algebra (`SphereProdBasisIdInt.gram_congr_of_basis_change`, which never asked for `P`
to be unimodular), specialised to the integral intersection form. The `P` here is
`Module.Basis.toMatrix Br v`, whose `(i,j)` entry is the `i`-th coordinate of `v j`. -/
theorem gram_family_congr (fc : IntFundamentalClass X) {n : ℕ}
    (Br : Module.Basis (Fin n) ℤ (Cohomology X 2)) (v : Fin n → Cohomology X 2) :
    (Br.toMatrix v)ᵀ * (Matrix.of fun i j => interFormInt fc (Br i) (Br j)) * (Br.toMatrix v)
      = Matrix.of fun i j => interFormInt fc (v i) (v j) :=
  gram_congr_of_basis_change (interFormInt fc) (⇑Br) v (Br.toMatrix v)
    (fun j => (Br.sum_repr (v j)).symm)

/-! ## §2. The headline: the signature from any nondegenerate family -/

/-- **THE FULL-RANK FAMILY SIGNATURE THEOREM.**

If `n` cohomology classes `v : Fin n → H²(X;ℤ)` have intersection Gram matrix `G` with `det G ≠ 0`,
then for **every** rank-`n` `IntH2Basis` datum `B` the intersection matrix has `latticeSig = σ(G)`.

No hypothesis relates `v` to `B`: the family need not be a basis, need not generate `H²(X;ℤ)`, and
its span may have arbitrarily large finite index. Nondegeneracy of `G` alone forces the coordinate
matrix `P` to have `det P ≠ 0` (since `det G = (det P)² · det (interMatrix)`), and §2 of
`LatticeSigFullRankSublattice` then identifies the two signatures.

Consequence for the welded Kummer `K3`: `σ` is computable from the 16 exceptional `(−2)`-classes plus
the 6 descended `T⁴` classes, which is a *strictly weaker* geometric obligation than the Gram
congruence that `KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram` asks for. -/
theorem latticeSig_interMatrix_of_fullRank_family (fc : IntFundamentalClass X)
    (B : IntH2Basis X) {n : ℕ} (h : B.rank = n) (v : Fin n → Cohomology X 2)
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j)
    (hdet : G.det ≠ 0) :
    latticeSig (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)) = latticeSig G := by
  set Br := B.basis.reindex (finCongr h) with hBr
  set P := Br.toMatrix v with hPdef
  set Gb : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => interFormInt fc (Br i) (Br j) with hGb
  have hGram : Pᵀ * Gb * P = G := by
    rw [hGb, hPdef, gram_family_congr fc Br v]
    ext i j
    exact hG i j
  have hPdet : P.det ≠ 0 := by
    intro h0
    apply hdet
    rw [← hGram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0]
    ring
  rw [reindex_interMatrix fc B h, ← hGb, ← hGram]
  exact (latticeSig_congr_of_det_ne_zero Gb P hPdet).symm

/-- **The same, packaged against a target value.** If the family's Gram is `G` with `det G ≠ 0` and
`σ(G) = s`, the intersection matrix has signature `s`. This is the shape a `hk3`-style consumer
(`UnitBlockCancellation.hk3_of_stable16_two`, whose second geometric input is `latticeSig M = −16`)
consumes directly. -/
theorem latticeSig_interMatrix_eq_of_fullRank_family (fc : IntFundamentalClass X)
    (B : IntH2Basis X) {n : ℕ} (h : B.rank = n) (v : Fin n → Cohomology X 2)
    (G : Matrix (Fin n) (Fin n) ℤ) (hG : ∀ i j, interFormInt fc (v i) (v j) = G i j)
    (hdet : G.det ≠ 0) {s : ℤ} (hs : latticeSig G = s) :
    latticeSig (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)) = s := by
  rw [latticeSig_interMatrix_of_fullRank_family fc B h v G hG hdet, hs]

/-- **`σ = −16` from a Kummer geometric family.** The concrete instance: 22 classes whose Gram is
`⟨−2⟩¹⁶ ⊕ 3H` — 16 pairwise-disjoint `(−2)`-spheres and the 6 descended `T⁴` classes — pin the
intersection matrix's signature to `−16` on any rank-22 basis datum.

This is (ii) of the K3 Gram obligation reduced to a *tabulation*: no basis of `H²(K3;ℤ)`, no Kummer
half-sums, no unimodularity, no Poincaré duality, and no gluing-signature machinery. -/
theorem latticeSig_interMatrix_neg16_of_kummerFamily (fc : IntFundamentalClass X)
    (B : IntH2Basis X) (h : B.rank = 22) (v : Fin 22 → Cohomology X 2)
    (hG : ∀ i j, interFormInt fc (v i) (v j) = kummerSubForm i j) :
    latticeSig (Matrix.reindex (finCongr h) (finCongr h) (interMatrix fc B)) = -16 :=
  latticeSig_interMatrix_eq_of_fullRank_family fc B h v kummerSubForm hG
    kummerSubForm_det_ne_zero kummerSubForm_latticeSig

/-! ## §3. Evenness is basis-free, and is NOT implied by the sublattice

The signature transports from a finite-index sublattice; **evenness does not** (an odd unimodular
overlattice can perfectly well contain an even sublattice of index `2⁸`). So the `IsEven` conjunct of
`IsEvenUnimodular` is genuinely separate geometric content — Wu/spin — and §3 only records the
basis-independence that makes it a statement about the manifold rather than about a chosen basis. -/

/-- **Evenness of the intersection matrix ⟺ every class has even self-intersection.**

`←` is immediate. `→` is the statement that an integral symmetric form which is even on a basis is
even on the whole lattice: `q(Σ cᵢ bᵢ) = Σ cᵢ² Mᵢᵢ + 2 Σ_{i<j} cᵢcⱼ Mᵢⱼ`. Proving the biconditional
makes `IsEven (interMatrix fc B)` visibly a property of `(X, fc)` and not of `B`, which is what lets
a Wu-class / spin argument (which produces the basis-free side) discharge it. -/
theorem isEven_interMatrix_iff (fc : IntFundamentalClass X) (B : IntH2Basis X) :
    IsEven (interMatrix fc B) ↔ ∀ a : Cohomology X 2, (2 : ℤ) ∣ interFormInt fc a a := by
  constructor
  · intro heven a
    -- expand `a` in the basis and induct over the (finite) support of its coordinates
    obtain ⟨c, hc⟩ : ∃ c : Fin B.rank →₀ ℤ, (B.basis.repr a) = c := ⟨_, rfl⟩
    have ha : a = ∑ i ∈ c.support, c i • B.basis i := by
      conv_lhs => rw [← B.basis.linearCombination_repr a]
      rw [hc]
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
    have key : ∀ s : Finset (Fin B.rank),
        (2 : ℤ) ∣ interFormInt fc (∑ i ∈ s, c i • B.basis i) (∑ i ∈ s, c i • B.basis i) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        set y := ∑ i ∈ s, c i • B.basis i with hy
        have hexp : interFormInt fc (c j • B.basis j + y) (c j • B.basis j + y)
            = c j * c j * interFormInt fc (B.basis j) (B.basis j)
              + 2 * (c j * interFormInt fc (B.basis j) y) + interFormInt fc y y := by
          simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
            smul_eq_mul]
          rw [interFormInt_symm fc y (B.basis j)]
          ring
        rw [hexp]
        refine dvd_add (dvd_add ?_ ⟨_, rfl⟩) ih
        exact Dvd.dvd.mul_left (heven j) _
    rw [ha]
    exact key c.support
  · intro h
    intro i
    rw [interMatrix_apply]
    exact h (B.basis i)

/-- **The `IsEvenUnimodular` input, decomposed into its two genuinely-geometric halves at the
manifold.** `IsSymmetricInt` is free (`interMatrix_isSymmetricInt`); what remains is unimodularity
(Poincaré duality: `det = ±1`) and evenness (Wu/spin: every self-intersection even). Stated so a
consumer can be handed the two halves from two independent geometric arguments. -/
theorem isEvenUnimodular_interMatrix_of_unimodular_of_even (fc : IntFundamentalClass X)
    (B : IntH2Basis X) (huni : IsUnimodular (interMatrix fc B))
    (heven : ∀ a : Cohomology X 2, (2 : ℤ) ∣ interFormInt fc a a) :
    IsEvenUnimodular (interMatrix fc B) :=
  ⟨interMatrix_isSymmetricInt fc B, huni, (isEven_interMatrix_iff fc B).mpr heven⟩

end SKEFTHawking.IntersectionSigFullRankFamily
