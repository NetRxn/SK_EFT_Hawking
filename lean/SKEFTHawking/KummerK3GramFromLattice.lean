/-
# Phase 5q.H — the welded `K3`'s Gram congruence, THROUGH THE LATTICE CLASSIFICATION

`KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram` reduced the whole E1 residual ledger of the
welded Kummer `K3` to a single obligation, the K3-lattice Gram congruence

    ∀ o, ∃ C hC, IntCongr (reindex (interMatrix [K3]_o C)) k3Form.

This module discharges that obligation *modulo the lattice classification*, i.e. routes it through

    UnitBlockCancellation.hk3_of_stable16_two :
      StableNegRank16Two → IsEvenUnimodular M → latticeSig M = −16 → IntCongr M k3Form

so that the Kummer side owes only the two **geometric** inputs (i) even-unimodularity and
(ii) `σ = −16`, and never has to exhibit a Gram *congruence* — in particular never has to produce the
Kummer half-sums that `SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis` shows a
basis-level attack requires.

## ⚠ The circularity that is deliberately NOT used

`KummerK3PoincareDuality.kummerK3_pdInput_of_gram` derives integral Poincaré duality **from** the Gram
congruence. On this route the Gram congruence is the *output*, so that arrow is unusable: it would be
a strict circle. Unimodularity is instead taken from the **forward** direction of the unconditional
biconditional `KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det` (i.e.
`IntPDDetCriterion.interMatrix_isUnit_det_of_intPD`), whose hypothesis is the genuine
`IntPoincareDuality` datum and mentions no congruence. `nonempty_intPD_iff_isUnit_det` is an
*equivalence*, so nothing is gained or lost by the packaging: at the welded `K3` "the intersection
matrix is unimodular" and "integral PD holds" are literally the same obligation, and this module says
so rather than pretending one discharges the other.

## The residual ledger this module produces

| input | status after this module |
|---|---|
| `StableNegRank16Two` | wt1's lattice lane (Eichler STEP 1) — **not** built here |
| (i-a) unimodularity | `≡ Nonempty (IntPoincareDuality [K3]_o)` — genuine integral PD, open |
| (i-b) evenness | `≡ ∀ a, 2 ∣ ⟨a ∪ a, [K3]⟩` — Wu/spin, open (NOT implied by the sublattice) |
| (ii) `σ = −16` | `⟸` 22 classes with Gram `⟨−2⟩¹⁶ ⊕ 3H` — no basis, no half-sums, no PD, no Novikov |

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3E1FromGram
import SKEFTHawking.UnitBlockCancellation
import SKEFTHawking.IntersectionSigFullRankFamily

namespace SKEFTHawking.KummerK3GramFromLattice

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SpinSigmaRoute (k3Form)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.IntersectionSigFullRankFamily

noncomputable section

/-! ## §1. The welded `K3`'s intersection matrix at the packaged rank-22 basis -/

/-- **The welded `K3`'s intersection matrix**, at the packaged (anonymous, `Classical.choice`)
rank-22 basis and reindexed to `Fin 22` — exactly the matrix the `hk3` field of
`KummerK3E1Package.kummerK3_hk3_of_geometric_basis` speaks about, and exactly the `M` that
`UnitBlockCancellation.hk3_of_stable16_two` consumes. -/
def kummerK3Gram (o : IntOrientation KummerK3) : Matrix (Fin 22) (Fin 22) ℤ :=
  Matrix.reindex (finCongr kummerK3IntH2Basis_rank) (finCongr kummerK3IntH2Basis_rank)
    (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis)

/-! ## §2. (i-a) Unimodularity — from GENUINE integral Poincaré duality, not from the Gram -/

/-- **Unimodularity of the welded `K3`'s intersection matrix from the genuine `IntPoincareDuality`
datum.** The forward direction of `KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det`, whose
hypothesis is the perfect-pairing isomorphism `H²(K3;ℤ) ≃ₗ Dual ℤ (H²(K3;ℤ))` itself — no Gram
congruence anywhere, so this is usable on the route that *produces* the Gram congruence.

Reindexing does not move the determinant (`Matrix.det_reindex_self`), so the conclusion is stated
directly at `kummerK3Gram`. -/
theorem kummerK3Gram_isUnimodular_of_intPD (o : IntOrientation KummerK3)
    (hpd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    IsUnimodular (kummerK3Gram o) := by
  have h := (KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det o).mp hpd
  show (kummerK3Gram o).det = 1 ∨ (kummerK3Gram o).det = -1
  rw [kummerK3Gram, Matrix.det_reindex_self]
  exact Int.isUnit_iff.mp h

/-- **The converse, recorded so the ledger is honest.** Unimodularity of the intersection matrix
*implies* the integral-PD datum, so (i-a) is not merely implied by PD — it **is** PD. Anyone hoping
to get unimodularity more cheaply than integral Poincaré duality on the welded carrier is looking for
something that provably does not exist. -/
theorem nonempty_intPD_of_kummerK3Gram_isUnimodular (o : IntOrientation KummerK3)
    (huni : IsUnimodular (kummerK3Gram o)) :
    Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)) := by
  refine (KummerK3PoincareDuality.nonempty_intPD_iff_isUnit_det o).mpr (Int.isUnit_iff.mpr ?_)
  have := huni
  rwa [kummerK3Gram, IsUnimodular, Matrix.det_reindex_self] at this

/-! ## §3. (i) Even-unimodularity from the two separated geometric halves -/

/-- **`IsEvenUnimodular (kummerK3Gram o)` from integral PD (unimodularity) plus even
self-intersections (Wu/spin).** Symmetry is free (`interMatrix_isSymmetricInt`); the two remaining
conjuncts are the two genuinely-geometric halves, supplied independently. -/
theorem kummerK3Gram_isEvenUnimodular (o : IntOrientation KummerK3)
    (hpd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ a : Cohomology KummerK3top 2,
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a) :
    IsEvenUnimodular (kummerK3Gram o) := by
  have hbase : IsEvenUnimodular
      (interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis) := by
    refine isEvenUnimodular_interMatrix_of_unimodular_of_even _ _ ?_ heven
    have := kummerK3Gram_isUnimodular_of_intPD o hpd
    rwa [kummerK3Gram, IsUnimodular, Matrix.det_reindex_self] at this
  exact isEvenUnimodular_reindex _ _ hbase

/-! ## §4. (ii) `σ = −16` from the Kummer geometric family — the full-rank sublattice route -/

/-- **`latticeSig (kummerK3Gram o) = −16` from 22 classes with Gram `⟨−2⟩¹⁶ ⊕ 3H`.**

The 16 exceptional `(−2)`-classes of the resolved fixed points together with the 6 descended `T⁴`
classes. They span only a proper index-`2⁸` sublattice of `H₂(K3;ℤ)` — which is fatal for a *basis*
attack and irrelevant here, because `det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ ≠ 0` and the signature is a real
invariant (`LatticeSigFullRank.latticeSig_congr_of_det_ne_zero`).

What this input is **not**: it is not a basis, not a generating family, not Poincaré duality, and not
signature-additivity-under-gluing. It is a table of 253 cup-product evaluations. -/
theorem kummerK3Gram_latticeSig_of_kummerFamily (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubForm i j) :
    latticeSig (kummerK3Gram o) = -16 :=
  latticeSig_interMatrix_neg16_of_kummerFamily _ kummerK3IntH2Basis kummerK3IntH2Basis_rank v hv

/-! ## §5. The assembly: the Gram congruence, and the E1 atoms -/

/-- **THE GRAM CONGRUENCE FROM THE LATTICE CLASSIFICATION.** With wt1's `StableNegRank16Two`, the two
geometric inputs (i) even-unimodularity and (ii) `σ = −16` deliver `IntCongr (kummerK3Gram o) k3Form`
for a single orientation. This is `UnitBlockCancellation.hk3_of_stable16_two` instantiated at the
welded carrier. -/
theorem kummerK3_hk3_of_stable (hstable : StableNegRank16Two) (o : IntOrientation KummerK3)
    (heu : IsEvenUnimodular (kummerK3Gram o)) (hsig : latticeSig (kummerK3Gram o) = -16) :
    IntCongr (kummerK3Gram o) k3Form :=
  hk3_of_stable16_two hstable _ heu hsig

/-- **The `∀ o` Gram statement — the exact hypothesis of
`KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram`** — from `StableNegRank16Two` plus the two
geometric inputs at every orientation. -/
theorem kummerK3_gram_of_stable (hstable : StableNegRank16Two)
    (heu : ∀ o : IntOrientation KummerK3, IsEvenUnimodular (kummerK3Gram o))
    (hsig : ∀ o : IntOrientation KummerK3, latticeSig (kummerK3Gram o) = -16) :
    ∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
      IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
        (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form := fun o =>
  ⟨kummerK3IntH2Basis, kummerK3IntH2Basis_rank, kummerK3_hk3_of_stable hstable o (heu o) (hsig o)⟩

/-- **The E1 atom triple of the welded `K3` from the lattice classification plus (i) and (ii).**
Composition of §5 with `KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram`. -/
theorem nonempty_kummerK3E1Atoms_of_stable (hstable : StableNegRank16Two)
    (heu : ∀ o : IntOrientation KummerK3, IsEvenUnimodular (kummerK3Gram o))
    (hsig : ∀ o : IntOrientation KummerK3, latticeSig (kummerK3Gram o) = -16) :
    Nonempty KummerK3E1Atoms :=
  KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram (kummerK3_gram_of_stable hstable heu hsig)

/-- **THE HEADLINE — the welded `K3`'s E1 atoms from three geometric inputs and one lattice input.**

The E1 residual ledger of the welded Kummer `K3`, restated with the Gram congruence eliminated:

* `hstable` — `StableNegRank16Two`, wt1's Eichler lane (pure lattice theory, no geometry);
* `hpd` — integral Poincaré duality at every orientation (`≡` unimodularity of the intersection
  matrix, by §2's biconditional — not derivable from the Gram on this route, and not derived from it);
* `heven` — every class has even self-intersection (Wu / `w₂ = 0` on the welded carrier);
* `hfam` — 22 classes whose intersection Gram is `⟨−2⟩¹⁶ ⊕ 3H`.

Compared with `KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram`'s single hypothesis, the
congruence — and with it the Kummer half-sums and any basis of `H₂(K3;ℤ)` — is gone; what remains are
three inputs each of which is a statement about *classes and cup products*, not about lattices. -/
theorem nonempty_kummerK3E1Atoms_of_stable_of_geometric (hstable : StableNegRank16Two)
    (hpd : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ (o : IntOrientation KummerK3) (a : Cohomology KummerK3top 2),
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfam : ∀ o : IntOrientation KummerK3, ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
        = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_of_stable hstable
    (fun o => kummerK3Gram_isEvenUnimodular o (hpd o) (heven o))
    (fun o => by
      obtain ⟨v, hv⟩ := hfam o
      exact kummerK3Gram_latticeSig_of_kummerFamily o v hv)

end

end SKEFTHawking.KummerK3GramFromLattice
