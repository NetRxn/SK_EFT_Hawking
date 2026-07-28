/-
# The welded `K3`'s E1 lane: the `∀ o` routes are VACUOUS, and the pinned-orientation repair

Every published entry point into `Nonempty KummerK3E1Atoms` quantifies its geometric hypothesis over
**all** integral orientations. By `IntOrientationScaling` that is fatal: `IntOrientation` admits
`n • [K3]` for every odd `n`, and an orientation of the welded `K3` exists unconditionally
(`KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond`), so

* **`pdInput`** — `∀ o, Nonempty (IntPoincareDuality [K3]_o)` — is **false**
  (`not_forall_intOrientation_pdInput`): scaling by `3` multiplies the Gram determinant by `3²²`,
  and a determinant cannot be a unit both before and after.
* **`hsig`** — `∀ o, latticeSig (kummerK3Gram o) = −16` — is **false**
  (`not_forall_latticeSig_neg16`): reversal negates the Gram, hence the signature.

Consequently `KummerK3E1Residuals` is **uninhabitable** (`not_kummerK3E1Residuals`), and the
following are all vacuously true — provable, but with hypotheses that can never be supplied:

| entry point | refuted via |
|---|---|
| `KummerK3SeamTransport.nonempty_kummerK3E1Atoms_of_pd` | `pdInput` |
| `KummerK3E1FromGram.nonempty_kummerK3E1Atoms_of_gram` / `_of_hk3` | `hgram`/`hk3` ⟹ `pdInput` |
| `KummerK3GramFromLattice.nonempty_kummerK3E1Atoms_of_stable` | `hsig` |
| `…_of_stable_of_geometric` | `hpd` (and `hfam`, by `KummerK3ForallOrientationFalse`) |
| `KummerK3E1Unconditional.nonempty_kummerK3E1Atoms_of_gramFacts` / `_of_geometric` / `…_nondegenerate` | `hsig` / `hpd` |
| `…_of_geoData` / `…_of_geoDataEven` | `hgeo` ⟹ `pdInput` (via `nonempty_intPD_of_capDual_span`) |

## What was actually wrong — and what was not

`KummerK3E1Atoms` bundles **one** orientation `orient` together with `pd` *against that orientation*.
That is the correct existential shape and is untouched: nothing here says the atoms are unreachable.
Only the **routes** were over-quantified — a `∀ o` was written where the consumer needs a single `o`.

§2 supplies the pinned replacements. Note what they show: `nonempty_kummerK3E1Atoms_at` needs
**integral Poincaré duality at one orientation and nothing else** — no evenness, no Gram, no lattice
theory. The Gram lane (`kummerK3_hk3_at`) is therefore not on the path to the E1 atoms at all; it is
on the path to the `σ = −16` Gram congruence that *other* consumers want, and it too is now stated
at a single orientation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationScaling
import SKEFTHawking.IntOrientationPrimitive
import SKEFTHawking.IntersectionDetFullRankFamily
import SKEFTHawking.IntersectionIndexFullRankFamily
import SKEFTHawking.KummerK3E1Unconditional
import SKEFTHawking.KummerK3E1FromGram

namespace SKEFTHawking.KummerK3E1Repair

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.LatticeSigFullRank
open SKEFTHawking.KummerK3GramFromLattice
open SKEFTHawking.KummerK3CapDualFamily
open SKEFTHawking.KummerK3E1Unconditional
open SKEFTHawking.KummerK3PoincareDuality
open SKEFTHawking.IntOrientationReverse
open SKEFTHawking.IntOrientationScaling
open SKEFTHawking.IntOrientationPrimitive
open SKEFTHawking.IntersectionDetFullRankFamily
open SKEFTHawking.IntersectionIndexFullRankFamily
open SKEFTHawking.KummerInvolution (torusFourForm torusFourForm_isEvenUnimodular)
open SKEFTHawking.SpinSigmaRoute (k3Form)

noncomputable section

/-! ## §1. The refutations -/

/-- **`pdInput` IS FALSE.** The welded `K3` has an orientation unconditionally, and `H²(K3;ℤ)` has
rank 22 > 0, so `IntOrientationScaling.not_forall_intOrientation_isUnimodular` applies verbatim —
integral PD at `3 • [K3]` would force `3²² · det = ±1` alongside `det = ±1`. -/
theorem not_forall_intOrientation_pdInput :
    ¬ (∀ o : IntOrientation KummerK3,
        Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) := by
  intro h
  obtain ⟨o⟩ := SKEFTHawking.KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond
  refine not_forall_intOrientation_isUnimodular o kummerK3IntH2Basis ?_ ?_
  · rw [kummerK3IntH2Basis_rank]; norm_num
  · intro o'
    exact Int.isUnit_iff.mp ((nonempty_intPD_iff_isUnit_det o').mp (h o'))

/-- **The E1 residual ledger is uninhabitable** — its `pdInput` field is the refuted statement. -/
theorem not_kummerK3E1Residuals : ¬ KummerK3E1Residuals :=
  fun r => not_forall_intOrientation_pdInput r.pdInput

/-- **Scaling the orientation scales the packaged Gram.** -/
theorem kummerK3Gram_smulOdd (o : IntOrientation KummerK3) {n : ℤ} (hn : Odd n) :
    kummerK3Gram (IntOrientation.smulOdd o hn) = n • kummerK3Gram o := by
  rw [kummerK3Gram, kummerK3Gram, interMatrix_smulOdd]
  rfl

/-- **`hsig` IS FALSE.** Reversal (`n = −1`) negates the Gram, and `latticeSig` is odd, so `∀ o` would
force `−16 = 16`. Sylvester, one line. -/
theorem not_forall_latticeSig_neg16 :
    ¬ (∀ o : IntOrientation KummerK3, latticeSig (kummerK3Gram o) = -16) := by
  intro h
  obtain ⟨o⟩ := SKEFTHawking.KummerK3SeamTransport.nonempty_intOrientation_kummerK3_uncond
  have h1 := h o
  have h2 := h (IntOrientation.smulOdd o (⟨-1, by ring⟩ : Odd (-1 : ℤ)))
  rw [kummerK3Gram_smulOdd, neg_one_zsmul, latticeSig_neg, h1] at h2
  omega

/-- **`hgram` IS FALSE** — the K10 span's obligation as published. It implies `pdInput`
(`kummerK3_pdInput_of_gram`), which §1 refutes. -/
theorem not_forall_gram :
    ¬ (∀ o : IntOrientation KummerK3, ∃ (C : IntH2Basis KummerK3top) (hC : C.rank = 22),
        IntCongr (Matrix.reindex (finCongr hC) (finCongr hC)
          (interMatrix (intFundamentalClassOfIntOrientation o) C)) k3Form) :=
  fun h => not_forall_intOrientation_pdInput (kummerK3_pdInput_of_gram h)

/-- **`hk3` on the packaged basis IS FALSE**, for the same reason. -/
theorem not_forall_hk3 : ¬ (∀ o : IntOrientation KummerK3, IntCongr (kummerK3Gram o) k3Form) :=
  fun h => not_forall_intOrientation_pdInput fun o => nonempty_intPD_of_hk3 o (h o)

/-- **`hgeo`, the terminal cap-dual datum, IS FALSE** — its spanning half already delivers `pdInput`
via `nonempty_intPD_of_capDual_span`. This is what refutes the two `KummerK3E1Unconditional`
entry points `…_of_geoData` and `…_of_geoDataEven`, whose *only* hypothesis it is. -/
theorem not_forall_geoData :
    ¬ (∀ o : IntOrientation KummerK3, ∃ (ι : Type) (a : ι → Cohomology KummerK3top 2)
        (c : ι → Homology KummerK3top 2) (_sel : Fin 22 → ι),
        (∀ i, capHInt 2 1 (a i) o.fundClass = c i)
          ∧ Submodule.span ℤ (Set.range c) = ⊤) := by
  intro h
  refine not_forall_intOrientation_pdInput fun o => ?_
  obtain ⟨ι, a, c, _, hcap, hspan⟩ := h o
  exact nonempty_intPD_of_capDual_span o a c hcap hspan

/-! ## §2. The repair — every route re-stated at ONE pinned orientation

Each theorem below is the `∀ o` entry point with the quantifier moved to a supplied argument. None is
refutable by the §1 argument: a single orientation carries no reversal and no rescaling. -/

/-- **THE PINNED E1 ENTRY POINT.** Integral Poincaré duality at ONE orientation *is* the whole E1
atom triple: the orientation is the `orient` field, `kummerK3IntH2Basis` is `B` (unconditional since
`H₁(K3;ℤ) = 0`), and `rank22` is the banked `b₂ = 22`. Compare
`KummerK3SeamTransport.nonempty_kummerK3E1Atoms_of_pd`, whose `∀ o` hypothesis §1 refutes. -/
theorem nonempty_kummerK3E1Atoms_at (o : IntOrientation KummerK3)
    (pd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    Nonempty KummerK3E1Atoms := by
  obtain ⟨pd⟩ := pd
  exact ⟨⟨o, kummerK3IntH2Basis, pd, kummerK3IntH2Basis_rank⟩⟩

/-- **The pinned Gram route** — the replacement for `nonempty_kummerK3E1Atoms_of_hk3`. -/
theorem nonempty_kummerK3E1Atoms_of_hk3_at (o : IntOrientation KummerK3)
    (hk3 : IntCongr (kummerK3Gram o) k3Form) : Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_at o (nonempty_intPD_of_hk3 o hk3)

/-- **The pinned cap-dual route** — the replacement for `…_of_geoData` / `…_of_geoDataEven`. Only the
*spanning* half of the datum is needed for the atoms; the Kronecker table is what the Gram lane
consumes, and is carried separately by `kummerK3_hk3_at`. -/
theorem nonempty_kummerK3E1Atoms_of_capDualSpan_at (o : IntOrientation KummerK3) {ι : Type}
    (a : ι → Cohomology KummerK3top 2) (c : ι → Homology KummerK3top 2)
    (hcap : ∀ i, capHInt 2 1 (a i) o.fundClass = c i)
    (hspan : Submodule.span ℤ (Set.range c) = ⊤) : Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_at o (nonempty_intPD_of_capDual_span o a c hcap hspan)

/-- **The pinned Gram congruence** — `KummerK3E1Unconditional.kummerK3_hk3_holds` fed from the two
geometric halves at the *same single* orientation, with the lattice input already discharged
(`stableNegRank16Two_holds`). The replacement for `kummerK3_gram_of_stable`. -/
theorem kummerK3_hk3_at (o : IntOrientation KummerK3)
    (hpd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ a : Cohomology KummerK3top 2,
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfam : ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
        = kummerSubForm i j) :
    IntCongr (kummerK3Gram o) k3Form := by
  obtain ⟨v, hv⟩ := hfam
  exact kummerK3_hk3_holds o (kummerK3Gram_isEvenUnimodular o hpd heven)
    (kummerK3Gram_latticeSig_of_kummerFamily o v hv)

/-- **The pinned three-input geometric route**, end to end: the `∀ o`-free replacement for
`nonempty_kummerK3E1Atoms_of_geometric`. It also records the honest dependency — `hpd` alone already
produces the atoms, so `heven`/`hfam` earn their place only through the Gram congruence. -/
theorem nonempty_kummerK3E1Atoms_and_hk3_at (o : IntOrientation KummerK3)
    (hpd : Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o)))
    (heven : ∀ a : Cohomology KummerK3top 2,
      (2 : ℤ) ∣ interFormInt (intFundamentalClassOfIntOrientation o) a a)
    (hfam : ∃ v : Fin 22 → Cohomology KummerK3top 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
        = kummerSubForm i j) :
    Nonempty KummerK3E1Atoms ∧ IntCongr (kummerK3Gram o) k3Form :=
  ⟨nonempty_kummerK3E1Atoms_at o hpd, kummerK3_hk3_at o hpd heven hfam⟩

/-! ## §3. The orientation you can actually use — PRIMITIVE, and produced unconditionally

Pinning the quantifier (§2) fixes the *shape*; it does not fix the *datum*. The orientation that
`nonempty_intOrientation_kummerK3_uncond` hands you is an arbitrary inhabitant of a structure that
admits `3 • [K3]`, and integral PD at `3 • [K3]` is FALSE — so "produce `o` from the seam route,
then prove PD at it" was never a viable plan either. `IntOrientationPrimitive` closes that, and at no
cost: the degree-4 producer was already choosing a basis vector. -/

/-- **A PRIMITIVE integral orientation of the welded `K3`, UNCONDITIONALLY.** Same three inputs the
unstrengthened producer used — `H₄(K3;ℤ)` free (`k3_h4_free`) and nontrivial (`nontrivial_h4K3`, from
the seam kernel) on the connected weld — now delivering a fundamental class that is not a proper
multiple. This is the orientation the K3 lane should be pinned to. -/
theorem nonempty_intOrientationPrim_kummerK3_uncond : Nonempty (IntOrientationPrim KummerK3) := by
  haveI := SKEFTHawking.KummerQTopVanish.k3_h4_free
  haveI := SKEFTHawking.KummerK3SeamTransport.nontrivial_h4K3
  exact nonempty_intOrientationPrim_of_free_nontrivial

/-- **E1 atoms from PD at the primitive orientation** — §2's entry point at the datum §3 produces. -/
theorem nonempty_kummerK3E1Atoms_of_prim (op : IntOrientationPrim KummerK3)
    (pd : Nonempty (IntPoincareDuality
      (intFundamentalClassOfIntOrientation op.toIntOrientation))) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_at op.toIntOrientation pd

/-- **The scale attack is dead on the strengthened datum**, concretely at the welded `K3`: `3 • [K3]`
is still a legal `IntOrientation` (that is the defect) but is **not** a legal `IntOrientationPrim`. -/
theorem not_isPrimitiveClass_smulOdd_three (o : IntOrientation KummerK3) :
    ¬ IsPrimitiveClass (IntOrientation.smulOdd o (by decide : Odd (3 : ℤ))).fundClass :=
  not_isPrimitiveClass_smulOdd o _ (by norm_num)

/-- **Reversal negates the packaged Gram.** -/
theorem kummerK3Gram_reverse (o : IntOrientation KummerK3) :
    kummerK3Gram (IntOrientation.reverse o) = - kummerK3Gram o := by
  rw [kummerK3Gram, kummerK3Gram]
  have h : interMatrix (intFundamentalClassOfIntOrientation (IntOrientation.reverse o))
      kummerK3IntH2Basis
        = - interMatrix (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis := by
    ext i j
    simp only [interMatrix, Matrix.of_apply, Matrix.neg_apply, interFormInt_reverse_orientation]
  rw [h]
  rfl

/-- **⛔ THE STRENGTHENING DOES NOT RESCUE SIGN-CARRYING CLAIMS.** `∀ op : IntOrientationPrim`, the
signature statement is *still* false, because reversal lifts to the strengthened structure (as it
must — a closed orientable manifold really has two orientations). Anyone tempted to read §3 as
"`∀ o` is fine again now" should read this: the sign defect is irreducible and `hsig` stays dead. -/
theorem not_forall_intOrientationPrim_latticeSig_neg16 :
    ¬ (∀ op : IntOrientationPrim KummerK3,
        latticeSig (kummerK3Gram op.toIntOrientation) = -16) := by
  intro h
  obtain ⟨op⟩ := nonempty_intOrientationPrim_kummerK3_uncond
  have h1 := h op
  have h2 := h (IntOrientationPrim.reverse op)
  rw [show (IntOrientationPrim.reverse op).toIntOrientation
      = IntOrientation.reverse op.toIntOrientation from rfl,
    kummerK3Gram_reverse, latticeSig_neg, h1] at h2
  omega

/-- **…but unimodularity IS sign-invariant** (`det (−G) = (−1)²² det G = det G`), so — unlike `hsig`
— a `∀ op : IntOrientationPrim` unimodularity claim survives *both* attacks. The scale attack cannot
run on the strengthened datum and the sign attack does not bite. `pdInput` is therefore a **live
target** again once the orientation is primitive, rather than the refuted statement §1 kills. -/
theorem isUnimodular_kummerK3Gram_reverse_iff (o : IntOrientation KummerK3) :
    IsUnimodular (kummerK3Gram (IntOrientation.reverse o)) ↔ IsUnimodular (kummerK3Gram o) := by
  rw [kummerK3Gram_reverse, IsUnimodular, IsUnimodular, Matrix.det_neg]
  norm_num

/-! ## §4. THE PAYOFF — Poincaré duality from the Kummer family AND its index

§3 says the orientation is now the right datum; it does not say how to get PD at it. This section
does, and it removes the last structural obstacle in the K3 lane: `IntersectionDetFullRankFamily`
turns "prove Poincaré duality on the welded `K3`" into an **arithmetic** statement about the
classical Kummer lattice computation, with no PD input anywhere (so the circularity fence
`k3-gram-must-not-use-pdInput-of-gram` is respected).

The numbers line up exactly, which is the whole point: `det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶`, the 16 exceptional
plus 6 descended classes span an index-`2⁸` sublattice, and `2¹⁶ = (2⁸)²`. Either fact alone gives
nothing; together they give unimodularity, hence PD, hence the E1 atoms. -/

/-- **`det kummerSubForm = ±2¹⁶`** — sharpening the banked `kummerSubForm_det_ne_zero` to its value.
`det ⟨−2⟩¹⁶ = (−2)¹⁶ = 2¹⁶` and the `3H` block is unimodular. -/
theorem kummerSubForm_det_eq : kummerSubForm.det = 2 ^ 16 ∨ kummerSubForm.det = -(2 ^ 16) := by
  rw [kummerSubForm, det_blockDiag, negTwoDiag_det]
  rcases torusFourForm_isEvenUnimodular.2.1 with h | h <;> rw [h]
  · left; norm_num
  · right; norm_num

/-- **UNIMODULARITY OF THE WELDED `K3`'s INTERSECTION FORM, from 22 classes and their index.**

The two geometric inputs are exactly the classical Kummer facts: the 16 exceptional `(−2)`-classes
plus the 6 descended `T⁴` classes have Gram `⟨−2⟩¹⁶ ⊕ 3H`, and they span a sublattice of index `2⁸`
(`SETTLED_FORKS: kummer-16-plus-6-geometric-block-is-not-a-basis` — the Kummer half-sums are the
missing `2⁸`). Since `det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ = ±(2⁸)²`, `IntersectionDetFullRankFamily` closes it. -/
theorem isUnimodular_kummerK3Gram_of_kummerFamily_index (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubForm i j)
    (hidx : (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det = 2 ^ 8
        ∨ (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det = -(2 ^ 8)) :
    IsUnimodular (kummerK3Gram o) := by
  have hsq : (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det ^ 2 = 2 ^ 16 := by
    rcases hidx with h | h <;> rw [h] <;> norm_num
  have hne : (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det ≠ 0 := by
    rcases hidx with h | h <;> rw [h] <;> norm_num
  refine isUnimodular_of_family_index (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis
    kummerK3IntH2Basis_rank v kummerSubForm hv hne ?_
  rcases kummerSubForm_det_eq with h | h
  · exact Or.inl (by rw [h, hsq])
  · exact Or.inr (by rw [h, hsq])

/-- **…hence integral Poincaré duality, hence the E1 atom triple.** THE K3 LANE, end to end, from two
statements about 22 explicit classes — no PD assumed anywhere on the way in. -/
theorem nonempty_kummerK3E1Atoms_of_kummerFamily_index (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubForm i j)
    (hidx : (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det = 2 ^ 8
        ∨ (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det = -(2 ^ 8)) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_at o
    (nonempty_intPD_of_kummerK3Gram_isUnimodular o
      (isUnimodular_kummerK3Gram_of_kummerFamily_index o v hv hidx))

/-- **THE INDEX HYPOTHESIS IS FORCED, not an over-ask.** If the welded `K3`'s form is unimodular then
any family with Gram `kummerSubForm` *must* have coordinate determinant `±2⁸`. So §4's second input
is exactly equivalent to what it buys, given the first — it is the geometry, not a convenience. -/
theorem coordMatrix_det_sq_of_isUnimodular (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubForm i j)
    (hu : IsUnimodular (kummerK3Gram o)) :
    (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det ^ 2 = 2 ^ 16 := by
  have hconv := det_family_eq_sq_of_isUnimodular (intFundamentalClassOfIntOrientation o)
    kummerK3IntH2Basis kummerK3IntH2Basis_rank v kummerSubForm hv hu
  have hnn : (0 : ℤ) ≤ (coordMatrix kummerK3IntH2Basis kummerK3IntH2Basis_rank v).det ^ 2 :=
    sq_nonneg _
  rcases kummerSubForm_det_eq with hd | hd <;> rcases hconv with hc | hc <;> rw [hd] at hc <;> omega

/-! ## §5. THE SUPPLY SHAPE — basis-free, and the one a geometer can actually discharge

§4's `hidx` is stated against `kummerK3IntH2Basis`, a `Classical.choice` extraction naming no
geometry: nobody can hand you the coordinates of the 16 exceptional classes in an anonymous basis.
`IntersectionIndexFullRankFamily` removes the basis — `|det P|` **is** the index of the subgroup the
family generates — so the obligation becomes two statements about cup products and subgroups. -/

/-- **THE K3 LANE'S TERMINAL ENTRY POINT.** Everything the welded Kummer `K3` still owes, in one
statement with no chosen basis and no Poincaré-duality input:

1. `hv` — 22 classes (the 16 exceptional `(−2)`-classes + the 6 descended `T⁴` classes) whose cup
   products tabulate `⟨−2⟩¹⁶ ⊕ 3H`;
2. `hli` — they are `ℤ`-independent (the 16-part is already `linearIndependent_excClass_of_block`);
3. `hcard` — they generate a subgroup of **index `2⁸`** (`SETTLED_FORKS:
   kummer-16-plus-6-geometric-block-is-not-a-basis`; the Kummer half-sums are the missing `2⁸`).

`det (⟨−2⟩¹⁶ ⊕ 3H) = ±2¹⁶ = ±(2⁸)²`, so 1+2+3 give unimodularity, hence integral PD at `o`, hence the
E1 atom triple. Note 1 and 3 are *both* needed and neither is implied by the other: a family that
were a basis (index 1) would give `det = ±2¹⁶`, i.e. emphatically not unimodular — which is exactly
right, since the 22 classes alone do not span. -/
theorem nonempty_kummerK3E1Atoms_of_kummerFamily_indexCard (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubForm i j)
    (hli : LinearIndependent ℤ v)
    (hcard : Nat.card (Cohomology KummerK3top 2 ⧸ Submodule.span ℤ (Set.range v)) = 2 ^ 8) :
    Nonempty KummerK3E1Atoms := by
  refine nonempty_kummerK3E1Atoms_at o (nonempty_intPD_of_kummerK3Gram_isUnimodular o ?_)
  refine isUnimodular_of_index_sq (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis
    kummerK3IntH2Basis_rank v kummerSubForm hv hli (by norm_num) hcard ?_
  rcases kummerSubForm_det_eq with h | h
  · exact Or.inl (by rw [h]; push_cast)
  · exact Or.inr (by rw [h]; push_cast)

/-! ## §6. THE SIGN OF THE `⟨−2⟩¹⁶` DIAGONAL IS NOT NEEDED FOR THE E1 ATOMS

The `⟨−2⟩¹⁶` block's open residual was never the *magnitude* `|⟨α_c, E_c⟩| = 2` — that is banked
unconditionally (`KummerPairTubeSeparation.pairCokerEquiv` / `pairCoker_card`, hypothesis-free) — but
the **sign**, which `TubeParity` cannot supply because it is deliberately mod-2.

For the E1 atoms that residual is **vacuous**: §5 runs entirely through `G.det`, and at rank 22 the
determinant cannot see the diagonal's sign. Explicitly, for **any** sign vector `ε : Fin 16 → {±1}`,

    det (⟨2ε⟩¹⁶ ⊕ 3H) = 2¹⁶ · (∏ ε) · det(3H) = ±2¹⁶ = ±(2⁸)²

so the criterion fires identically. The signed value is still needed for the `σ = −16` **Gram
congruence** (`kummerK3_hk3_at`) that other consumers want — signature is very much sign-sensitive —
but it is off the path to integral PD and the atom triple. -/

/-- A `⟨2ε⟩ⁿ` diagonal block — the `⟨−2⟩ⁿ` block with each sign left free. -/
def signedTwoDiag {n : ℕ} (ε : Fin n → ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.diagonal fun c => 2 * ε c

/-- `⟨2ε⟩ⁿ` at the all-`−1` sign vector **is** `⟨−2⟩ⁿ`, so §6 genuinely generalizes §4–§5. -/
theorem signedTwoDiag_neg_one (n : ℕ) : signedTwoDiag (fun _ : Fin n => (-1 : ℤ)) = negTwoDiag n := by
  rw [signedTwoDiag, negTwoDiag]
  norm_num

/-- **`det ⟨2ε⟩ⁿ = ±2ⁿ`, whatever the signs.** -/
theorem signedTwoDiag_det {n : ℕ} (ε : Fin n → ℤ) (hε : ∀ c, ε c = 1 ∨ ε c = -1) :
    (signedTwoDiag ε).det = 2 ^ n ∨ (signedTwoDiag ε).det = -(2 ^ n) := by
  have hprod : (signedTwoDiag ε).det = 2 ^ n * ∏ c, ε c := by
    rw [signedTwoDiag, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hunit : IsUnit (∏ c, ε c) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      fun c _ => Int.isUnit_iff.mpr (hε c)
  rcases Int.isUnit_iff.mp hunit with h | h
  · exact Or.inl (by rw [hprod, h, mul_one])
  · exact Or.inr (by rw [hprod, h, mul_neg_one])

/-- The Kummer sublattice form with the 16 exceptional signs left free. -/
def kummerSubFormSigned (ε : Fin 16 → ℤ) : Matrix (Fin 22) (Fin 22) ℤ :=
  SKEFTHawking.SpinSigmaRoute.blockDiag (signedTwoDiag ε) torusFourForm

@[simp] theorem kummerSubFormSigned_neg_one :
    kummerSubFormSigned (fun _ => (-1 : ℤ)) = kummerSubForm := by
  rw [kummerSubFormSigned, kummerSubForm, signedTwoDiag_neg_one]

/-- **`det (⟨2ε⟩¹⁶ ⊕ 3H) = ±2¹⁶` for every sign vector** — the whole point of §6. -/
theorem kummerSubFormSigned_det (ε : Fin 16 → ℤ) (hε : ∀ c, ε c = 1 ∨ ε c = -1) :
    (kummerSubFormSigned ε).det = 2 ^ 16 ∨ (kummerSubFormSigned ε).det = -(2 ^ 16) := by
  rw [kummerSubFormSigned, det_blockDiag]
  rcases signedTwoDiag_det ε hε with hd | hd <;>
    rcases torusFourForm_isEvenUnimodular.2.1 with ht | ht <;> rw [hd, ht]
  · left; norm_num
  · right; norm_num
  · right; norm_num
  · left; norm_num

/-- **THE SIGN-FREE TERMINAL.** The E1 atom triple from 22 classes whose Gram is `⟨2ε⟩¹⁶ ⊕ 3H` for an
*arbitrary* sign vector, plus independence and index `2⁸`. Strictly weaker than §5's hypothesis
(`kummerSubFormSigned_neg_one` shows §5 is the case `ε ≡ −1`), same conclusion — so the open signed
`−2` diagonal is **not** on the path to the atoms; only `|⟨α_c, E_c⟩| = 2`, which is banked, is. -/
theorem nonempty_kummerK3E1Atoms_of_signedKummerFamily (o : IntOrientation KummerK3)
    (ε : Fin 16 → ℤ) (hε : ∀ c, ε c = 1 ∨ ε c = -1)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubFormSigned ε i j)
    (hli : LinearIndependent ℤ v)
    (hcard : Nat.card (Cohomology KummerK3top 2 ⧸ Submodule.span ℤ (Set.range v)) = 2 ^ 8) :
    Nonempty KummerK3E1Atoms := by
  refine nonempty_kummerK3E1Atoms_at o (nonempty_intPD_of_kummerK3Gram_isUnimodular o ?_)
  refine isUnimodular_of_index_sq (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis
    kummerK3IntH2Basis_rank v (kummerSubFormSigned ε) hv hli (by norm_num) hcard ?_
  rcases kummerSubFormSigned_det ε hε with h | h
  · exact Or.inl (by rw [h]; push_cast)
  · exact Or.inr (by rw [h]; push_cast)

/-! ## §7. ⚠ THE TORUS BLOCK IS PROBABLY **DOUBLED**, AND THEN THE INDEX IS `2¹¹`, NOT `2⁸`

A diligence check on §5/§6's numbers, run before building the index fact rather than after.

`kummerSubForm`'s torus block is `torusFourForm`, and the banked Gram
`interMatrix_t4_intCongr_torusFourForm` computes it **on `T⁴` itself** — the notebook already flags
that it is *not* descended to `Q = T⁴°/τ` or to the weld. Descending should not be free: `π : T⁴° → Q`
is a degree-2 quotient, `π_*π^* = 2`, and `τ` acts trivially on `H₂(T⁴)` (it is `(−1)⁴`), so

    π_*α · π_*β = 2 (α · β),

i.e. the descended six classes carry `3H(2)`, not `3H`. The arithmetic then moves too:
`det (⟨2ε⟩¹⁶ ⊕ 3H(2)) = ±2¹⁶ · (−4)³ = ±2²²`, so the index is `2¹¹`, not `2⁸` — and `2¹¹ = 2⁵ · 2⁶`
is exactly the classical factorization (`[K : Π] = 2⁵` for the Kummer lattice over the span of the
sixteen `e_i`, times `2⁶` for the whole thing inside `H₂(K3;ℤ)`).

⚠ **Status of that identification: lead-derived from the covering-degree argument and cross-checked
against the index arithmetic; NOT verified against a primary source in this session.** So this
section does not *replace* §6 — it ships the general form plus BOTH instantiations, and the
`2⁸` reading stays available and consistent for its own family (16 mutually orthogonal roots inside
`2(−E₈)` together with the `3H` summand really do have Gram `⟨−2⟩¹⁶ ⊕ 3H` and index `2⁸`; that family
is simply *not* the geometric 16+6). Whichever normalization the geometry actually delivers, the
terminal below accepts it. -/

/-- **THE GENERAL K3 TERMINAL.** Gram `G`, index `k`, side condition `det G = ±k²`. Every numeric
reading of the Kummer lattice — `(⟨−2⟩¹⁶ ⊕ 3H, 2⁸)`, `(⟨−2⟩¹⁶ ⊕ 3H(2), 2¹¹)`, or any other — is an
instantiation, so a later correction to the normalization costs a `norm_num`, not a redesign. -/
theorem nonempty_kummerK3E1Atoms_of_family_index (o : IntOrientation KummerK3)
    (v : Fin 22 → Cohomology KummerK3top 2) (G : Matrix (Fin 22) (Fin 22) ℤ)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
    (hli : LinearIndependent ℤ v) {k : ℕ} (hk : k ≠ 0)
    (hcard : Nat.card (Cohomology KummerK3top 2 ⧸ Submodule.span ℤ (Set.range v)) = k)
    (hdet : G.det = ((k : ℤ)) ^ 2 ∨ G.det = - ((k : ℤ)) ^ 2) :
    Nonempty KummerK3E1Atoms :=
  nonempty_kummerK3E1Atoms_at o (nonempty_intPD_of_kummerK3Gram_isUnimodular o
    (isUnimodular_of_index_sq (intFundamentalClassOfIntOrientation o) kummerK3IntH2Basis
      kummerK3IntH2Basis_rank v G hv hli hk hcard hdet))

/-- The Kummer sublattice form with the torus block **doubled** — the descended-`π_*` normalization. -/
def kummerSubFormGeo (ε : Fin 16 → ℤ) : Matrix (Fin 22) (Fin 22) ℤ :=
  SKEFTHawking.SpinSigmaRoute.blockDiag (signedTwoDiag ε) ((2 : ℤ) • torusFourForm)

/-- **`det (⟨2ε⟩¹⁶ ⊕ 3H(2)) = ±2²²`** — `det (2 • A) = 2⁶ det A` on a rank-6 block. -/
theorem kummerSubFormGeo_det (ε : Fin 16 → ℤ) (hε : ∀ c, ε c = 1 ∨ ε c = -1) :
    (kummerSubFormGeo ε).det = 2 ^ 22 ∨ (kummerSubFormGeo ε).det = -(2 ^ 22) := by
  rw [kummerSubFormGeo, det_blockDiag, Matrix.det_smul, Fintype.card_fin]
  rcases signedTwoDiag_det ε hε with hd | hd <;>
    rcases torusFourForm_isEvenUnimodular.2.1 with ht | ht <;> rw [hd, ht]
  · left; norm_num
  · right; norm_num
  · right; norm_num
  · left; norm_num

/-- **THE GEOMETRIC-NORMALIZATION TERMINAL** — Gram `⟨2ε⟩¹⁶ ⊕ 3H(2)` at index `2¹¹`. Same three
inputs as §6, with the two numbers that the descended torus block moves. -/
theorem nonempty_kummerK3E1Atoms_of_geoKummerFamily (o : IntOrientation KummerK3)
    (ε : Fin 16 → ℤ) (hε : ∀ c, ε c = 1 ∨ ε c = -1)
    (v : Fin 22 → Cohomology KummerK3top 2)
    (hv : ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j)
      = kummerSubFormGeo ε i j)
    (hli : LinearIndependent ℤ v)
    (hcard : Nat.card (Cohomology KummerK3top 2 ⧸ Submodule.span ℤ (Set.range v)) = 2 ^ 11) :
    Nonempty KummerK3E1Atoms := by
  refine nonempty_kummerK3E1Atoms_of_family_index o v (kummerSubFormGeo ε) hv hli
    (by norm_num) hcard ?_
  rcases kummerSubFormGeo_det ε hε with h | h
  · exact Or.inl (by rw [h]; push_cast)
  · exact Or.inr (by rw [h]; push_cast)

end

end SKEFTHawking.KummerK3E1Repair
