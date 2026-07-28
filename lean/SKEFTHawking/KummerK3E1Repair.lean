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

end

end SKEFTHawking.KummerK3E1Repair
