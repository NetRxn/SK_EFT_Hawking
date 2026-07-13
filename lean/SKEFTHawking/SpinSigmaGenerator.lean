/-
# Phase 5q.H (N1a / N5) — the K3 lattice, and `hg`'s arithmetic discharged

The σ-route door (`SpinSigmaRouteDoor` / `SpinSigmaRouteWitness`) consumes the generator witness
`hg : R.sig (DataBordismGrp.mk ξ g) = -16` (the `Ω₄^{Spin} ≅ ℤ` generator, K3 with σ = −16) as a
disclosed input. Its honest residual (documented in `SpinSigmaRouteWitness.lean`): `hg` is NOT
kernel-pure dischargeable for an *abstract* presentation `R` — an abstract `SpinSigmaPresentation`
carries no σ = −16 class, and building a synthetic one is the settled-dead
`synthetic-smith-map-to-tied-carrier` / `synthetic-grade-ker-bot-nogo` framing (deliberately NOT
attempted here).

**What this module DOES discharge (kernel-pure).** `hg` factors through `R.sig_eq` into an
*arithmetic* half and a *geometric* half:

    R.sig [g] = latticeSig (R.form g)            (sig_eq — the presentation computes σ)

so `hg` ⟺ `latticeSig (R.form g) = −16`. The arithmetic target — the signature of the K3
intersection lattice `II(K3) = 2·(−E₈) ⊕ 3·H` — is built and certified here from the in-tree E₈ /
hyperbolic substrate, with NO geometry and NO `native_decide`:

* `blockDiag` + `latticeSig_blockDiag` + `isEvenUnimodular_blockDiag` — the block-diagonal engine
  (`σ(A ⊕ B) = σ(A) + σ(B)`, even-unimodularity preserved), reusing `LatticeSigBlock`;
* `k3Form` — the rank-22 K3 lattice `2·(−E8lit) ⊕ 3·Hyp`;
* `k3Form_latticeSig : latticeSig k3Form = -16` — the K3 signature, from `neg_e8lit_latticeSig` and
  `hyp_latticeSig` via block additivity (Milnor–Husemoller normal form of `II(K3)`);
* `k3Form_isEvenUnimodular` — `k3Form` is a genuine even unimodular (hence spin) intersection form.

**The reduction.** `sig_neg16_of_form_latticeSig_neg16` reduces `hg` to
`latticeSig (R.form g) = −16`; `latticeSig_eq_neg16_of_congr_k3` grounds that concretely (any rank-22
form `IntCongr` to `k3Form` has signature −16). The **minimal irreducible geometric residual** left is
exactly: *a genuine spin structured 4-manifold `g : StrMfd ξ` whose intersection form
(E1's `interMatrix` Gram matrix) realizes the K3 lattice `k3Form`* — i.e. K3's smooth realization (DR
route `Omega4Spin_Z_formalization_route_20260706.md` §5: the abstract even-form generator, K3's
Kähler/Freedman existence being the sole geometric input). The `door_via_k3_generator` capstone
re-expresses the σ-route door taking this lattice residual (`hform`) in place of the abstract `hg`,
so the two remaining geometric residuals are named at finest grain: the K3 realization (`hform`) and
the forgetful bridge `F [g] = g8` (`himg`, E3's N1b), alongside `hexact` (the completeness key).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SpinSigmaRoute
import SKEFTHawking.SpinSigmaRouteDoor
import SKEFTHawking.SpinSigmaRouteWitness
import SKEFTHawking.PinPlusGMWitness
import SKEFTHawking.E8Signature
import SKEFTHawking.LatticeSigBlock
import SKEFTHawking.HyperbolicNormalForm
import SKEFTHawking.ThetaDefiniteDischarge

namespace SKEFTHawking.SpinSigmaRoute

open scoped Manifold
open Matrix
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMTiedData SKEFTHawking.GuillouMarin
open SKEFTHawking.PinPlusGMWitness

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {ξ : TangentialData X k I}

universe u

/-! ### The block-diagonal engine (reindexed to `Fin (na + nb)`) -/

/-- The **block-diagonal sum** of two integer forms, reindexed to `Fin (na + nb)` so it lands in the
`latticeSig` (`Fin n`) world. `A ⊕ B` with zero off-diagonal blocks. -/
noncomputable def blockDiag {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) : Matrix (Fin (na + nb)) (Fin (na + nb)) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

theorem blockDiag_def {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) :
    blockDiag A B = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := rfl

/-- **Block additivity of the signature:** `σ(A ⊕ B) = σ(A) + σ(B)` for even unimodular blocks
(nondegenerate, so `latticeSigOf_fromBlocks` applies). -/
theorem latticeSig_blockDiag {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B) :
    latticeSig (blockDiag A B) = latticeSig A + latticeSig B := by
  rw [← latticeSigOf_fin, blockDiag_def, latticeSigOf_reindex,
    latticeSigOf_fromBlocks _ _ hA.radical_eq_bot hB.radical_eq_bot,
    latticeSigOf_fin, latticeSigOf_fin]

/-- **Even-unimodularity is preserved by block-diagonal sums.** Symmetry, `det = det A · det B = ±1`,
and even diagonal all pass through `fromBlocks` + `reindex`. -/
theorem isEvenUnimodular_blockDiag {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ) (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B) :
    IsEvenUnimodular (blockDiag A B) := by
  obtain ⟨hsymA, hdetA, hevenA⟩ := hA
  obtain ⟨hsymB, hdetB, hevenB⟩ := hB
  refine ⟨?_, ?_, ?_⟩
  · show (blockDiag A B)ᵀ = blockDiag A B
    rw [blockDiag_def, Matrix.reindex_apply, Matrix.transpose_submatrix,
      Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero, hsymA, hsymB]
  · have hdet : (blockDiag A B).det = A.det * B.det := by
      rw [blockDiag_def, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    show (blockDiag A B).det = 1 ∨ (blockDiag A B).det = -1
    rw [hdet]
    rcases hdetA with h1 | h1 <;> rcases hdetB with h2 | h2 <;> rw [h1, h2] <;> norm_num
  · intro i
    rw [blockDiag_def, Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with j | j
    · exact hevenA j
    · exact hevenB j

/-! ### The K3 intersection lattice `II(K3) = 2·(−E₈) ⊕ 3·H` -/

/-- The even unimodular `−E₈` block (`E8lit(−1)`, signature `−8`). -/
theorem isEvenUnimodular_negE8 : IsEvenUnimodular (-E8lit) :=
  isEvenUnimodular_neg E8lit e8lit_even_unimodular

/-- The hyperbolic plane `H` is even unimodular. -/
theorem isEvenUnimodular_hyp : IsEvenUnimodular Hyp :=
  ⟨hyp_symm, hyp_unimodular, hyp_even⟩

/-- **The K3 intersection lattice** `II(K3) = (−E₈) ⊕ (−E₈) ⊕ H ⊕ H ⊕ H` (rank 22). The concrete even
unimodular integer form of signature `−16` that a genuine K3 structured manifold's intersection form
realizes. -/
noncomputable def k3Form : Matrix (Fin 22) (Fin 22) ℤ :=
  blockDiag (blockDiag (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) Hyp

/-- **`k3Form` is even unimodular** — a genuine (spin) intersection form. -/
theorem k3Form_isEvenUnimodular : IsEvenUnimodular k3Form := by
  have h16 : IsEvenUnimodular (blockDiag (-E8lit) (-E8lit)) :=
    isEvenUnimodular_blockDiag _ _ isEvenUnimodular_negE8 isEvenUnimodular_negE8
  have h18 : IsEvenUnimodular (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) :=
    isEvenUnimodular_blockDiag _ _ h16 isEvenUnimodular_hyp
  have h20 : IsEvenUnimodular (blockDiag (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) :=
    isEvenUnimodular_blockDiag _ _ h18 isEvenUnimodular_hyp
  exact isEvenUnimodular_blockDiag _ _ h20 isEvenUnimodular_hyp

/-- **`latticeSig k3Form = −16`** — the K3 signature, computed from `σ(−E₈) = −8` and `σ(H) = 0` via
block additivity (Milnor–Husemoller normal form of `II(K3)`). Kernel-pure; no `native_decide` on the
22×22 matrix. This is the arithmetic content of the `Ω₄^{Spin} ≅ ℤ` generator's `σ = −16`. -/
theorem k3Form_latticeSig : latticeSig k3Form = -16 := by
  have h16 : IsEvenUnimodular (blockDiag (-E8lit) (-E8lit)) :=
    isEvenUnimodular_blockDiag _ _ isEvenUnimodular_negE8 isEvenUnimodular_negE8
  have h18 : IsEvenUnimodular (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) :=
    isEvenUnimodular_blockDiag _ _ h16 isEvenUnimodular_hyp
  have h20 : IsEvenUnimodular (blockDiag (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) :=
    isEvenUnimodular_blockDiag _ _ h18 isEvenUnimodular_hyp
  show latticeSig (blockDiag (blockDiag (blockDiag (blockDiag (-E8lit) (-E8lit)) Hyp) Hyp) Hyp) = -16
  rw [latticeSig_blockDiag _ _ h20 isEvenUnimodular_hyp,
    latticeSig_blockDiag _ _ h18 isEvenUnimodular_hyp,
    latticeSig_blockDiag _ _ h16 isEvenUnimodular_hyp,
    latticeSig_blockDiag _ _ isEvenUnimodular_negE8 isEvenUnimodular_negE8,
    neg_e8lit_latticeSig, hyp_latticeSig]
  norm_num

/-! ### `hg` reduced to its geometric residual -/

/-- **`hg` ⟺ the intersection form of some structured manifold has signature `−16`** (immediate via
`sig_eq`): the abstract generator hypothesis is exactly a lattice statement about `R.form`. -/
theorem exists_sig_neg16_iff_exists_form_latticeSig_neg16 (R : SpinSigmaPresentation ξ) :
    (∃ g : StrMfd ξ, R.sig (DataBordismGrp.mk ξ g) = -16) ↔
      (∃ g : StrMfd ξ, latticeSig (R.form g) = -16) := by
  simp_rw [R.sig_eq]

/-- **`hg` from the form signature** — a structured manifold whose intersection form has signature
`−16` witnesses `hg`. The ARITHMETIC half of `hg`, isolated: the residual is now purely
`latticeSig (R.form g) = −16` (a lattice condition on the E1 Gram matrix), NO abstract σ. -/
theorem sig_neg16_of_form_latticeSig_neg16 (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hform : latticeSig (R.form g) = -16) : R.sig (DataBordismGrp.mk ξ g) = -16 := by
  rw [R.sig_eq]; exact hform

/-- **Any rank-22 form congruent to the K3 lattice has signature `−16`** — grounds the residual
concretely on `k3Form`. A genuine K3 structured manifold's intersection form is `IntCongr` to `k3Form`
(Milnor–Husemoller: `II(K3)` is the unique even unimodular form of rank 22, signature −16), so this
discharges the arithmetic of `hg` for it. -/
theorem latticeSig_eq_neg16_of_congr_k3 (M : Matrix (Fin 22) (Fin 22) ℤ)
    (hcong : IntCongr M k3Form) : latticeSig M = -16 := by
  rw [← hcong.latticeSig, k3Form_latticeSig]

/-- **`hg` from K3's lattice realization** — the maximally-faithful geometric residual: a rank-22
structured manifold whose intersection form is `IntCongr` to the K3 lattice `k3Form` has class
signature `−16`. The rank-22 `Fin`-transport is handled once (reindex-invariance of the signature),
so the residual for downstream is exactly "`g`'s intersection form realizes `II(K3)`". -/
theorem sig_neg16_of_form_congr_k3 (R : SpinSigmaPresentation ξ) (g : StrMfd ξ)
    (hr : R.rank g = 22)
    (hcong : IntCongr (Matrix.reindex (finCongr hr) (finCongr hr) (R.form g)) k3Form) :
    R.sig (DataBordismGrp.mk ξ g) = -16 := by
  rw [R.sig_eq]
  have h1 : latticeSig (Matrix.reindex (finCongr hr) (finCongr hr) (R.form g)) = -16 :=
    latticeSig_eq_neg16_of_congr_k3 _ hcong
  rwa [← latticeSigOf_fin, latticeSigOf_reindex, latticeSigOf_fin] at h1

/-! ### The σ-route door taking the lattice residual in place of the abstract `hg` -/

/-- **The σ-route door with `hg`'s arithmetic discharged.** The witness door
`omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_g8` re-expressed to consume the *lattice* residual
`hform : latticeSig (R.form g) = −16` (grounded on the certified `k3Form`) in place of the abstract
`hg : R.sig [g] = −16`. Given the two N1a freezes, Rokhlin `16 ∣ σ`, the forgetful `F` with the bridge
`F [g] = g8` (K3 forgets to the grade-8 Kummer class), and the KT §5 exactness `hexact`, the tied GM
carrier is `≃+ ZMod 16`. The remaining geometric residuals are now named at finest grain:
* `hform` — K3's smooth realization (a structured spin 4-mfd whose intersection form has σ = −16;
  concretely `IntCongr (R.form g) k3Form`, `latticeSig k3Form = −16` proven);
* `himg` — the forgetful bridge `F [g] = g8` (E3's N1b geometric Smith transport);
* `hexact` — the KT §5 completeness key (apex-equivalent to `hbound`/`hthom`). -/
theorem door_via_k3_generator (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts)
    (hB : R.SphereProductBounds) (g : StrMfd ξ) (hform : latticeSig (R.form g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (himg : F (DataBordismGrp.mk ξ g) = g8)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
        = (forgetGen F g).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_g8 R hA hB g
    (sig_neg16_of_form_latticeSig_neg16 R g hform) hdvd F himg hexact

/-- **The σ-route door taking K3's lattice realization directly** — the fully-decomposed capstone with
`hg` replaced by the sharpest geometric residual: a rank-22 structured spin manifold `g` whose
intersection form `IntCongr`s to the K3 lattice `k3Form`. The arithmetic (`σ(k3Form) = −16`) is
discharged; the remaining inputs are exactly the three named geometric residuals — the K3 realization
(`hr`+`hcong`), the forgetful bridge `F [g] = g8` (`himg`), and the KT §5 exactness (`hexact`). -/
theorem door_via_k3_realization (R : SpinSigmaPresentation ξ) (hA : R.RealizesSphereProducts)
    (hB : R.SphereProductBounds) (g : StrMfd ξ) (hr : R.rank g = 22)
    (hcong : IntCongr (Matrix.reindex (finCongr hr) (finCongr hr) (R.form g)) k3Form)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (F : DataBordismGrp ξ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (himg : F (DataBordismGrp.mk ξ g) = g8)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
        = (forgetGen F g).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_via_sigma_route_g8 R hA hB g
    (sig_neg16_of_form_congr_k3 R g hr hcong) hdvd F himg hexact

end SKEFTHawking.SpinSigmaRoute
