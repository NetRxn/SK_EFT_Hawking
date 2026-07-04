/-
# Phase 5q.H · E1 — the EVENNESS conjunct of `IsEvenUnimodular interMatrix` via ℤ→ℤ/2 Wu

Substrate-G foundation brick. Discharges the **even** conjunct of `AlgebraicRokhlin.IsEvenUnimodular
(interMatrix fc B)` — one of the three conjuncts (`symmetric ∧ unimodular ∧ even`) the DONE lattice
`σ÷16` leg consumes. The `symmetric` conjunct is already discharged upstream
(`IntersectionMatrixInt.interMatrix_isSymmetricInt`); `unimodular` (Poincaré duality) is a SEPARATE,
harder community-scale core (NOT this brick).

## The idea (standard: evenness = mod-2 Wu)

For `a : H²(M;ℤ)`, the diagonal `interFormInt fc a a = ⟨a ∪ a, [M]⟩ ∈ ℤ`. Reduce mod 2 through the
**ℤ→ℤ/2 reduction bridge** `redH : H²(M;ℤ) →+ H²(M;ℤ/2)` (integral cochains reduced pointwise by
`Int.cast : ℤ → ZMod 2`). The bridge is a genuine construction — both models are functions on the SAME
singular simplices; the only difference is base ring + the alternating signs `(-1)^i`, which reduce to
`1` in char 2 (`(-1 : ZMod 2) = 1`), matching the mod-2 file's unsigned coboundary. So the reduced
diagonal is `⟨(redH a) ∪ (redH a), [M]₂⟩ = ⟨Sq²(redH a), [M]₂⟩` (top square on H² is `Sq²`), which by
the singular Wu relation is `⟨v₂ ∪ (redH a), [M]₂⟩`. When the manifold's `w₂ = 0` (Spin) — an oriented
4-manifold has `v₁ = 0` so `w₂ = v₂`, hence `v₂ = 0` — this is `0`. Therefore `interFormInt fc a a`
is even (`2 ∣ ⟨a∪a,[M]⟩`), i.e. `interMatrix` is EVEN.

The `w₂ = 0` datum enters as a disclosed structure field (NOT an axiom), packaged as the vanishing of
the mod-2 Wu functional `y ↦ ⟨Sq²(y), [M]₂⟩` on `H²(M;ℤ/2)` (which is exactly `v₂ = 0` ⟺ Spin),
together with the compatibility `fc.eval ≡ μ₂ ∘ redH mod 2` tying the integral fundamental class to the
mod-2 one. Registered in `HYPOTHESIS_REGISTRY` as `spinWu_even_datum`.

All proofs kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCupInt
import SKEFTHawking.SingularIntersectionFormInt
import SKEFTHawking.IntersectionMatrixInt
import SKEFTHawking.SingularCohomologyMod2
import SKEFTHawking.PoincareDualityWu
import SKEFTHawking.AlgebraicRokhlin

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking SKEFTHawking.SingularCohomologyInt

variable {X : TopCat}

/-! ## §1. The ℤ→ℤ/2 reduction bridge on cochains -/

/-- **Pointwise mod-2 reduction of integral cochains**, `SingularCochainInt X n → SingularCochain X n`,
`(redC f)(σ) = (f σ : ZMod 2)` — the integer cochain reduced mod 2 (both are functions on the SAME
singular simplices). -/
noncomputable def redC (X : TopCat) (n : ℕ) (f : SingularCochainInt X n) :
    SKEFTHawking.SingularCohomologyMod2.SingularCochain X n :=
  fun σ => (f σ : ZMod 2)

@[simp] theorem redC_apply (X : TopCat) (n : ℕ) (f : SingularCochainInt X n)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    redC X n f σ = (f σ : ZMod 2) := rfl

/-- `redC` is `ℤ`-linear (with the `ZMod 2`-module viewed as a `ℤ`-module by restriction of scalars):
it is additive and commutes with integer scaling via `Int.cast` being a ring hom. -/
theorem redC_add (X : TopCat) (n : ℕ) (f g : SingularCochainInt X n) :
    redC X n (f + g) = redC X n f + redC X n g := by
  funext σ
  simp [redC_apply, Pi.add_apply]

/-- **The two `face` operations agree** — the integral-model `face` and the mod-2-model `face` are the
same simplicial operation (both `= (TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ`). -/
theorem face_eq {n : ℕ} (i : Fin (n + 2))
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    face i σ = SKEFTHawking.SingularCohomologyMod2.face i σ := rfl

/-- **The reduction bridge commutes with the coboundary** (cochain level): reducing the signed integral
coboundary mod 2 gives the mod-2 unsigned coboundary. The alternating signs `(-1)^i` reduce to `1` in
char 2, so the signed integer sum reduces to the mod-2 file's plain sum over the faces. -/
theorem redC_coboundary (X : TopCat) (n : ℕ) (f : SingularCochainInt X n) :
    redC X (n + 1) (coboundary X n f)
      = SKEFTHawking.SingularCohomologyMod2.coboundary X n (redC X n f) := by
  funext σ
  simp only [redC_apply, coboundary_apply, SingularCohomologyMod2.coboundary_apply, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    show (-1 : ZMod 2) = 1 from by decide, one_pow, one_mul, face_eq]

/-- **The two `frontFace` operations agree** across the ℤ and ℤ/2 models. -/
theorem frontFace_eq {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    frontFace σ = SKEFTHawking.SingularCohomologyMod2.frontFace (p := p) (q := q) σ := rfl

/-- **The two `backFace` operations agree** across the ℤ and ℤ/2 models. -/
theorem backFace_eq {p q : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (p + q)))) :
    backFace σ = SKEFTHawking.SingularCohomologyMod2.backFace (p := p) (q := q) σ := rfl

/-- **The reduction bridge commutes with the cup product** (cochain level, Alexander–Whitney): the
integral cup `(f ∪ g)(σ) = f(front σ) · g(back σ)` reduces mod 2 to the mod-2 cup of the reductions,
since `Int.cast` is a ring hom and the front/back faces agree across models. -/
theorem redC_cup {p q : ℕ} (f : SingularCochainInt X p) (g : SingularCochainInt X q) :
    redC X (p + q) (cup f g)
      = SKEFTHawking.SingularCohomologyMod2.cup (redC X p f) (redC X q g) := by
  funext σ
  simp only [redC_apply, cup_apply, SingularCohomologyMod2.cup_apply, Int.cast_mul,
    frontFace_eq, backFace_eq]

/-- `redC` as a genuine `ℤ`-linear map `SingularCochainInt X n →ₗ[ℤ] SingularCochain X n`
(the mod-2 target is a `ℤ`-module by restriction of scalars along `ℤ → ZMod 2`). Additive by
`redC_add`; commutes with integer scaling since `Int.cast` respects `ℤ`-scalar multiplication on
`ZMod 2`-valued functions. -/
noncomputable def redCₗ (X : TopCat) (n : ℕ) :
    SingularCochainInt X n →ₗ[ℤ] SKEFTHawking.SingularCohomologyMod2.SingularCochain X n where
  toFun := redC X n
  map_add' := redC_add X n
  map_smul' c f := by
    funext σ
    show ((c • f) σ : ZMod 2) = ((c • redC X n f) σ)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, redC_apply, Int.cast_mul, ← zsmul_eq_mul]

@[simp] theorem redCₗ_apply (X : TopCat) (n : ℕ) (f : SingularCochainInt X n) :
    redCₗ X n f = redC X n f := rfl

/-! ## §2. Descent to cohomology: the reduction bridge `redH : H*(X;ℤ) →ₗ H*(X;ℤ/2)` -/

/-- `redCₗ` sends an integral cocycle to a mod-2 cocycle: `δ(redC z) = redC(δ z) = redC 0 = 0`
(well-defined by `redC_coboundary`). -/
theorem redC_mem_ker (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n)) :
    redC X n (z : SingularCochainInt X n)
      ∈ LinearMap.ker (SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n) := by
  rw [LinearMap.mem_ker]
  have hf0 : coboundary X n (z : SingularCochainInt X n) = 0 := LinearMap.mem_ker.mp z.2
  show SKEFTHawking.SingularCohomologyMod2.coboundary X n
      (redC X n (z : SingularCochainInt X n)) = 0
  rw [← redC_coboundary, hf0]
  funext σ
  simp [redC]

/-- `redCₗ` carries integral cocycles to mod-2 cocycles: `ker δⁿ_ℤ →ₗ ker δⁿ_{ℤ/2}`. -/
noncomputable def redKer (X : TopCat) (n : ℕ) :
    (LinearMap.ker (coboundaryₗ X n)) →ₗ[ℤ]
      (LinearMap.ker (SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n)) where
  toFun z := ⟨redC X n (z : SingularCochainInt X n), redC_mem_ker X n z⟩
  map_add' z w := by
    apply Subtype.ext
    show redC X n ((z : SingularCochainInt X n) + w) = redC X n z + redC X n w
    exact redC_add X n _ _
  map_smul' c z := by
    apply Subtype.ext
    show redC X n (c • (z : SingularCochainInt X n)) = c • redC X n (z : SingularCochainInt X n)
    exact (redCₗ X n).map_smul c (z : SingularCochainInt X n)

@[simp] theorem redKer_coe (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n)) :
    ((redKer X n z : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n))
      = redC X n (z : SingularCochainInt X n) := rfl

/-- `redKer` maps an integral coboundary to a mod-2 coboundary (a coboundary `z = δ w` reduces to
`redC z = δ(redC w)` by `redC_coboundary`), so the reduction descends to the quotient cohomology. -/
theorem redKer_mem_coboundary (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n))
    (hz : (z : SingularCochainInt X n) ∈ coboundaryRange X n) :
    (redKer X n z : SKEFTHawking.SingularCohomologyMod2.SingularCochain X n)
      ∈ SKEFTHawking.SingularCohomologyMod2.coboundaryRange X n := by
  cases n with
  | zero =>
    rw [show coboundaryRange X 0 = ⊥ from rfl, Submodule.mem_bot] at hz
    rw [show SKEFTHawking.SingularCohomologyMod2.coboundaryRange X 0 = ⊥ from rfl,
      Submodule.mem_bot]
    show redC X 0 (z : SingularCochainInt X 0) = 0
    rw [hz]; funext σ; simp [redC]
  | succ m =>
    obtain ⟨w, hw⟩ := hz
    refine ⟨redC X m w, ?_⟩
    show SKEFTHawking.SingularCohomologyMod2.coboundary X m (redC X m w)
      = redC X (m + 1) (z : SingularCochainInt X (m + 1))
    rw [← redC_coboundary]
    show redC X (m + 1) (coboundary X m w) = redC X (m + 1) (z : SingularCochainInt X (m + 1))
    exact congrArg (redC X (m + 1)) hw

/-- **The ℤ→ℤ/2 reduction bridge on cohomology** `redH : Hⁿ(X;ℤ) →ₗ[ℤ] Hⁿ(X;ℤ/2)`. Descends the cochain
reduction `redC` (pointwise `Int.cast`) to cohomology classes: `redH [z] = [redC z]`. This is the
genuine map connecting the from-scratch integral cohomology `SingularCohomologyInt.Cohomology` to the
on-main mod-2 Wu substrate `SingularCohomologyMod2.Cohomology`. It is `ℤ`-linear (the mod-2 codomain is
a `ℤ`-module by restriction of scalars along `ℤ → ZMod 2`); the two cochain complexes are the SAME
functions on singular simplices, so the reduction is genuine and its `mk`-rule holds by `rfl`. -/
noncomputable def redH (X : TopCat) (n : ℕ) :
    Cohomology X n →ₗ[ℤ] SKEFTHawking.SingularCohomologyMod2.Cohomology X n :=
  Submodule.liftQ _
    (((SKEFTHawking.SingularCohomologyMod2.coboundaryRange X n).submoduleOf
        (LinearMap.ker (SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n))).mkQ.restrictScalars ℤ
      ∘ₗ (redKer X n))
    (by
      intro z hz
      rw [LinearMap.mem_ker, LinearMap.comp_apply]
      show ((SKEFTHawking.SingularCohomologyMod2.coboundaryRange X n).submoduleOf
        (LinearMap.ker (SKEFTHawking.SingularCohomologyMod2.coboundaryₗ X n))).mkQ
          (redKer X n z) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
      apply redKer_mem_coboundary X n z
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hz
      exact hz)

/-- **`redH [z] = [redC z]`** — the reduction bridge on a cohomology class is the class of the reduced
cocycle. The computation rule that makes `redH` concrete. -/
@[simp] theorem redH_mk (X : TopCat) (n : ℕ) (z : LinearMap.ker (coboundaryₗ X n)) :
    redH X n (Cohomology.mk X n z)
      = SKEFTHawking.SingularCohomologyMod2.Cohomology.mk X n (redKer X n z) :=
  rfl

/-- **The reduction bridge commutes with the cup product `H²×H²→H⁴`**:
`redH (a ∪ b) = (redH a) ∪ (redH b)`. Descends the cochain-level `redC_cup` (Alexander–Whitney is the
same simplicial formula in both models; `Int.cast` is a ring hom). This is the load-bearing cohomology
compatibility that lets the integral diagonal `⟨a∪a,[M]⟩` be computed in the mod-2 Wu substrate. -/
theorem redH_cupH24 (a b : Cohomology X 2) :
    redH X 4 (cupH24 a b)
      = SKEFTHawking.SingularCohomologyMod2.cupH24 (redH X 2 a) (redH X 2 b) := by
  obtain ⟨za, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [cupH24_mk_mk]
  show redH X 4 (Cohomology.mk X 4 _) = _
  rw [redH_mk]
  show SKEFTHawking.SingularCohomologyMod2.Cohomology.mk X 4 _
    = SKEFTHawking.SingularCohomologyMod2.cupH24
        (Submodule.Quotient.mk (redKer X 2 za))
        (Submodule.Quotient.mk (redKer X 2 zb))
  rw [SKEFTHawking.SingularCohomologyMod2.cupH24_mk_mk]
  show SKEFTHawking.SingularCohomologyMod2.Cohomology.mk X 4 _
    = SKEFTHawking.SingularCohomologyMod2.Cohomology.mk X 4 _
  apply congrArg
  apply Subtype.ext
  exact redC_cup (p := 2) (q := 2) (za : SingularCochainInt X 2) (zb : SingularCochainInt X 2)

/-! ## §3. The evenness of the intersection form via the mod-2 Wu criterion (Spin ⟹ even) -/

/-- **The Spin/Wu evenness datum** for a closed oriented 4-manifold — the disclosed geometric input to
the EVEN conjunct of `IsEvenUnimodular interMatrix`, packaged as a structure (NO axiom).

It carries, tied to the integral fundamental class `fc : IntFundamentalClass X`:
* `mu2 : H⁴(X;ℤ/2) → ℤ/2` — the mod-2 fundamental-class functional `⟨·, [M]₂⟩` (the on-main Wu
  substrate's `PoincareDual4Mid.mu` shape; every closed manifold is ℤ/2-orientable);
* `eval_compat` — the ℤ→ℤ/2 compatibility `((fc.eval ω : ℤ) : ZMod 2) = mu2 (redH ω)` tying the
  integral evaluation `⟨·,[M]⟩` to the mod-2 one through the reduction bridge `redH`;
* `wu_vanish` — **the Spin condition, functional form**: `∀ y : H²(X;ℤ/2), mu2 (Sq² y) = 0`. Since
  the singular Wu relation gives `⟨v₂ ∪ y, [M]₂⟩ = ⟨Sq² y, [M]₂⟩`, this is exactly `v₂ = 0`. For an
  oriented 4-manifold `v₁ = w₁ = 0` so `w₂ = v₂`; hence `v₂ = 0 ⟺ w₂ = 0 ⟺ M is Spin`. (`Sq²` on
  `H²` is the top square `cupSquare2 y = cupH24 y y`, from `SingularCohomologyMod2`.)

Disclosed tracked hypothesis `spinWu_even_datum` (`HYPOTHESIS_REGISTRY`; discharge = build the ℤ/2
fundamental class + PD `PoincareDual4Mid` from the manifold, take `mu2 = P.mu`, and derive `wu_vanish`
from `w₂(TM) = 0`). Everything in §3 holds for an arbitrary such datum, so it is the ONLY unproved
input to evenness. -/
structure SpinWuDatum (fc : IntFundamentalClass X) where
  /-- The mod-2 fundamental-class functional `μ₂ = ⟨·, [M]₂⟩ : H⁴(X;ℤ/2) →ₗ[ZMod 2] ZMod 2`. -/
  mu2 : SKEFTHawking.SingularCohomologyMod2.Cohomology X 4 →ₗ[ZMod 2] ZMod 2
  /-- ℤ→ℤ/2 compatibility of the two fundamental-class evaluations through the reduction bridge:
  `((⟨ω,[M]⟩ : ℤ) : ZMod 2) = ⟨redH ω, [M]₂⟩`. -/
  eval_compat : ∀ ω : Cohomology X 4, ((fc.eval ω : ℤ) : ZMod 2) = mu2 (redH X 4 ω)
  /-- **Spin, as the vanishing of the mod-2 Wu functional** `y ↦ ⟨Sq² y, [M]₂⟩ = μ₂(y ∪ y)`. Equal to
  `v₂ = 0` via the Wu relation; `= w₂ = 0` on an oriented 4-manifold. -/
  wu_vanish : ∀ y : SKEFTHawking.SingularCohomologyMod2.Cohomology X 2,
    mu2 (SKEFTHawking.SingularCohomologyMod2.cupH24 y y) = 0

/-- **The diagonal of the integral intersection form is even** — `2 ∣ ⟨a ∪ a, [M]⟩` for every
`a ∈ H²(M;ℤ)`, given the Spin/Wu datum.

Proof: reduce mod 2. `((interFormInt fc a a : ℤ) : ZMod 2) = μ₂(redH (a ∪ a)) = μ₂((redH a) ∪ (redH a))`
(bridge compatibility `eval_compat` + cup compatibility `redH_cupH24`), which is `μ₂(Sq²(redH a)) = 0`
by the Spin condition `wu_vanish`. Hence the diagonal casts to `0` in `ZMod 2`, i.e. is divisible by 2. -/
theorem interFormInt_diag_even (fc : IntFundamentalClass X) (D : SpinWuDatum fc)
    (a : Cohomology X 2) :
    (2 : ℤ) ∣ interFormInt fc a a := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from by norm_num,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd _ 2]
  rw [interFormInt_apply]
  rw [D.eval_compat (cupH24 a a), redH_cupH24 a a]
  exact D.wu_vanish (redH X 2 a)

/-- **The integer intersection matrix is EVEN** (`AlgebraicRokhlin.IsEven`) — every diagonal entry
`interMatrix i i = ⟨bᵢ ∪ bᵢ, [M]⟩` is divisible by `2`, given the Spin/Wu datum. This is the **EVEN
conjunct** of `IsEvenUnimodular (interMatrix fc B)` — the last semi-mirror-able piece, discharged from
the mod-2 Wu criterion through the ℤ→ℤ/2 reduction bridge. (The remaining conjuncts: `symmetric` is
already discharged `interMatrix_isSymmetricInt`; `unimodular`/Poincaré-duality is the separate core.) -/
theorem interMatrix_even_of_spinWu (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (D : SpinWuDatum fc) :
    IsEven (interMatrix fc B) := by
  intro i
  rw [interMatrix_apply]
  exact interFormInt_diag_even fc D (B.basis i)

/-- **`IsEvenUnimodular interMatrix` reduces to exactly its UNIMODULAR (Poincaré-duality) conjunct.**

With the two semi-mirror-able conjuncts discharged — `symmetric` (from graded-commutativity,
`interMatrix_isSymmetricInt`) and `even` (from the mod-2 Wu criterion through the reduction bridge,
`interMatrix_even_of_spinWu`) — the full even-unimodular hypothesis of the DONE lattice `σ÷16` leg is
supplied by JUST the remaining `IsUnimodular (interMatrix fc B)` predicate (Poincaré duality: the
intersection form is a perfect pairing, `det = ±1`). This isolates the community-scale PD core as the
sole residual algebraic input to `IsEvenUnimodular`. -/
theorem isEvenUnimodular_of_unimodular (fc : IntFundamentalClass X) (B : IntH2Basis X)
    (D : SpinWuDatum fc) (huni : IsUnimodular (interMatrix fc B)) :
    IsEvenUnimodular (interMatrix fc B) :=
  ⟨interMatrix_isSymmetricInt fc B, huni, interMatrix_even_of_spinWu fc B D⟩

end SKEFTHawking.SingularCohomologyInt
