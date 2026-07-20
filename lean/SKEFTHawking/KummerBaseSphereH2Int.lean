import Mathlib
import SKEFTHawking.KummerResolutionPieceH2
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SingularProdContractibleInt
import SKEFTHawking.SingularSphereMiddleInt
import SKEFTHawking.SingularSphereHighDegreeInt
import SKEFTHawking.DiskManifold

/-!
# Phase 5q.H — K6′a leg 3′: the base `S²` integral `H₂ ≅ ℤ` (the K7 exceptional-class feeder)

The zero section of the Euler−2 disk bundle `E` (`KummerResolutionPiece.ResE`) is the standard
two-chart sphere `BaseS2` (two closed unit disks in `ℂ` glued by `z ↦ z⁻¹` on the equator). The
sibling `KummerResolutionPieceH2` already shows the zero-section inclusion is a homology iso in every
positive degree (`zeroSectionHomologyEquivInt`, `zeroSectionH2EquivInt`). What remains — and what the
K7 rank-22 Mayer–Vietoris accounting actually consumes (16×) — is the **value**: `H₂(S²; ℤ) ≅ ℤ`,
hence `H₂(E; ℤ) ≅ ℤ` with the zero-section class as generator.

This module builds the explicit homeomorphism `BaseS2 ≃ₜ Sph 2` (the metric sphere in `𝔼³`) by two
hemisphere maps assembled from `DiskManifold.assemble` and the `ℂ ≃ₗᵢ 𝔼²` isometry: the lower/upper
hemispheres agree on the equator exactly under `z ↦ z⁻¹` (`= conj` there). Transporting the banked
top-sphere homology `topSphereIsoInt 1 : H₂(Sph 2) ≅ ℤ` back along this homeo
(`homeoHomologyEquivInt`) gives `baseS2H2EquivInt : H₂(BaseS2) ≅ ℤ`; composing with the sibling's
`zeroSectionH2EquivInt` gives `resEH2EquivInt : H₂(E) ≅ ℤ`, with the falsifiable generator pin
`resEH2_generator_pin`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry` / `axiom` / `native_decide` /
`maxHeartbeats`.
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceH2
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SingularSphereMiddleInt (sphere_homology_oneInt)
open SKEFTHawking.SingularSphereHighDegreeInt (sphere_homology_high)
open SKEFTHawking.DiskManifold (assemble assemble_ofLp_last assemble_ofLp_castSucc splitLo splitLo_ofLp
  continuous_assemble)

namespace SKEFTHawking.KummerBaseSphereH2Int

noncomputable section

/-- The standard ℝ-linear isometry `ℂ ≃ₗᵢ[ℝ] 𝔼²` (canonical orthonormal basis of `𝔼²`). -/
noncomputable def cxLI : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- The hemisphere height `√(1 - ‖z‖²)` of a disk point. -/
def hgt (z : Disk) : ℝ := Real.sqrt (1 - ‖(z : ℂ)‖ ^ 2)

theorem hgt_nonneg (z : Disk) : 0 ≤ hgt z := Real.sqrt_nonneg _

theorem norm_sq_le_one (z : Disk) : ‖(z : ℂ)‖ ^ 2 ≤ 1 := by
  have h : ‖(z : ℂ)‖ ≤ 1 := z.2
  nlinarith [norm_nonneg (z : ℂ)]

theorem sq_hgt (z : Disk) : hgt z ^ 2 = 1 - ‖(z : ℂ)‖ ^ 2 := by
  rw [hgt, Real.sq_sqrt]; linarith [norm_sq_le_one z]

/-! ### Local round-trip lemmas for `assemble` (re-derived to keep imports lean). -/

theorem splitLo_assemble (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : splitLo (assemble a s) = a := by
  apply WithLp.ofLp_injective
  funext i
  rw [splitLo_ofLp, assemble_ofLp_castSucc]

theorem assemble_splitLo (v : EuclideanSpace ℝ (Fin 3)) :
    assemble (splitLo v) (v.ofLp (Fin.last 2)) = v := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [assemble_ofLp_last]
  · rw [assemble_ofLp_castSucc, splitLo_ofLp]

/-- `‖assemble a s‖² = ‖a‖² + s²`. -/
theorem normSq_assemble (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    ‖assemble a s‖ ^ 2 = ‖a‖ ^ 2 + s ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      EuclideanSpace.norm_eq (x := a), Real.sq_sqrt (by positivity),
      Fin.sum_univ_castSucc (n := 2)]
  simp only [assemble_ofLp_castSucc, assemble_ofLp_last, Real.norm_eq_abs, sq_abs]

theorem norm_cxLI (z : ℂ) : ‖cxLI z‖ = ‖z‖ := cxLI.norm_map z

theorem hgt_eq_zero_of_norm_one {z : Disk} (h : ‖(z : ℂ)‖ = 1) : hgt z = 0 := by
  have : hgt z ^ 2 = 0 := by rw [sq_hgt, h]; ring
  nlinarith [hgt_nonneg z, this]

/-! ### §1. The hemisphere assembly map and its descent to `BaseS2`. -/

/-- Lower/upper hemisphere assembly on the disjoint union `D² ⊔ D²`. Chart 0 goes to the lower
hemisphere (`z ↦ (z, -√(1-‖z‖²))`), chart 1 to the upper (`w ↦ (conj w, +√(1-‖w‖²))`); they agree on
the equator exactly under `z ↦ z⁻¹ = conj z`. -/
def toSphFun : Disk ⊕ Disk → EuclideanSpace ℝ (Fin 3) :=
  Sum.elim (fun z => assemble (cxLI (z : ℂ)) (- hgt z))
           (fun w => assemble (cxLI ((starRingEnd ℂ) (w : ℂ))) (hgt w))

theorem toSphFun_mem (x : Disk ⊕ Disk) : ‖toSphFun x‖ = 1 := by
  have key : ∀ (c : ℂ) (s : ℝ), s ^ 2 = 1 - ‖c‖ ^ 2 → ‖assemble (cxLI c) s‖ = 1 := by
    intro c s hs
    have h2 : ‖assemble (cxLI c) s‖ ^ 2 = 1 := by rw [normSq_assemble, norm_cxLI, hs]; ring
    nlinarith [norm_nonneg (assemble (cxLI c) s), h2]
  cases x with
  | inl z => exact key (z : ℂ) (- hgt z) (by rw [neg_sq, sq_hgt])
  | inr w =>
      refine key ((starRingEnd ℂ) (w : ℂ)) (hgt w) ?_
      rw [sq_hgt]; simp

def toSphSubtype (x : Disk ⊕ Disk) : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨toSphFun x, by rw [mem_sphere_zero_iff_norm]; exact toSphFun_mem x⟩

theorem toSphSubtype_respects {a b : Disk ⊕ Disk} (h : baseRel a b) :
    toSphSubtype a = toSphSubtype b := by
  rcases h with rfl | hg
  · rfl
  · apply Subtype.ext
    show toSphFun a = toSphFun b
    cases a with
    | inl p =>
      cases b with
      | inr q =>
        obtain ⟨hp1, hpq⟩ := (hg : baseGlued p q)
        have hqp : (q : ℂ) = (starRingEnd ℂ) (p : ℂ) := by
          rw [hpq, conj_eq_inv_of_norm_one hp1]
        have hq1 : ‖(q : ℂ)‖ = 1 := by rw [hqp, Complex.norm_conj]; exact hp1
        show assemble (cxLI (p : ℂ)) (- hgt p) = assemble (cxLI ((starRingEnd ℂ) (q : ℂ))) (hgt q)
        rw [hgt_eq_zero_of_norm_one hp1, hgt_eq_zero_of_norm_one hq1, neg_zero, hqp,
          Complex.conj_conj]
      | inl _ => exact (hg : False).elim
    | inr q =>
      cases b with
      | inl p =>
        obtain ⟨hp1, hpq⟩ := (hg : baseGlued p q)
        have hqp : (q : ℂ) = (starRingEnd ℂ) (p : ℂ) := by
          rw [hpq, conj_eq_inv_of_norm_one hp1]
        have hq1 : ‖(q : ℂ)‖ = 1 := by rw [hqp, Complex.norm_conj]; exact hp1
        show assemble (cxLI ((starRingEnd ℂ) (q : ℂ))) (hgt q) = assemble (cxLI (p : ℂ)) (- hgt p)
        rw [hgt_eq_zero_of_norm_one hp1, hgt_eq_zero_of_norm_one hq1, neg_zero, hqp,
          Complex.conj_conj]
      | inr _ => exact (hg : False).elim

/-- **The hemisphere homeomorphism map** `BaseS2 → S²` (before the compact-to-T2 upgrade). -/
def baseToSph : BaseS2 → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Quotient.lift toSphSubtype (fun _ _ h => toSphSubtype_respects h)

theorem continuous_hgt : Continuous hgt := by
  apply Real.continuous_sqrt.comp
  exact continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2)

theorem continuous_toSphFun : Continuous toSphFun := by
  apply Continuous.sumElim
  · exact continuous_assemble.comp (Continuous.prodMk
      (cxLI.continuous.comp continuous_subtype_val) continuous_hgt.neg)
  · exact continuous_assemble.comp (Continuous.prodMk
      (cxLI.continuous.comp ((Complex.continuous_conj).comp continuous_subtype_val)) continuous_hgt)

theorem continuous_baseToSph : Continuous baseToSph :=
  continuous_quot_lift _ (Continuous.subtype_mk continuous_toSphFun _)

/-! ### §2. Bijectivity of the hemisphere map. -/

/-- `assemble` is injective in both blocks. -/
theorem assemble_inj {a1 a2 : EuclideanSpace ℝ (Fin 2)} {s1 s2 : ℝ}
    (h : assemble a1 s1 = assemble a2 s2) : a1 = a2 ∧ s1 = s2 := by
  refine ⟨?_, ?_⟩
  · rw [← splitLo_assemble a1 s1, ← splitLo_assemble a2 s2, h]
  · rw [← assemble_ofLp_last a1 s1, ← assemble_ofLp_last a2 s2, h]

theorem norm_one_of_hgt_eq_zero {z : Disk} (h : hgt z = 0) : ‖(z : ℂ)‖ = 1 := by
  have h2 : (1 : ℝ) - ‖(z : ℂ)‖ ^ 2 = 0 := by rw [← sq_hgt, h]; ring
  nlinarith [norm_nonneg (z : ℂ), h2]

theorem baseToSph_injective : Function.Injective baseToSph := by
  intro x y hxy
  induction x using Quotient.ind with
  | _ a =>
    induction y using Quotient.ind with
    | _ b =>
      have hfun : toSphFun a = toSphFun b := Subtype.ext_iff.mp hxy
      refine Quotient.sound ?_
      cases a with
      | inl z =>
        cases b with
        | inl z' =>
          obtain ⟨ha, _⟩ := assemble_inj hfun
          exact Or.inl (congrArg Sum.inl (Subtype.ext (cxLI.injective ha)))
        | inr w =>
          obtain ⟨ha, hs⟩ := assemble_inj hfun
          have hz0 : hgt z = 0 := by nlinarith [hgt_nonneg z, hgt_nonneg w, hs]
          have hz1 : ‖(z : ℂ)‖ = 1 := norm_one_of_hgt_eq_zero hz0
          have hzw : (z : ℂ) = (starRingEnd ℂ) (w : ℂ) := cxLI.injective ha
          refine Or.inr (show baseGlued z w from ⟨hz1, ?_⟩)
          have hwz : (w : ℂ) = (starRingEnd ℂ) (z : ℂ) := by
            rw [hzw]; exact (Complex.conj_conj _).symm
          rw [hwz, conj_eq_inv_of_norm_one hz1]
      | inr w =>
        cases b with
        | inl z' =>
          obtain ⟨ha, hs⟩ := assemble_inj hfun
          have hz0 : hgt z' = 0 := by nlinarith [hgt_nonneg z', hgt_nonneg w, hs]
          have hz1 : ‖(z' : ℂ)‖ = 1 := norm_one_of_hgt_eq_zero hz0
          have hzw : (starRingEnd ℂ) (w : ℂ) = (z' : ℂ) := cxLI.injective ha
          refine Or.inr (show baseGlued z' w from ⟨hz1, ?_⟩)
          have hwz : (w : ℂ) = (starRingEnd ℂ) (z' : ℂ) := by
            rw [← hzw, Complex.conj_conj]
          rw [hwz, conj_eq_inv_of_norm_one hz1]
        | inr w' =>
          obtain ⟨ha, _⟩ := assemble_inj hfun
          have hww : (w : ℂ) = (w' : ℂ) :=
            (starRingEnd ℂ).injective (cxLI.injective ha)
          exact Or.inl (congrArg Sum.inr (Subtype.ext hww))

theorem baseToSph_surjective : Function.Surjective baseToSph := by
  rintro ⟨v, hv⟩
  have hnv : ‖v‖ = 1 := mem_sphere_zero_iff_norm.mp hv
  have hav : assemble (splitLo v) (v.ofLp (Fin.last 2)) = v := assemble_splitLo v
  set a := splitLo v with ha
  set s := v.ofLp (Fin.last 2) with hs
  have hnorm : ‖a‖ ^ 2 + s ^ 2 = 1 := by rw [← normSq_assemble, hav, hnv]; norm_num
  have hale : ‖a‖ ≤ 1 := by nlinarith [norm_nonneg a, sq_nonneg s]
  have hdmem : ‖cxLI.symm a‖ ≤ 1 := by rw [cxLI.symm.norm_map]; exact hale
  rcases le_total s 0 with hsle | hsge
  · refine ⟨baseChart0 ⟨cxLI.symm a, hdmem⟩, ?_⟩
    apply Subtype.ext
    show assemble (cxLI ((⟨cxLI.symm a, hdmem⟩ : Disk) : ℂ)) (- hgt ⟨cxLI.symm a, hdmem⟩) = v
    have hco : ((⟨cxLI.symm a, hdmem⟩ : Disk) : ℂ) = cxLI.symm a := rfl
    have hh : hgt ⟨cxLI.symm a, hdmem⟩ = -s := by
      rw [hgt, hco, cxLI.symm.norm_map, show (1 : ℝ) - ‖a‖ ^ 2 = s ^ 2 from by linarith,
        Real.sqrt_sq_eq_abs, abs_of_nonpos hsle]
    rw [hco, cxLI.apply_symm_apply, hh, neg_neg, hav]
  · have hcmem : ‖(starRingEnd ℂ) (cxLI.symm a)‖ ≤ 1 := by rw [Complex.norm_conj]; exact hdmem
    refine ⟨baseChart1 ⟨(starRingEnd ℂ) (cxLI.symm a), hcmem⟩, ?_⟩
    apply Subtype.ext
    show assemble (cxLI ((starRingEnd ℂ) ((⟨(starRingEnd ℂ) (cxLI.symm a), hcmem⟩ : Disk) : ℂ)))
      (hgt ⟨(starRingEnd ℂ) (cxLI.symm a), hcmem⟩) = v
    have hco : ((⟨(starRingEnd ℂ) (cxLI.symm a), hcmem⟩ : Disk) : ℂ)
        = (starRingEnd ℂ) (cxLI.symm a) := rfl
    have hh : hgt ⟨(starRingEnd ℂ) (cxLI.symm a), hcmem⟩ = s := by
      rw [hgt, hco, Complex.norm_conj, cxLI.symm.norm_map,
        show (1 : ℝ) - ‖a‖ ^ 2 = s ^ 2 from by linarith,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hsge]
    rw [hco, Complex.conj_conj, cxLI.apply_symm_apply, hh, hav]

/-! ### §3. The homeomorphism `BaseS2 ≃ₜ S²` and the integral `H₂ ≅ ℤ` package. -/

instance : CompactSpace BaseS2 := inferInstanceAs (CompactSpace (Quotient baseSetoid))

/-- **The homeomorphism `BaseS2 ≃ₜ S²`** (the two-chart sphere to the metric sphere in `𝔼³`), from
the continuous hemisphere bijection upgraded by compact-to-`T2`. -/
def baseHomeoSph : BaseS2 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective baseToSph ⟨baseToSph_injective, baseToSph_surjective⟩)
    continuous_baseToSph

/-- **`H₂(BaseS²; ℤ) ≅ ℤ`** — the integral second homology of the base sphere is free of rank one,
via the homeomorphism to the metric `S²` and the banked top-sphere homology `topSphereIsoInt 1`. -/
def baseS2H2EquivInt : Homology (TopCat.of BaseS2) 2 ≃ₗ[ℤ] ℤ :=
  (homeoHomologyEquivInt (X := TopCat.of BaseS2) (Y := Sph 2) baseHomeoSph 2).trans
    (topSphereIsoInt 1)

/-- **`H₂(E; ℤ) ≅ ℤ`** — the headline: the integral second homology of the Euler−2 disk bundle is
free of rank one. Composes the zero-section homology iso `zeroSectionH2EquivInt` (`E`-side to
base-`S²`-side) with `baseS2H2EquivInt`. This is the exceptional-class input the K7 rank-22
Mayer–Vietoris accounting consumes (16×). -/
def resEH2EquivInt : Homology (TopCat.of ResE) 2 ≃ₗ[ℤ] ℤ :=
  zeroSectionH2EquivInt.symm.trans baseS2H2EquivInt

/-- **The generator pin (falsifiable)**: the zero-section pushforward of the base-`S²` generator
`baseS2H2EquivInt.symm 1` is the generator of `H₂(E; ℤ)` — it maps to `1` under `resEH2EquivInt`.
(`zeroSectionH2EquivInt` is literally the pushforward `Homology.mapInt zeroSectionC 2`.) -/
theorem resEH2_generator_pin :
    resEH2EquivInt (Homology.mapInt zeroSectionC 2 (baseS2H2EquivInt.symm 1)) = 1 := by
  have hmap : Homology.mapInt zeroSectionC 2 (baseS2H2EquivInt.symm 1)
      = zeroSectionH2EquivInt (baseS2H2EquivInt.symm 1) := rfl
  rw [hmap]
  show baseS2H2EquivInt
      (zeroSectionH2EquivInt.symm (zeroSectionH2EquivInt (baseS2H2EquivInt.symm 1))) = 1
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

/-! ### §4. Stretch — the vanishing degrees of `H_*(E; ℤ)` (K7 bookkeeping).

`H₁(E) = H₃(E) = H₄(E) = 0`, each via the same `E ≃ S²` transport (`zeroSectionHomologyEquivInt`
in the positive degree, then `homeoHomologyEquivInt baseHomeoSph` to the metric sphere) against the
banked `Sⁿ` vanishing lemmas. `H₀(E) ≅ ℤ` (connectedness) is a degree-0 statement outside the
positive-degree homotopy-invariance equivalence and is left to the degree-0 machinery. -/

theorem resE_homology_one_eq_zero (x : Homology (TopCat.of ResE) 1) : x = 0 := by
  set e := (zeroSectionHomologyEquivInt 0).symm.trans
    (homeoHomologyEquivInt (X := Btop) (Y := Sph 2) baseHomeoSph 1) with he
  have hx0 : e x = 0 := sphere_homology_oneInt (by norm_num) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

theorem resE_homology_three_eq_zero (x : Homology (TopCat.of ResE) 3) : x = 0 := by
  set e := (zeroSectionHomologyEquivInt 2).symm.trans
    (homeoHomologyEquivInt (X := Btop) (Y := Sph 2) baseHomeoSph 3) with he
  have hx0 : e x = 0 := sphere_homology_high 2 3 (by norm_num) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

theorem resE_homology_four_eq_zero (x : Homology (TopCat.of ResE) 4) : x = 0 := by
  set e := (zeroSectionHomologyEquivInt 3).symm.trans
    (homeoHomologyEquivInt (X := Btop) (Y := Sph 2) baseHomeoSph 4) with he
  have hx0 : e x = 0 := sphere_homology_high 2 4 (by norm_num) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

end

end SKEFTHawking.KummerBaseSphereH2Int
