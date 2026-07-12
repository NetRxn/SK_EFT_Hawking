/-
# Phase 5q.H (N5 witness tower) — `H₂(S²×S²; ℤ) ≅ ℤ²` COMPUTED:
# the `SphereProdHData` freeze's H₂ slice discharged (arc slice 3)

The round-5 polar product cover (`SphereProdHOneInt`: `A = S²×(S²∖{v})`, `B = S²×(S²∖{−v})`) run
at degree 2, consuming slice 1+2's intersection data (`SphereProdPuncturedPlaneInt`:
`H₁(A∩B;ℤ) ≅ ℤ`, `H₂(A∩B;ℤ) ≅ ℤ`, both realized by FIRST-coordinate collapses through the
`interProdHomeo` transport). The MV LES segment

  `H₂(A∩B) →[Δ₂] H₂(A)⊕H₂(B) →[Σ₂] H₂(S²×S²) →[δ] H₁(A∩B) →[Δ₁] H₁(A)⊕H₁(B) = 0`

computes:
* legs collapse (`coverAEquivInt`/`coverBEquivInt`): `H₂(A) ≅ H₂(B) ≅ H₂(S²;ℤ) ≅ ℤ`
  (`prodSetContractibleEquivInt` + the stereographic contraction of the punctured factor);
* **the master-lemma pattern** (§2, the `SphereProdPuncturedPlaneInt` §6 continuation): every
  collapse is `Homology.mapInt` of the literal first-coordinate map `p ↦ p.1.1`, so the
  `Δ₂`-coordinates are the DIAGONAL of `(H₂(S²))²` (`diag_fst`/`diag_snd` — the intersection is
  path-connected here, so no clopen-split bookkeeping is even needed);
* `δ` is SURJECTIVE onto `H₁(A∩B) ≅ ℤ` (`Δ₁ = 0` against the collapsed legs' `H₁ = 0` +
  exactness at `H₁(A∩B)`), with a chosen generator preimage `deltaGen`;
* `ker δ = im Σ₂ ≅ ℤ` (`sumInto`, the S² top class pushed through the `A`-leg; injective by the
  diagonal kernel, onto `ker δ` by the diagonal correction);
* the extension `0 → ℤ →[sumInto] H₂(S²×S²) →[δ̄] ℤ → 0` splits by the chosen `deltaGen`
  (`ℤ` free): **`sphereProdHTwoEquivInt : H₂(S²×S²;ℤ) ≃ₗ[ℤ] ℤ × ℤ`** (`psi` bijective), plus the
  `Module.Free`/`Module.Finite` instances replacing the `SphereProdHData.free2`/`finite2` freeze.

Generator bookkeeping for the Gram pin (§5, slice-4 exports — the coordinates of the two
generators, NOT the intersection form, which stays a separate geometric statement):
* generator 1 (`sumInto 1`) reads `1` under the FIRST-factor projection (`sumInto_prodFst`) and
  `0` under the SECOND (`sumInto_prodSnd` — the leg's second factor is the contractible punctured
  sphere), i.e. it IS the `[S²×pt]` factor class in projection coordinates;
* generator 2 (`deltaGen`) is pinned by its δ-value `1` on the puncture-circle class
  (`deltaGen_spec`, `deltaBar_psi`) — canonical exactly modulo generator 1 (the split choice).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProdPuncturedPlaneInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc puncturedHomeo antipode)
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularLocalHomologyInt (eucl_homology_trivialInt)
open SKEFTHawking.SingularLineMinusPointInt (topSphereIsoInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.SphereProdHOneInt (coverA coverB coverAB_cover
  coverA_homology_one_eq_zero coverB_homology_one_eq_zero
  puncContraction slice_puncContraction_zero slice_puncContraction_one)
open SKEFTHawking.SphereProdPuncturedPlaneInt (coverInterHOneEquivInt coverInterHTwoEquivInt
  coverInterFstCM coverInter_collapse_two interProdHomeo slitProdHTwoViaFst slitProdHTwoEquivInt)
open SKEFTHawking.SpinSigmaRoute (SphereProd)

namespace SKEFTHawking.SphereProdHTwoInt

/-- `S²×S²` as the MV carrier (the polar product cover's ambient; `= TopCat.of SphereProd` by
`rfl`, the witness tower's spelling). -/
abbrev SphSph : TopCat := ProdSp (Sph 2) (Sph 2)

/-! ## §1. The degree-generic leg collapses `Hₙ₊₁(A) ≅ Hₙ₊₁(B) ≅ Hₙ₊₁(S²;ℤ)` -/

/-- `Hₙ₊₁(S²×(S²∖{v}); ℤ) ≅ Hₙ₊₁(S²;ℤ)` — the `A`-leg collapse at every positive degree (the
degree-generic form of `coverA_homology_one_eq_zero`'s inline equivalence). -/
noncomputable def coverAEquivInt (v : ↑(Sph 2)) (n : ℕ) :
    Homology (sub (coverA v)) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  prodSetContractibleEquivInt (Sph 2) (Sph 2) ({v}ᶜ : Set ↑(Sph 2))
    ((puncturedHomeo 2 v).symm 0) (puncContraction 2 v)
    (slice_puncContraction_zero 2 v) (slice_puncContraction_one 2 v) n

/-- `Hₙ₊₁(S²×(S²∖{−v}); ℤ) ≅ Hₙ₊₁(S²;ℤ)` — the `B`-leg collapse at the antipode. -/
noncomputable def coverBEquivInt (v : ↑(Sph 2)) (n : ℕ) :
    Homology (sub (coverB v)) (n + 1) ≃ₗ[ℤ] Homology (Sph 2) (n + 1) :=
  prodSetContractibleEquivInt (Sph 2) (Sph 2) ({antipode v}ᶜ : Set ↑(Sph 2))
    ((puncturedHomeo 2 (antipode v)).symm 0) (puncContraction 2 (antipode v))
    (slice_puncContraction_zero 2 (antipode v)) (slice_puncContraction_one 2 (antipode v)) n

/-! ## §2. The master lemma: every collapse is the first-coordinate `mapInt`
(the `SphereProdPuncturedPlaneInt` §6 pattern, continued at the S²×S² cover) -/

/-- The first-coordinate collapse of a subset of `S²×S²`. -/
def fstCM (T : Set ↑SphSph) : C(↥(sub (X := SphSph) T), ↑(Sph 2)) :=
  ⟨fun p => (p : ↑SphSph).1, continuous_fst.comp continuous_subtype_val⟩

/-- **The `A`-leg collapse is the first-coordinate pushforward** — the canonical `mapInt` form of
`coverAEquivInt` (homeo seam + projection compose to the literal `p ↦ p.1.1`). -/
theorem coverAEquivInt_eq_mapInt (v : ↑(Sph 2)) (n : ℕ)
    (y : Homology (sub (coverA v)) (n + 1)) :
    coverAEquivInt v n y = Homology.mapInt (fstCM (coverA v)) (n + 1) y := by
  show Homology.mapInt (prodFst (Sph 2) (sub ({v}ᶜ : Set ↑(Sph 2)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo (Sph 2) (Sph 2) ({v}ᶜ : Set ↑(Sph 2)),
         (prodSetHomeo (Sph 2) (Sph 2) ({v}ᶜ : Set ↑(Sph 2))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The `B`-leg collapse in canonical `mapInt` form. -/
theorem coverBEquivInt_eq_mapInt (v : ↑(Sph 2)) (n : ℕ)
    (y : Homology (sub (coverB v)) (n + 1)) :
    coverBEquivInt v n y = Homology.mapInt (fstCM (coverB v)) (n + 1) y := by
  show Homology.mapInt (prodFst (Sph 2) (sub ({antipode v}ᶜ : Set ↑(Sph 2)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo (Sph 2) (Sph 2) ({antipode v}ᶜ : Set ↑(Sph 2)),
         (prodSetHomeo (Sph 2) (Sph 2) ({antipode v}ᶜ : Set ↑(Sph 2))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Pushing an intersection class into the `A`-leg and collapsing = collapsing the intersection
directly (both are `p ↦ p.1.1`; the naturality square closes by `← mapInt_comp` + `rfl`). -/
theorem coverA_collapse_inter (v : ↑(Sph 2))
    (w : Homology (sub (coverA v ∩ coverB v)) 2) :
    coverAEquivInt v 1 (Homology.mapInt
        (subIncl (Set.inter_subset_left (s := coverA v) (t := coverB v))) 2 w)
      = Homology.mapInt (coverInterFstCM v) 2 w := by
  rw [coverAEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Same for the `B`-leg — the SAME first-coordinate map. -/
theorem coverB_collapse_inter (v : ↑(Sph 2))
    (w : Homology (sub (coverA v ∩ coverB v)) 2) :
    coverBEquivInt v 1 (Homology.mapInt
        (subIncl (Set.inter_subset_right (s := coverA v) (t := coverB v))) 2 w)
      = Homology.mapInt (coverInterFstCM v) 2 w := by
  rw [coverBEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The slice-2 intersection coordinate READS OFF the first-coordinate collapse:
`coverInterHTwoEquivInt v w = topSphereIsoInt 1 (mapInt (coverInterFstCM v) 2 w)`
(`coverInter_collapse_two` unpacked at the equivalence level). -/
theorem coverInterHTwoEquivInt_eq_fst (v : ↑(Sph 2))
    (w : Homology (sub (coverA v ∩ coverB v)) 2) :
    coverInterHTwoEquivInt v w
      = topSphereIsoInt 1 (Homology.mapInt (coverInterFstCM v) 2 w) := by
  show topSphereIsoInt 1 (slitProdHTwoViaFst
      (homeoHomologyEquivInt (interProdHomeo v) 2 w)) = _
  rw [coverInter_collapse_two]

/-- **The `Δ₂`-image is the DIAGONAL, first coordinate**: in `(H₂(S²))²` coordinates the
`A`-component of `Δ₂ w` is the first-coordinate collapse of `w`. -/
theorem diag_fst (v : ↑(Sph 2)) (w : Homology (sub (coverA v ∩ coverB v)) 2) :
    coverAEquivInt v 1 ((mvHomDiagInt (coverA v) (coverB v) 2 w).1)
      = Homology.mapInt (coverInterFstCM v) 2 w :=
  coverA_collapse_inter v w

/-- **The `Δ₂`-image is the DIAGONAL, second coordinate** — the `B`-component is the SAME
collapse. -/
theorem diag_snd (v : ↑(Sph 2)) (w : Homology (sub (coverA v ∩ coverB v)) 2) :
    coverBEquivInt v 1 ((mvHomDiagInt (coverA v) (coverB v) 2 w).2)
      = Homology.mapInt (coverInterFstCM v) 2 w :=
  coverB_collapse_inter v w

/-! ## §3. δ is onto `H₁(A∩B) ≅ ℤ`, and `ker δ = im Σ₂` is the `sumInto` line -/

/-- `Δ₁ = 0`: both legs have `H₁ = 0`. -/
theorem mvHomDiag_one_eq_zero (v : ↑(Sph 2))
    (w : Homology (sub (coverA v ∩ coverB v)) 1) :
    mvHomDiagInt (coverA v) (coverB v) 1 w = 0 :=
  Prod.ext (coverA_homology_one_eq_zero v _) (coverB_homology_one_eq_zero v _)

/-- **δ is surjective**: exactness at `H₁(A∩B)` against `Δ₁ = 0`. -/
theorem exists_delta_preimage (v : ↑(Sph 2))
    (w : Homology (sub (coverA v ∩ coverB v)) 1) :
    ∃ x : Homology SphSph 2,
      mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) x = w :=
  (mv_exact_interInt (coverA v) (coverB v) 1 (coverAB_cover v) w).mp
    (mvHomDiag_one_eq_zero v w)

/-- **The second generator**: a chosen δ-preimage of the `H₁(A∩B) ≅ ℤ` generator (the
puncture-circle class). Canonical exactly modulo `im Σ₂ = ker δ` — the split choice. -/
noncomputable def deltaGen (v : ↑(Sph 2)) : Homology SphSph 2 :=
  (exists_delta_preimage v ((coverInterHOneEquivInt v).symm 1)).choose

/-- The defining δ-value of the second generator. -/
theorem deltaGen_spec (v : ↑(Sph 2)) :
    mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) (deltaGen v)
      = (coverInterHOneEquivInt v).symm 1 :=
  (exists_delta_preimage v ((coverInterHOneEquivInt v).symm 1)).choose_spec

/-- **The `Σ₂`-line** `t ↦ Σ₂((A-leg collapse)⁻¹(t·[S²]), 0)`: the S² top class pushed through the
`A`-leg — the first generator's parametrization. -/
noncomputable def sumInto (v : ↑(Sph 2)) : ℤ →ₗ[ℤ] Homology SphSph 2 :=
  (mvHomSumInt (coverA v) (coverB v) 2).comp
    ((LinearMap.inl ℤ _ _).comp
      (((coverAEquivInt v 1).symm.toLinearMap).comp ((topSphereIsoInt 1).symm.toLinearMap)))

theorem sumInto_apply (v : ↑(Sph 2)) (t : ℤ) :
    sumInto v t = mvHomSumInt (coverA v) (coverB v) 2
      ((coverAEquivInt v 1).symm ((topSphereIsoInt 1).symm t), 0) := rfl

/-- The `Σ₂`-line lies in `ker δ` (the complex condition `δ ∘ Σ₂ = 0`). -/
theorem delta_sumInto (v : ↑(Sph 2)) (t : ℤ) :
    mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) (sumInto v t) = 0 := by
  rw [sumInto_apply]
  exact mvDeltaInt_mvHomSumInt (coverA v) (coverB v) 1 (coverAB_cover v) _

/-- `sumInto` is injective: a vanishing image lies in `im Δ₂` (middle exactness), whose
coordinates are DIAGONAL — but the second coordinate of `(s, 0)` collapses to `0`, so the diagonal
value, hence `t`, is `0`. -/
theorem sumInto_injective (v : ↑(Sph 2)) : Function.Injective (sumInto v) := by
  refine (injective_iff_map_eq_zero (sumInto v)).mpr fun t ht => ?_
  rw [sumInto_apply] at ht
  obtain ⟨w, hw⟩ := (mv_exact_middleInt (coverA v) (coverB v) 1 (coverAB_cover v) _).mp ht
  have h1 := diag_fst v w
  have h2 := diag_snd v w
  have hw1 : (mvHomDiagInt (coverA v) (coverB v) 2 w).1
      = (coverAEquivInt v 1).symm ((topSphereIsoInt 1).symm t) := by rw [hw]
  have hw2 : (mvHomDiagInt (coverA v) (coverB v) 2 w).2 = 0 := by rw [hw]
  rw [hw1, LinearEquiv.apply_symm_apply] at h1
  rw [hw2, map_zero] at h2
  have : (topSphereIsoInt 1).symm t = 0 := h1.trans h2.symm
  exact (LinearEquiv.map_eq_zero_iff _).mp this

/-- **`ker δ ⊆ im sumInto`**: a δ-vanishing class lifts to the legs (exactness at `H₂(X)`);
correcting the lift `(u, u')` by the diagonal class with value `B-collapse(u')` moves it into
`(s, 0)`-normal form without changing the image. -/
theorem mem_range_sumInto_of_delta_eq_zero (v : ↑(Sph 2)) (x : Homology SphSph 2)
    (hx : mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) x = 0) :
    ∃ t : ℤ, sumInto v t = x := by
  obtain ⟨⟨u, u'⟩, hxeq⟩ :=
    (mv_exact_ambientInt (coverA v) (coverB v) 1 (coverAB_cover v) x).mp hx
  set d := coverBEquivInt v 1 u' with hd
  set s := (coverAEquivInt v 1).symm (coverAEquivInt v 1 u - d) with hs
  set w := (coverInterHTwoEquivInt v).symm (topSphereIsoInt 1 d) with hwdef
  have hwfst : Homology.mapInt (coverInterFstCM v) 2 w = d := by
    apply (topSphereIsoInt 1).injective
    rw [← coverInterHTwoEquivInt_eq_fst v w, hwdef,
      (coverInterHTwoEquivInt v).apply_symm_apply]
  have hΔ : mvHomDiagInt (coverA v) (coverB v) 2 w = (u - s, u') := by
    refine Prod.ext ?_ ?_
    · apply (coverAEquivInt v 1).injective
      rw [diag_fst v w, hwfst, map_sub, hs, LinearEquiv.apply_symm_apply, sub_sub_cancel]
    · apply (coverBEquivInt v 1).injective
      rw [diag_snd v w, hwfst]
  have hker : mvHomSumInt (coverA v) (coverB v) 2 (u - s, u') = 0 := by
    rw [← hΔ]
    exact mvHomSumInt_mvHomDiagInt (coverA v) (coverB v) 2 w
  refine ⟨topSphereIsoInt 1 (coverAEquivInt v 1 u - d), ?_⟩
  rw [sumInto_apply, LinearEquiv.symm_apply_apply]
  rw [← hxeq,
    show (u, u') = ((s, 0) : Homology (sub (coverA v)) 2 × Homology (sub (coverB v)) 2)
        + (u - s, u') from by
      rw [Prod.mk_add_mk, add_sub_cancel, zero_add],
    map_add, hker, add_zero]

/-! ## §4. The split extension: `H₂(S²×S²; ℤ) ≅ ℤ²` -/

/-- **The rank-2 comparison map** `(s, m) ↦ sumInto s + m·deltaGen`: the `Σ₂`-line plus the chosen
δ-section — the split of `0 → ℤ → H₂(S²×S²) → ℤ → 0`. -/
noncomputable def psi (v : ↑(Sph 2)) : ℤ × ℤ →ₗ[ℤ] Homology SphSph 2 :=
  (sumInto v).coprod (LinearMap.toSpanSingleton ℤ _ (deltaGen v))

theorem psi_apply (v : ↑(Sph 2)) (s m : ℤ) :
    psi v (s, m) = sumInto v s + m • deltaGen v := rfl

/-- **The δ̄-readout of `psi`**: the second coordinate is exactly the δ-value on the
puncture-circle class — the generator-2 pin. -/
theorem deltaBar_psi (v : ↑(Sph 2)) (s m : ℤ) :
    coverInterHOneEquivInt v
      (mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) (psi v (s, m))) = m := by
  rw [psi_apply, map_add, delta_sumInto, zero_add, map_smul, deltaGen_spec, map_smul,
    LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

theorem psi_injective (v : ↑(Sph 2)) : Function.Injective (psi v) := by
  refine (injective_iff_map_eq_zero (psi v)).mpr fun p hp => ?_
  obtain ⟨s, m⟩ := p
  have hm : m = 0 := by
    have h := deltaBar_psi v s m
    rw [hp, map_zero, map_zero] at h
    exact h.symm
  have hs' : sumInto v s = 0 := by
    have h := hp
    rw [psi_apply, hm, zero_smul, add_zero] at h
    exact h
  have hs0 : s = 0 := sumInto_injective v (hs'.trans (map_zero (sumInto v)).symm)
  exact Prod.ext hs0 hm

theorem psi_surjective (v : ↑(Sph 2)) : Function.Surjective (psi v) := by
  intro x
  set m := coverInterHOneEquivInt v
    (mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v) x) with hm
  have hδ0 : mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v)
      (x - m • deltaGen v) = 0 := by
    have h : coverInterHOneEquivInt v (mvDeltaInt (coverA v) (coverB v) 1 (coverAB_cover v)
        (x - m • deltaGen v)) = 0 := by
      rw [map_sub, map_smul, deltaGen_spec, map_sub, map_smul,
        LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one, ← hm, sub_self]
    exact (coverInterHOneEquivInt v).map_eq_zero_iff.mp h
  obtain ⟨t, ht⟩ := mem_range_sumInto_of_delta_eq_zero v (x - m • deltaGen v) hδ0
  refine ⟨(t, m), ?_⟩
  rw [psi_apply, ht, sub_add_cancel]

/-- **`H₂(S²×S²; ℤ) ≅ ℤ²`** — the slice-3 headline, at the witness tower's carrier
`TopCat.of SphereProd` (definitionally the MV carrier `ProdSp (Sph 2) (Sph 2)`). Replaces the
`SphereProdHData.free2`/`finite2` freeze. -/
noncomputable def sphereProdHTwoEquivInt :
    Homology (TopCat.of SphereProd) 2 ≃ₗ[ℤ] ℤ × ℤ :=
  (LinearEquiv.ofBijective (psi (basePoint 2))
    ⟨psi_injective (basePoint 2), psi_surjective (basePoint 2)⟩).symm

/-- The headline's inverse parametrization: `(s, m) ↦ sumInto s + m·deltaGen` at the polar
basepoint — the two-generator normal form. -/
theorem sphereProdHTwoEquivInt_symm_apply (s m : ℤ) :
    sphereProdHTwoEquivInt.symm (s, m)
      = sumInto (basePoint 2) s + m • deltaGen (basePoint 2) :=
  psi_apply (basePoint 2) s m

/-- **`H₂(S²×S²;ℤ)` is free — COMPUTED** (was the frozen `SphereProdHData.free2`). -/
instance : Module.Free ℤ (Homology (TopCat.of SphereProd) 2) :=
  Module.Free.of_equiv sphereProdHTwoEquivInt.symm

/-- **`H₂(S²×S²;ℤ)` is finite — COMPUTED** (was the frozen `SphereProdHData.finite2`). -/
instance : Module.Finite ℤ (Homology (TopCat.of SphereProd) 2) :=
  Module.Finite.equiv sphereProdHTwoEquivInt.symm

/-! ## §5. Generator bookkeeping for the Gram pin (slice-4 exports)

The two generators' coordinates under the factor projections — the identification data slice 4's
intersection-form work consumes. NOT the intersection form itself (a separate geometric
statement). -/

/-- The second-factor projection `S²×S² → S²`. -/
def sndCM : C(↑SphSph, ↑(Sph 2)) := ⟨Prod.snd, continuous_snd⟩

/-- **Generator 1 reads `1` under the first-factor projection**: `sumInto t` collapses to
`t·[S²]` — it IS the `[S²×pt]` factor class in first-projection coordinates. -/
theorem sumInto_prodFst (v : ↑(Sph 2)) (t : ℤ) :
    Homology.mapInt (prodFst (Sph 2) (Sph 2)) 2 (sumInto v t)
      = (topSphereIsoInt 1).symm t := by
  rw [sumInto_apply, mvHomSumInt_apply, map_zero, sub_zero, ← LinearMap.comp_apply,
    ← Homology.mapInt_comp]
  have hcm : Homology.mapInt ((prodFst (Sph 2) (Sph 2)).comp (ambIncl (coverA v))) 2
      ((coverAEquivInt v 1).symm ((topSphereIsoInt 1).symm t))
      = coverAEquivInt v 1 ((coverAEquivInt v 1).symm ((topSphereIsoInt 1).symm t)) := by
    rw [coverAEquivInt_eq_mapInt]
    rfl
  rw [hcm, LinearEquiv.apply_symm_apply]

/-- The second-coordinate collapse of the `A`-leg into its punctured second factor. -/
def legASndCM (v : ↑(Sph 2)) : C(↥(sub (coverA v)), ↑(Apunc 2 v)) :=
  ⟨fun p => ⟨(p : ↑SphSph).2, p.2.2⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩

/-- The punctured-sphere inclusion `S²∖{v} ↪ S²`. -/
def puncIncl (v : ↑(Sph 2)) : C(↑(Apunc 2 v), ↑(Sph 2)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- `H₂(S²∖{v}; ℤ) = 0` — the punctured sphere is `ℝ²` (stereographic), integrally acyclic. -/
theorem apunc_homology_two_eq_zero (v : ↑(Sph 2)) (x : Homology (Apunc 2 v) 2) : x = 0 :=
  (homeoHomologyEquivInt (X := Apunc 2 v) (Y := Eucl 2) (puncturedHomeo 2 v)
    2).map_eq_zero_iff.mp (eucl_homology_trivialInt 2 1 _)

/-- **Generator 1 dies under the second-factor projection**: the `A`-leg's second factor is the
contractible punctured sphere, so the projection factors through `H₂(S²∖{v};ℤ) = 0`. With
`sumInto_prodFst`: generator 1 has projection coordinates `(1, 0)`. -/
theorem sumInto_prodSnd (v : ↑(Sph 2)) (t : ℤ) :
    Homology.mapInt sndCM 2 (sumInto v t) = 0 := by
  rw [sumInto_apply, mvHomSumInt_apply, map_zero, sub_zero, ← LinearMap.comp_apply,
    ← Homology.mapInt_comp,
    show sndCM.comp (ambIncl (coverA v)) = (puncIncl v).comp (legASndCM v) from rfl,
    Homology.mapInt_comp, LinearMap.comp_apply,
    apunc_homology_two_eq_zero v (Homology.mapInt (legASndCM v) 2 _), map_zero]

end SKEFTHawking.SphereProdHTwoInt
