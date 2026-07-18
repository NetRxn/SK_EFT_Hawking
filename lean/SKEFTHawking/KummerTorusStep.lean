/-
# Phase 5q.H — the reusable Künneth-with-`S¹` step lemma `H_*(Y × S¹;ℤ)`

The K3 (= Kummer) generator needs `H₂(T⁴;ℤ) ≅ ℤ⁶` for the project's custom
`SingularHomologyInt.Homology`. Rather than a bespoke 4-fold Künneth, this module builds the
**reusable circle-product step**: for a general first factor `Y : TopCat`, the integral homology of
`Y × S¹` splits `H_{k+2}(Y × S¹;ℤ) ≅ H_{k+2}(Y;ℤ) ⊕ H_{k+1}(Y;ℤ)` in every degree `≥ 2` (the
positive-degree step). Iterating from the banked `T² = Circle × Circle` base case gives `T³`, `T⁴`.

This is the exact `T²` Mayer–Vietoris chase (`KummerHomologyT2`) with the *first* factor abstracted
from `Sph 1` to a variable `Y`. The **second** factor is still `Sph 1`, so every circle-specific
gadget (the doubly-punctured-circle homeomorphism `equatorHomeo`/`dpcHomeo`, the two half-line arcs
`posHomeo`/`negHomeo`/`rayContraction`/`posSetContraction`, the `Punc 1` section point `puncPt`) is
reused verbatim from `KummerHomologyT2`. Only the first-factor-dependent pieces (the polar cover
`covA`/`covB` of `Y × S¹`, the leg collapses onto `Y`, the intersection two-arc split, the
first-coordinate collapse) are re-abstracted here over `Y`.

**Route (positive-degree step, output degree `k+2 ≥ 2`).** The polar MV cover of `Y × S¹`
(`covA = Y × (S¹∖{v})`, `covB = Y × (S¹∖{−v})`) has each leg collapse onto `Y`, and the
intersection `Y × (S¹∖{v,−v}) = Y × (ℝ∖0)` is two clopen arcs, each collapsing onto `Y` — so
`H_n(covA∩covB) ≅ H_n(Y) ⊕ H_n(Y)` with the first-coordinate collapse `firstCollapse` surjective.
The MV LES then gives the short exact sequence `0 → im Σ → H_{k+2}(Y×S¹) → ker Δ_{k+1} → 0`, whose:
* right end `ker Δ_{k+1} = ker firstCollapse` is a rank-`b` free kernel of a surjection from the
  rank-`2b` intersection homology (`b = finrank H_{k+1}(Y)`);
* left end `im Σ = im αGen` is the image of the injective first-circle generator
  `αGen : H_{k+2}(Y) → H_{k+2}(Y×S¹)` (`= Σ ∘ inl ∘ legA⁻¹`), free of rank `a = finrank H_{k+2}(Y)`.
With the right end free, the SES splits (`LinearMap.exists_rightInverse_of_surjective`), so
`H_{k+2}(Y×S¹)` is free of rank `a + b`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerHomologyT2

/-- **Kernel finrank identity for a surjection over a PID.** For `f : M → N` surjective from a free
finite `R`-module `M` over a PID domain `R`, `finrank (ker f) + finrank N = finrank M` (quotient
rank-nullity via `quotKerEquivOfSurjective`). Stated over a general PID (not fixed to `ℤ`) so the
quotient's `Module R` instance is unique, dodging the `ℤ`-module `AddCommGroup.toIntModule`
diamond. -/
theorem ker_finrank_add {R : Type} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
    {M N : Type} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.finrank R (LinearMap.ker f) + Module.finrank R N = Module.finrank R M := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [(f.quotKerEquivOfSurjective hf).finrank_eq] at h1
  omega

namespace SKEFTHawking.KummerTorusStep

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularSphereAcyclic (Sph Apunc puncturedHomeo antipode ne_antipode)
open SKEFTHawking.SphereProdHOneInt (puncContraction slice_puncContraction_zero
  slice_puncContraction_one)
open SKEFTHawking.SingularProdContractibleInt (ProdSp prodFst prodSect prodSetHomeo
  prodSetContractibleEquivInt homeoHomologyEquivInt homeoContraction slice_homeoContraction_zero
  slice_homeoContraction_one prodFst_comp_prodSect homeoHomologyEquivInt_apply)
open SKEFTHawking.SingularLineMinusPointInt (circleH1EquivInt)
open SKEFTHawking.SingularSphereBottom (basePoint)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularClopenSplitInt (splitHIntEquiv)
open SKEFTHawking.SingularLineMinusPoint (posSet)
open SKEFTHawking.SingularStarConvexSlit (slice_starConvexContraction_zero
  slice_starConvexContraction_one)
open SKEFTHawking.SingularPuncturedRetract (Punc)

/-! ## §1. The polar MV cover of `Y × S¹` and the leg collapses -/

variable (Y : TopCat)

/-- `Y × S¹` as the MV carrier (`ProdSp Y (Sph 1)`). -/
abbrev Tor : TopCat := ProdSp Y (Sph 1)

/-- The `A`-leg of the polar product cover: `Y × (S¹∖{v})` (full first factor). -/
abbrev covA (v : ↑(Sph 1)) : Set ↑(Tor Y) :=
  (Set.univ : Set ↑Y) ×ˢ ({v}ᶜ : Set ↑(Sph 1))

/-- The `B`-leg of the polar product cover: `Y × (S¹∖{−v})`. -/
abbrev covB (v : ↑(Sph 1)) : Set ↑(Tor Y) :=
  (Set.univ : Set ↑Y) ×ˢ ({antipode v}ᶜ : Set ↑(Sph 1))

/-- The polar product cover is an interior cover of `Y × S¹` (both legs open; the second factors'
complements of `v ≠ −v` exhaust the circle). Same proof as `KummerHomologyT2.covAB_cover`, with the
first factor abstracted to `Y`. -/
theorem covAB_cover (v : ↑(Sph 1)) :
    (⋃ U ∈ ({covA Y v, covB Y v} : Set (Set ↑(Tor Y))), interior U) = Set.univ := by
  have hA : IsOpen (covA Y v) := isOpen_univ.prod isOpen_compl_singleton
  have hB : IsOpen (covB Y v) := isOpen_univ.prod isOpen_compl_singleton
  rw [Set.biUnion_pair, hA.interior_eq, hB.interior_eq, ← Set.prod_union, ← Set.compl_inter,
    Set.eq_univ_iff_forall]
  intro x
  refine Set.mem_prod.mpr ⟨Set.mem_univ _, ?_⟩
  rw [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_singleton_iff]
  rintro ⟨rfl, h2⟩
  exact ne_antipode _ h2

/-- `Hₙ₊₁(Y×(S¹∖{v}); ℤ) ≅ Hₙ₊₁(Y;ℤ)` — the `A`-leg collapse (the punctured circle is
contractible, `puncContraction`). -/
noncomputable def legAEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covA Y v)) (n + 1) ≃ₗ[ℤ] Homology Y (n + 1) :=
  prodSetContractibleEquivInt Y (Sph 1) ({v}ᶜ : Set ↑(Sph 1))
    ((puncturedHomeo 1 v).symm 0) (puncContraction 1 v)
    (slice_puncContraction_zero 1 v) (slice_puncContraction_one 1 v) n

/-- `Hₙ₊₁(Y×(S¹∖{−v}); ℤ) ≅ Hₙ₊₁(Y;ℤ)` — the `B`-leg collapse at the antipode. -/
noncomputable def legBEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covB Y v)) (n + 1) ≃ₗ[ℤ] Homology Y (n + 1) :=
  prodSetContractibleEquivInt Y (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1))
    ((puncturedHomeo 1 (antipode v)).symm 0) (puncContraction 1 (antipode v))
    (slice_puncContraction_zero 1 (antipode v)) (slice_puncContraction_one 1 (antipode v)) n

/-! ## §2. The disconnected intersection `covA∩covB = Y × (S¹∖{v,−v}) ≅ Y × (ℝ∖0)` -/

/-- The cover legs intersect in `Y × (S¹∖{v,−v})` (product-set intersection reassociation). -/
theorem covAB_inter (v : ↑(Sph 1)) :
    covA Y v ∩ covB Y v
      = (Set.univ : Set ↑Y) ×ˢ (({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ)) := by
  rw [Set.prod_inter_prod, Set.univ_inter]

/-- **The intersection `covA∩covB ≃ₜ Y × (ℝ∖0)`** — the disconnected doubly-punctured-circle factor
made explicit as `Punc 1` (reusing the circle-only `KummerHomologyT2.dpcHomeo`), ready to be
clopen-split into the two arcs. -/
noncomputable def intHomeo (v : ↑(Sph 1)) :
    ↑(sub (covA Y v ∩ covB Y v)) ≃ₜ ↑(ProdSp Y (Punc 1)) :=
  (Homeomorph.setCongr (covAB_inter Y v)).trans
    ((prodSetHomeo Y (Sph 1) (({v}ᶜ : Set ↑(Sph 1)) ∩ ({antipode v}ᶜ))).trans
      ((Homeomorph.refl ↑Y).prodCongr (KummerHomologyT2.dpcHomeo v)))

/-- The positive-arc clopen slice `Y × posSet` of `Y × (ℝ∖0)`. -/
abbrev arcU : Set ↑(ProdSp Y (Punc 1)) := (Set.univ : Set ↑Y) ×ˢ posSet

/-- `Y × posSet` is clopen (product of clopens). -/
theorem isClopen_arcU : IsClopen (arcU Y) :=
  isClopen_univ.prod SKEFTHawking.SingularLineMinusPoint.isClopen_posSet

/-- Its complement is `Y × posSetᶜ` (full first factor, so complementation is in the second). -/
theorem arcUcompl_eq : (arcU Y)ᶜ = (Set.univ : Set ↑Y) ×ˢ (posSetᶜ) := by
  ext p
  simp only [arcU, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, true_and]

/-- **The positive-arc leg collapse** `Hₙ₊₁(Y × posSet; ℤ) ≅ Hₙ₊₁(Y;ℤ)` (reusing the circle-only
`KummerHomologyT2.posHomeo`/`posSetContraction`/`rayContraction`). -/
noncomputable def arcPosEquivInt (n : ℕ) :
    Homology (sub (X := ProdSp Y (Punc 1)) ((Set.univ : Set ↑Y) ×ˢ posSet)) (n + 1)
      ≃ₗ[ℤ] Homology Y (n + 1) :=
  prodSetContractibleEquivInt Y (Punc 1) posSet
    (KummerHomologyT2.posHomeo.symm ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ),
      KummerHomologyT2.posRayPt_mem⟩)
    KummerHomologyT2.posSetContraction
    (slice_homeoContraction_zero KummerHomologyT2.posHomeo KummerHomologyT2.rayContraction
      (slice_starConvexContraction_zero KummerHomologyT2.starConvex_posRay))
    (slice_homeoContraction_one KummerHomologyT2.posHomeo KummerHomologyT2.rayContraction
      ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), KummerHomologyT2.posRayPt_mem⟩
      (slice_starConvexContraction_one KummerHomologyT2.starConvex_posRay
        KummerHomologyT2.posRayPt_mem)) n

/-- **The negative-arc leg collapse** `Hₙ₊₁(Y × posSetᶜ; ℤ) ≅ Hₙ₊₁(Y;ℤ)`. -/
noncomputable def arcNegEquivInt (n : ℕ) :
    Homology (sub (X := ProdSp Y (Punc 1)) ((Set.univ : Set ↑Y) ×ˢ (posSetᶜ))) (n + 1)
      ≃ₗ[ℤ] Homology Y (n + 1) :=
  prodSetContractibleEquivInt Y (Punc 1) (posSetᶜ)
    ((KummerHomologyT2.negHomeo.trans KummerHomologyT2.posHomeo).symm
      ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), KummerHomologyT2.posRayPt_mem⟩)
    KummerHomologyT2.posSetComplContraction
    (slice_homeoContraction_zero (KummerHomologyT2.negHomeo.trans KummerHomologyT2.posHomeo)
      KummerHomologyT2.rayContraction
      (slice_starConvexContraction_zero KummerHomologyT2.starConvex_posRay))
    (slice_homeoContraction_one (KummerHomologyT2.negHomeo.trans KummerHomologyT2.posHomeo)
      KummerHomologyT2.rayContraction
      ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), KummerHomologyT2.posRayPt_mem⟩
      (slice_starConvexContraction_one KummerHomologyT2.starConvex_posRay
        KummerHomologyT2.posRayPt_mem)) n

/-- **The intersection two-arc split** `Hₙ₊₁(covA∩covB; ℤ) ≅ Hₙ₊₁(Y;ℤ) × Hₙ₊₁(Y;ℤ)`: the
doubly-punctured circle is TWO disjoint arcs, so at every positive degree the intersection homology
is the direct sum of the two arc-legs, each collapsed onto `Y`. -/
noncomputable def interArcSplitEquivInt (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covA Y v ∩ covB Y v)) (n + 1)
      ≃ₗ[ℤ] Homology Y (n + 1) × Homology Y (n + 1) :=
  (homeoHomologyEquivInt (intHomeo Y v) (n + 1)).trans
    ((splitHIntEquiv (isClopen_arcU Y) (n + 1)).symm.trans
      (LinearEquiv.prodCongr (arcPosEquivInt Y n)
        ((homeoHomologyEquivInt (Homeomorph.setCongr (arcUcompl_eq Y)) (n + 1)).trans
          (arcNegEquivInt Y n))))

/-! ## §3. The first-coordinate collapse, its surjectivity, and `ker Δ = ker firstCollapse` -/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularMayerVietorisLES (subIncl ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt

/-- The first-coordinate collapse `p ↦ p.1.1` of a subset of `Y×S¹` onto the first factor `Y`. -/
def fstCM (T : Set ↑(Tor Y)) : C(↥(sub (X := Tor Y) T), ↑Y) :=
  ⟨fun p => (p : ↑(Tor Y)).1, continuous_fst.comp continuous_subtype_val⟩

/-- **The `A`-leg collapse is the first-coordinate pushforward** — the canonical `mapInt` form of
`legAEquivInt` (homeo seam + projection compose to the literal `p ↦ p.1.1`). -/
theorem legAEquivInt_eq_mapInt (v : ↑(Sph 1)) (n : ℕ) (y : Homology (sub (covA Y v)) (n + 1)) :
    legAEquivInt Y v n y = Homology.mapInt (fstCM Y (covA Y v)) (n + 1) y := by
  show Homology.mapInt (prodFst Y (sub ({v}ᶜ : Set ↑(Sph 1)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo Y (Sph 1) ({v}ᶜ : Set ↑(Sph 1)),
         (prodSetHomeo Y (Sph 1) ({v}ᶜ : Set ↑(Sph 1))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- The `B`-leg collapse in canonical `mapInt` form. -/
theorem legBEquivInt_eq_mapInt (v : ↑(Sph 1)) (n : ℕ) (y : Homology (sub (covB Y v)) (n + 1)) :
    legBEquivInt Y v n y = Homology.mapInt (fstCM Y (covB Y v)) (n + 1) y := by
  show Homology.mapInt (prodFst Y (sub ({antipode v}ᶜ : Set ↑(Sph 1)))) (n + 1)
      (Homology.mapInt
        ⟨prodSetHomeo Y (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1)),
         (prodSetHomeo Y (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1))).continuous⟩ (n + 1) y)
      = _
  rw [← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- **`legA ∘ iA∗ = firstCollapse`** at every positive degree: pushing an intersection class into
the `A`-leg and collapsing = collapsing the intersection's first coordinate directly. -/
theorem covA_collapse_inter (v : ↑(Sph 1)) (n : ℕ)
    (w : Homology (sub (covA Y v ∩ covB Y v)) (n + 1)) :
    legAEquivInt Y v n (Homology.mapInt
        (subIncl (Set.inter_subset_left (s := covA Y v) (t := covB Y v))) (n + 1) w)
      = Homology.mapInt (fstCM Y (covA Y v ∩ covB Y v)) (n + 1) w := by
  rw [legAEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- Same for the `B`-leg — the SAME first-coordinate collapse. -/
theorem covB_collapse_inter (v : ↑(Sph 1)) (n : ℕ)
    (w : Homology (sub (covA Y v ∩ covB Y v)) (n + 1)) :
    legBEquivInt Y v n (Homology.mapInt
        (subIncl (Set.inter_subset_right (s := covA Y v) (t := covB Y v))) (n + 1) w)
      = Homology.mapInt (fstCM Y (covA Y v ∩ covB Y v)) (n + 1) w := by
  rw [legBEquivInt_eq_mapInt, ← LinearMap.comp_apply, ← Homology.mapInt_comp]
  rfl

/-- A chosen nonzero point of `ℝ¹∖0 = Punc 1` (the section basepoint for the `Y` projection). -/
noncomputable def puncPt : ↑(Punc 1) := KummerHomologyT2.puncPt

/-- **`mapInt (prodFst) : Hₙ₊₁(Y×(ℝ∖0)) → Hₙ₊₁(Y)` is surjective** — the projection has the section
`x ↦ (x, puncPt)` (`ℝ∖0` is nonempty). -/
theorem prodFst_punc_surjective (n : ℕ) :
    Function.Surjective (Homology.mapInt (prodFst Y (Punc 1)) (n + 1)) := by
  intro z
  refine ⟨Homology.mapInt (prodSect Y (Punc 1) (puncPt)) (n + 1) z, ?_⟩
  have h : (Homology.mapInt (prodFst Y (Punc 1)) (n + 1)).comp
      (Homology.mapInt (prodSect Y (Punc 1) (puncPt)) (n + 1)) = LinearMap.id := by
    rw [← Homology.mapInt_comp, prodFst_comp_prodSect, Homology.mapInt_id]
  exact LinearMap.congr_fun h z

/-- **The first-coordinate collapse `Hₙ₊₁(covA∩covB) → Hₙ₊₁(Y)` is surjective** — it factors as the
`Punc 1` projection after the intersection homeomorphism `intHomeo` (which preserves the first
coordinate), and the projection is surjective. -/
theorem firstCollapse_surjective (v : ↑(Sph 1)) (n : ℕ) :
    Function.Surjective (Homology.mapInt (fstCM Y (covA Y v ∩ covB Y v)) (n + 1)) := by
  have hrw : fstCM Y (covA Y v ∩ covB Y v)
      = (prodFst Y (Punc 1)).comp ⟨intHomeo Y v, (intHomeo Y v).continuous⟩ := rfl
  rw [hrw, Homology.mapInt_comp]
  refine (prodFst_punc_surjective Y n).comp ?_
  intro z
  obtain ⟨y, hy⟩ := (homeoHomologyEquivInt (intHomeo Y v) (n + 1)).surjective z
  exact ⟨y, (homeoHomologyEquivInt_apply (intHomeo Y v) (n + 1) y).symm.trans hy⟩

/-- The first-coordinate collapse `Hₙ₊₁(covA∩covB) →ₗ[ℤ] Hₙ₊₁(Y)` as a linear map. -/
noncomputable def firstCollapseLM (v : ↑(Sph 1)) (n : ℕ) :
    Homology (sub (covA Y v ∩ covB Y v)) (n + 1) →ₗ[ℤ] Homology Y (n + 1) :=
  Homology.mapInt (fstCM Y (covA Y v ∩ covB Y v)) (n + 1)

/-- **`ker Δ = ker (firstCollapse)`** at every positive degree: a class dies under the
Mayer–Vietoris diagonal `Δ` iff it dies under the first-coordinate collapse — both legs collapse
`iA∗`/`iB∗` to that same collapse (`covA_collapse_inter`/`covB_collapse_inter`), and the legs are
isomorphisms. -/
theorem ker_delta_eq (v : ↑(Sph 1)) (n : ℕ) :
    LinearMap.ker (mvHomDiagInt (covA Y v) (covB Y v) (n + 1))
      = LinearMap.ker (firstCollapseLM Y v n) := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_ker, mvHomDiagInt_apply, Prod.mk_eq_zero, firstCollapseLM]
  constructor
  · rintro ⟨hA, _⟩
    rw [← covA_collapse_inter Y v n w, hA, map_zero]
  · intro hF
    exact ⟨(legAEquivInt Y v n).map_eq_zero_iff.mp ((covA_collapse_inter Y v n w).trans hF),
      (legBEquivInt Y v n).map_eq_zero_iff.mp ((covB_collapse_inter Y v n w).trans hF)⟩

/-- **The inclusion `iB∗ : Hₙ₊₁(covA∩covB) → Hₙ₊₁(covB)` is surjective** — `legB ∘ iB∗ =
firstCollapse` (`covB_collapse_inter`) is surjective and `legB` is an iso. -/
theorem iB_surjective (v : ↑(Sph 1)) (n : ℕ) :
    Function.Surjective (Homology.mapInt
      (subIncl (Set.inter_subset_right (s := covA Y v) (t := covB Y v))) (n + 1)) := by
  intro y
  obtain ⟨w, hw⟩ := firstCollapse_surjective Y v n (legBEquivInt Y v n y)
  refine ⟨w, (legBEquivInt Y v n).injective ?_⟩
  rw [covB_collapse_inter Y v n w, hw]

/-! ## §4. The first-circle generator `alphaGen` and its range `= ker δ` -/

/-- **The first-circle generator** `alphaGen : H_{k+2}(Y) → H_{k+2}(Y×S¹)`,
`c ↦ Σ((legA⁻¹ c, 0))`: the `Y`-class pushed through the `A`-leg into `im Σ`. The generalization of
`KummerHomologyT2.alphaGen` to a variable first factor `Y` and general degree. -/
noncomputable def alphaGen (v : ↑(Sph 1)) (n : ℕ) :
    Homology Y (n + 1) →ₗ[ℤ] Homology (Tor Y) (n + 1) :=
  (mvHomSumInt (covA Y v) (covB Y v) (n + 1)).comp
    ((LinearMap.inl ℤ _ _).comp (legAEquivInt Y v n).symm.toLinearMap)

theorem alphaGen_apply (v : ↑(Sph 1)) (n : ℕ) (c : Homology Y (n + 1)) :
    alphaGen Y v n c
      = mvHomSumInt (covA Y v) (covB Y v) (n + 1) ((legAEquivInt Y v n).symm c, 0) := rfl

/-- **`alphaGen` is injective**: `alphaGen c = 0` puts `(legA⁻¹ c, 0) ∈ ker Σ = im Δ` (middle
exactness); its second coordinate `iB∗ w = 0` forces `firstCollapse w = 0`
(`covB_collapse_inter`), and its first coordinate then reads the collapse `legA⁻¹ c = 0`
(`covA_collapse_inter`), so `c = 0`. Valid at every output degree `n+1 ≥ 1`. -/
theorem alphaGen_injective (v : ↑(Sph 1)) (n : ℕ) : Function.Injective (alphaGen Y v n) := by
  refine (injective_iff_map_eq_zero (alphaGen Y v n)).mpr fun c hc => ?_
  rw [alphaGen_apply] at hc
  obtain ⟨w, hw⟩ := (mv_exact_middleInt (covA Y v) (covB Y v) n (covAB_cover Y v) _).mp hc
  rw [mvHomDiagInt_apply] at hw
  have hfst := congrArg Prod.fst hw
  have hsnd := congrArg Prod.snd hw
  simp only at hfst hsnd
  have hFC : Homology.mapInt (fstCM Y (covA Y v ∩ covB Y v)) (n + 1) w = 0 := by
    rw [← covB_collapse_inter Y v n w, hsnd, map_zero]
  have hc' := covA_collapse_inter Y v n w
  rw [hfst, LinearEquiv.apply_symm_apply, hFC] at hc'
  exact hc'

/-- **`range alphaGen = ker δ`** (` = im Σ`, ambient exactness). The `A`-part `Σ(u,0)` is directly
`alphaGen (legA u)`; the `B`-part `Σ(0,v')` equals `−Σ(iA∗ w, 0)` for a `w` with `iB∗ w = v'`
(`iB_surjective` + the MV complex condition `Σ ∘ Δ = 0`), so it too lies in `range alphaGen`. -/
theorem alphaGen_range_eq_ker_delta (v : ↑(Sph 1)) (n : ℕ) :
    LinearMap.range (alphaGen Y v n)
      = LinearMap.ker (mvDeltaInt (covA Y v) (covB Y v) n (covAB_cover Y v)) := by
  have hkExact : LinearMap.ker (mvDeltaInt (covA Y v) (covB Y v) n (covAB_cover Y v))
      = LinearMap.range (mvHomSumInt (covA Y v) (covB Y v) (n + 1)) :=
    (mv_exact_ambientInt (covA Y v) (covB Y v) n (covAB_cover Y v)).linearMap_ker_eq
  rw [hkExact]
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    rw [alphaGen_apply]
    exact LinearMap.mem_range_self _ _
  · rintro _ ⟨p, rfl⟩
    obtain ⟨u, v'⟩ := p
    obtain ⟨w, hw⟩ := iB_surjective Y v n v'
    set iAw := Homology.mapInt
      (subIncl (Set.inter_subset_left (s := covA Y v) (t := covB Y v))) (n + 1) w with hiAw
    -- `Σ(iAw, v') = Σ(Δw) = 0`, so `Σ(u, v') = Σ(u − iAw, 0) = alphaGen(legA (u − iAw))`.
    have hΔ : mvHomSumInt (covA Y v) (covB Y v) (n + 1) (iAw, v') = 0 := by
      have := mvHomSumInt_mvHomDiagInt (covA Y v) (covB Y v) (n + 1) w
      rwa [mvHomDiagInt_apply, hw] at this
    have hkey : alphaGen Y v n (legAEquivInt Y v n (u - iAw))
        = mvHomSumInt (covA Y v) (covB Y v) (n + 1) (u - iAw, 0) := by
      rw [alphaGen_apply, LinearEquiv.symm_apply_apply]
    have hdiff : mvHomSumInt (covA Y v) (covB Y v) (n + 1) (u, v')
        - mvHomSumInt (covA Y v) (covB Y v) (n + 1) (u - iAw, 0) = 0 := by
      rw [← map_sub]
      have hp : ((u, v') - (u - iAw, 0) : Homology (sub (covA Y v)) (n + 1)
          × Homology (sub (covB Y v)) (n + 1)) = (iAw, v') := by
        rw [Prod.mk_sub_mk, sub_zero]; congr 1; abel
      rw [hp]; exact hΔ
    have hval : mvHomSumInt (covA Y v) (covB Y v) (n + 1) (u, v')
        = alphaGen Y v n (legAEquivInt Y v n (u - iAw)) := by
      rw [hkey, ← sub_eq_zero]; exact hdiff
    rw [hval]
    exact LinearMap.mem_range_self _ _

/-! ## §5. The positive-degree circle-product step lemma -/

/-- **The positive-degree circle-product step (free-finite form).** For `Y : TopCat` with free finite
integral homology in degrees `k+1, k+2`, the homology of `Y × S¹` in degree `k+2` is free finite of
rank `finrank H_{k+2}(Y) + finrank H_{k+1}(Y)`. This is the MV short exact sequence
`0 → im Σ → H_{k+2}(Y×S¹) → ker Δ → 0` split by the projectivity of its free right end
`ker Δ ≅ H_{k+1}(Y)` (rank `b`), with left end `im Σ = im αGen ≅ H_{k+2}(Y)` (rank `a`). The reusable
step: iterating from `T² = Circle²` builds `H₂(T³), H₂(T⁴)`. -/
theorem stepPos_free_finrank (Y : TopCat) (k : ℕ)
    [Module.Free ℤ (Homology Y (k + 2))] [Module.Finite ℤ (Homology Y (k + 2))]
    [Module.Free ℤ (Homology Y (k + 1))] [Module.Finite ℤ (Homology Y (k + 1))] :
    Module.Free ℤ (Homology (Tor Y) (k + 2)) ∧ Module.Finite ℤ (Homology (Tor Y) (k + 2)) ∧
      Module.finrank ℤ (Homology (Tor Y) (k + 2))
        = Module.finrank ℤ (Homology Y (k + 2)) + Module.finrank ℤ (Homology Y (k + 1)) := by
  set v : ↑(Sph 1) := basePoint 1 with hv
  have hcov := covAB_cover Y v
  -- Intersection homology at degree `k+1` is free finite of rank `2 · finrank H_{k+1}(Y)`.
  haveI hIF : Module.Free ℤ (Homology (sub (covA Y v ∩ covB Y v)) (k + 1)) :=
    Module.Free.of_equiv (interArcSplitEquivInt Y v k).symm
  haveI hIFin : Module.Finite ℤ (Homology (sub (covA Y v ∩ covB Y v)) (k + 1)) :=
    Module.Finite.equiv (interArcSplitEquivInt Y v k).symm
  have h2b : Module.finrank ℤ (Homology (sub (covA Y v ∩ covB Y v)) (k + 1))
      = Module.finrank ℤ (Homology Y (k + 1)) + Module.finrank ℤ (Homology Y (k + 1)) := by
    rw [(interArcSplitEquivInt Y v k).finrank_eq, Module.finrank_prod]
  -- The MV diagonal kernel `K = ker Δ` at degree `k+1`, and the connecting `δ` corestricted to it.
  set K := LinearMap.ker (mvHomDiagInt (covA Y v) (covB Y v) (k + 1)) with hK
  have hKfin : Module.finrank ℤ K = Module.finrank ℤ (Homology Y (k + 1)) := by
    have hsurj : Function.Surjective (firstCollapseLM Y v k) := firstCollapse_surjective Y v k
    have hrn := ker_finrank_add (firstCollapseLM Y v k) hsurj
    have hKeq : Module.finrank ℤ K
        = Module.finrank ℤ (LinearMap.ker (firstCollapseLM Y v k)) :=
      (LinearEquiv.ofEq _ _ (ker_delta_eq Y v k)).finrank_eq
    rw [hKeq]; omega
  set δ := mvDeltaInt (covA Y v) (covB Y v) (k + 1) hcov with hδ
  set q : Homology (Tor Y) (k + 2) →ₗ[ℤ] K :=
    δ.codRestrict K (fun x => LinearMap.mem_ker.mpr (mvHomDiagInt_mvDeltaInt _ _ _ hcov x)) with hq
  have hqsurj : Function.Surjective q := by
    rintro ⟨y, hy⟩
    have hyr : y ∈ LinearMap.range δ := by
      rw [← (mv_exact_interInt (covA Y v) (covB Y v) (k + 1) hcov).linearMap_ker_eq]; exact hy
    obtain ⟨x, hx⟩ := hyr
    exact ⟨x, Subtype.ext hx⟩
  have hkerq : LinearMap.ker q = LinearMap.range (alphaGen Y v (k + 1)) := by
    rw [hq, LinearMap.ker_codRestrict]; exact (alphaGen_range_eq_ker_delta Y v (k + 1)).symm
  -- `ker q = im αGen ≅ H_{k+2}(Y)` — free finite of rank `a`.
  haveI hαF : Module.Free ℤ ↥(LinearMap.range (alphaGen Y v (k + 1))) :=
    Module.Free.of_equiv (LinearEquiv.ofInjective (alphaGen Y v (k + 1)) (alphaGen_injective Y v (k + 1)))
  haveI hαFin : Module.Finite ℤ ↥(LinearMap.range (alphaGen Y v (k + 1))) :=
    Module.Finite.equiv (LinearEquiv.ofInjective (alphaGen Y v (k + 1)) (alphaGen_injective Y v (k + 1)))
  haveI hKerqF : Module.Free ℤ ↥(LinearMap.ker q) :=
    Module.Free.of_equiv (LinearEquiv.ofEq _ _ hkerq).symm
  haveI hKerqFin : Module.Finite ℤ ↥(LinearMap.ker q) :=
    Module.Finite.equiv (LinearEquiv.ofEq _ _ hkerq).symm
  have hkerq_fin : Module.finrank ℤ ↥(LinearMap.ker q) = Module.finrank ℤ (Homology Y (k + 2)) := by
    rw [(LinearEquiv.ofEq _ _ hkerq).finrank_eq,
      ← (LinearEquiv.ofInjective (alphaGen Y v (k + 1))
        (alphaGen_injective Y v (k + 1))).finrank_eq]
  -- Split the SES `0 → ker q → H_{k+2}(Y×S¹) → K → 0` (right end `K` free ⟹ projective).
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  have hexact : Function.Exact (⇑(LinearMap.ker q).subtype) (⇑q) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  set e : Homology (Tor Y) (k + 2) ≃ₗ[ℤ] (↥(LinearMap.ker q) × K) :=
    (hexact.splitSurjectiveEquiv (Submodule.injective_subtype _) ⟨s, hs⟩).1 with he
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_prod, hkerq_fin, hKfin]

/-! ## §6. The degree-1 circle-product step (reduced-`H₀` right end) -/

open SKEFTHawking.SingularH0PathConnectedInt (augHInt_injective_pathConnected)
open SKEFTHawking.SingularLineMinusPointInt (augHInt augHInt_naturality augHInt_surjective
  augHInt_ker_iso_int augHIntKerEquivOfHomeo)
open SKEFTHawking.SphereProdHOneInt (pathConnectedSpace_of_homeo pathConnectedSpace_prod)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)

/-- The `A`-leg `Y × (S¹∖{v})` is path-connected (for path-connected `Y`). -/
theorem pathConnected_covA [PathConnectedSpace ↑Y] (v : ↑(Sph 1)) :
    PathConnectedSpace ↑(sub (covA Y v)) := by
  haveI : PathConnectedSpace ↑(sub ({v}ᶜ : Set ↑(Sph 1))) := KummerHomologyT2.pathConnected_apunc v
  haveI : PathConnectedSpace ↑(ProdSp Y (sub ({v}ᶜ : Set ↑(Sph 1)))) := pathConnectedSpace_prod
  exact pathConnectedSpace_of_homeo (prodSetHomeo Y (Sph 1) ({v}ᶜ : Set ↑(Sph 1))).symm

/-- The `B`-leg `Y × (S¹∖{−v})` is path-connected. -/
theorem pathConnected_covB [PathConnectedSpace ↑Y] (v : ↑(Sph 1)) :
    PathConnectedSpace ↑(sub (covB Y v)) := by
  haveI : PathConnectedSpace ↑(sub ({antipode v}ᶜ : Set ↑(Sph 1))) :=
    KummerHomologyT2.pathConnected_apunc (antipode v)
  haveI : PathConnectedSpace ↑(ProdSp Y (sub ({antipode v}ᶜ : Set ↑(Sph 1)))) :=
    pathConnectedSpace_prod
  exact pathConnectedSpace_of_homeo (prodSetHomeo Y (Sph 1) ({antipode v}ᶜ : Set ↑(Sph 1))).symm

/-- The positive clopen piece `Y × posSet` of the intersection is path-connected. -/
theorem pathConnected_arcU [PathConnectedSpace ↑Y] : PathConnectedSpace ↑(sub (arcU Y)) := by
  haveI := KummerHomologyT2.pathConnected_posSet
  haveI : PathConnectedSpace ↑(ProdSp Y (sub posSet)) := pathConnectedSpace_prod
  exact pathConnectedSpace_of_homeo (prodSetHomeo Y (Punc 1) posSet).symm

/-- The negative clopen piece `Y × posSetᶜ` of the intersection is path-connected. -/
theorem pathConnected_arcUcompl [PathConnectedSpace ↑Y] :
    PathConnectedSpace ↑(sub (arcU Y)ᶜ) := by
  haveI := KummerHomologyT2.pathConnected_posSetCompl
  haveI : PathConnectedSpace ↑(ProdSp Y (sub (posSetᶜ))) := pathConnectedSpace_prod
  exact pathConnectedSpace_of_homeo
    ((Homeomorph.setCongr (arcUcompl_eq Y)).trans (prodSetHomeo Y (Punc 1) (posSetᶜ))).symm

/-- The augmentation of the positive intersection piece is bijective (path-connected + nonempty). -/
theorem augHInt_arcU_bijective [PathConnectedSpace ↑Y] :
    Function.Bijective (augHInt (sub (arcU Y))) := by
  haveI := pathConnected_arcU Y
  exact ⟨augHInt_injective_pathConnected,
    augHInt_surjective _ (constSimplex (Classical.arbitrary _) 0)⟩

/-- The augmentation of the negative intersection piece is bijective. -/
theorem augHInt_arcUcompl_bijective [PathConnectedSpace ↑Y] :
    Function.Bijective (augHInt (sub (arcU Y)ᶜ)) := by
  haveI := pathConnected_arcUcompl Y
  exact ⟨augHInt_injective_pathConnected,
    augHInt_surjective _ (constSimplex (Classical.arbitrary _) 0)⟩

/-- **`H̃₀(covA∩covB;ℤ) ≅ ℤ`** — the reduced degree-0 homology of the disconnected intersection
(`Y × (ℝ∖0)`, two path components, for path-connected `Y`): the clopen two-arc split has both pieces
augmentation-bijective, so `ker (augHInt) ≅ ℤ`, transported from `Y × Punc 1` across `intHomeo`. -/
theorem reducedH0_inter_iso_int [PathConnectedSpace ↑Y] (v : ↑(Sph 1)) :
    Nonempty (↥(LinearMap.ker (augHInt (sub (covA Y v ∩ covB Y v)))) ≃ₗ[ℤ] ℤ) :=
  ⟨(augHIntKerEquivOfHomeo ⟨intHomeo Y v, (intHomeo Y v).continuous⟩
      ⟨(intHomeo Y v).symm, (intHomeo Y v).symm.continuous⟩
      (ContinuousMap.ext fun x => (intHomeo Y v).symm_apply_apply x)
      (ContinuousMap.ext fun x => (intHomeo Y v).apply_symm_apply x)).trans
    (augHInt_ker_iso_int (isClopen_arcU Y) (augHInt_arcU_bijective Y)
      (augHInt_arcUcompl_bijective Y)).some⟩

/-- **`ker Δ₀ = ker (augHInt)`** — a degree-0 class dies under the MV diagonal `Δ₀` iff it dies under
the augmentation (both legs path-connected so their augmentations are injective;
`augHInt_naturality`). -/
theorem ker_delta0_eq [PathConnectedSpace ↑Y] (v : ↑(Sph 1)) :
    LinearMap.ker (mvHomDiagInt (covA Y v) (covB Y v) 0)
      = LinearMap.ker (augHInt (sub (covA Y v ∩ covB Y v))) := by
  haveI := pathConnected_covA Y v
  haveI := pathConnected_covB Y v
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_ker, mvHomDiagInt_apply, Prod.mk_eq_zero]
  constructor
  · rintro ⟨hA, _⟩
    rw [← augHInt_naturality (subIncl (Set.inter_subset_left (s := covA Y v) (t := covB Y v))) w,
      hA, map_zero]
  · intro hAug
    refine ⟨?_, ?_⟩
    · apply augHInt_injective_pathConnected (X := sub (covA Y v))
      rw [map_zero,
        augHInt_naturality (subIncl (Set.inter_subset_left (s := covA Y v) (t := covB Y v))) w]
      exact hAug
    · apply augHInt_injective_pathConnected (X := sub (covB Y v))
      rw [map_zero,
        augHInt_naturality (subIncl (Set.inter_subset_right (s := covA Y v) (t := covB Y v))) w]
      exact hAug

/-- **The degree-1 circle-product step (free-finite form), for path-connected `Y`.** The homology of
`Y × S¹` in degree `1` is free finite of rank `finrank H₁(Y) + 1`. Same MV split as `stepPos`, but
the right end is the reduced `H₀` of the disconnected intersection (`ker Δ₀ ≅ ℤ`, one class fewer
than the two arc components), which for path-connected `Y` is `finrank H₀(Y) = 1`. Delivers
`H₁(T³) ≅ ℤ³` from the banked `H₁(T²) ≅ ℤ²`. -/
theorem stepDeg1_free_finrank (Y : TopCat) [PathConnectedSpace ↑Y]
    [Module.Free ℤ (Homology Y 1)] [Module.Finite ℤ (Homology Y 1)] :
    Module.Free ℤ (Homology (Tor Y) 1) ∧ Module.Finite ℤ (Homology (Tor Y) 1) ∧
      Module.finrank ℤ (Homology (Tor Y) 1) = Module.finrank ℤ (Homology Y 1) + 1 := by
  set v : ↑(Sph 1) := basePoint 1 with hv
  have hcov := covAB_cover Y v
  -- Right end `K = ker Δ₀ ≅ ℤ` (reduced `H₀`), free finite of rank 1.
  obtain ⟨eK0⟩ := reducedH0_inter_iso_int Y v
  set K := LinearMap.ker (mvHomDiagInt (covA Y v) (covB Y v) 0) with hK
  have hKeqAug : K = LinearMap.ker (augHInt (sub (covA Y v ∩ covB Y v))) := ker_delta0_eq Y v
  set eK : K ≃ₗ[ℤ] ℤ := (LinearEquiv.ofEq _ _ hKeqAug).trans eK0 with heK
  haveI hKF : Module.Free ℤ K := Module.Free.of_equiv eK.symm
  haveI hKFin : Module.Finite ℤ K := Module.Finite.equiv eK.symm
  have hKfin : Module.finrank ℤ K = 1 := by rw [eK.finrank_eq, Module.finrank_self]
  -- Left end `ker q = im αGen ≅ H₁(Y)`, free finite of rank `finrank H₁(Y)`.
  set δ := mvDeltaInt (covA Y v) (covB Y v) 0 hcov with hδ
  set q : Homology (Tor Y) 1 →ₗ[ℤ] K :=
    δ.codRestrict K (fun x => LinearMap.mem_ker.mpr (mvHomDiagInt_mvDeltaInt _ _ _ hcov x)) with hq
  have hqsurj : Function.Surjective q := by
    rintro ⟨y, hy⟩
    have hyr : y ∈ LinearMap.range δ := by
      rw [← (mv_exact_interInt (covA Y v) (covB Y v) 0 hcov).linearMap_ker_eq]; exact hy
    obtain ⟨x, hx⟩ := hyr
    exact ⟨x, Subtype.ext hx⟩
  have hkerq : LinearMap.ker q = LinearMap.range (alphaGen Y v 0) := by
    rw [hq, LinearMap.ker_codRestrict]; exact (alphaGen_range_eq_ker_delta Y v 0).symm
  haveI hαF : Module.Free ℤ ↥(LinearMap.range (alphaGen Y v 0)) :=
    Module.Free.of_equiv (LinearEquiv.ofInjective (alphaGen Y v 0) (alphaGen_injective Y v 0))
  haveI hαFin : Module.Finite ℤ ↥(LinearMap.range (alphaGen Y v 0)) :=
    Module.Finite.equiv (LinearEquiv.ofInjective (alphaGen Y v 0) (alphaGen_injective Y v 0))
  haveI hKerqF : Module.Free ℤ ↥(LinearMap.ker q) :=
    Module.Free.of_equiv (LinearEquiv.ofEq _ _ hkerq).symm
  haveI hKerqFin : Module.Finite ℤ ↥(LinearMap.ker q) :=
    Module.Finite.equiv (LinearEquiv.ofEq _ _ hkerq).symm
  have hkerq_fin : Module.finrank ℤ ↥(LinearMap.ker q) = Module.finrank ℤ (Homology Y 1) := by
    rw [(LinearEquiv.ofEq _ _ hkerq).finrank_eq,
      ← (LinearEquiv.ofInjective (alphaGen Y v 0) (alphaGen_injective Y v 0)).finrank_eq]
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hqsurj)
  have hexact : Function.Exact (⇑(LinearMap.ker q).subtype) (⇑q) := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  set e : Homology (Tor Y) 1 ≃ₗ[ℤ] (↥(LinearMap.ker q) × K) :=
    (hexact.splitSurjectiveEquiv (Submodule.injective_subtype _) ⟨s, hs⟩).1 with he
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, Module.finrank_prod, hkerq_fin, hKfin]

end SKEFTHawking.KummerTorusStep
