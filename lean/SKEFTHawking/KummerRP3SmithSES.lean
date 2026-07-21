import Mathlib
import SKEFTHawking.ChainComplexLESInt
import SKEFTHawking.KummerRP3TransferInt
import SKEFTHawking.KummerRP3SphereHomeo

/-!
# The interlocking integral Smith SESs of `S³ → ℝP³`, instantiated

This module feeds the abstract SES→LES engine (`ChainComplexLESInt`) with the two interlocking
short exact sequences of the antipodal double cover (all levelwise facts banked in
`SingularInvolutionSmithInt` + `KummerRP3TransferInt`):

* **SES-III** `0 → B → C(S³) --p₊--> C(ℝP³) → 0` (`B = D·C`, `ker p₊ = im D`),
* **SES-I** `0 → A → C(S³) --D'--> B → 0` (`A = N·C`, `ker D = im N`),

and computes the low-degree homology of the subcomplexes by augmentation:

* `hmlEquivHomology` — the engine's `Hml (chainBoundary X) ≅ Homology X` bridge,
* `hmlB_zero_equiv : H₀(B;ℤ) ≅ ℤ/2` (the norm-parity class — the torsion seed of `H₁(ℝP³)`),
* `Hmap_inclB_zero` — `H₀(B) → H₀(S³)` is the zero map,
* `Hmap_inclA_zero_injective` — `H₀(A) → H₀(S³)` is injective,
* `hmlB_one_eq_zero : H₁(B;ℤ) = 0` (via the SES-I LES against `H₁(S³) = 0`).

The solve (`KummerRP3HomologySolve`) chains these through the SES-III LES to get
`H₂(ℝP³;ℤ) = 0` (the K7 `b₂` priority) and `H₁(ℝP³;ℤ) ≅ ℤ/2`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3Covering (S3top RP3top mkRP3C negS3C negS3C_comp_negS3C
  normChain diffChain chainBoundary_diffChain chainBoundary_normChain diffChain_normChain
  normChain_diffChain)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology
  boundary_comp_boundary)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single
  augmentationInt_chainBoundary augmentationInt_mapChainInt)
open SKEFTHawking.SingularInvolutionSmithInt (ker_diffChain_eq_range_normChain
  ker_normChain_eq_range_diffChain)
open SKEFTHawking.KummerRP3TransferInt (mapSimplex_negS3C_ne mapChainInt_surjective
  ker_mapChainInt_eq_range_diffChain)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.ChainComplexLESInt

namespace SKEFTHawking.KummerRP3SmithSES

noncomputable section

/-! ## §0. The engine ↔ project homology bridge -/

/-- **The engine-homology bridge**: the abstract `Hml` of the singular chain complex IS the
project's `Homology` (the definitions agree by cases on the degree). -/
def hmlEquivHomology (X : TopCat) (n : ℕ) :
    Hml (chainBoundary X) n ≃ₗ[ℤ] Homology X n :=
  match n with
  | 0 => LinearEquiv.refl ℤ _
  | _ + 1 => LinearEquiv.refl ℤ _

/-- Transported sphere input: `Hml`-form `H₁(S³;ℤ) = 0`. -/
theorem hml_s3_one_eq_zero (x : Hml (chainBoundary S3top) 1) : x = 0 := by
  have h := SKEFTHawking.KummerRP3SphereHomeo.s3_homology_one_eq_zero
    (hmlEquivHomology S3top 1 x)
  have h2 := (hmlEquivHomology S3top 1).symm_apply_apply x
  rw [h, map_zero] at h2
  exact h2.symm

/-- Transported sphere input: `Hml`-form `H₂(S³;ℤ) = 0`. -/
theorem hml_s3_two_eq_zero (x : Hml (chainBoundary S3top) 2) : x = 0 := by
  have h := SKEFTHawking.KummerRP3SphereHomeo.s3_homology_two_eq_zero
    (hmlEquivHomology S3top 2 x)
  have h2 := (hmlEquivHomology S3top 2).symm_apply_apply x
  rw [h, map_zero] at h2
  exact h2.symm

/-! ## §1. The subcomplexes `B = D·C` and `A = N·C` -/

/-- The difference subcomplex `Bₙ = D·Cₙ(S³;ℤ)` as a submodule. -/
def Bmod (n : ℕ) : Submodule ℤ (SingularChainInt S3top n) :=
  LinearMap.range (diffChain negS3C n)

/-- The norm subcomplex `Aₙ = N·Cₙ(S³;ℤ)` as a submodule. -/
def Amod (n : ℕ) : Submodule ℤ (SingularChainInt S3top n) :=
  LinearMap.range (normChain negS3C n)

/-- The `B`-subcomplex carrier family (named, so the engine's higher-order unification
pattern-solves the carrier). -/
abbrev Bc (n : ℕ) : Type := ↥(Bmod n)

/-- The `A`-subcomplex carrier family. -/
abbrev Ac (n : ℕ) : Type := ↥(Amod n)

/-- The boundary restricts to `B` (D is a chain map). -/
theorem boundary_mem_Bmod {n : ℕ} {c : SingularChainInt S3top (n + 1)} (hc : c ∈ Bmod (n + 1)) :
    chainBoundary S3top n c ∈ Bmod n := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨chainBoundary S3top n w, (chainBoundary_diffChain negS3C n w).symm⟩

/-- The boundary restricts to `A` (N is a chain map). -/
theorem boundary_mem_Amod {n : ℕ} {c : SingularChainInt S3top (n + 1)} (hc : c ∈ Amod (n + 1)) :
    chainBoundary S3top n c ∈ Amod n := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨chainBoundary S3top n w, (chainBoundary_normChain negS3C n w).symm⟩

/-- The differential of the `B`-subcomplex. -/
def dB (n : ℕ) : Bc (n + 1) →ₗ[ℤ] Bc n :=
  (chainBoundary S3top n).restrict (fun _c hc => boundary_mem_Bmod hc)

/-- The differential of the `A`-subcomplex. -/
def dA (n : ℕ) : Ac (n + 1) →ₗ[ℤ] Ac n :=
  (chainBoundary S3top n).restrict (fun _c hc => boundary_mem_Amod hc)

/-! ## §2. The SES hypothesis packages -/

/-- `∂∘∂ = 0` for the middle complex `C(S³)`. -/
theorem hddC : ∀ (n : ℕ) (x : SingularChainInt S3top (n + 2)),
    chainBoundary S3top n (chainBoundary S3top (n + 1) x) = 0 :=
  fun n x => boundary_comp_boundary S3top n x

/-- SES-III mono leg: the inclusion `B ↪ C` is a chain map. -/
theorem hf_inclB : ∀ (n : ℕ) (x : ↥(Bmod (n + 1))),
    chainBoundary S3top n ((Bmod (n + 1)).subtype x) = (Bmod n).subtype (dB n x) :=
  fun _n _x => rfl

/-- SES-III epi leg: `p₊ = mapChainInt mkRP3C` is a chain map. -/
theorem hg_proj : ∀ (n : ℕ) (x : SingularChainInt S3top (n + 1)),
    chainBoundary RP3top n (mapChainInt mkRP3C (n + 1) x)
      = mapChainInt mkRP3C n (chainBoundary S3top n x) :=
  fun _n x => SKEFTHawking.SingularFunctorialityInt.chainBoundary_mapChainInt mkRP3C x

theorem hfinj_inclB : ∀ n, Function.Injective ((Bmod n).subtype) :=
  fun n => Submodule.injective_subtype (Bmod n)

theorem hgsurj_proj : ∀ n, Function.Surjective (mapChainInt mkRP3C n) :=
  fun n => mapChainInt_surjective n

/-- SES-III exactness: `im (B ↪ C) = ker p₊`. -/
theorem hexact_III : ∀ n,
    LinearMap.range ((Bmod n).subtype) = LinearMap.ker (mapChainInt mkRP3C n) := by
  intro n
  rw [Submodule.range_subtype, ker_mapChainInt_eq_range_diffChain]
  rfl

/-- SES-I mono leg: the inclusion `A ↪ C` is a chain map. -/
theorem hf_inclA : ∀ (n : ℕ) (x : ↥(Amod (n + 1))),
    chainBoundary S3top n ((Amod (n + 1)).subtype x) = (Amod n).subtype (dA n x) :=
  fun _n _x => rfl

/-- SES-I epi leg: the corestricted difference `D' : C → B` is a chain map. -/
theorem hg_diff : ∀ (n : ℕ) (x : SingularChainInt S3top (n + 1)),
    dB n ((diffChain negS3C (n + 1)).rangeRestrict x)
      = (diffChain negS3C n).rangeRestrict (chainBoundary S3top n x) :=
  fun n x => Subtype.ext (chainBoundary_diffChain negS3C n x)

theorem hfinj_inclA : ∀ n, Function.Injective ((Amod n).subtype) :=
  fun n => Submodule.injective_subtype (Amod n)

theorem hgsurj_diff : ∀ n, Function.Surjective ((diffChain negS3C n).rangeRestrict) :=
  fun n => (diffChain negS3C n).surjective_rangeRestrict

/-- SES-I exactness: `im (A ↪ C) = ker D'` — the generic free-involution Smith exactness. -/
theorem hexact_I : ∀ n,
    LinearMap.range ((Amod n).subtype)
      = LinearMap.ker ((diffChain negS3C n).rangeRestrict) := by
  intro n
  rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict,
    ker_diffChain_eq_range_normChain negS3C_comp_negS3C (fun σ => mapSimplex_negS3C_ne σ)]
  rfl

/-! ## §3. The named LES maps (all engine implicits pinned) -/

/-- The engine's boundaries of the singular complex ARE the project's boundaries. -/
theorem boundaries_eq (X : TopCat) (n : ℕ) :
    ChainComplexLESInt.boundaries (chainBoundary X) n
      = SKEFTHawking.SingularHomologyInt.boundaries X n := rfl

/-- `H(B ↪ C)` — the SES-III mono leg on homology. -/
def inclBH (n : ℕ) : Hml dB n →ₗ[ℤ] Hml (chainBoundary S3top) n :=
  Hmap (dM := dB) (dN := chainBoundary S3top) (f := fun k => (Bmod k).subtype) hf_inclB n

/-- `H(A ↪ C)` — the SES-I mono leg on homology. -/
def inclAH (n : ℕ) : Hml dA n →ₗ[ℤ] Hml (chainBoundary S3top) n :=
  Hmap (dM := dA) (dN := chainBoundary S3top) (f := fun k => (Amod k).subtype) hf_inclA n

/-- `H(p₊)` — the SES-III epi leg on homology. -/
def projH (n : ℕ) : Hml (chainBoundary S3top) n →ₗ[ℤ] Hml (chainBoundary RP3top) n :=
  Hmap (dM := chainBoundary S3top) (dN := chainBoundary RP3top)
    (f := fun k => mapChainInt mkRP3C k) hg_proj n

/-- `H(D')` — the SES-I epi leg on homology. -/
def diffH (n : ℕ) : Hml (chainBoundary S3top) n →ₗ[ℤ] Hml dB n :=
  Hmap (dM := chainBoundary S3top) (dN := dB)
    (f := fun k => (diffChain negS3C k).rangeRestrict) hg_diff n

/-- The SES-III connecting `δ : Hₙ₊₁(ℝP³) → Hₙ(B)`. -/
def deltaIII (n : ℕ) : Hml (chainBoundary RP3top) (n + 1) →ₗ[ℤ] Hml dB n :=
  delta hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- The SES-I connecting `δ' : Hₙ₊₁(B) → Hₙ(A)`. -/
def deltaI (n : ℕ) : Hml dB (n + 1) →ₗ[ℤ] Hml dA n :=
  delta hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-- SES-III LES exactness at `Hₙ₊₁(ℝP³)`: `ker δ = im H(p₊)`. -/
theorem exact_projH_deltaIII (n : ℕ) : Function.Exact (projH (n + 1)) (deltaIII n) :=
  exact_Hmap_delta hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- SES-III LES exactness at `Hₙ(B)`: `ker H(incl B) = im δ`. -/
theorem exact_deltaIII_inclBH (n : ℕ) : Function.Exact (deltaIII n) (inclBH n) :=
  exact_delta_Hmap hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- SES-I LES exactness at `Hₙ₊₁(B)`: `ker δ' = im H(D')`. -/
theorem exact_diffH_deltaI (n : ℕ) : Function.Exact (diffH (n + 1)) (deltaI n) :=
  exact_Hmap_delta hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-- SES-I LES exactness at `Hₙ(A)`: `ker H(incl A) = im δ'`. -/
theorem exact_deltaI_inclAH (n : ℕ) : Function.Exact (deltaI n) (inclAH n) :=
  exact_delta_Hmap hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-! ## §4. Augmentation calculus on the subcomplexes -/

/-- The augmentation kills the difference operator: `ε(D c) = 0`. -/
theorem aug_diffChain (c : SingularChainInt S3top 0) :
    augmentationInt S3top (diffChain negS3C 0 c) = 0 := by
  show augmentationInt S3top (c - mapChainInt negS3C 0 c) = 0
  rw [map_sub, augmentationInt_mapChainInt, sub_self]

/-- The augmentation doubles on the norm operator: `ε(N c) = 2·ε(c)`. -/
theorem aug_normChain (c : SingularChainInt S3top 0) :
    augmentationInt S3top (normChain negS3C 0 c) = 2 * augmentationInt S3top c := by
  show augmentationInt S3top (c + mapChainInt negS3C 0 c) = _
  rw [map_add, augmentationInt_mapChainInt, two_mul]

/-- A basepoint of the `ℂ²`-sphere. -/
def basePt : S3 := ⟨((1 : ℂ), (0 : ℂ)), by simp⟩

/-- Path-connectedness of the covering sphere, on the `TopCat` carrier. -/
instance : PathConnectedSpace ↑S3top :=
  SKEFTHawking.KummerK7Opener.instPathConnectedS3

/-- The basepoint's constant `0`-simplex. -/
def baseSimplex : (TopCat.toSSet.obj S3top).obj (op (SimplexCategory.mk 0)) :=
  constSimplex (X := S3top) basePt 0

theorem aug_single_baseSimplex : augmentationInt S3top (Finsupp.single baseSimplex 1) = 1 :=
  augmentationInt_single S3top baseSimplex 1

/-! ## §5. `H₀(B;ℤ) ≅ ℤ/2` — the norm-parity class -/

/-- The mod-2 augmentation `C₀(S³;ℤ) → ℤ/2`. -/
def mod2aug : SingularChainInt S3top 0 →ₗ[ℤ] ZMod 2 :=
  (Int.castAddHom (ZMod 2)).toIntLinearMap.comp (augmentationInt S3top)

theorem mod2aug_apply (c : SingularChainInt S3top 0) :
    mod2aug c = ((augmentationInt S3top c : ℤ) : ZMod 2) := rfl

/-- `mod2aug` kills the norm subcomplex `A₀` (its augmentations are even). -/
theorem mod2aug_Amod (a : SingularChainInt S3top 0) (ha : a ∈ Amod 0) : mod2aug a = 0 := by
  obtain ⟨c, rfl⟩ := ha
  rw [mod2aug_apply, aug_normChain]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact ⟨augmentationInt S3top c, by push_cast; ring⟩

/-- `ker D₀ = A₀` — the generic free-involution Smith exactness at level 0. -/
theorem kerD_eq_Amod : LinearMap.ker (diffChain negS3C 0) = Amod 0 := by
  rw [ker_diffChain_eq_range_normChain negS3C_comp_negS3C (fun σ => mapSimplex_negS3C_ne σ)]
  rfl

/-- The first-isomorphism identification `B₀ ≅ C₀/A₀`. -/
def bQuotEquiv : Bc 0 ≃ₗ[ℤ] (SingularChainInt S3top 0 ⧸ Amod 0) :=
  (LinearMap.quotKerEquivRange (diffChain negS3C 0)).symm.trans
    (Submodule.quotEquivOfEq _ _ kerD_eq_Amod)

/-- The mod-2 augmentation descended to `C₀/A₀`. -/
def thetaA : (SingularChainInt S3top 0 ⧸ Amod 0) →ₗ[ℤ] ZMod 2 :=
  Submodule.liftQ (Amod 0) mod2aug (fun a ha => mod2aug_Amod a ha)

/-- **The norm-parity functional** `ψ : B₀ → ℤ/2`: for `b = D c`, `ψ b = ε(c) mod 2`
(well-defined: two `D`-preimages differ by `ker D = A₀`, whose augmentation is even). -/
def psiB : Bc 0 →ₗ[ℤ] ZMod 2 := thetaA.comp bQuotEquiv.toLinearMap

/-- **The `ψ` computation rule**: for ANY `c` with `D c = b`, `ψ b = ε(c) mod 2`. -/
theorem psiB_spec (b : Bc 0) (c : SingularChainInt S3top 0)
    (hc : diffChain negS3C 0 c = (b : SingularChainInt S3top 0)) :
    psiB b = ((augmentationInt S3top c : ℤ) : ZMod 2) := by
  have h1 : LinearMap.quotKerEquivRange (diffChain negS3C 0)
      (Submodule.Quotient.mk c) = b := by
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
    exact hc
  have h2 : (LinearMap.quotKerEquivRange (diffChain negS3C 0)).symm b
      = Submodule.Quotient.mk c := by
    rw [← h1, LinearEquiv.symm_apply_apply]
  show thetaA (bQuotEquiv b) = _
  rw [show bQuotEquiv b = (Submodule.quotEquivOfEq _ _ kerD_eq_Amod)
      ((LinearMap.quotKerEquivRange (diffChain negS3C 0)).symm b) from rfl,
    h2, Submodule.quotEquivOfEq_mk]
  show mod2aug c = _
  rw [mod2aug_apply]

/-- `ψ` of the basepoint difference class is `1`. -/
theorem psiB_base :
    psiB ⟨diffChain negS3C 0 (Finsupp.single baseSimplex 1),
      ⟨Finsupp.single baseSimplex 1, rfl⟩⟩ = 1 := by
  rw [psiB_spec _ (Finsupp.single baseSimplex 1) rfl, aug_single_baseSimplex]
  rfl

/-- `ψ` kills the `B`-boundaries (`∂B₁ ∋ ∂(D w) = D(∂ w)`, and `ε∘∂ = 0`). -/
theorem psiB_boundary (z : ↥(Bmod 0)) (hz : z ∈ ChainComplexLESInt.boundaries dB 0) :
    psiB z = 0 := by
  obtain ⟨w, hw⟩ := hz
  obtain ⟨v, hv⟩ := w.2
  have hzc : diffChain negS3C 0 (chainBoundary S3top 0 v) = (z : SingularChainInt S3top 0) := by
    have h1 : (z : SingularChainInt S3top 0) = chainBoundary S3top 0 (w : _) := by
      rw [← hw]
      rfl
    rw [h1, ← hv, chainBoundary_diffChain]
  rw [psiB_spec z _ hzc, augmentationInt_chainBoundary]
  rfl

/-- **`H₀(B;ℤ) → ℤ/2`, on classes** — descends `ψ` through the boundary quotient. -/
def phiB : Hml dB 0 →ₗ[ℤ] ZMod 2 :=
  Submodule.liftQ _ (psiB.comp (ChainComplexLESInt.cycles dB 0).subtype) (by
    rintro z hz
    rw [mem_submoduleOf] at hz
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    exact psiB_boundary _ hz)

theorem phiB_mk (z : ChainComplexLESInt.cycles dB 0) :
    phiB (Hml.mk dB 0 z) = psiB (z : ↥(Bmod 0)) := rfl

/-- **`φ : H₀(B;ℤ) → ℤ/2` is injective**: an even-parity `B₀`-chain is a `B`-boundary
(correct the parity by a norm chain, then fill by path-connectedness of `S³`). -/
theorem phiB_injective : Function.Injective phiB := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dB 0 x
  rw [LinearMap.mem_ker, phiB_mk] at hx
  obtain ⟨c, hc⟩ := (z : ↥(Bmod 0)).2
  rw [psiB_spec _ c hc, ZMod.intCast_zmod_eq_zero_iff_dvd] at hx
  obtain ⟨m, hm⟩ := hx
  set c' := c - m • normChain negS3C 0 (Finsupp.single baseSimplex 1) with hc'
  have haug : augmentationInt S3top c' = 0 := by
    rw [hc', map_sub, map_smul, aug_normChain, aug_single_baseSimplex, hm]
    push_cast
    ring
  have hbd : c' ∈ SKEFTHawking.SingularHomologyInt.boundaries S3top 0 :=
    SKEFTHawking.SingularH0PathConnectedInt.mem_boundaries_of_augmentationInt_eq_zero
      (X := S3top) basePt c' haug
  obtain ⟨w, hw⟩ := hbd
  have hDc' : diffChain negS3C 0 c' = (z : ↥(Bmod 0)) := by
    rw [hc', map_sub, map_smul, ← LinearMap.comp_apply, diffChain_normChain
      negS3C_comp_negS3C, LinearMap.zero_apply, smul_zero, sub_zero]
    exact hc
  rw [Hml.mk_eq_zero_iff]
  refine ⟨⟨diffChain negS3C 1 w, ⟨w, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show chainBoundary S3top 0 (diffChain negS3C 1 w) = _
  rw [chainBoundary_diffChain, hw, hDc']

/-- **`φ : H₀(B;ℤ) → ℤ/2` is surjective** (the basepoint difference class hits `1`). -/
theorem phiB_surjective : Function.Surjective phiB := by
  intro t
  have hcases : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases hcases t with ht | ht
  · exact ⟨0, by rw [map_zero, ht]⟩
  · refine ⟨Hml.mk dB 0 ⟨⟨diffChain negS3C 0 (Finsupp.single baseSimplex 1),
      ⟨Finsupp.single baseSimplex 1, rfl⟩⟩, Submodule.mem_top⟩, ?_⟩
    rw [phiB_mk, psiB_base, ht]

/-- **`H₀(B;ℤ) ≅ ℤ/2`** — the norm-parity class of the difference subcomplex: the torsion seed
that becomes `H₁(ℝP³;ℤ) ≅ ℤ/2` through the SES-III connecting map. -/
def hmlB_zero_equiv : Hml dB 0 ≃ₗ[ℤ] ZMod 2 :=
  LinearEquiv.ofBijective phiB ⟨phiB_injective, phiB_surjective⟩

/-! ## §6. The degree-0 inclusion maps -/

/-- **`H₀(B) → H₀(S³) is zero**: every `B₀`-chain has augmentation `0`, hence bounds in `C(S³)`
(path-connectedness). -/
theorem inclBH_zero (x : Hml dB 0) : inclBH 0 x = 0 := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dB 0 x
  have hrw : inclBH 0 (Hml.mk dB 0 z)
      = Hml.mk (chainBoundary S3top) 0 (cyclesMap (dM := dB) (dN := chainBoundary S3top)
          (f := fun k => (Bmod k).subtype) hf_inclB 0 z) := rfl
  rw [hrw, Hml.mk_eq_zero_iff]
  obtain ⟨c, hc⟩ := (z : Bc 0).2
  have hmem : ((z : Bc 0) : SingularChainInt S3top 0)
      ∈ SKEFTHawking.SingularHomologyInt.boundaries S3top 0 := by
    refine SKEFTHawking.SingularH0PathConnectedInt.mem_boundaries_of_augmentationInt_eq_zero
      (X := S3top) basePt _ ?_
    rw [← hc, aug_diffChain]
  exact hmem

/-- **`H₀(A) → H₀(S³) is injective**: an `A₀`-chain bounding in `C(S³)` has augmentation `0`;
halving (`ε(Nc) = 2ε(c)`) and filling `c` by path-connectedness exhibits it as an `A`-boundary. -/
theorem inclAH_injective : Function.Injective (inclAH 0) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dA 0 x
  rw [LinearMap.mem_ker] at hx
  have hrwA : inclAH 0 (Hml.mk dA 0 z)
      = Hml.mk (chainBoundary S3top) 0 (cyclesMap (dM := dA) (dN := chainBoundary S3top)
          (f := fun k => (Amod k).subtype) hf_inclA 0 z) := rfl
  rw [hrwA, Hml.mk_eq_zero_iff] at hx
  obtain ⟨w, hw⟩ := hx
  have hw' : chainBoundary S3top 0 w = ((z : Ac 0) : SingularChainInt S3top 0) := hw
  obtain ⟨c, hc⟩ := (z : Ac 0).2
  have haugz : augmentationInt S3top ((z : Ac 0) : SingularChainInt S3top 0) = 0 := by
    rw [← hw', augmentationInt_chainBoundary]
  have haugc : augmentationInt S3top c = 0 := by
    rw [← hc, aug_normChain] at haugz
    omega
  obtain ⟨v, hv⟩ :=
    SKEFTHawking.SingularH0PathConnectedInt.mem_boundaries_of_augmentationInt_eq_zero
      (X := S3top) basePt c haugc
  rw [Hml.mk_eq_zero_iff]
  refine ⟨⟨normChain negS3C 1 v, ⟨v, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show chainBoundary S3top 0 (normChain negS3C 1 v) = _
  rw [chainBoundary_normChain, hv, hc]

/-! ## §7. `H₁(B;ℤ) = 0` — the SES-I LES against `H₁(S³) = 0` -/

/-- **`H₁(B;ℤ) = 0`**: the SES-I connecting embeds `H₁(B)` into `H₀(A)` (as the kernel of the
injective `H₀(A) → H₀(S³)`), and its incoming map factors through `H₁(S³) = 0`. -/
theorem hmlB_one_eq_zero (x : Hml dB 1) : x = 0 := by
  -- δ'₀ x dies in H₀(A) since H(inclA)(δ'₀ x) = 0 and H(inclA) is injective
  have hcomp : inclAH 0 (deltaI 0 x) = 0 :=
    (exact_deltaI_inclAH 0).apply_apply_eq_zero x
  have hdelta : deltaI 0 x = 0 := by
    apply inclAH_injective
    rw [hcomp, map_zero]
  -- exactness at H₁(B): x comes from H₁(S³) = 0
  obtain ⟨y, hy⟩ := (exact_diffH_deltaI 0 x).mp hdelta
  rw [← hy, hml_s3_one_eq_zero y, map_zero]

end

end SKEFTHawking.KummerRP3SmithSES
