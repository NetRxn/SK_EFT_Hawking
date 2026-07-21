import Mathlib
import SKEFTHawking.ChainComplexLESInt
import SKEFTHawking.KummerQuotientTransferInt
import SKEFTHawking.KummerRP3SmithSES
import SKEFTHawking.KummerPuncturedPathConn

/-!
# The interlocking integral Smith SESs of `T⁴° → Q`, instantiated

The `Q = T⁴°/τ` mirror of `KummerRP3SmithSES`: the abstract SES→LES engine
(`ChainComplexLESInt`) fed with the two interlocking short exact sequences of the free double
cover `qmk : T⁴° ↠ Q` (levelwise facts banked in `SingularInvolutionSmithInt` +
`KummerQuotientTransferInt`):

* **SES-III** `0 → B → C(T⁴°) --p₊--> C(Q) → 0` (`B = D·C`, `ker p₊ = im D`),
* **SES-I** `0 → A → C(T⁴°) --D'--> B → 0` (`A = N·C`, `ker D = im N`),

with the named LES maps (`inclBH`, `inclAH`, `projH`, `diffH`, `deltaIII`, `deltaI`), all four
exactness statements, the homology-level transfer `transferH` and deck action `tauH` with the two
**composition identities**

* `transferH_projH : t ∘ p̄ = 1 + τ_*` (from the chain identity `tr ∘ p₊ = N`),
* `inclBH_diffH : ι_B ∘ D̄ = 1 − τ_*`,

and the degree-0 augmentation calculus on the path-connected `T⁴°`
(`KummerPuncturedPathConn`):

* `inclAH_injective` — `H₀(A) → H₀(T⁴°)` is injective,
* `deltaI_zero_eq_zero` — the SES-I connecting `H₁(B) → H₀(A)` vanishes,
* `diffH_one_surjective` — `D̄ : H₁(T⁴°) → H₁(B)` is onto.

The solve (`KummerQuotientH2Solve`) chains these with the `τ_*`-eigenvalue detection to get
`H₂(Q;ℤ) ≅ ℤ⁶` — the single open input of the K7 `b₂ = 22` window.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open CategoryTheory Opposite
open SKEFTHawking.KummerQuotientCovering (PTtop Qtop tauC qmkC tauC_comp_self)
open SKEFTHawking.KummerPuncturedTorus (puncturedTorus)
open SKEFTHawking.KummerFreeQuotient (witnessPoint witnessPoint_mem)
open SKEFTHawking.KummerRP3Covering (normChain diffChain chainBoundary_diffChain
  chainBoundary_normChain)
open SKEFTHawking.SingularHomologyInt (SingularChainInt chainBoundary Homology
  boundary_comp_boundary)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt)
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single
  augmentationInt_chainBoundary augmentationInt_mapChainInt)
open SKEFTHawking.SingularInvolutionSmithInt (ker_diffChain_eq_range_normChain
  ker_normChain_eq_range_diffChain)
open SKEFTHawking.KummerQuotientTransferInt (mapSimplex_tauC_ne mapChainInt_surjective
  ker_mapChainInt_eq_range_diffChain transferChainInt chainBoundary_transferChainInt
  transferChainInt_mapChainInt)
open SKEFTHawking.SingularHomotopyInvariance (constSimplex)
open SKEFTHawking.ChainComplexLESInt
open SKEFTHawking.KummerRP3SmithSES (hmlEquivHomology boundaries_eq)

namespace SKEFTHawking.KummerQuotientSmithSES

noncomputable section

/-! ## §1. The subcomplexes `B = D·C` and `A = N·C` -/

/-- The difference subcomplex `Bₙ = D·Cₙ(T⁴°;ℤ)` as a submodule. -/
def Bmod (n : ℕ) : Submodule ℤ (SingularChainInt PTtop n) :=
  LinearMap.range (diffChain tauC n)

/-- The norm subcomplex `Aₙ = N·Cₙ(T⁴°;ℤ)` as a submodule. -/
def Amod (n : ℕ) : Submodule ℤ (SingularChainInt PTtop n) :=
  LinearMap.range (normChain tauC n)

/-- The `B`-subcomplex carrier family. -/
abbrev Bc (n : ℕ) : Type := ↥(Bmod n)

/-- The `A`-subcomplex carrier family. -/
abbrev Ac (n : ℕ) : Type := ↥(Amod n)

/-- The boundary restricts to `B` (D is a chain map). -/
theorem boundary_mem_Bmod {n : ℕ} {c : SingularChainInt PTtop (n + 1)} (hc : c ∈ Bmod (n + 1)) :
    chainBoundary PTtop n c ∈ Bmod n := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨chainBoundary PTtop n w, (chainBoundary_diffChain tauC n w).symm⟩

/-- The boundary restricts to `A` (N is a chain map). -/
theorem boundary_mem_Amod {n : ℕ} {c : SingularChainInt PTtop (n + 1)} (hc : c ∈ Amod (n + 1)) :
    chainBoundary PTtop n c ∈ Amod n := by
  obtain ⟨w, rfl⟩ := hc
  exact ⟨chainBoundary PTtop n w, (chainBoundary_normChain tauC n w).symm⟩

/-- The differential of the `B`-subcomplex. -/
def dB (n : ℕ) : Bc (n + 1) →ₗ[ℤ] Bc n :=
  (chainBoundary PTtop n).restrict (fun _c hc => boundary_mem_Bmod hc)

/-- The differential of the `A`-subcomplex. -/
def dA (n : ℕ) : Ac (n + 1) →ₗ[ℤ] Ac n :=
  (chainBoundary PTtop n).restrict (fun _c hc => boundary_mem_Amod hc)

/-! ## §2. The SES hypothesis packages -/

/-- `∂∘∂ = 0` for the middle complex `C(T⁴°)`. -/
theorem hddC : ∀ (n : ℕ) (x : SingularChainInt PTtop (n + 2)),
    chainBoundary PTtop n (chainBoundary PTtop (n + 1) x) = 0 :=
  fun n x => boundary_comp_boundary PTtop n x

/-- SES-III mono leg: the inclusion `B ↪ C` is a chain map. -/
theorem hf_inclB : ∀ (n : ℕ) (x : ↥(Bmod (n + 1))),
    chainBoundary PTtop n ((Bmod (n + 1)).subtype x) = (Bmod n).subtype (dB n x) :=
  fun _n _x => rfl

/-- SES-III epi leg: `p₊ = mapChainInt qmkC` is a chain map. -/
theorem hg_proj : ∀ (n : ℕ) (x : SingularChainInt PTtop (n + 1)),
    chainBoundary Qtop n (mapChainInt qmkC (n + 1) x)
      = mapChainInt qmkC n (chainBoundary PTtop n x) :=
  fun _n x => SKEFTHawking.SingularFunctorialityInt.chainBoundary_mapChainInt qmkC x

theorem hfinj_inclB : ∀ n, Function.Injective ((Bmod n).subtype) :=
  fun n => Submodule.injective_subtype (Bmod n)

theorem hgsurj_proj : ∀ n, Function.Surjective (mapChainInt qmkC n) :=
  fun n => mapChainInt_surjective n

/-- SES-III exactness: `im (B ↪ C) = ker p₊`. -/
theorem hexact_III : ∀ n,
    LinearMap.range ((Bmod n).subtype) = LinearMap.ker (mapChainInt qmkC n) := by
  intro n
  rw [Submodule.range_subtype, ker_mapChainInt_eq_range_diffChain]
  rfl

/-- SES-I mono leg: the inclusion `A ↪ C` is a chain map. -/
theorem hf_inclA : ∀ (n : ℕ) (x : ↥(Amod (n + 1))),
    chainBoundary PTtop n ((Amod (n + 1)).subtype x) = (Amod n).subtype (dA n x) :=
  fun _n _x => rfl

/-- SES-I epi leg: the corestricted difference `D' : C → B` is a chain map. -/
theorem hg_diff : ∀ (n : ℕ) (x : SingularChainInt PTtop (n + 1)),
    dB n ((diffChain tauC (n + 1)).rangeRestrict x)
      = (diffChain tauC n).rangeRestrict (chainBoundary PTtop n x) :=
  fun n x => Subtype.ext (chainBoundary_diffChain tauC n x)

theorem hfinj_inclA : ∀ n, Function.Injective ((Amod n).subtype) :=
  fun n => Submodule.injective_subtype (Amod n)

theorem hgsurj_diff : ∀ n, Function.Surjective ((diffChain tauC n).rangeRestrict) :=
  fun n => (diffChain tauC n).surjective_rangeRestrict

/-- SES-I exactness: `im (A ↪ C) = ker D'` — the generic free-involution Smith exactness. -/
theorem hexact_I : ∀ n,
    LinearMap.range ((Amod n).subtype)
      = LinearMap.ker ((diffChain tauC n).rangeRestrict) := by
  intro n
  rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict,
    ker_diffChain_eq_range_normChain tauC_comp_self (fun σ => mapSimplex_tauC_ne σ)]
  rfl

/-! ## §3. The named LES maps and the composition identities -/

/-- `H(B ↪ C)` — the SES-III mono leg on homology. -/
def inclBH (n : ℕ) : Hml dB n →ₗ[ℤ] Hml (chainBoundary PTtop) n :=
  Hmap (dM := dB) (dN := chainBoundary PTtop) (f := fun k => (Bmod k).subtype) hf_inclB n

/-- `H(A ↪ C)` — the SES-I mono leg on homology. -/
def inclAH (n : ℕ) : Hml dA n →ₗ[ℤ] Hml (chainBoundary PTtop) n :=
  Hmap (dM := dA) (dN := chainBoundary PTtop) (f := fun k => (Amod k).subtype) hf_inclA n

/-- `H(p₊)` — the SES-III epi leg on homology. -/
def projH (n : ℕ) : Hml (chainBoundary PTtop) n →ₗ[ℤ] Hml (chainBoundary Qtop) n :=
  Hmap (dM := chainBoundary PTtop) (dN := chainBoundary Qtop)
    (f := fun k => mapChainInt qmkC k) hg_proj n

/-- `H(D')` — the SES-I epi leg on homology. -/
def diffH (n : ℕ) : Hml (chainBoundary PTtop) n →ₗ[ℤ] Hml dB n :=
  Hmap (dM := chainBoundary PTtop) (dN := dB)
    (f := fun k => (diffChain tauC k).rangeRestrict) hg_diff n

/-- The SES-III connecting `δ : Hₙ₊₁(Q) → Hₙ(B)`. -/
def deltaIII (n : ℕ) : Hml (chainBoundary Qtop) (n + 1) →ₗ[ℤ] Hml dB n :=
  delta hf_inclB hg_proj hddC hfinj_inclB hgsurj_proj hexact_III n

/-- The SES-I connecting `δ' : Hₙ₊₁(B) → Hₙ(A)`. -/
def deltaI (n : ℕ) : Hml dB (n + 1) →ₗ[ℤ] Hml dA n :=
  delta hf_inclA hg_diff hddC hfinj_inclA hgsurj_diff hexact_I n

/-- SES-III LES exactness at `Hₙ₊₁(Q)`: `ker δ = im H(p₊)`. -/
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

/-- The homology-level deck action `τ_* : Hₙ(T⁴°) → Hₙ(T⁴°)`. -/
def tauH (n : ℕ) : Hml (chainBoundary PTtop) n →ₗ[ℤ] Hml (chainBoundary PTtop) n :=
  Hmap (dM := chainBoundary PTtop) (dN := chainBoundary PTtop)
    (f := fun k => mapChainInt tauC k)
    (fun _n x => SKEFTHawking.SingularFunctorialityInt.chainBoundary_mapChainInt tauC x) n

/-- The homology-level transfer `t : Hₙ(Q) → Hₙ(T⁴°)`. -/
def transferH (n : ℕ) : Hml (chainBoundary Qtop) n →ₗ[ℤ] Hml (chainBoundary PTtop) n :=
  Hmap (dM := chainBoundary Qtop) (dN := chainBoundary PTtop)
    (f := fun k => transferChainInt k)
    (fun n c => (chainBoundary_transferChainInt n c).symm ▸
      (chainBoundary_transferChainInt n c)) n

/-- **`t ∘ p̄ = 1 + τ_*` on `Hₙ(T⁴°)`** — the homology norm identity, from the chain identity
`tr ∘ p₊ = N` (`transferChainInt_mapChainInt`). -/
theorem transferH_projH (n : ℕ) (x : Hml (chainBoundary PTtop) n) :
    transferH n (projH n x) = x + tauH n x := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary PTtop) n x
  show transferH n (projH n (Hml.mk (chainBoundary PTtop) n z))
    = Hml.mk (chainBoundary PTtop) n z + tauH n (Hml.mk (chainBoundary PTtop) n z)
  have h1 : transferH n (projH n (Hml.mk (chainBoundary PTtop) n z))
      = Hml.mk (chainBoundary PTtop) n
        ⟨transferChainInt n (mapChainInt qmkC n (z : SingularChainInt PTtop n)), by
          have hz := map_mem_cycles (dM := chainBoundary PTtop) (dN := chainBoundary Qtop)
            (f := fun k => mapChainInt qmkC k) hg_proj z.2
          exact map_mem_cycles (dM := chainBoundary Qtop) (dN := chainBoundary PTtop)
            (f := fun k => transferChainInt k)
            (fun n c => chainBoundary_transferChainInt n c) hz⟩ := rfl
  rw [h1]
  have h2 : tauH n (Hml.mk (chainBoundary PTtop) n z)
      = Hml.mk (chainBoundary PTtop) n
        ⟨mapChainInt tauC n (z : SingularChainInt PTtop n),
          map_mem_cycles (dM := chainBoundary PTtop) (dN := chainBoundary PTtop)
            (f := fun k => mapChainInt tauC k)
            (fun _n x => SKEFTHawking.SingularFunctorialityInt.chainBoundary_mapChainInt tauC x)
            z.2⟩ := rfl
  rw [h2]
  rw [show Hml.mk (chainBoundary PTtop) n z + Hml.mk (chainBoundary PTtop) n
        ⟨mapChainInt tauC n (z : SingularChainInt PTtop n), _⟩
      = Hml.mk (chainBoundary PTtop) n
        (z + ⟨mapChainInt tauC n (z : SingularChainInt PTtop n), _⟩) from rfl]
  congr 1
  apply Subtype.ext
  show transferChainInt n (mapChainInt qmkC n (z : SingularChainInt PTtop n))
    = (z : SingularChainInt PTtop n) + mapChainInt tauC n (z : SingularChainInt PTtop n)
  rw [transferChainInt_mapChainInt]
  rfl

/-- **`ι_B ∘ D̄ = 1 − τ_*` on `Hₙ(T⁴°)`** — the inclusion of the corestricted difference is the
difference operator on homology. -/
theorem inclBH_diffH (n : ℕ) (x : Hml (chainBoundary PTtop) n) :
    inclBH n (diffH n x) = x - tauH n x := by
  obtain ⟨z, rfl⟩ := Hml.mk_surjective (chainBoundary PTtop) n x
  have h1 : inclBH n (diffH n (Hml.mk (chainBoundary PTtop) n z))
      = Hml.mk (chainBoundary PTtop) n
        ⟨(Bmod n).subtype ((diffChain tauC n).rangeRestrict (z : SingularChainInt PTtop n)), by
          have hz := map_mem_cycles (dM := chainBoundary PTtop) (dN := dB)
            (f := fun k => (diffChain tauC k).rangeRestrict) hg_diff z.2
          exact map_mem_cycles (dM := dB) (dN := chainBoundary PTtop)
            (f := fun k => (Bmod k).subtype) hf_inclB hz⟩ := rfl
  rw [h1]
  have h2 : tauH n (Hml.mk (chainBoundary PTtop) n z)
      = Hml.mk (chainBoundary PTtop) n
        ⟨mapChainInt tauC n (z : SingularChainInt PTtop n),
          map_mem_cycles (dM := chainBoundary PTtop) (dN := chainBoundary PTtop)
            (f := fun k => mapChainInt tauC k)
            (fun _n x => SKEFTHawking.SingularFunctorialityInt.chainBoundary_mapChainInt tauC x)
            z.2⟩ := rfl
  rw [h2]
  rw [show Hml.mk (chainBoundary PTtop) n z - Hml.mk (chainBoundary PTtop) n
        ⟨mapChainInt tauC n (z : SingularChainInt PTtop n), _⟩
      = Hml.mk (chainBoundary PTtop) n
        (z - ⟨mapChainInt tauC n (z : SingularChainInt PTtop n), _⟩) from rfl]
  congr 1

/-! ## §4. Augmentation calculus and the degree-0 injectivity -/

/-- The augmentation kills the difference operator: `ε(D c) = 0`. -/
theorem aug_diffChain (c : SingularChainInt PTtop 0) :
    augmentationInt PTtop (diffChain tauC 0 c) = 0 := by
  show augmentationInt PTtop (c - mapChainInt tauC 0 c) = 0
  rw [map_sub, augmentationInt_mapChainInt, sub_self]

/-- The augmentation doubles on the norm operator: `ε(N c) = 2·ε(c)`. -/
theorem aug_normChain (c : SingularChainInt PTtop 0) :
    augmentationInt PTtop (normChain tauC 0 c) = 2 * augmentationInt PTtop c := by
  show augmentationInt PTtop (c + mapChainInt tauC 0 c) = _
  rw [map_add, augmentationInt_mapChainInt, two_mul]

/-- A basepoint of the punctured torus (the banked witness `(i, 1, 1, 1)`). -/
def basePt : ↥puncturedTorus := ⟨witnessPoint, witnessPoint_mem⟩

/-- Path-connectedness of the covering punctured torus, on the `TopCat` carrier. -/
instance : PathConnectedSpace ↑PTtop :=
  inferInstanceAs (PathConnectedSpace (↥puncturedTorus))

/-- The basepoint's constant `0`-simplex. -/
def baseSimplex : (TopCat.toSSet.obj PTtop).obj (op (SimplexCategory.mk 0)) :=
  constSimplex (X := PTtop) basePt 0

theorem aug_single_baseSimplex : augmentationInt PTtop (Finsupp.single baseSimplex 1) = 1 :=
  augmentationInt_single PTtop baseSimplex 1

/-- **`H₀(A) → H₀(T⁴°)` is injective**: an `A₀`-chain bounding in `C(T⁴°)` has augmentation `0`;
halving (`ε(Nc) = 2ε(c)`) and filling `c` by path-connectedness exhibits it as an `A`-boundary. -/
theorem inclAH_injective : Function.Injective (inclAH 0) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Hml.mk_surjective dA 0 x
  rw [LinearMap.mem_ker] at hx
  have hrwA : inclAH 0 (Hml.mk dA 0 z)
      = Hml.mk (chainBoundary PTtop) 0 (cyclesMap (dM := dA) (dN := chainBoundary PTtop)
          (f := fun k => (Amod k).subtype) hf_inclA 0 z) := rfl
  rw [hrwA, Hml.mk_eq_zero_iff] at hx
  obtain ⟨w, hw⟩ := hx
  have hw' : chainBoundary PTtop 0 w = ((z : Ac 0) : SingularChainInt PTtop 0) := hw
  obtain ⟨c, hc⟩ := (z : Ac 0).2
  have haugz : augmentationInt PTtop ((z : Ac 0) : SingularChainInt PTtop 0) = 0 := by
    rw [← hw', augmentationInt_chainBoundary]
  have haugc : augmentationInt PTtop c = 0 := by
    rw [← hc, aug_normChain] at haugz
    omega
  obtain ⟨v, hv⟩ :=
    SKEFTHawking.SingularH0PathConnectedInt.mem_boundaries_of_augmentationInt_eq_zero
      (X := PTtop) basePt c haugc
  rw [Hml.mk_eq_zero_iff]
  refine ⟨⟨normChain tauC 1 v, ⟨v, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  show chainBoundary PTtop 0 (normChain tauC 1 v) = _
  rw [chainBoundary_normChain, hv, hc]

/-! ## §5. The low-degree walk pieces -/

/-- **The SES-I connecting `δ'₀ : H₁(B) → H₀(A)` vanishes** — its post-composition with the
injective `H₀(A) → H₀(T⁴°)` is zero by exactness. -/
theorem deltaI_zero_eq_zero (x : Hml dB 1) : deltaI 0 x = 0 := by
  apply inclAH_injective
  rw [map_zero]
  exact (exact_deltaI_inclAH 0).apply_apply_eq_zero x

/-- **`D̄ : H₁(T⁴°) → H₁(B)` is surjective** — exactness at `H₁(B)` against the vanishing
connecting `δ'₀`. -/
theorem diffH_one_surjective : Function.Surjective (diffH 1) := fun y =>
  (exact_diffH_deltaI 0 y).mp (deltaI_zero_eq_zero y)

end

end SKEFTHawking.KummerQuotientSmithSES
