/-
# Phase 5q.H — K7 finale: `TubeSeparates` from the resolution-piece PAIR, not from a parity identity

`KummerK3TorsionFree` reduced `Torsion(H₂(K3;ℤ)) = ⊥` (hence `kummerK3_b2_target`) to
`TubeSeparates`, and offered `TubeParity` (`tubeCoord = δ₁` as maps into `(ℤ/2)¹⁶`) as the
geometric statement supplying it. This module discharges `TubeSeparates` from a **strictly more
local** input — one that mentions neither `tubeCoord` nor `δ₁` nor any mod-2 identification:

> **`PairH2TwoTorsionFree`** — `H₂(eImage, collar; ℤ)` has no 2-torsion.

`eImage ≃ₜ 16 × ResE` and `collar ≃ 16 × ℝP³`, so this is exactly "the relative `H₂` of the
`𝒪(−2)`-disk-bundle resolution piece `(E, ∂E)` is torsion-free", i.e. `H₂(ResE, ∂ResE;ℤ) ≅ ℤ`
per copy. §6 proves the two forms are **equivalent** (`pairH2TwoTorsionFree_iff_equiv`), so
nothing is weakened by taking the no-2-torsion form as the hypothesis.

## Why the pair, and why no parity computation is needed

The MV connecting map is *defined* Barratt–Whitehead-style through this very pair
(`SingularMayerVietorisLESInt.mvConnectingInt`): with `A = qThick`, `B = eImage`,

`δ₁ = (seam iso) ∘ ∂^{(B,C)} ∘ excision⁻¹ ∘ j_*^{(K3, A)}`  (`k7Delta_one_eq`),

so `pairQ := excision⁻¹ ∘ j_*^{(K3,A)} : H₂(K3;ℤ) → H₂(eImage, collar;ℤ)` kills the `A`-summand
(`pairQ_ambIncl_qThick`) and sends the `B`-summand to the pair projection
(`pairQ_ambIncl_eImage`). Hence for every `x`, writing `2x = Σ₂ p`,

`2 · pairQ x = pairProj (−p₂)`  (`two_smul_pairQ`).

Now §1's rigidity lemma (`exact_two_smul_ker_iff`) applies: in an exact `L →ᵏ M →ᵈ N` with `k`
injective and `M` free of 2-torsion, `2q = k n` forces `d q = 0 ↔ n ∈ 2·L`. That is precisely
`δ₁ x = 0 ↔ tubeCoord x = 0` — the **kernel** half of `TubeParity`, which is all the torsion
argument consumes. The per-copy mod-2 identifications, the Euler-number sign and the orientation
bookkeeping that made a full parity identity expensive never enter.

## The Euler number is still visible, and still falsifiable

`pairProj` is injective (`pairProj_injective`, from `H₂(collar;ℤ) = 0`) and `pairBdry` is
surjective (`pairBdry_surjective`, from `H₁(eImage;ℤ) = 0`), so

`0 → H₂(eImage;ℤ) ≅ ℤ¹⁶ → H₂(eImage, collar;ℤ) → (ℤ/2)¹⁶ → 0`

is exact: `pairCokerEquiv` pins the cokernel of the pair projection to `(ℤ/2)¹⁶` on the nose, with
the numerical form `pairCoker_card : Nat.card = 2 ^ 16`. An `𝒪(−1)` piece would give the trivial
group here and an `𝒪(−3)` piece `(ℤ/3)¹⁶`, so this is the `ℝP³ = S³/±1` clutching geometry
recorded homologically — the same "Euler number −2" content, landed unconditionally rather than
assumed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.

**Elaboration note.** Every call below that takes the ambient `TopCat` implicitly (`homProjInt`,
`homIncl`, `connectingInt`, `excisionEquivInt`, `seamHomologyEquivInt`, …) pins it with
`(X := …)`. Leaving it to unification forces the elaborator to solve `↑?X ≟ KummerK3` and it
diverges into a `isDefEq` heartbeat wall on the `RelHomologyInt` module instances.
-/
import Mathlib
import SKEFTHawking.KummerK3TorsionFree

namespace SKEFTHawking.KummerPairTubeSeparation

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (EIndex eImage)
open scoped SKEFTHawking.KummerK7Delta1Image
open SKEFTHawking.KummerK7MVAssembly
  (qThick k7_hcov k7Delta interH2_eq_zero eImageH1_eq_zero interH1EquivInt eImageH2EquivInt)
open SKEFTHawking.KummerK7Delta1Window
  (Sigma2 pieceBlock sigma2SourceEquiv ker_k7Delta_one)
open SKEFTHawking.KummerK3TorsionFree
  (TubeSeparates blockCoord sigma2_blockCoord tubeCoord redMod2)

noncomputable section

/-! ## §1. The 2-divisibility rigidity of a 2-torsion-free extension

Pure algebra, and the whole reason no parity computation is needed: in an exact
`L →ᵏ M →ᵈ N` with `k` injective and `M` free of 2-torsion, an element `q` whose double is
`k n` is detected by `d` exactly when `n` fails to be 2-divisible. -/

/-- **The 2-divisibility rigidity lemma.** If `k` is injective, `Function.Exact k d`, and `M` has
no 2-torsion, then for `q` with `2 • q = k n`: `d q = 0 ↔ n ∈ 2 • L`.

This is the algebraic engine of the module: it converts "the relative group has no 2-torsion"
into "the connecting map detects exactly the classes that are not halvable in the piece". -/
theorem exact_two_smul_ker_iff {L M N : Type*} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    (k : L →ₗ[ℤ] M) (d : M →ₗ[ℤ] N) (hk : Function.Injective k) (hex : Function.Exact k d)
    (h2 : ∀ m : M, (2 : ℤ) • m = 0 → m = 0) {q : M} {n : L} (hq : (2 : ℤ) • q = k n) :
    d q = 0 ↔ ∃ m : L, n = (2 : ℤ) • m := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := (hex q).mp h
    refine ⟨m, hk ?_⟩
    rw [map_smul, hm]
    exact hq.symm
  · rintro ⟨m, rfl⟩
    have h3 : (2 : ℤ) • (q - k m) = 0 := by
      rw [smul_sub, hq, map_smul, sub_self]
    have h4 : q = k m := sub_eq_zero.mp (h2 _ h3)
    rw [h4]
    exact (hex (k m)).mpr ⟨m, rfl⟩

/-! ## §2. The resolution-piece pair `(eImage, collar)` -/

/-- `eImage` as a space in its own right — the 16-fold resolution piece `16 × ResE`. -/
abbrev ESub : TopCat := sub (X := KummerK3top) eImage

/-- The collar `qThick ∩ eImage`, seen intrinsically inside `eImage` — the excision
representation the MV connecting map is built from. -/
abbrev CollarInE : Set ↥ESub := restr (X := KummerK3top) qThick eImage

/-- **`H₂(eImage, collar; ℤ)`** — the relative group of the 16-fold resolution-piece pair
`(E, ∂E)`. Every remaining question about `Torsion(H₂(K3;ℤ))` lives here. -/
abbrev PairH2 : Type := RelHomologyInt CollarInE 2

/-- The pair projection `H₂(eImage;ℤ) → H₂(eImage, collar;ℤ)` — the `×(±2)` map of the
`𝒪(−2)`-piece pair sequence. -/
def pairProj : Homology ESub 2 →ₗ[ℤ] PairH2 :=
  homProjInt (X := ESub) CollarInE 2

/-- The pair connecting map `H₂(eImage, collar;ℤ) → H₁(collar;ℤ)`. -/
def pairBdry : PairH2 →ₗ[ℤ] Homology (sub (X := ESub) CollarInE) 1 :=
  connectingInt (X := ESub) CollarInE 1

/-- **The excision half of the MV connecting map**: `H₂(K3;ℤ) → H₂(eImage, collar;ℤ)`. -/
def pairQ : Homology KummerK3top 2 →ₗ[ℤ] PairH2 :=
  ((excisionEquivInt (X := KummerK3top) qThick eImage 1 k7_hcov).symm.toLinearMap).comp
    (homProjInt (X := KummerK3top) qThick 2)

/-- **`δ₁` factors through the pair** — definitional unfolding of `mvDeltaInt`, recorded so the
whole chase can be run inside `(eImage, collar)`. -/
theorem k7Delta_one_eq (x : Homology KummerK3top 2) :
    k7Delta 1 x
      = seamHomologyEquivInt (X := KummerK3top) qThick eImage 1 (pairBdry (pairQ x)) := rfl

/-- The `qThick`-summand dies in the pair (`j_* ∘ i_* = 0`). -/
theorem pairQ_ambIncl_qThick (u : Homology (sub (X := KummerK3top) qThick) 2) :
    pairQ (Homology.mapInt (ambIncl (X := KummerK3top) qThick) 2 u) = 0 := by
  rw [Homology.mapInt_ambIncl (X := KummerK3top)]
  simp only [pairQ, LinearMap.comp_apply,
    SingularSphereHomologyInt.homProjInt_homIncl (X := KummerK3top), map_zero]

/-- The `eImage`-summand goes to the pair projection (excision naturality). -/
theorem pairQ_ambIncl_eImage (v : Homology ESub 2) :
    pairQ (Homology.mapInt (ambIncl (X := KummerK3top) eImage) 2 v) = pairProj v := by
  rw [Homology.mapInt_ambIncl (X := KummerK3top)]
  simp only [pairQ, pairProj, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    ← excisionMap_homProjInt (X := KummerK3top)]
  exact (excisionEquivInt (X := KummerK3top) qThick eImage 1 k7_hcov).symm_apply_apply _

/-! ## §3. The pair short exact sequence `0 → ℤ¹⁶ → H₂(eImage, collar) → (ℤ/2)¹⁶ → 0` -/

/-- `H₂(collar;ℤ) = 0` in the excision representation. -/
theorem collarInE_H2_eq_zero (w : Homology (sub (X := ESub) CollarInE) 2) : w = 0 :=
  (LinearEquiv.map_eq_zero_iff
    (seamHomologyEquivInt (X := KummerK3top) qThick eImage 2)).mp (interH2_eq_zero _)

/-- **`pairProj` is injective** — `H₂(collar;ℤ) = 0` kills the incoming leg of the pair LES. -/
theorem pairProj_injective : Function.Injective pairProj := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  obtain ⟨w, rfl⟩ :=
    (SingularSphereHomologyInt.exact_homIncl_homProjInt (X := ESub) CollarInE 2 v).mp hv
  rw [collarInE_H2_eq_zero w, map_zero]

/-- **`pairBdry` is surjective** — `H₁(eImage;ℤ) = 0` kills the outgoing leg of the pair LES. -/
theorem pairBdry_surjective : Function.Surjective pairBdry := fun w =>
  (SingularLocalHomologyInt.exact_connectingInt_homIncl (X := ESub) CollarInE 1 w).mp
    (eImageH1_eq_zero _)

/-- Pair-LES exactness at `H₂(eImage, collar;ℤ)`: `ker ∂ = im j_*`. -/
theorem pair_exact : Function.Exact pairProj pairBdry :=
  SingularLocalHomologyInt.exact_homProjInt_connectingInt (X := ESub) CollarInE 1

/-- `H₁(collar;ℤ) ≅ (ℤ/2)¹⁶` in the excision representation. -/
def pairCollarH1Equiv : Homology (sub (X := ESub) CollarInE) 1 ≃ₗ[ℤ] (EIndex → ZMod 2) :=
  (seamHomologyEquivInt (X := KummerK3top) qThick eImage 1).trans interH1EquivInt

/-- **The pair cokernel is `(ℤ/2)¹⁶` on the nose** — the homological form of the resolution
piece's Euler number `−2`. An `𝒪(−1)` piece would give the trivial group here and an `𝒪(−3)`
piece `(ℤ/3)¹⁶`, so this equivalence is a falsifiable pin on the `ℝP³ = S³/±1` clutching. -/
def pairCokerEquiv : (PairH2 ⧸ LinearMap.range pairProj) ≃ₗ[ℤ] (EIndex → ZMod 2) :=
  ((Submodule.quotEquivOfEq _ _ pair_exact.linearMap_ker_eq.symm).trans
    (pairBdry.quotKerEquivOfSurjective pairBdry_surjective)).trans pairCollarH1Equiv

/-- **The pair cokernel has exactly `2¹⁶` elements** — the numerical form of the Euler-number pin,
and a falsifiable one: any other self-intersection number of the resolution piece changes it. -/
theorem pairCoker_card : Nat.card (PairH2 ⧸ LinearMap.range pairProj) = 2 ^ 16 := by
  rw [Nat.card_congr pairCokerEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, SKEFTHawking.KummerWeld.eIndex_card]

/-! ## §4. The residual, stated locally -/

/-- **The residual hypothesis** — `H₂(eImage, collar; ℤ)` has no 2-torsion. Equivalently (§3's
short exact sequence) the relative `H₂` of the 16-fold resolution-piece pair is the free `ℤ¹⁶`,
i.e. `H₂(ResE, ∂ResE;ℤ) ≅ ℤ` per copy. This mentions no mod-2 identification, no orientation
convention and no class of `H₂(K3;ℤ)` — it is a statement about the local model alone. -/
def PairH2TwoTorsionFree : Prop := ∀ m : PairH2, (2 : ℤ) • m = 0 → m = 0

/-- **`H₂(ResE, ∂ResE;ℤ) ≅ ℤ¹⁶` supplies the residual** — the freeness form of the geometric input
implies the minimal (no-2-torsion) form actually consumed. -/
theorem pairH2TwoTorsionFree_of_equiv (e : PairH2 ≃ₗ[ℤ] (EIndex → ℤ)) : PairH2TwoTorsionFree := by
  intro m hm
  have h1 : (2 : ℤ) • e m = 0 := by rw [← map_smul, hm, map_zero]
  have h2 : e m = 0 := by
    funext i
    show e m i = 0
    have h3 : (2 : ℤ) * e m i = 0 := congrFun h1 i
    omega
  exact e.injective (by rw [h2, map_zero])

/-! ## §5. `TubeSeparates` — discharged from the pair -/

/-- The `Σ₂`-preimage of `2x`, in the `H₂(qThick) × H₂(eImage)` representation. -/
def halfPair (x : Homology KummerK3top 2) :
    Homology (sub (X := KummerK3top) qThick) 2 × Homology ESub 2 :=
  sigma2SourceEquiv.symm (blockCoord x)

theorem sigma2_halfPair (x : Homology KummerK3top 2) :
    Sigma2 (halfPair x) = (2 : ℤ) • x := sigma2_blockCoord x

theorem eImageH2_halfPair (x : Homology KummerK3top 2) :
    eImageH2EquivInt (halfPair x).2 = (blockCoord x).2 := by
  have h1 : sigma2SourceEquiv (halfPair x) = blockCoord x :=
    LinearEquiv.apply_symm_apply _ _
  have h2 : (sigma2SourceEquiv (halfPair x)).2 = eImageH2EquivInt (halfPair x).2 := by
    simp [sigma2SourceEquiv]
  rw [← h2, h1]

/-- **The doubling identity in the pair**: `2 · pairQ x = pairProj (−(halfPair x).2)`. The
`qThick`-summand of `Σ₂` dies under `pairQ` and the `eImage`-summand becomes the pair projection,
so the entire `H₂(K3;ℤ)`-side collapses onto a single element of `H₂(eImage;ℤ)`. -/
theorem two_smul_pairQ (x : Homology KummerK3top 2) :
    (2 : ℤ) • pairQ x = pairProj (-(halfPair x).2) := by
  rw [← map_smul, ← sigma2_halfPair x, mvHomSumInt_apply, map_sub, pairQ_ambIncl_qThick,
    pairQ_ambIncl_eImage, zero_sub, map_neg]

/-- `tubeCoord x = 0` says exactly that the `E`-half of `x` is 2-divisible in `H₂(eImage;ℤ)`. -/
theorem tubeCoord_eq_zero_iff_two_dvd (x : Homology KummerK3top 2) :
    tubeCoord x = 0 ↔ ∃ m, -(halfPair x).2 = (2 : ℤ) • m := by
  constructor
  · intro hx
    have hE : ∀ i, (((blockCoord x).2 i : ℤ) : ZMod 2) = 0 := fun i => congrFun hx i
    obtain ⟨w, hcoord⟩ : ∃ w : EIndex → ℤ, (blockCoord x).2 = (2 : ℤ) • w := by
      refine ⟨fun i => (blockCoord x).2 i / 2, ?_⟩
      funext i
      obtain ⟨c, hc⟩ : (2 : ℤ) ∣ (blockCoord x).2 i := by
        have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((blockCoord x).2 i) 2).mp (hE i)
        exact_mod_cast h5
      show (blockCoord x).2 i = (2 : ℤ) * ((blockCoord x).2 i / 2)
      rw [hc]
      omega
    have hh : (halfPair x).2 = (2 : ℤ) • eImageH2EquivInt.symm w := by
      apply eImageH2EquivInt.injective
      rw [eImageH2_halfPair, map_smul, LinearEquiv.apply_symm_apply, hcoord]
    exact ⟨-eImageH2EquivInt.symm w, by rw [hh, smul_neg]⟩
  · rintro ⟨m, hm⟩
    have h1 : (halfPair x).2 = (2 : ℤ) • (-m) := by rw [smul_neg, ← hm, neg_neg]
    have h2 : (blockCoord x).2 = (2 : ℤ) • eImageH2EquivInt (-m) := by
      rw [← eImageH2_halfPair, h1, map_smul]
    funext i
    show (((blockCoord x).2 i : ℤ) : ZMod 2) = 0
    rw [h2]
    show (((2 : ℤ) * eImageH2EquivInt (-m) i : ℤ) : ZMod 2) = 0
    push_cast
    rw [show ((2 : ZMod 2)) = 0 from rfl, zero_mul]

/-- **`TubeSeparates` from the pair.** The 2-torsion-freeness of `H₂(eImage, collar;ℤ)` is the
only geometric input: §1's rigidity lemma turns it into "`δ₁` kills exactly the classes whose
`E`-half is 2-divisible", which is `TubeSeparates` verbatim. -/
theorem tubeSeparates_of_pairH2TwoTorsionFree (h : PairH2TwoTorsionFree) : TubeSeparates := by
  intro x hx
  have hker := (exact_two_smul_ker_iff pairProj pairBdry pairProj_injective pair_exact h
    (two_smul_pairQ x)).mpr ((tubeCoord_eq_zero_iff_two_dvd x).mp hx)
  have hδ : k7Delta 1 x = 0 := by rw [k7Delta_one_eq, hker, map_zero]
  have h3 : x ∈ LinearMap.ker (k7Delta 1) := hδ
  rwa [ker_k7Delta_one] at h3

/-! ## §6. The residual is EXACTLY `H₂(ResE, ∂ResE;ℤ) ≅ ℤ¹⁶`

`pairH2TwoTorsionFree_of_equiv` (§4) is one direction. This section proves the converse, so the
hypothesis consumed by §5 is not a weakening into something unrelated: it is *equivalent* to the
freeness statement the geometry is expected to deliver. -/

instance : Module.Finite ℤ (Homology ESub 2) := Module.Finite.equiv eImageH2EquivInt.symm

instance : Module.Finite ℤ ↥(LinearMap.range pairProj) := Module.Finite.range pairProj

instance : Finite (PairH2 ⧸ LinearMap.range pairProj) :=
  Finite.of_injective pairCokerEquiv pairCokerEquiv.injective

instance : Module.Finite ℤ (PairH2 ⧸ LinearMap.range pairProj) := Module.Finite.of_finite

/-- **`H₂(eImage, collar;ℤ)` is finitely generated** — a free `ℤ¹⁶` sublattice with finite
cokernel. -/
instance instPairH2Finite : Module.Finite ℤ PairH2 :=
  Module.Finite.of_submodule_quotient (LinearMap.range pairProj)

/-- **Every class of the pair group doubles into the free sublattice** — the cokernel has
exponent 2 (§3). -/
theorem two_smul_mem_range_pairProj (m : PairH2) : (2 : ℤ) • m ∈ LinearMap.range pairProj := by
  have h1 : (2 : ℤ) • ((LinearMap.range pairProj).mkQ m) = 0 := by
    apply pairCokerEquiv.injective
    rw [map_smul, map_zero]
    funext i
    show (2 : ℤ) • pairCokerEquiv ((LinearMap.range pairProj).mkQ m) i = 0
    rw [two_smul]
    exact CharTwo.add_self_eq_zero _
  rw [← map_smul] at h1
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

/-- **The free sublattice is torsion-free in the pair group** — it is the injective image of
`H₂(eImage;ℤ) ≅ ℤ¹⁶`. -/
theorem torsion_inf_range_pairProj_eq_bot :
    Submodule.torsion ℤ PairH2 ⊓ LinearMap.range pairProj = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro t ht
  rw [Submodule.mem_inf] at ht
  obtain ⟨htor, v, rfl⟩ := ht
  obtain ⟨⟨n, hn⟩, hsmul⟩ := (Submodule.mem_torsion_iff _).mp htor
  have h1 : pairProj (n • v) = 0 := by rw [map_smul]; exact hsmul
  have h2 : n • v = 0 := pairProj_injective (by rw [h1, map_zero])
  have h3 : n • eImageH2EquivInt v = 0 := by rw [← map_smul, h2, map_zero]
  have hn0 : (n : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hn
  have h4 : eImageH2EquivInt v = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h hn0
    · exact h
  rw [show v = 0 from eImageH2EquivInt.map_eq_zero_iff.mp h4, map_zero]

/-- **The residual, restated**: `H₂(eImage, collar;ℤ)` has no 2-torsion iff it is torsion-free.
The `⟸` direction is immediate; the `⟹` direction is the content — a torsion class doubles into
the free sublattice, dies there, and is then killed by the hypothesis. -/
theorem pairH2TwoTorsionFree_iff_torsion_eq_bot :
    PairH2TwoTorsionFree ↔ Submodule.torsion ℤ PairH2 = ⊥ := by
  constructor
  · intro h
    rw [Submodule.eq_bot_iff]
    intro t ht
    have h1 : (2 : ℤ) • t ∈ Submodule.torsion ℤ PairH2 ⊓ LinearMap.range pairProj :=
      ⟨Submodule.smul_mem _ _ ht, two_smul_mem_range_pairProj t⟩
    rw [torsion_inf_range_pairProj_eq_bot] at h1
    exact h t h1
  · intro h m hm
    have h1 : m ∈ Submodule.torsion ℤ PairH2 :=
      (Submodule.mem_torsion_iff _).mpr
        ⟨⟨2, by norm_num [mem_nonZeroDivisors_iff_ne_zero]⟩, hm⟩
    rw [h] at h1
    exact h1

/-- The doubling map `H₂(eImage, collar;ℤ) → im pairProj`. -/
def doubleIntoPairRange : PairH2 →ₗ[ℤ] ↥(LinearMap.range pairProj) :=
  LinearMap.codRestrict _ ((2 : ℤ) • LinearMap.id) two_smul_mem_range_pairProj

/-- Halving through the free sublattice: `m ↦ pairProj⁻¹(2m)` in `ℤ¹⁶` coordinates. -/
def pairHalve : PairH2 →ₗ[ℤ] (EIndex → ℤ) :=
  eImageH2EquivInt.toLinearMap.comp
    (((LinearEquiv.ofInjective pairProj pairProj_injective).symm.toLinearMap).comp
      doubleIntoPairRange)

theorem pairHalve_injective (h : PairH2TwoTorsionFree) : Function.Injective pairHalve := by
  rw [injective_iff_map_eq_zero]
  intro m hm
  simp only [pairHalve, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.map_eq_zero_iff] at hm
  refine h m ?_
  have h3 : (2 : ℤ) • m = ((0 : ↥(LinearMap.range pairProj)) : PairH2) :=
    congrArg Subtype.val hm
  simpa using h3

theorem finrank_pairH2_source : Module.finrank ℤ (EIndex → ℤ) = 16 := by
  rw [Module.finrank_pi, SKEFTHawking.KummerWeld.eIndex_card]

/-- **`H₂(ResE, ∂ResE;ℤ) ≅ ℤ¹⁶` from the residual** — the converse of
`pairH2TwoTorsionFree_of_equiv`. Together the two make the hypothesis consumed by §5 *equivalent*
to the geometric statement "the relative `H₂` of the resolution-piece pair is the free `ℤ¹⁶`". -/
theorem pairH2_equiv_of_twoTorsionFree (h : PairH2TwoTorsionFree) :
    Nonempty (PairH2 ≃ₗ[ℤ] (EIndex → ℤ)) := by
  have htor : Submodule.torsion ℤ PairH2 = ⊥ := pairH2TwoTorsionFree_iff_torsion_eq_bot.mp h
  haveI : Module.IsTorsionFree ℤ PairH2 := by
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mpr htor
  haveI : Module.Free ℤ PairH2 := Module.free_of_finite_type_torsion_free'
  have hle : Module.finrank ℤ PairH2 ≤ 16 := by
    have h1 := LinearMap.finrank_le_finrank_of_injective (pairHalve_injective h)
    rwa [finrank_pairH2_source] at h1
  have hge : 16 ≤ Module.finrank ℤ PairH2 := by
    have h1 := LinearMap.finrank_le_finrank_of_injective
      (f := pairProj.comp eImageH2EquivInt.symm.toLinearMap)
      (pairProj_injective.comp eImageH2EquivInt.symm.injective)
    rwa [finrank_pairH2_source] at h1
  have hcard : Module.finrank ℤ PairH2 = 16 := le_antisymm hle hge
  have hcards : Fintype.card EIndex = Fintype.card (Module.Free.ChooseBasisIndex ℤ PairH2) := by
    rw [SKEFTHawking.KummerWeld.eIndex_card, ← Module.finrank_eq_card_chooseBasisIndex, hcard]
  exact ⟨(Module.Free.chooseBasis ℤ PairH2).equivFun.trans
    (LinearEquiv.funCongrLeft ℤ ℤ (Fintype.equivOfCardEq hcards))⟩


/-- **The residual in its two equivalent forms** — `H₂(eImage, collar;ℤ)` has no 2-torsion iff it
is the free `ℤ¹⁶`. So the hypothesis §5 consumes is not a weakening: it *is* the mission-form
statement `H₂(ResE, ∂ResE;ℤ) ≅ ℤ` (16 copies). -/
theorem pairH2TwoTorsionFree_iff_equiv :
    PairH2TwoTorsionFree ↔ Nonempty (PairH2 ≃ₗ[ℤ] (EIndex → ℤ)) :=
  ⟨pairH2_equiv_of_twoTorsionFree, fun ⟨e⟩ => pairH2TwoTorsionFree_of_equiv e⟩

/-! ## §7. The finale -/

/-- **`Torsion(H₂(K3;ℤ)) = ⊥` from the resolution-piece pair.** -/
theorem kummerK3_torsion_free_of_pairH2TwoTorsionFree (h : PairH2TwoTorsionFree) :
    Submodule.torsion ℤ (Homology KummerK3top 2) = ⊥ :=
  SKEFTHawking.KummerK3TorsionFree.torsion_eq_bot_of_tubeSeparates
    (tubeSeparates_of_pairH2TwoTorsionFree h)

/-- **`H₂(K3;ℤ) ≅ ℤ²²` from the resolution-piece pair.** -/
theorem kummerK3_H2_equiv_of_pairH2TwoTorsionFree (h : PairH2TwoTorsionFree) :
    Nonempty (Homology KummerK3top 2 ≃ₗ[ℤ] (Fin 22 → ℤ)) :=
  SKEFTHawking.KummerK7Delta1Window.kummerK3_H2_equiv_of_torsion_free
    (kummerK3_torsion_free_of_pairH2TwoTorsionFree h)

/-- **`kummerK3_b2_target` from the resolution-piece pair** — the ℤ²² headline, with its residual
relocated from a parity identity on all of `H₂(K3;ℤ)` to the 2-torsion-freeness of the local
model's relative `H₂`. -/
theorem kummerK3_b2_target_of_pairH2TwoTorsionFree (h : PairH2TwoTorsionFree) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  SKEFTHawking.KummerK7Delta1Window.kummerK3_b2_target_of_torsion_free
    (kummerK3_torsion_free_of_pairH2TwoTorsionFree h)

end

end SKEFTHawking.KummerPairTubeSeparation
