/-
# `Hₚ(Q;ℤ) = 0` for `p ≥ 4` — THE Q-SIDE TOP-DEGREE VANISHING, and the residual it discharges

`KummerPunctureTopVanish` reduced the whole remaining `orientInput` residual (modulo descent) to the
single statement `H₅(Q;ℤ) = 0` for the free quotient `Q = T⁴°/τ`, and observed that the Q-side
two-step Smith recursion (`hmlQ_step`) runs *upward*, so degrees 4 and 5 are its base cases: **a
genuine `Q`-side geometric input is required, and no amount of `T⁴°`-side data terminates it.**

This module supplies that input — and it is **not** a quotient good cover. `Q` is a compact
4-manifold with boundary, so it has no good cover argument as cheap as the `ℝP³` one, and the
τ-invariant peel of `KummerPuncturedTorusHighVanish` does not descend without building the whole
quotient tower. Instead the input comes from **above**, through the weld that is already banked:

## Route — the ambient is the welded `K3`, not the punctured torus

`KummerWeld.KummerK3 = Q ∪_{16 × ℝP³} (16 × E)` is a **compact** smooth 4-manifold
(`KummerWeld` compactness + `KummerK3Manifold.isManifold_R4_kummerK3`, on the `𝓡 4` model via the
flat-model transport). Two independent facts follow:

1. **§1 — the whole-manifold good-compact stage.** `SingularCompactManifoldTopVanishInt` (the
   ambient-generic "closed `n`-manifolds are homologically `n`-dimensional" module extracted from
   this argument) gives `Hₚ(K3;ℤ) = 0` for `p ≥ 5` **and** `H₄(K3;ℤ)` free, off nothing but the
   charted structure — no orientation, no duality, hence no circularity with `orientInput`. The
   only local work is supplying the `𝓡 4` charted instance by the flat-model transport.
2. **§2–§3 — descend along the banked K7 Mayer–Vietoris.** `KummerK7MVAssembly` already has the
   unconditional collar-thickened cover (`k7_hcov`), the piece models
   (`qThickHnEquivInt : Hₙ₊₁(qThick) ≅ Hₙ₊₁(Q)`, `eImageHnEquivInt`, `interHnEquivInt`) and the
   exactness. Above degree 3 the seam is sixteen `ℝP³`s (`rp3_homology_high_unconditional`) and the
   `E`-side is sixteen `S²`s, so `Σₚ` is injective for `p ≥ 4`; with `Hₚ(K3;ℤ) = 0` for `p ≥ 5` this
   gives `Hₚ(qThick;ℤ) = 0`, hence **`Hₚ(Q;ℤ) = 0` for every `p ≥ 5`**.
3. **§4 — degree 4, the sharp end.** `H₄(K3;ℤ) ≅ ℤ` is *not* zero-shaped, so the MV alone cannot
   kill `H₄(Q;ℤ)`. The transfer does the other half: `t₄ : H₄(Q;ℤ) → H₄(T⁴°;ℤ)` has zero target
   (`KummerPunctureTopVanish.h4PT`) and `p̄ ∘ t = 2` (`KummerK3H3SeamWindow.projH_transferH`), so
   every degree-4 `Q`-class is 2-torsion; `Σ₄` embeds it in the **free** `H₄(K3;ℤ)` of §1, which has
   none. Hence `H₄(Q;ℤ) = 0` — the "compact 4-manifold with nonempty boundary has no top homology"
   statement, obtained without any boundary/collar duality.

## Consequences shipped here

* **`q_homology_top`** — `Hₚ(Q;ℤ) = 0` for every `p ≥ 4` (both base cases of `hmlQ_high`);
* **`transferH_three_injective`** — `t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)` is injective, **unconditionally**
  (the `_uncond` iff of `KummerPunctureTopVanish` with its right-hand side discharged);
* **`h3Q_twoTorsionFree`** — **`H₃(Q;ℤ)` is 2-torsion-free, unconditionally** — the statement the
  `orientInput` chain had been carrying as a hypothesis since the Smith sequence was built;
* **`k7Delta3Coord_injective` / `h4K3EquivKerQSeamCoord3`** — with both degree-4 pieces dead the
  weld window sharpens to `0 → H₄(K3;ℤ) ↪ ℤ¹⁶ → H₃(Q;ℤ) ↠ H₃(K3;ℤ) → 0`, identifying
  `H₄(K3;ℤ) ≅ ker qSeamCoord3` — so `H₄(K3;ℤ)` is a subgroup of `ℤ¹⁶`, computed by the sixteen seam
  coordinates.

## What is NOT claimed

`orientInput` (`KummerK3E1Package.KummerK3H3TwoTorsionFree`) is **not** discharged. Its banked
reformulation `KummerK3H3SeamWindow.kummerK3H3TwoTorsionFree_iff_qSeamCoord3_two_saturated` asks
that `im qSeamCoord3` be **2-saturated** in `H₃(Q;ℤ)`; 2-torsion-freeness of the ambient `H₃(Q;ℤ)`
does not imply 2-saturation of a subgroup, so the residual survives — it is now exactly a statement
about the sixteen seam classes inside a group known to be 2-torsion-free. Nothing here consumes the
EVEN descent form `im p_* ⊆ 2 · im qSeamCoord3` (settled non-reducing / expected false in
`docs/dev-loops/SETTLED_FORKS.md`); `h3Q_torsionFree_of_ptTorsionFree` carries its `T⁴°`-side
hypothesis explicitly rather than assuming it.

## Vacuity attack

`k3_homology_high` is not vacuous: `H₂(K3;ℤ)` contains a rank-22 free block
(`KummerPuncturedMV.kummerK3_b2_window`), so `K3` is very far from acyclic; the threshold is the
manifold dimension. `q_homology_top` is not vacuous and its threshold is sharp — `H₃(Q;ℤ)` does not
vanish (`KummerK3H3SeamWindow.qSeamCoord3_surjective_iff_h3K3_eq_zero` reads `H₃(K3;ℤ)` off it, and
`H₂(Q;ℤ) ≅ ℤ⁶` is banked), so `p ≥ 4` cannot be weakened to `p ≥ 3`. `q_homology_four` is not a
`Σ₄`-triviality: `Σ₄` alone gives only `H₄(Q;ℤ) ↪ H₄(K3;ℤ)`, and the transfer alone gives only
"2-torsion"; both halves are load-bearing.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerK3Manifold
import SKEFTHawking.KummerK7MVAssembly
import SKEFTHawking.SingularCompactManifoldTopVanishInt
import SKEFTHawking.KummerPunctureTopVanish

namespace SKEFTHawking.KummerQTopVanish

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.KummerWeld (KummerK3)
open SKEFTHawking.KummerK7Opener (KummerK3top)

noncomputable section

/-! ## §1. The whole-manifold good-compact stage of the welded `K3` -/

/-- **The `K3` good-compact stage at `K = K3` itself.** `K3` is a compact `C^∞` 4-manifold on the
`𝓡 4` model (`KummerK3Manifold.isManifold_R4_kummerK3`, via the flat-model transport), so the
Hatcher-3.27 cofinality of the Poincaré-duality tower (`vanishAbove_cofinalInt`, whose ball-freeness
input is the *theorem* `hballFreeInt_dim4` in dimension 4) applies with `W = K = univ`; the compact
`K'` it produces is forced to be all of `K3`. Since `univᶜ = ∅` and `Hᵢ(M | ∅) ≅ Hᵢ(M;ℤ)`
(`relHomologyEmptyEquivInt`), the stage reads off as two absolute statements about `K3`. -/
theorem k3_univ_stage :
    (∀ i, 4 < i → ∀ x : Homology KummerK3top i, x = 0) ∧
      Module.Free ℤ (Homology KummerK3top 4) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) KummerK3 :=
    SKEFTHawking.ManifoldModelTransport.transportedChartedSpace
      (SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 3) KummerK3
  exact ⟨fun i hi x => SingularCompactManifoldTopVanishInt.homology_high_dim4 i hi x,
    SingularCompactManifoldTopVanishInt.top_homology_free_dim4⟩

/-- **`Hₚ(K3;ℤ) = 0` for every `p ≥ 5`** — the welded Kummer `K3` is homologically 4-dimensional.
Unconditional, and independent of `orientInput` (it uses only the smooth 4-manifold structure). -/
theorem k3_homology_high (p : ℕ) (hp : 4 < p) (x : Homology KummerK3top p) : x = 0 :=
  k3_univ_stage.1 p hp x

/-- **`H₄(K3;ℤ)` is free** — top-degree freeness of the good-compact stage. In particular
`H₄(K3;ℤ)` is torsion-free, which is what kills the `Q`-side degree-4 2-torsion in §4. -/
theorem k3_h4_free : Module.Free ℤ (Homology KummerK3top 4) := k3_univ_stage.2

/-! ## §2. The high-degree K7 piece table -/

open SKEFTHawking.KummerWeld (EIndex eImage)
open SKEFTHawking.KummerResolutionPiece (ResE RP3)
open SKEFTHawking.KummerResolutionPieceH2 (Btop zeroSectionHomologyEquivInt)
open SKEFTHawking.KummerBaseSphereH2Int (baseHomeoSph)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLESInt (mvHomSumInt mvHomDiagInt)
open SKEFTHawking.KummerK7MVAssembly (qThick interHnEquivInt eImageHnEquivInt
  qThickHnEquivInt k7_exact_middle)
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)
open SKEFTHawking.KummerQuotientCovering (Qtop PTtop)

/-- `Hₚ(E;ℤ) = 0` for `p ≥ 3` — the resolution piece retracts onto its zero section `S²`. -/
theorem resE_homology_high (p : ℕ) (hp : 2 < p) (x : Homology (TopCat.of ResE) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  set e := (zeroSectionHomologyEquivInt k).symm.trans
    (homeoHomologyEquivInt (X := Btop) (Y := Sph 2) baseHomeoSph (k + 1)) with he
  have hx0 : e x = 0 :=
    SKEFTHawking.SingularSphereHighDegreeInt.sphere_homology_high 2 (k + 1) (by omega) _
  have h := e.symm_apply_apply x
  rw [hx0, map_zero] at h
  exact h.symm

/-- `Hₚ(eImage;ℤ) = 0` for `p ≥ 3` — sixteen copies of `E`. -/
theorem eImage_homology_high (p : ℕ) (hp : 2 < p)
    (x : Homology (sub (X := KummerK3top) eImage) p) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (eImageHnEquivInt p)).mp
    (funext fun _ => resE_homology_high p hp _)

/-- `Hₚ(collar;ℤ) = 0` for `p ≥ 4` — sixteen copies of `ℝP³`. -/
theorem inter_homology_high (p : ℕ) (hp : 3 < p)
    (x : Homology (sub (X := KummerK3top) (qThick ∩ eImage)) p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  exact (LinearEquiv.map_eq_zero_iff (interHnEquivInt k)).mp
    (funext fun _ => SKEFTHawking.KummerRP3HomologyUnconditional.rp3_homology_high_unconditional
      (k + 1) (by omega) _)

/-! ## §3. `Hₚ(Q;ℤ) = 0` for `p ≥ 5` -/

/-- `Σₚ` is injective for `p ≥ 4` — `Hₚ(collar) = 0` kills the incoming diagonal. -/
theorem k7Sum_high_injective (p : ℕ) (hp : 3 < p) :
    Function.Injective (mvHomSumInt (X := KummerK3top) qThick eImage p) := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  intro a b hab
  have hker : mvHomSumInt (X := KummerK3top) qThick eImage (k + 1) (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨w, hw⟩ := (k7_exact_middle k (a - b)).mp hker
  rw [inter_homology_high (k + 1) hp w, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

/-- `Hₚ(qThick;ℤ) = 0` for `p ≥ 5`. -/
theorem qThick_homology_high (p : ℕ) (hp : 4 < p)
    (x : Homology (sub (X := KummerK3top) qThick) p) : x = 0 := by
  have h : mvHomSumInt (X := KummerK3top) qThick eImage p (x, 0) = 0 :=
    k3_homology_high p hp _
  have h2 : ((x, 0) : Homology (sub (X := KummerK3top) qThick) p ×
      Homology (sub (X := KummerK3top) eImage) p) = 0 :=
    k7Sum_high_injective p (by omega) (by rw [h, map_zero])
  exact congrArg Prod.fst h2

/-- **`Hₚ(Q;ℤ) = 0` for every `p ≥ 5`.** -/
theorem q_homology_high (p : ℕ) (hp : 4 < p) (x : Homology Qtop p) : x = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
  exact (LinearEquiv.map_eq_zero_iff (qThickHnEquivInt k).symm).mp
    (qThick_homology_high (k + 1) hp _)

/-! ## §4. `H₄(Q;ℤ) = 0` — the degree-4 transfer bound against the free `H₄(K3;ℤ)` -/

open SKEFTHawking.ChainComplexLESInt (Hml)
open SKEFTHawking.SingularHomologyInt (chainBoundary)
open SKEFTHawking.KummerRP3SmithSES (hmlEquivHomology)
open SKEFTHawking.KummerQuotientSmithSES (projH transferH)
open SKEFTHawking.KummerK7MVAssembly (k7Sum4_injective)
open SKEFTHawking.KummerPunctureTopVanish (h4PT h5PT)

/-- A free ℤ-module has no 2-torsion. -/
theorem eq_zero_of_add_self_eq_zero_of_free {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] {z : M} (hz : z + z = 0) : z = 0 := by
  rcases (Module.Basis.smul_eq_zero (Module.Free.chooseBasis ℤ M) (c := (2 : ℤ)) (x := z)).mp
    (by rw [two_smul]; exact hz) with h | h
  · exact absurd h (by norm_num)
  · exact h

/-- **Every degree-4 class of `Q` is 2-torsion, unconditionally** — the transfer
`t₄ : H₄(Q;ℤ) → H₄(T⁴°;ℤ)` has zero target (`KummerPunctureTopVanish.h4PT`), and `p̄ ∘ t = 2`
(`KummerK3H3SeamWindow.projH_transferH`). -/
theorem qH4_two_smul_eq_zero (y : Hml (chainBoundary Qtop) 4) : (2 : ℤ) • y = 0 := by
  have h := SKEFTHawking.KummerK3H3SeamWindow.projH_transferH 4 y
  rw [h4PT (transferH 4 y), map_zero] at h
  exact h.symm

/-- `Homology`-idiom form of `qH4_two_smul_eq_zero`, in the instance-neutral `x + x` shape. -/
theorem qH4_add_self_eq_zero (x : Homology (TopCat.of FreeQuotient) 4) : x + x = 0 := by
  have h := qH4_two_smul_eq_zero ((hmlEquivHomology Qtop 4).symm x)
  have h2 : (hmlEquivHomology Qtop 4).symm x + (hmlEquivHomology Qtop 4).symm x = 0 := by
    rw [← h]; abel
  have h3 := congrArg (hmlEquivHomology Qtop 4) h2
  rwa [map_add, LinearEquiv.apply_symm_apply, map_zero] at h3

/-- **`H₄(Q;ℤ) = 0`.** The `Q`-side degree-4 homology is 2-torsion (transfer) *and* embeds in
`H₄(K3;ℤ)` (`k7Sum4_injective`, whose seam input `interH4_eq_zero` is banked), which is free
(`k3_h4_free`) — so it vanishes. Sharp: this is exactly the "compact 4-manifold with nonempty
boundary has no top homology" statement, obtained without any boundary/collar duality. -/
theorem q_homology_four (x : Homology Qtop 4) : x = 0 := by
  haveI := k3_h4_free
  have hu2 : (qThickHnEquivInt 3).symm x + (qThickHnEquivInt 3).symm x = 0 := by
    have h := congrArg (qThickHnEquivInt 3).symm (qH4_add_self_eq_zero x)
    rwa [map_add, map_zero] at h
  have hs : mvHomSumInt (X := KummerK3top) qThick eImage 4 ((qThickHnEquivInt 3).symm x, 0) = 0 := by
    refine eq_zero_of_add_self_eq_zero_of_free ?_
    rw [← map_add, Prod.mk_add_mk, hu2, add_zero]
    simp
  have h2 : (((qThickHnEquivInt 3).symm x, 0) :
      Homology (sub (X := KummerK3top) qThick) 4 ×
        Homology (sub (X := KummerK3top) eImage) 4) = 0 :=
    k7Sum4_injective (by rw [hs, map_zero])
  exact (LinearEquiv.map_eq_zero_iff (qThickHnEquivInt 3).symm).mp (congrArg Prod.fst h2)

/-! ## §5. `Hₚ(Q;ℤ) = 0` for every `p ≥ 4`, and the residual it discharges -/

/-- **THE Q-SIDE TOP-DEGREE VANISHING: `Hₚ(Q;ℤ) = 0` for every `p ≥ 4`.** -/
theorem q_homology_top (p : ℕ) (hp : 4 ≤ p) (x : Homology Qtop p) : x = 0 := by
  rcases Nat.lt_or_ge 4 p with h | h
  · exact q_homology_high p h x
  · have hp4 : p = 4 := le_antisymm h hp
    subst hp4
    exact q_homology_four x

/-- `Hml`-engine form of `q_homology_top`. -/
theorem q_hml_top (p : ℕ) (hp : 4 ≤ p) (x : Hml (chainBoundary Qtop) p) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (hmlEquivHomology Qtop p)).mp (q_homology_top p hp _)

/-- **`H₅(Q;ℤ) = 0`** — the single statement the `orientInput` residual had been reduced to. -/
theorem h5Q (x : Homology Qtop 5) : x = 0 := q_homology_top 5 (by omega) x

/-- `Hml` form of `h5Q`. -/
theorem h5Q_hml (x : Hml (chainBoundary Qtop) 5) : x = 0 := q_hml_top 5 (by omega) x

/-- `Hml` form of `H₄(Q;ℤ) = 0`. -/
theorem h4Q_hml (x : Hml (chainBoundary Qtop) 4) : x = 0 := q_hml_top 4 (by omega) x

/-- **THE DEGREE-3 TRANSFER IS INJECTIVE, UNCONDITIONALLY.** `t : H₃(Q;ℤ) → H₃(T⁴°;ℤ)` — the
`_uncond` iff of `KummerPunctureTopVanish` with its right-hand side now discharged. -/
theorem transferH_three_injective : Function.Injective (transferH 3) :=
  SKEFTHawking.KummerPunctureTopVanish.transferH_three_injective_of_h5Q h5Q

/-- **`H₃(Q;ℤ) IS 2-TORSION-FREE, UNCONDITIONALLY.** -/
theorem h3Q_twoTorsionFree (y : Homology (TopCat.of FreeQuotient) 3) (hy : (2 : ℤ) • y = 0) :
    y = 0 :=
  SKEFTHawking.KummerPunctureTopVanish.twoTorsionFree_of_h5Q h5Q y hy

/-- **`H₃(Q;ℤ)` is torsion-free as soon as `H₃(T⁴°;ℤ)` is** — with the transfer now injective the
whole torsion question on the free quotient transports to the punctured torus. The 2-primary half
is unconditional (`h3Q_twoTorsionFree`); only odd torsion of `H₃(T⁴°;ℤ)` is still an input. -/
theorem h3Q_torsionFree_of_ptTorsionFree
    (hPT : ∀ (x : Hml (chainBoundary PTtop) 3) (m : ℤ), m ≠ 0 → m • x = 0 → x = 0)
    (y : Hml (chainBoundary Qtop) 3) (m : ℤ) (hm : m ≠ 0) (hy : m • y = 0) : y = 0 := by
  refine transferH_three_injective ?_
  rw [map_zero]
  refine hPT _ m hm ?_
  rw [← map_zsmul, hy, map_zero]

/-! ## §6. What the degree-4 vanishing does to the `orientInput` window -/

open SKEFTHawking.KummerK3H3SeamWindow (k7Delta3Coord qSeamCoord3 exact_k7Sum4_k7Delta3Coord)

/-- `H₄(qThick;ℤ) = 0`. -/
theorem qThick_homology_four (x : Homology (sub (X := KummerK3top) qThick) 4) : x = 0 :=
  (LinearEquiv.map_eq_zero_iff (qThickHnEquivInt 3)).mp (q_homology_four _)

/-- **`∂₄ : H₄(K3;ℤ) → ℤ¹⁶` IS INJECTIVE.** `ker ∂₄ = im Σ₄` (`exact_k7Sum4_k7Delta3Coord`) and
both degree-4 pieces of the weld now vanish — `H₄(qThick;ℤ) = 0` (this module) and
`H₄(eImage;ℤ) = 0` (banked). So the `b₂`/orientation window of the weld sharpens from

    H₄(qThick) ⊕ H₄(eImage) --Σ₄--> H₄(K3) --∂₄--> ℤ¹⁶ --qSeamCoord3--> H₃(Q) ↠ H₃(K3) → 0

to `0 → H₄(K3;ℤ) --∂₄--> ℤ¹⁶ --qSeamCoord3--> H₃(Q;ℤ) ↠ H₃(K3;ℤ) → 0`: the sixteen seam
coordinates now compute `H₄(K3;ℤ)` on the nose as `ker qSeamCoord3`, and the seam span
`im qSeamCoord3 ≅ ℤ¹⁶ / H₄(K3;ℤ)`. -/
theorem k7Delta3Coord_injective : Function.Injective k7Delta3Coord := by
  intro a b hab
  have h : k7Delta3Coord (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨u, hu⟩ := (exact_k7Sum4_k7Delta3Coord (a - b)).mp h
  have hu0 : u = 0 :=
    Prod.ext (qThick_homology_four u.1)
      (SKEFTHawking.KummerK7MVAssembly.eImageH4_eq_zero u.2)
  rw [hu0, map_zero] at hu
  exact sub_eq_zero.mp hu.symm

/-- `∂₄` lands in `ker qSeamCoord3` (the degree-3 window's exactness at `ℤ¹⁶`). -/
theorem qSeamCoord3_k7Delta3Coord (a : Homology KummerK3top 4) :
    qSeamCoord3 (k7Delta3Coord a) = 0 :=
  (SKEFTHawking.KummerK3H3SeamWindow.exact_k7Delta3Coord_qSeamCoord3 _).mpr ⟨a, rfl⟩

/-- **`H₄(K3;ℤ) ≅ ker (qSeamCoord3 : ℤ¹⁶ → H₃(Q;ℤ))`.** With `∂₄` injective, the degree-3 window's
left end is an isomorphism onto the kernel: the top homology of the welded `K3` is *computed* by the
sixteen seam coordinates, and in particular is a subgroup of `ℤ¹⁶` (free of rank at most 16). This is
the sharpened replacement for the old window, in which `H₄(K3;ℤ)` was only known modulo the then-open
`H₄(Q;ℤ)`. -/
def h4K3EquivKerQSeamCoord3 :
    Homology KummerK3top 4 ≃ₗ[ℤ] LinearMap.ker qSeamCoord3 :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict (LinearMap.ker qSeamCoord3) k7Delta3Coord qSeamCoord3_k7Delta3Coord)
    ⟨fun a b h => k7Delta3Coord_injective (congrArg Subtype.val h),
      fun v => by
        obtain ⟨a, ha⟩ := (SKEFTHawking.KummerK3H3SeamWindow.exact_k7Delta3Coord_qSeamCoord3
          (v : EIndex → ℤ)).mp (LinearMap.mem_ker.mp v.2)
        exact ⟨a, Subtype.ext ha⟩⟩

end

end SKEFTHawking.KummerQTopVanish
