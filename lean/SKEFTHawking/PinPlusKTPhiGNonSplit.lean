/-
# Phase 5q.H — `hΦg` IDENTIFIED: the residual generator-image atom **IS** `KTNonSplit`

**The question this module settles.** `PinPlusKTAssemblyResiduals.kt_equiv_zmod16_of_residuals_ofKRS_phig`
carries seven hypotheses, the last of which is the geometric atom

  `hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g) = ktKernelRep prov`

introduced by `PinPlusKTBinderDischarge` as the 8→7 replacement for the W-D binder pair
`{hcyc : SpinImageCyclic, h2 : k₀ + k₀ = 0}`. Neither member of that pair is discharged anywhere in
tree: `SpinImageCyclic` is a `def … : Prop` whose ONLY route
(`PinPlusKTKernelSpinRoute.spinImageCyclic_of_presentation`) itself takes `hΦg` as a hypothesis, so
"`hcyc ⟹ hΦg`" composed with "`hΦg ⟹ hcyc`" is a strict CIRCLE, not a discharge.

**The result.** Over the rest of the residual row, `hΦg` is EQUIVALENT to the project's own named
W-D binder `KTNonSplit prov` (`k₀ ≠ 0`) — `phiG_eq_ktKernelRep_iff_ktNonSplit`. The non-circular
direction is `phiG_eq_ktKernelRep_of_nonSplit`, and it runs entirely through banked facts:

* `charPairBrown_ktKernelRep` — `k₀` is a `charPairBrown`-kernel class (PROVED, unconditional);
* `hKRS : KernelReducesToSpin` — so `k₀` is broad-sector (`EmptySigmaRepresentable`);
* `hcol : RankZeroCollapsesToEmptySurf` ⟹ `SectorIsGeometric` ⟹ `Φ` covers the broad sector
  (`spinForgetPhi_range_of_sectorIsGeometric`) — so `k₀ = Φ w`;
* `SpinSigmaRoute.generates` (the row's `hA`/`hB`/`hg`/`hdvd`) — so `w = n • [g]`, i.e. `k₀ = n • Φ[g]`;
* `spinForgetPhi_add_self` — `Φ[g]` is 2-torsion (PROVED, structure-TIED through the rank-0 sector,
  NOT universal `revStr`-triviality, so the no-go `dataBordism_two_torsion_of_revStr_trivial` is not
  reproduced), so `zsmul_of_two_torsion` gives `k₀ = 0 ∨ k₀ = Φ[g]`;
* `KTNonSplit` kills the first branch. Hence `Φ[g] = k₀`.

**Net row effect — 7 ⟶ 6.** The `hΦg` route needs `hker : KerPhiSubDoubles` (to manufacture `hfwd`
for the dA leaf); the `KTNonSplit` route does NOT. `kt_equiv_zmod16_of_row_of_nonSplit` reaches the
same `≃+ ZMod 16` conclusion from `{hKRS, row, hA, hB, hcol, KTNonSplit}` — six hypotheses, all of
them named project objects, `hker` dropped. The `{hcyc, h2}` pair frozen since the W-D wave is
discharged here as a by-product (`spinImageCyclic_of_row_of_nonSplit`,
`ktKernelRep_add_self_of_row_of_nonSplit`) — from `KTNonSplit`, never from itself.

**Anti-vacuity (this is not a both-sides-zero equation).** `phiG_ne_zero` proves `Φ[g] ≠ 0` from
`hfwd` + `σ[g] = −16` + `not_thirtytwo_dvd_neg_sixteen`, so the degenerate reading of `hΦg` (both
sides `0`) is REFUTED over the row; `ktNonSplit_of_phiG` is the converse arrow, making the
equivalence sharp. Consequently the row certifies genuine non-triviality of BOTH groups
(`nontrivial_dataBordismGrp_spinEmptyData`, `nontrivial_t2DataBordismGrp_of_row`) — conditionally on
the row, which is the honest status: unconditional non-triviality of `DataBordismGrp (spinEmptyData
prov)` remains OPEN (it sits downstream of the σ-presentation R-atom, which is a row input here).

**Fences honored.** `k0-to-k1-transport-refuted` — every statement is `k`-generic (`{k : WithTop ℕ∞}`),
no `k = 0` specialization anywhere. `freeze-a-atoms-satisfiable-with-zero-geometry` — nothing here
touches `rank`; `SpinSigmaRoute.generates` is consumed as a black box through `hA`/`hB`/`hg`/`hdvd`.
`5qH-injectivity-routes-all-equal-one-completeness-prop` — no route-hopping: this does not claim a
new route to the conclusion, it IDENTIFIES the unnamed atom `hΦg` with the already-tracked binder
`KTNonSplit`, which is exactly the "all routes equal one completeness Prop" statement made kernel-fact.
`dataBordism_two_torsion_of_revStr_trivial` — untouched (the 2-torsion used is the enhancement-tied
`spinForgetPhi_add_self`, never universal `revStr`-triviality).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTBinderDischarge

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTAssemblyResiduals

namespace SKEFTHawking.PinPlusKTPhiGNonSplit

variable {k : WithTop ℕ∞}
variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-! ## §1. The `hΦg`-FREE half of the cyclic classification

`spinImageCyclic_of_presentation` uses its `hΦg` hypothesis for exactly one purpose: to rewrite the
generator image `Φ[g]` into `k₀` at the very end. Dropping it leaves a statement that is just as
strong and is NOT circular — the broad sector is cyclic generated by `Φ[g]` itself. Everything in
§2–§4 is built on this one lemma. -/

/-- **The broad spin sector is cyclic on `Φ[g]`** (the `hΦg`-free half of
`spinImageCyclic_of_presentation`): given the σ-presentation freezes (`hA`/`hB`), the `σ = −16`
generator `g`, Rokhlin (`hdvd`), and the concrete sphere-collapse atom `hcol`, every
`EmptySigmaRepresentable` class is an integer multiple of the GENERATOR IMAGE `Φ[g]`. No `hΦg`, no
`k₀` — hence no circularity with `spinForgetPhi_g_eq_ktKernelRep_of_cyclic`. -/
theorem emptySigma_eq_zsmul_phiG
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    {y : T2DataBordismGrp (pinPlusCharPairData prov)} (hy : EmptySigmaRepresentable prov y) :
    ∃ n : ℤ, y = n • spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) := by
  obtain ⟨w, rfl⟩ := spinForgetPhi_range_of_sectorIsGeometric prov
    (sectorIsGeometric_of_rankZeroCollapsesToEmptySurf prov hcol) y hy
  obtain ⟨n, rfl⟩ := R.generates hA hB g hg hdvd w
  exact ⟨n, by rw [map_zsmul]⟩

/-- **`Φ[g]` is 2-torsion** — a re-exposure of `spinForgetPhi_add_self` in the `(2 : ℤ) • _ = 0`
shape `zsmul_of_two_torsion` consumes. Enhancement-tied through the rank-0 sector, NOT universal
`revStr`-triviality (the refuted `dataBordism_two_torsion_of_revStr_trivial` is not in play). -/
theorem two_zsmul_phiG (g : StrMfd (spinEmptyData prov)) :
    (2 : ℤ) • spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = 0 := by
  rw [two_zsmul]; exact spinForgetPhi_add_self prov _

/-! ## §2. ANTI-VACUITY — `hΦg` is not a both-sides-zero equation

The cheapest way an equation between group elements can be worthless is for both sides to be `0` in
a degenerate group. Over the row that reading is REFUTED: the ÷32 bank forces `Φ[g] ≠ 0`. -/

/-- **The generator image is NONZERO** (`Φ[g] ≠ 0`) — the anti-vacuity certificate for `hΦg`. If
`Φ[g] = 0` then the KT "only if" `hfwd` forces `32 ∣ σ[g] = −16`, refuted by the banked
`not_thirtytwo_dvd_neg_sixteen`. So an `hΦg` discharge can never be the degenerate `0 = 0`. -/
theorem phiG_ne_zero
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) ≠ 0 := by
  intro h0
  have h32 := hfwd _ h0
  rw [hg] at h32
  exact not_thirtytwo_dvd_neg_sixteen h32

/-- **`hΦg ⟹ KTNonSplit`** (the forward arrow of the identification): if the generator image is
`k₀`, then `k₀ ≠ 0` because `Φ[g] ≠ 0`. So `hΦg` is at least as strong as the project's hardest
named open bit — it cannot be discharged more cheaply than `KTNonSplit` itself. -/
theorem ktNonSplit_of_phiG
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov) :
    KTNonSplit prov := fun h0 => phiG_ne_zero prov R g hg hfwd (hΦg.trans h0)

/-! ## §3. THE IDENTIFICATION — `KTNonSplit ⟹ hΦg`, and the sharp equivalence -/

/-- **THE KEY ARROW — `KTNonSplit ⟹ hΦg`, non-circular.** `k₀` is a `charPairBrown`-kernel class
(`charPairBrown_ktKernelRep`, unconditional), so `hKRS` puts it in the broad spin sector; §1 then
writes it as `n • Φ[g]`; `Φ[g]` is 2-torsion, so `zsmul_of_two_torsion` gives `k₀ = 0` or
`k₀ = Φ[g]`; `KTNonSplit` kills the first. Consumes NO `SpinImageCyclic`, NO `hΦg`, NO
`KerPhiSubDoubles` — the circle through `spinImageCyclic_of_presentation` is avoided entirely. -/
theorem phiG_eq_ktKernelRep_of_nonSplit
    (hKRS : KernelReducesToSpin prov)
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov := by
  obtain ⟨n, hn⟩ := emptySigma_eq_zsmul_phiG prov R hA hB g hg hdvd hcol
    (hKRS _ (charPairBrown_ktKernelRep prov))
  rcases zsmul_of_two_torsion _ (two_zsmul_phiG prov g) n with h | h
  · exact absurd (hn.trans h) hns
  · exact (hn.trans h).symm

/-- **THE SHARP IDENTIFICATION** — over the residual row, the unnamed geometric atom `hΦg` is
EXACTLY the named W-D binder `KTNonSplit`. Forward: `ktNonSplit_of_phiG` (the ÷32 bank).
Backward: `phiG_eq_ktKernelRep_of_nonSplit` (the sector-cyclicity route). This is the honest cost
statement for the whole `hΦg` lane: closing `hΦg` is neither easier nor harder than closing the
non-split bit `8 • [ℝP⁴] ≠ 0`, which the dossier §5 records as the most likely stall point. -/
theorem phiG_eq_ktKernelRep_iff_ktNonSplit
    (hKRS : KernelReducesToSpin prov)
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g) = ktKernelRep prov
      ↔ KTNonSplit prov :=
  ⟨ktNonSplit_of_phiG prov R g hg hfwd,
    phiG_eq_ktKernelRep_of_nonSplit prov hKRS R hA hB g hg hdvd hcol⟩

/-! ## §4. THE FROZEN W-D BINDER PAIR `{hcyc, h2}`, DISCHARGED FROM `KTNonSplit`

Hypotheses 7–8 of the historical eight-row. `PinPlusKTBinderDischarge` REPLACED them with `hΦg`
(a reduction, not a discharge — its own §-header records `hcyc`'s route as "the (unbuilt)
spin-specialization map `Φ`"). With `Φ` now built and §3 in hand they are genuinely discharged. -/

/-- **`hcyc` DISCHARGED** — `SpinImageCyclic` from the row + `KTNonSplit`. Not circular: the
generator image is supplied by §3, which never consults `SpinImageCyclic`. -/
theorem spinImageCyclic_of_row_of_nonSplit
    (hKRS : KernelReducesToSpin prov)
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    SpinImageCyclic prov := by
  intro y hy
  obtain ⟨n, hn⟩ := emptySigma_eq_zsmul_phiG prov R hA hB g hg hdvd hcol hy
  exact ⟨n, by rw [hn, phiG_eq_ktKernelRep_of_nonSplit prov hKRS R hA hB g hg hdvd hcol hns]⟩

/-- **`h2` DISCHARGED** — the 2-torsion `k₀ + k₀ = 0` from the row + `KTNonSplit`, by transporting
the enhancement-tied `spinForgetPhi_add_self` across the identification `Φ[g] = k₀`. -/
theorem ktKernelRep_add_self_of_row_of_nonSplit
    (hKRS : KernelReducesToSpin prov)
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    ktKernelRep prov + ktKernelRep prov = 0 := by
  rw [← phiG_eq_ktKernelRep_of_nonSplit prov hKRS R hA hB g hg hdvd hcol hns]
  exact spinForgetPhi_add_self prov _

/-- **`KTKernelCard` from the row + `KTNonSplit`** — the `{0, k₀}` kernel cover. Every kernel class
is broad-sector (`hKRS`), hence `n • Φ[g]` (§1), hence `0` or `Φ[g]` (2-torsion), hence `0` or `k₀`
(§3). This is what lets the headline below bypass `KerPhiSubDoubles` entirely. -/
theorem ktKernelCard_of_row_of_nonSplit
    (hKRS : KernelReducesToSpin prov)
    (R : SpinSigmaPresentation (spinEmptyData prov))
    (hA : R.RealizesSphereProducts) (hB : R.SphereProductBounds)
    (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hdvd : ∀ x, (16 : ℤ) ∣ R.sig x)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    KTKernelCard prov := by
  intro x hx
  obtain ⟨n, hn⟩ := emptySigma_eq_zsmul_phiG prov R hA hB g hg hdvd hcol (hKRS x hx)
  rcases zsmul_of_two_torsion _ (two_zsmul_phiG prov g) n with h | h
  · exact Or.inl (hn.trans h)
  · exact Or.inr ((hn.trans h).trans
      (phiG_eq_ktKernelRep_of_nonSplit prov hKRS R hA hB g hg hdvd hcol hns))

/-! ## §5. THE 7 ⟶ 6 HEADLINE — the residual row in named binders only -/

/-- **THE ROW SHRINK, 7 ⟶ 6.** `kt_equiv_zmod16_of_residuals_ofKRS_phig` needs
`{hKRS, row, hA, hB, hcol, hker, hΦg}`. Replacing the unnamed atom `hΦg` by the binder it is
equivalent to (§3) makes `hker : KerPhiSubDoubles` REDUNDANT — it entered only to manufacture the
dA leaf's `hfwd`, whereas `KTNonSplit` reaches `KTKernelCard` directly (§4) and the assembly of
record `kt_equiv_zmod16` consumes exactly `{KTKernelCard, KTNonSplit}`. Six hypotheses, every one a
named project object. -/
theorem kt_equiv_zmod16_of_row_of_nonSplit
    (hKRS : KernelReducesToSpin prov) (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16 prov
    (ktKernelCard_of_row_of_nonSplit prov hKRS row.R hA hB row.g row.hg row.hdvd hcol hns) hns

/-- **The Rokhlin-16 twin of the shrunk row** — `Nat.card Ω₄^{Pin⁺} = 16` from the same six
hypotheses. Pure transport of `Nat.card (ZMod 16) = 16` across the additive equivalence. -/
theorem rokhlin_sixteen_of_row_of_nonSplit
    (hKRS : KernelReducesToSpin prov) (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcol : RankZeroCollapsesToEmptySurf prov)
    (hns : KTNonSplit prov) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData prov)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_row_of_nonSplit prov hKRS row hA hB hcol hns
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-! ## §6. NON-TRIVIALITY of the two carriers, over the row

The lead-facing caveat: unconditional non-triviality of `DataBordismGrp (spinEmptyData prov)` is NOT
established in tree (it sits downstream of the open σ-presentation R-atom). What IS now established
is the CONDITIONAL statement — over the row, both the spin source and the Pin⁺ target are honestly
non-trivial, which is what stops any `hΦg` discharge from being worthless-by-degeneracy. -/

/-- **The K3 generator class is nonzero in the spin carrier** — over the row, `[g] ≠ 0` in
`DataBordismGrp (spinEmptyData prov)`, because its `Φ`-image is nonzero and `Φ 0 = 0`. -/
theorem mk_g_ne_zero
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    DataBordismGrp.mk (spinEmptyData prov) g ≠ 0 := by
  intro h0
  exact phiG_ne_zero prov R g hg hfwd (by rw [h0, map_zero])

/-- **The spin carrier is non-trivial over the row** — `DataBordismGrp (spinEmptyData prov)` has at
least two elements. CONDITIONAL (on the σ-presentation row + `hfwd`); the unconditional statement
remains open, which is exactly why the row is where the non-triviality is claimed. -/
theorem nontrivial_dataBordismGrp_spinEmptyData
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    Nontrivial (DataBordismGrp (spinEmptyData prov)) :=
  ⟨⟨DataBordismGrp.mk (spinEmptyData prov) g, 0, mk_g_ne_zero prov R g hg hfwd⟩⟩

/-- **The Pin⁺ carrier is non-trivial over the row** — `Φ[g] ≠ 0` witnesses it directly. Together
with the previous theorem this rules out the degenerate reading of every `hΦg`-shaped statement in
this lane: neither side of `hΦg` lives in a known-trivial group. -/
theorem nontrivial_t2DataBordismGrp_of_row
    (R : SpinSigmaPresentation (spinEmptyData prov)) (g : StrMfd (spinEmptyData prov))
    (hg : R.sig (DataBordismGrp.mk (spinEmptyData prov) g) = -16)
    (hfwd : ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ R.sig x) :
    Nontrivial (T2DataBordismGrp (pinPlusCharPairData prov)) :=
  ⟨⟨spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) g), 0,
    phiG_ne_zero prov R g hg hfwd⟩⟩

end SKEFTHawking.PinPlusKTPhiGNonSplit
