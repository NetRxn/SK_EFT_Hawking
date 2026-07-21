/-
# Phase 5q.H close-out (Lane C0) — THE `DualSpinFromW` CONSTRUCTION, OPENED ONE LEVEL DEEPER:
# the KT Lemma 5.3 "only if" dual-spin submanifold decomposed into its three named atoms
# (transversal `w₁`-dual representative / `V`-is-spin / double-cover σ-doubling), with the
# lattice core of the σ-doubling DISCHARGED and the two genuine geometric leaves named exactly.

`PinPlusKTDualSpinSubmanifold.DualSpinFromW` bundles the FINISHED KT "only if" datum: `V` embedded
in the ambient `W` (atom a), `V`'s spin lattice `Vspin` (atom b), and `hdouble : σ(M) = 2·σ(V)`
(atom c) as a single lumped equation. This module OPENS that construction against the tethered
witness's actual data: it separates `hdouble` into its two geometric steps — (c.1) cobordism
invariance `σ(M) = σ(∂E(V))` (the deep leaf: `M` and `∂E(V)` cobound the orientable `W ∖ E(V)`) and
(c.2) the double-cover σ-multiplicativity `σ(∂E(V)) = 2·σ(V)` — and DISCHARGES the lattice arithmetic
of (c.2) on the canonical double `edgeDoubleSpin` (banked `latticeSig_blockDiag`). The opened form
projects back onto `DualSpinFromW` (§4), so it feeds the banked, NON-CIRCULAR `hfwd` chain unchanged
(§5). Follows `PinPlusKTDualSpinSubmanifold` (#180): the named atom opened to its constituents.

## The mathematics (`ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md`; KT-LMS-151 §5, Lemma 5.3 p.216)

KT "only if": a closed spin `M⁴` that Pin⁺-bounds does so via a Pin⁺ `W⁵`; take `V ⊂ W` dual to
`w₁(W)`; `V` is SPIN (`w₁(V) = w₁(W)|V − w₁(ν) = 0`, `ν` the normal line bundle with
`w₁(ν) = w₁(W)|V`; `w₂(V) = 0` by the Pin⁺ Wu relation); `∂E(V)` (the boundary of `V`'s tubular
neighbourhood) is the `w₁(ν)`-classified double cover, so `σ(M) = σ(∂E) = 2·σ(V)`; Rokhlin
`16 ∣ σ(V)` (banked, `SmoothSpinManifold4.rokhlin`) ⟹ `32 ∣ σ(M)`.

## THE ORIENTABILITY ADJUDICATION (a load-bearing finding for the lead — get it right, state it)

The scout sets up "a Pin⁺ `W⁵` with **orientable** `∂W = M`". Precisely:

* **`∂W = M` is ORIENTABLE (spin).** Both ends of the empty-Σ sector bordism are spin manifolds; `M`
  is the spin class. Hence `w₁(W)|M = 0` — the `w₁(W)`-dual `V` is pushed off the boundary and is a
  CLOSED (`∂V = ∅`) submanifold of the interior.
* **`W` is Pin⁺ and GENUINELY NON-ORIENTABLE (`w₁(W) ≠ 0`) on the load-bearing kernel classes.** If
  `W` were orientable then `w₁(W) = 0`, the dual `V` is empty/degenerate, and the argument gives
  `σ(M) = 2·σ(∅) = 0` — the trivial sub-case (`σ = 0`). The entire ÷32 content is POWERED BY `W`'s
  non-orientability: `V` is the codim-1 `w₁(W)`-dual and exists non-trivially exactly when
  `w₁(W) ≠ 0`. So the `hfwd` consumption is on `ker Φ` where `W` is the Pin⁺ (generally
  non-orientable) bordism between spin ends — `w₁(W)` CAN and DOES vanish only in the `σ = 0` case.
  The scout's "Pin⁺ `W`" anatomy is the correct one; a spin (orientable) `W` would already force
  `σ(M) = 0` and never see K3.
* **`V` is SPIN, hence ORIENTABLE.** `w₁(V) = 0` (the `w₁(ν) = w₁(W)|V` cancellation via Whitney) and
  `w₂(V) = 0` (Pin⁺ Wu). So `V` is a genuine closed spin 4-manifold with an honest signature and
  Rokhlin `16 ∣ σ(V)` applies (this module's `Vspin : SmoothSpinManifold4`).
* **`∂E(V) → V` is the `w₁(ν) = w₁(W)|V`-classified double cover** — NOT the orientation double cover
  of `V` (which is trivial, since `V` is orientable): `w₁(ν)` is a distinct class that need not
  vanish even though `w₁(TV) = 0`. `σ(∂E(V)) = 2·σ(V)` holds by Hirzebruch signature-multiplicativity
  of the 2-fold cover, realized at the lattice level by `edgeDoubleSpin` (`latticeSig_blockDiag`).

## Dimension bookkeeping (the Q-vs-V verdict, inherited)
`x`/`M` = 4-dim spin (empty Σ); `W = b.W` = 5-dim Pin⁺; `V` = 4-dim codim-1 `w₁(W)`-dual;
`∂E(V)` = 4-dim (the `w₁(ν)`-cover of `V`); `Q = real.Q` = 3-dim codim-2 membrane (`Q ≠ V`, settled).

## The decomposition into named atoms (what discharged / what stays a leaf)
* **atom (a) — transversal `w₁`-dual representative** `V ⊂ W`: the genuinely deep piece (smooth
  transversality of the `w₁(W)`-classifier's zero locus; no in-tree/Mathlib transversality). NAMED as
  constructed data (`Vspace`/`ιV`/`hclosed` — the codim-1 closed embedding), inherited from
  `DualSpinFromW`. STAYS A LEAF.
* **atom (b) — `V` is spin**: the Wu/duality certificate `w₁(V) = w₂(V) = 0`. Its OUTPUT is
  `Vspin : SmoothSpinManifold4` (even-unimodular form + the Rokhlin topological factor — the spin
  certificate's arithmetic content). The characteristic-class vanishing is the docstring-named
  geometric justification; the lattice output is carried. STAYS A LEAF (the vanishing), DISCHARGED
  (the `16 ∣ σ(V)` consequence, via `Vspin.rokhlin`).
* **atom (c) — the double-cover σ-doubling**, OPENED into two steps:
  * (c.1) `hcob : σ(M) = σ(∂E(V))` — cobordism invariance (`M`, `∂E(V)` cobound orientable
    `W ∖ E(V)`). STAYS A LEAF (the geometric content).
  * (c.2) `hcover : σ(∂E(V)) = 2·σ(V)` — the 2-fold-cover σ-multiplicativity. DISCHARGED at the
    lattice level on the canonical double `edgeDoubleSpin` via `latticeSig_blockDiag` (banked). Carried
    as a leaf field on the abstract `edge`, and BANKED on the canonical realization (`edgeDoubleSpin_sig`).

## The #179 convergence verdict (shared-infrastructure check with dC's collapse atom)
`PinPlusKTSectorGeometricReduce.RankZeroCollapsesToEmptySurf` (dC's atom) collapses a rank-0
characteristic SURFACE (`Σ`, tracked by the codim-2 membrane `Q`) to empty via the membrane-realization
machinery (`emptySourceRealizationTied`). This module's `V` is the codim-1 `w₁(W)`-dual — DIMENSIONALLY
DISJOINT from `Q` (4-dim codim-1 vs 3-dim codim-2; the settled `Q ≠ V`). The two constructions share NO
infrastructure: dC routes through the `Σ`-collapse surgery/membrane realization; this routes through the
`latticeSig` block engine (`edgeDoubleSpin`) + the inherited embedding leaf. The ONLY shared element is
the CONVENTION "name the geometric leaf as Type-valued constructed data over the tethered `W`" — a
packaging convention, not shared machinery. VERDICT: no common surgery atom; the codim-1/codim-2 split is
real and the machineries are separate.

## NON-CIRCULARITY (fork `geometric-phi-does-not-close-hfwd-fakeability`, round-10/11 audit)
Every proof here consumes ZERO facts about `k₀ = 8•[ℝP⁴]` (`ktKernelRep`), `KTNonSplit`, or the row's
`hΦg`. The new content uses only: `latticeSig_blockDiag` / `isEvenUnimodular_blockDiag` (banked lattice
algebra), `SmoothSpinManifold4.rokhlin` (banked Rokhlin), and the inherited `DualSpinFromW` projection
onto the already-audited `hfwd_of_row_of_supplyGeo`. The `hfwd` derivation still routes through
`KerPhiSubDoubles` (a PURE SPIN-SIDE statement), non-circular by proof inspection.

## Fences honored (18-fork fence, `KernelNoGos.lean`)
`geometric-phi-does-not-close-hfwd-fakeability`: deepens the audit-friendly supply one level; the hfwd
route is unchanged (non-circular by inspection). `enriques-datum-refuted-as-shaped`: no `EnriquesDatum`
constructed/consumed. `untethered-membrane-factors-relation`: nothing rebuilds an untethered variant —
the construction is keyed on the tethered witness's `b.W` (via `DualSpinFromW`'s ambient). The
binary-partition / free-membrane-kernel / synthetic-grade-ker-⊥ forks: untouched (no black-box Prop, no
grade-ker manipulation).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTDualSpinSubmanifold

open scoped Manifold
open Topology
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTLemma53Wave
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTDualSpinSubmanifold

namespace SKEFTHawking.PinPlusKTDualSpinConstruction

variable {k : WithTop ℕ∞}

/-! ## §1. Atom (c.2) DISCHARGED — the double-cover σ-doubling at the lattice level.

`∂E(V)`, the `w₁(ν)`-classified 2-fold cover of the spin `V`, has `σ(∂E(V)) = 2·σ(V)` by Hirzebruch
signature-multiplicativity. `edgeDoubleSpin V` is the CANONICAL lattice realization of that σ-value:
the even-unimodular block-double `V.form ⊕ V.form` (`latticeSig` `= 2·σ(V)`, banked). It IS spin (a
cover of the spin `V`), so it carries a genuine `SmoothSpinManifold4` datum. -/

/-- **The lattice realization of `∂E(V)`** — the double-cover 4-manifold whose intersection form is the
even-unimodular block-double of `V`'s, with `σ = 2·σ(V)`. The `topo` factor is inherited from `V`'s
Rokhlin `16 ∣ σ(V)`. This BANKS the lattice core of atom (c.2). -/
noncomputable def edgeDoubleSpin (V : SmoothSpinManifold4) : SmoothSpinManifold4 where
  rank := V.rank + V.rank
  form := blockDiag V.form V.form
  even_unimod := isEvenUnimodular_blockDiag _ _ V.even_unimod V.even_unimod
  topo := by
    have hd : latticeSig (blockDiag V.form V.form) = 2 * V.sig := by
      rw [latticeSig_blockDiag _ _ V.even_unimod V.even_unimod]
      simp only [SmoothSpinManifold4.sig]; ring
    rw [hd]
    obtain ⟨c, hc⟩ := V.rokhlin
    rw [hc]
    omega

/-- **The banked σ-doubling** — `σ(∂E(V)) = 2·σ(V)` on the canonical double, via `latticeSig_blockDiag`.
This is the DISCHARGED lattice content of atom (c.2). -/
@[simp] theorem edgeDoubleSpin_sig (V : SmoothSpinManifold4) : (edgeDoubleSpin V).sig = 2 * V.sig := by
  show latticeSig (blockDiag V.form V.form) = 2 * V.sig
  rw [latticeSig_blockDiag _ _ V.even_unimod V.even_unimod]
  simp only [SmoothSpinManifold4.sig]; ring

/-! ## §2. The opened construction — `DualSpinConstruction`, the three named atoms with (c) split. -/

/-- **`DualSpinFromW` OPENED one level deeper** (Type-valued CONSTRUCTED DATA, the honest deeper leaf).
For a bounded spin `M⁴` (`σ = sigM`) bounding a Pin⁺ `W⁵`, this exposes the atoms `DualSpinFromW`
bundles as finished data:

* atom (a): `Vspace`/`ιV`/`hclosed` — `V` as a CLOSED codim-1 subspace of the ambient `W` (the
  transversal `w₁(W)`-dual representative; deep leaf, inherited).
* atom (b): `Vspin : SmoothSpinManifold4` — `V`'s spin lattice (Wu-certificate output).
* atom (c), SPLIT into its two geometric steps against the tethered `W`:
  * `edge : SmoothSpinManifold4` — `∂E(V)`, the `w₁(ν)`-cover of `V`, as a closed spin 4-manifold.
  * `hcover : edge.sig = 2 · Vspin.sig` — the 2-fold-cover σ-multiplicativity (BANKABLE on the
    canonical double `edgeDoubleSpin`, `edgeDoubleSpin_sig`).
  * `hcob : sigM = edge.sig` — cobordism invariance `σ(M) = σ(∂E(V))` (the deep geometric leaf: `M`
    and `∂E(V)` cobound the orientable `W ∖ E(V)`).

`hdouble : sigM = 2·Vspin.sig` is now DERIVED (`hcob.trans hcover`), not assumed — the opening. -/
structure DualSpinConstruction (W : Type) [TopologicalSpace W] (sigM : ℤ) where
  /-- atom (a): the underlying space of the `w₁(W)`-dual submanifold `V` (a closed 4-manifold). -/
  Vspace : Type
  [Vtop : TopologicalSpace Vspace]
  /-- atom (a): `V ↪ W`, realized as a subspace of the ambient 5-dim null-bordism total space. -/
  ιV : C(Vspace, W)
  /-- atom (a): `V` is a CLOSED submanifold of `W` (the codim-1 `w₁`-dual). -/
  hclosed : IsClosedEmbedding ⇑ιV
  /-- atom (b): `V`'s spin lattice datum (even-unimodular form + Rokhlin topological factor). -/
  Vspin : SmoothSpinManifold4
  /-- atom (c): `∂E(V)`, the `w₁(ν)`-classified double cover of `V`, as a closed spin 4-manifold. -/
  edge : SmoothSpinManifold4
  /-- atom (c.2): the double-cover σ-multiplicativity `σ(∂E(V)) = 2·σ(V)` (bankable on the canonical
      double via `edgeDoubleSpin_sig`). -/
  hcover : edge.sig = 2 * Vspin.sig
  /-- atom (c.1): cobordism invariance `σ(M) = σ(∂E(V))` — `M` and `∂E(V)` cobound orientable
      `W ∖ E(V)` (the deep geometric leaf). -/
  hcob : sigM = edge.sig

attribute [instance] DualSpinConstruction.Vtop

/-! ## §3. The two-step σ-doubling assembles into the lumped `hdouble`. -/

/-- **The opened σ-doubling recovers `hdouble`** — `σ(M) = σ(∂E(V)) = 2·σ(V)` composes the cobordism
invariance (c.1) with the double-cover multiplicativity (c.2). This is the discharge of the assembly:
the two named geometric steps reproduce `DualSpinFromW`'s lumped `hdouble`. -/
theorem DualSpinConstruction.hdouble {W : Type} [TopologicalSpace W] {sigM : ℤ}
    (d : DualSpinConstruction W sigM) : sigM = 2 * d.Vspin.sig :=
  d.hcob.trans d.hcover

/-! ## §4. Projection back onto the named atom `DualSpinFromW` (forget `edge`, collapse the two steps). -/

/-- **The opened construction projects onto `DualSpinFromW`** — forget the intermediate `∂E(V)` datum
and collapse the two-step σ-doubling into the single `hdouble`. This is the bridge that lets the deeper
opening feed `DualSpinFromW`'s banked machinery (`toDiv32`, `thirtytwo_dvd`) and the `hfwd` chain
unchanged. -/
def DualSpinConstruction.toDualSpinFromW {W : Type} [TopologicalSpace W] {sigM : ℤ}
    (d : DualSpinConstruction W sigM) : DualSpinFromW W sigM where
  Vspace := d.Vspace
  ιV := d.ιV
  hclosed := d.hclosed
  Vspin := d.Vspin
  hdouble := d.hdouble

/-- **`32 ∣ σ(M)` straight from the opened construction** (via the projection + banked Rokhlin
arithmetic). Consumes NO `k₀` facts. -/
theorem DualSpinConstruction.thirtytwo_dvd {W : Type} [TopologicalSpace W] {sigM : ℤ}
    (d : DualSpinConstruction W sigM) : (32 : ℤ) ∣ sigM :=
  d.toDualSpinFromW.thirtytwo_dvd

/-! ## §5. The geometric sharpness supply from the OPENED construction, feeding the banked `hfwd`. -/

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **The KT-"only if" sharpness supply built from the OPENED construction** — per kernel element `x`,
the ambient `W` together with the deeper `DualSpinConstruction` over it (with `∂E(V)` and the two-step
σ-doubling exposed). Its projection `toGeo` yields the banked `KTSharpnessSupplyGeo`. -/
structure KTSharpnessSupplyConstr (R : SpinSigmaPresentation (spinEmptyData prov)) where
  /-- the ambient null-bordism total space per kernel element (intended value `TopCat.of b.W`). -/
  amb : ∀ x, spinForgetPhi prov x = 0 → TopCat
  /-- the OPENED dual-spin construction over that ambient (with `∂E(V)` + the two-step σ-doubling). -/
  constr : ∀ x (hx : spinForgetPhi prov x = 0), DualSpinConstruction (amb x hx) (R.sig x)

/-- **The opened supply projects onto the banked `KTSharpnessSupplyGeo`** — collapse each opened
construction to its `DualSpinFromW`. -/
noncomputable def KTSharpnessSupplyConstr.toGeo {R : SpinSigmaPresentation (spinEmptyData prov)}
    (S : KTSharpnessSupplyConstr R) : KTSharpnessSupplyGeo prov R where
  amb := S.amb
  dual := fun x hx => (S.constr x hx).toDualSpinFromW

/-- **`ker Φ ⊆ doubles` from the OPENED supply** (over the presentation row): the deeper geometric
construction feeds the banked, non-circular σ/16-iso route. Consumes NO `k₀`/`KTNonSplit`/`hΦg` facts. -/
theorem kerPhiSubDoubles_of_row_of_supplyConstr (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupplyConstr row.R) :
    KerPhiSubDoubles prov :=
  kerPhiSubDoubles_of_row_of_supplyGeo row hCob hBase hBnd S.toGeo

/-- **The end-to-end KT "only if" `hfwd` from the OPENED construction** (capstone): from the
presentation row, the terminal Freeze-A atoms, and the geometric sharpness supply with `V ⊂ W`, `∂E(V)`,
and the two-step σ-doubling all exposed, the KT "only if" `∀ x, Φ x = 0 → 32 ∣ σ(x)` — routed through
`KerPhiSubDoubles`, hence NON-CIRCULAR by proof inspection (ZERO `k₀`/`KTNonSplit`/`hΦg` facts). The
`dA` leaf's `hfwd` on its TRUE geometry, opened to the embedded submanifold AND its tubular double cover. -/
theorem hfwd_of_row_of_supplyConstr (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupplyConstr row.R) :
    ∀ x, spinForgetPhi prov x = 0 → (32 : ℤ) ∣ row.R.sig x :=
  hfwd_of_row_of_supplyGeo row hCob hBase hBnd S.toGeo

/-! ## §6. Non-vacuity anchor — the opened construction is inhabited at K3-strength (`σ(V) = −16`). -/

/-- **Non-vacuity of the opened construction** on the forced kernel signature `σ(M) = −32`
(`spinForgetPhi_double_mem_ker` keeps `σ = −32 ≠ 0`): inhabited with `V = K3` (`σ(V) = −16`), `∂E(V) =
edgeDoubleSpin K3` (`σ(∂E) = −32 = 2·σ(V)`, banked), and cobordism invariance `−32 = σ(∂E)`. The
embedding is on a trivial ambient (`PUnit`) purely to witness inhabitability; the load-bearing arithmetic
(`Vspin = K3`, `edge`, the two-step σ-doubling) is real. -/
noncomputable def k3DualSpinConstruction : DualSpinConstruction PUnit (-32) where
  Vspace := PUnit
  ιV := ContinuousMap.id _
  hclosed := IsClosedEmbedding.id
  Vspin := k3Spin
  edge := edgeDoubleSpin k3Spin
  hcover := by rw [edgeDoubleSpin_sig]
  hcob := by rw [edgeDoubleSpin_sig, k3Spin_sig]; norm_num

/-- Non-vacuity check: the opened K3 construction's `σ(M) = −32` is `32`-divisible via the general
`thirtytwo_dvd` — the two-step σ-doubling + Rokhlin arithmetic on the genuine generator. -/
theorem k3DualSpinConstruction_thirtytwo_dvd : (32 : ℤ) ∣ (-32 : ℤ) :=
  k3DualSpinConstruction.thirtytwo_dvd

end SKEFTHawking.PinPlusKTDualSpinConstruction
