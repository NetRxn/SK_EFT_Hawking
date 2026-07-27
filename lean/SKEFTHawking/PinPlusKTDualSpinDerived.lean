/-
# Phase 5q.H — the `hker` lane's REPLACEMENT interface: a dual-spin datum whose lattice is DERIVED

## Why this module exists

`hker` (`PinPlusKTKerPhiDoubles.KerPhiSubDoubles`) is one of the seven remaining binders of the
16-convergence assembly row. Both previously-named routes to it are **kernel-refuted**:

* **fork 31 `hker-ambient-pin-does-not-restore-geometry`** — `PinPlusKTHkerAmbPinGate.
  nonempty_dualSpinFromW_iff_thirtytwo_dvd` : `Nonempty (DualSpinFromW W sigM) ↔ 32 ∣ sigM`,
  at EVERY `T2` ambient `W`, and `dualSpinFamily_iff_pointwise_thirtytwo_dvd` upgrades that to an
  arbitrary ambient *family*. So pinning `amb` to the genuine tethered `b.W` buys nothing.
* **fork 32 `hker-opener-supplyGeo-is-non-reducing`** — `nonempty_ktSharpnessSupplyGeo_iff_hfwd` :
  the consumed supply is *equivalent* to the `hfwd` conclusion it is supposed to establish.

**The structural root**, recorded as a theorem in that same gate module
(`dualSpin_arith_independent_of_embedding`): `SmoothSpinManifold4` (`SpinRokhlinInterface.lean:62`)
is **pure lattice data** — `rank` / `form` / `even_unimod` / `topo`, with **no underlying space**. So
in `DualSpinFromW` the topological half (`Vspace` / `ιV` / `hclosed`) and the arithmetic half
(`Vspin` / `hdouble`) are disconnected *by construction*: the empty submanifold closed-embeds into any
`T2` `W`, while `spinOfSigMul16 m` supplies a lattice of signature `16·m`. The two halves never have
to meet, because there is no carrier for them to meet on.

## What this module does

It builds the interface the gate module's verdict actually points at: **the lattice is not supplied,
it is DERIVED from `Vspace`'s own integral (co)homology** — the `SpinSigmaAtomPkg` pattern
(fundamental class + `H²` basis + integral Poincaré duality on an actual closed 4-manifold), rather
than a free `SmoothSpinManifold4`.

The point is not stylistic. §3 proves the vacuity attack that killed `DualSpinFromW` **fails** here,
and does so *quantitatively*: `|σ(M)| ≤ 2·b₂(V)` (`abs_sig_le_two_mul_rank`). Where the refuted
interface is inhabited at `Vspace := PEmpty` for every `32 ∣ sigM` — carrying no topological
information whatsoever — the derived interface forces an actual space with `b₂(V) ≥ |σ(M)|/2`. On the
live kernel element `2[g]` (`σ = −32`, `sig_not_vanishing_on_ker`) that is `b₂(V) ≥ 16`:
K3-strength, exactly the content KT Lemma 5.3 "only if" is supposed to carry.

## ⚠ What this module does NOT claim (read before consuming)

**This does not discharge `hker`, and it is not claimed to be sufficient.** §4 records the honest
remaining gap: the only tie between `V` and `W` is still `hclosed : IsClosedEmbedding ιV`, which is
weak. A `w₁(W)`-duality certificate — `[V]` Poincaré-dual to `w₁(W)`, stated as an actual
(co)homological identity on `W` — is the field that would carry the *reduction*; without it the
interface constrains `V` but does not yet make `V` a function of `W`. That question is **open**, not
settled: see §4. No no-go is asserted here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTDualSpinSubmanifold
import SKEFTHawking.PinPlusKTHkerAmbPinGate
import SKEFTHawking.PinPlusKTSpinSigmaAtomReduce

namespace SKEFTHawking.PinPlusKTDualSpinDerived

open scoped Manifold
open Topology
open SKEFTHawking SKEFTHawking.SingularCohomologyInt SKEFTHawking.SingularHomologyInt
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTDualSpinSubmanifold

noncomputable section

/-! ## §1. The interface — the lattice is derived, not supplied -/

/-- **The dual-spin datum with a DERIVED intersection lattice.**

Field-by-field against the refuted `DualSpinFromW`:

| `DualSpinFromW` | here |
|---|---|
| `Vspace` + `[TopologicalSpace]` | `Vspace` + the full **closed-4-manifold** instance block (`T2`, `CompactSpace`, `Nonempty`, `ChartedSpace (EuclideanSpace ℝ (Fin 4))`) |
| `ιV` / `hclosed` | unchanged |
| **`Vspin : SmoothSpinManifold4`** (free lattice data) | **`orient` / `B` / `pd` / `heven` / `topo`** — the lattice is `interMatrix` of `Vspace`'s own `H²` basis against its own fundamental class |
| `hdouble : sigM = 2 * Vspin.sig` | `hdouble : sigM = 2 * latticeSig (interMatrix …)` |

The instance block is doing real work: `IntOrientation` is only *stated* for a compact, nonempty,
`T2`, `EuclideanSpace ℝ (Fin 4)`-charted carrier, so `Vspace := PEmpty` — the exact witness fork 31
used — cannot even be written down here. -/
structure DualSpinDerivedFromW (W : Type) [TopologicalSpace W] (sigM : ℤ) where
  /-- the underlying space of the `w₁(W)`-dual submanifold `V`, as an actual closed 4-manifold. -/
  Vspace : Type
  [Vtop : TopologicalSpace Vspace]
  [VT2 : T2Space Vspace]
  [Vcpt : CompactSpace Vspace]
  [Vne : Nonempty Vspace]
  [Vchart : ChartedSpace (EuclideanSpace ℝ (Fin 4)) Vspace]
  /-- `V ↪ W`: `V` realized inside the 5-dimensional null-bordism total space. -/
  ιV : C(Vspace, W)
  /-- `V` is a CLOSED submanifold of `W` (the codim-1 `w₁`-dual). -/
  hclosed : IsClosedEmbedding ⇑ιV
  /-- the integral orientation of `V`, i.e. `[V] ∈ H₄(V;ℤ)` with its mod-2 compatibility. -/
  orient : IntOrientation Vspace
  /-- the finite free `H²(V;ℤ)` basis — `B.rank = b₂(V)`. -/
  B : IntH2Basis (TopCat.of Vspace)
  /-- integral Poincaré duality on `V` (the UNIMODULARITY input). -/
  pd : IntPoincareDuality (intFundamentalClassOfIntOrientation orient)
  /-- `V` spin ⟹ its intersection form is even unimodular (Wu + PD). Stated about the DERIVED
  matrix, so it is a fact about `V`'s topology, not a free lattice choice. -/
  heven : IsEvenUnimodular (interMatrix (intFundamentalClassOfIntOrientation orient) B)
  /-- the topological factor `2 ∣ σ(V)/8` — Rokhlin's irreducible input, again stated about the
  DERIVED matrix. -/
  topo : (2 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfIntOrientation orient) B) / 8
  /-- the tubular double-cover σ-doubling `σ(M) = 2·σ(V)`, against `V`'s own derived signature. -/
  hdouble : sigM = 2 * latticeSig (interMatrix (intFundamentalClassOfIntOrientation orient) B)

namespace DualSpinDerivedFromW

variable {W : Type} [TopologicalSpace W] {sigM : ℤ}

attribute [instance] Vtop VT2 Vcpt Vne Vchart

/-- **`V`'s derived intersection matrix** — the Gram matrix of `V`'s own integral intersection form
on its own `H²` basis. Not a parameter: a function of `orient` and `B`. -/
def form (d : DualSpinDerivedFromW W sigM) : Matrix (Fin d.B.rank) (Fin d.B.rank) ℤ :=
  interMatrix (intFundamentalClassOfIntOrientation d.orient) d.B

/-- `σ(V)`, derived. -/
def sigV (d : DualSpinDerivedFromW W sigM) : ℤ := latticeSig d.form

theorem hdouble' (d : DualSpinDerivedFromW W sigM) : sigM = 2 * d.sigV := d.hdouble

/-! ## §2. Projection onto the banked lattice interface, and `32 ∣ σ(M)`

Everything the refuted interface delivered still fires — the derived datum is strictly more
informative, so nothing downstream is lost. -/

/-- **The derived lattice, packaged as the banked `SmoothSpinManifold4`.** The three lattice fields
are now *computed* from `V`: `rank := b₂(V)`, `form := interMatrix …`. Only `topo` remains a stated
hypothesis — and it is Rokhlin's irreducible topological input (the atlas KEYSTONE
`hyp:rokhlin_sigma_mod_16`), asserted about an actual manifold rather than about free lattice data. -/
def toSmoothSpinManifold4 (d : DualSpinDerivedFromW W sigM) : SmoothSpinManifold4 where
  rank := d.B.rank
  form := d.form
  even_unimod := d.heven
  topo := d.topo

@[simp] theorem toSmoothSpinManifold4_sig (d : DualSpinDerivedFromW W sigM) :
    d.toSmoothSpinManifold4.sig = d.sigV := rfl

/-- **Forward compatibility: the derived datum produces the banked one.** So every consumer of
`DualSpinFromW` — `toDiv32`, `thirtytwo_dvd`, the `KTSharpnessSupply` assembly — accepts a derived
datum unchanged. The converse does NOT hold (§3). -/
def toDualSpinFromW (d : DualSpinDerivedFromW W sigM) : DualSpinFromW W sigM where
  Vspace := d.Vspace
  Vtop := d.Vtop
  ιV := d.ιV
  hclosed := d.hclosed
  Vspin := d.toSmoothSpinManifold4
  hdouble := d.hdouble

/-- **`32 ∣ σ(M)`** — Rokhlin `16 ∣ σ(V)` on the derived lattice composed with the σ-doubling. -/
theorem thirtytwo_dvd (d : DualSpinDerivedFromW W sigM) : (32 : ℤ) ∣ sigM :=
  d.toDualSpinFromW.thirtytwo_dvd

/-! ## §3. THE SEPARATION — the fork-31 vacuity attack fails here, quantitatively

This is the substantive content of the module. Fork 31's witness is `Vspace := PEmpty` with
`Vspin := spinOfSigMul16 m`: the datum exists at every `32 ∣ sigM` and constrains the topology not at
all. Below: a derived datum forces a *numerical* lower bound on the second Betti number of an actual
space. The bound is `norm_num`-checkable at the live kernel element, and it is falsifiable — a
carrier with too-small `H²` provably cannot carry a nonzero signature. -/

/-- **THE SEPARATION BOUND — `|σ(M)| ≤ 2·b₂(V)`.** The derived datum ties the ambient signature to
the second Betti number of an *actual* space, via Sylvester's `|σ| ≤ rank` (`abs_latticeSig_le`).
Nothing of this shape is available for `DualSpinFromW`, whose `Vspin.rank` is a free parameter with
no relation to `Vspace`. -/
theorem abs_sig_le_two_mul_rank (d : DualSpinDerivedFromW W sigM) :
    |sigM| ≤ 2 * (d.B.rank : ℤ) := by
  have h : |d.sigV| ≤ (d.B.rank : ℤ) := abs_latticeSig_le d.form
  -- NB: `rw [d.hdouble']` is motive-incorrect — `sigM` occurs in `d`'s own TYPE, so abstracting it
  -- breaks `d.sigV`. Go through `congrArg`, which needs no motive over the goal.
  have h2 : |sigM| = 2 * |d.sigV| := by
    have hd : |sigM| = |2 * d.sigV| := congrArg (fun x : ℤ => |x|) d.hdouble'
    rw [hd, abs_mul]
    norm_num
  omega

/-- **b₂ lower bound, the usable form** — a derived datum at signature `sigM` needs a carrier with
`b₂(V) ≥ |σ(M)|/2`. -/
theorem rank_ge (d : DualSpinDerivedFromW W sigM) : |sigM| / 2 ≤ (d.B.rank : ℤ) := by
  have h := d.abs_sig_le_two_mul_rank
  omega

/-- **The trivial-`H²` kill.** If `V`'s second cohomology is trivial then its `H²` basis is empty:
a basis vector of a subsingleton module would have to be both nonzero and zero. This is the exact
place the fork-31 witness died: `PEmpty` (and equally `PUnit`) has no `H²` to carry a signature. -/
theorem rank_eq_zero_of_subsingleton_h2 (d : DualSpinDerivedFromW W sigM)
    (h : Subsingleton (Cohomology (TopCat.of d.Vspace) 2)) : d.B.rank = 0 := by
  haveI := h
  by_contra hne
  obtain ⟨n, hn⟩ : ∃ n, d.B.rank = n + 1 := ⟨d.B.rank - 1, by omega⟩
  have hi : d.B.basis (Fin.cast hn.symm 0) ≠ 0 := d.B.basis.ne_zero _
  exact hi (Subsingleton.elim _ _)

/-- **A carrier with trivial `H²` forces `σ(M) = 0`** — so at any nonzero signature the derived datum
is genuinely unavailable on such a carrier. Contrast `nonempty_dualSpinFromW_iff_thirtytwo_dvd`,
which hands one over at `PEmpty` for *every* `32 ∣ sigM`. -/
theorem sig_eq_zero_of_subsingleton_h2 (d : DualSpinDerivedFromW W sigM)
    (h : Subsingleton (Cohomology (TopCat.of d.Vspace) 2)) : sigM = 0 := by
  have hr := d.rank_eq_zero_of_subsingleton_h2 h
  have hb := d.abs_sig_le_two_mul_rank
  rw [hr] at hb
  have hz : |sigM| ≤ 0 := by simpa using hb
  exact abs_nonpos_iff.mp hz

end DualSpinDerivedFromW

/-- **The `b₂` bound at a general `32·m`** — the quantitative form of §3 at the signatures the `hker`
lane actually meets. -/
theorem rank_ge_of_sig_eq_thirtytwo_mul
    {W : Type} [TopologicalSpace W] {m : ℤ} (d : DualSpinDerivedFromW W (32 * m)) :
    16 * |m| ≤ (d.B.rank : ℤ) := by
  have h := d.abs_sig_le_two_mul_rank
  rw [abs_mul] at h
  norm_num at h
  omega

/-- **THE SEPARATION — the fork-31 witness class is excluded.**

Stated as the two *independent* facts, at a fixed ambient `W` and a nonzero signature `32·m`:

* the **refuted** interface is inhabited — `nonempty_dualSpinFromW_iff_thirtytwo_dvd`, whose witness
  is `Vspace := PEmpty` with `Vspin := spinOfSigMul16 m`: a carrier with no `H²` at all;
* **no derived datum has such a carrier** — a trivial-`H²` carrier forces `σ(M) = 0` (§3), which
  `m ≠ 0` rules out.

So the exact witness class that made fork 31 a refutation cannot inhabit the derived interface. That
is the kernel-checked reason to re-base the `hker` lane here.

⚠ **What this does NOT say.** It does not say the derived interface is *uninhabited* at `32·m` — it
cannot, and no such claim is made: `KummerK3` is a genuine candidate carrier (still open). The
separation is between the two interfaces' admissible witnesses, not a non-existence result. The
`b₂ ≥ 16·|m|` bound is a separate theorem (`rank_ge_of_sig_eq_thirtytwo_mul`), deliberately not
bundled in here — it would be a redundant conjunct, since it implies this one. -/
theorem derived_excludes_fork31_witness_class
    (W : Type) [TopologicalSpace W] [T2Space W] {m : ℤ} (hm : m ≠ 0) :
    Nonempty (DualSpinFromW W (32 * m))
      ∧ ∀ d : DualSpinDerivedFromW W (32 * m),
          ¬ Subsingleton (Cohomology (TopCat.of d.Vspace) 2) := by
  refine ⟨(PinPlusKTHkerAmbPinGate.nonempty_dualSpinFromW_iff_thirtytwo_dvd W (32 * m)).mpr
      ⟨m, rfl⟩, fun d hsub => ?_⟩
  have h0 : (32 : ℤ) * m = 0 := d.sig_eq_zero_of_subsingleton_h2 hsub
  exact hm (by omega)

/-- **The bound at the live kernel element.** The row's forced kernel element `2[g]` keeps
`σ = −32` (`sig_not_vanishing_on_ker`), so a derived dual-spin datum there needs `b₂(V) ≥ 16` —
a `norm_num`-backed, falsifiable statement of exactly the K3-strength the KT "only if" claims.
(Stated at the concrete `−32`, not schematically, so it is checkable rather than decorative.) -/
theorem rank_ge_sixteen_at_sig_neg_thirtytwo
    {W : Type} [TopologicalSpace W] (d : DualSpinDerivedFromW W (-32)) :
    16 ≤ (d.B.rank : ℤ) := by
  have h := d.abs_sig_le_two_mul_rank
  norm_num at h
  omega

/-! ## §4. The remaining tie — `w₁`-duality (OPEN, deliberately not encoded as a no-go)

§3 shows the derived interface is not vacuous in the way `DualSpinFromW` is. It does **not** show the
interface is sufficient, and this section states the gap rather than papering over it.

**What is still weak.** The only field relating `V` to `W` is `hclosed : IsClosedEmbedding ιV`. A
closed embedding constrains `V` inside `W` topologically but says nothing about *which* class `V`
represents. So a putative inhabiter could, in principle, produce a free-floating closed spin
4-manifold of signature `σ(M)/2` (classically these exist for every value in `16ℤ` — connected sums of
`K3` and `S²×S²`) and embed it into a large enough `W`, never using `W`'s geometry. That would make
the interface reduce to "`σ(M)/2` is a realizable spin signature", i.e. back to `32 ∣ σ(M)`.

**Why this is NOT recorded as a settled no-go.** The argument above is *not* in-tree: it needs the
realization construction (an actual closed 4-manifold with an `IntPoincareDuality` datum of every
signature in `16ℤ`), which this project does not have — the single such carrier under construction is
`KummerK3`, and it is still open (`KummerK3E1Residuals`). So the sketch is a **route caution**, not a
kernel-checked refutation, and per Invariant #17 it stays prose here rather than entering
`KERNEL_NOGO_REGISTRY`. Do not cite it as settled.

**What would close it.** A `w₁`-duality certificate stated as an actual cohomological identity on
`W` — `[V] ∈ H₄(W;ℤ/2)` Poincaré-dual to `w₁(W) ∈ H¹(W;ℤ/2)` — is what makes `V` a *function of*
`W` rather than an independent choice. That is the field to build next, and the in-tree substrate for
it is the relative Lefschetz–Wu / `[W,∂W]` tower already used by the capstone lane. This module
deliberately stops short of asserting such a field, because a bare `Prop` named `IsW1Dual` with no
(co)homological content would be exactly the kind of free field §1 was written to eliminate. -/

/-! ## §5. The supply layer, re-based — so the lane is usable, not just designed

§1–§3 replace one datum. This section re-bases the *consumed* shape on it, mirroring
`KTSharpnessSupplyGeo` field-for-field, so the derived interface plugs into the existing
`KerPhiSubDoubles` chain with no downstream edit. -/

variable {k : WithTop ℕ∞}

variable (prov : CharPairWProviderPerOp (𝓡 4) k)

/-- **The KT-"only if" supply over the DERIVED datum** — the exact shape of `KTSharpnessSupplyGeo`,
with `DualSpinFromW` swapped for `DualSpinDerivedFromW`. Per kernel element `x`: an ambient
null-bordism total space together with a dual-spin submanifold whose intersection lattice is computed
from its own homology.

⚠ **`amb` IS STILL A FREE `TopCat` FIELD, and that is a KNOWN, REGISTERED weakness — not fixed here.**
`SETTLED_FORKS.md` (`hker-opener-supplyGeo-is-non-reducing`, 2026-07-27) states the real work as
(1) an `amb`-PINNED supply shape that makes the unpinned-ambient exploit *type-level unavailable*
rather than a permanent data-inspection obligation, and (2) the genuine `w₁(W)`-dual spin
submanifold. **This module addresses neither (1) nor (2).** What it does is strengthen the `V` side —
the lattice can no longer float free of the carrier — which is a prerequisite for (2) being
meaningful, and it leaves (1) exactly where round-12 spec 1 put it. Do not read `toSupplyGeo` +
`kerPhiSubDoubles_of_row_of_supplyDerived` as "the lane is re-based and now reducing"; read it as
"the derived datum plugs in, and the ambient pin is still owed".

Consequently `abs_sig_le_two_mul_rank` below is a bound on `V`, and it holds *whatever* `amb` is —
it is not, and must not be cited as, a fix for the free ambient. -/
structure KTSharpnessSupplyDerived (R : SpinSigmaPresentation (spinEmptyData prov)) where
  /-- the ambient null-bordism total space per kernel element. -/
  amb : ∀ x, spinForgetPhi prov x = 0 → TopCat
  /-- the dual-spin submanifold datum over that ambient, with the σ-doubling against `V`'s own
  derived signature. -/
  dual : ∀ x (hx : spinForgetPhi prov x = 0), DualSpinDerivedFromW (amb x hx) (R.sig x)

variable {prov}

/-- **The derived supply projects onto the banked geometric supply** — pointwise
`toDualSpinFromW`. Every existing consumer therefore accepts a derived supply unchanged. -/
def KTSharpnessSupplyDerived.toSupplyGeo {R : SpinSigmaPresentation (spinEmptyData prov)}
    (S : KTSharpnessSupplyDerived prov R) : KTSharpnessSupplyGeo prov R where
  amb := S.amb
  dual := fun x hx => (S.dual x hx).toDualSpinFromW

/-- **`ker Φ ⊆ doubles` from the derived supply** — the full banked chain, unchanged. -/
theorem kerPhiSubDoubles_of_row_of_supplyDerived (row : SpinPresentationRow prov)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBnd : row.R.SphereProductBounds)
    (S : KTSharpnessSupplyDerived prov row.R) :
    KerPhiSubDoubles prov :=
  kerPhiSubDoubles_of_row_of_supplyGeo row hCob hBase hBnd S.toSupplyGeo

/-- **THE FORK-32 NON-TRANSFER, per kernel element.** Fork 32
(`nonempty_ktSharpnessSupplyGeo_iff_hfwd`) says `KTSharpnessSupplyGeo` is *equivalent* to its own
conclusion `∀ x ∈ ker Φ, 32 ∣ σ(x)`, so it reduces nothing. That equivalence proof works by handing
back a `DualSpinFromW` built on a point with a free lattice; it has **no analogue here**, because a
derived supply additionally carries, at every kernel element, a numerical constraint on an actual
space: `|σ(x)| ≤ 2·b₂(V_x)`.

This is the statement to check a future "we inhabited the supply" claim against: an inhabiter must
exhibit, per kernel element, a closed 4-manifold with an `IntPoincareDuality` datum and second Betti
number at least `|σ(x)|/2`. On the forced kernel element (`σ = −32`) that is `b₂ ≥ 16`.

⚠ This is NOT a claim that fork 32's equivalence is *false* for the derived supply — only that its
proof does not carry over, and that any replacement must clear this bound. Whether the derived supply
is still equivalent to `hfwd` is exactly the §4 open question. -/
theorem KTSharpnessSupplyDerived.abs_sig_le_two_mul_rank
    {R : SpinSigmaPresentation (spinEmptyData prov)} (S : KTSharpnessSupplyDerived prov R)
    (x : DataBordismGrp (spinEmptyData prov)) (hx : spinForgetPhi prov x = 0) :
    |R.sig x| ≤ 2 * (((S.dual x hx).B.rank : ℕ) : ℤ) :=
  (S.dual x hx).abs_sig_le_two_mul_rank

end

end SKEFTHawking.PinPlusKTDualSpinDerived
