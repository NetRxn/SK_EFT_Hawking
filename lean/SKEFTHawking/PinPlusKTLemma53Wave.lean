/-
# Phase 5q.H W-D — THE LEMMA-5.3 WAVE (both directions of KT §5 Lemma 5.3, p.216)

⛔ HARD SCOPE (round-8 `PinPlusKTSectorGate` + round-9 `PinPlusKTStepGate` — BINDING): this module
DISCHARGES NOTHING of the round-8 TRIPLE `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` (nor
`KummerWitness`). It packages KT Lemma 5.3's two geometric directions as NAMED leaf-data structures
(the `AmbientSurgeryDatum` pattern — `PinPlusKTSurgeryTrace`), banks the genuinely in-tree ÷32
arithmetic (σ-doubling + Rokhlin `16 ∣ σ`), and wires each leaf to the sector Prop it feeds. Every
leaf structure has ZERO in-tree inhabitants OFF the fenced degenerate worlds (the real spin carrier /
the genuine `Ω₄^{Spin} → Ω₄^{Pin⁺}` forgetful map are unbuilt), so every reduction is CONDITIONAL,
discharging nothing — exactly like `kernelReducesToSpin_of_ambientDatumSupply`.

## G8-1 provider-inhabitation rider (unchanged, applies to EVERY per-`prov` result here)
`CharPairWProviderPerOp (𝓡 4) k` has no unconditional in-tree inhabitant (only `ofCylinderEngine`,
consuming the SINGLE remaining Track-2 residual `cylData` — addClosure was discharged by PinPlusCharPairWProviderClosed; round-10 kernel-encoded the dependency as nonempty_provider_of_cylData). Every per-`prov` theorem below is CONDITIONAL, not
vacuous, with ZERO live instances until Track-2's `cylData`/`addClosure` land an in-tree `prov`.

## The two directions (KT-LMS-151 §5, Lemma 5.3, p.216; `ScoutReport_KT_Lemma53_div32_Habegger_Enriques.md`)

**Direction A — the "only if" (sharpness, `32 ∣ σ`) → `KTNonSplit`/`KummerWitness.2` (§A).**
KT: if a spin `M` Pin⁺-bounds `W⁵`, then `32 ∣ σ(M)`. Anatomy: `V ⊂ W` dual to `w₁(W)` is SPIN;
`∂E(V)` (boundary of its tubular nbhd) is the orientation double cover; `σ(M) = σ(∂E) = 2·σ(V)`; the
in-tree Rokhlin `16 ∣ σ(V)` (`SmoothSpinManifold4.rokhlin`) finishes: `32 ∣ 2·σ(V)`.
* IN-TREE ARITHMETIC (BANKED, unconditional): `Div32BoundingDatum` (the dual spin submanifold `V` +
  the σ-doubling `σ(M) = 2·σ(V)`) ⟹ `32 ∣ σ(M)` (`Div32BoundingDatum.thirtytwo_dvd_sigM`), with the
  K3 lattice (`k3Form`, `σ = −16`) as a CONCRETE non-vacuity witness (`k3BoundingDatum`).
* CARRIER REDUCTION (CONDITIONAL): `DualSpinForwardDatum` packages the carrier-level forward
  direction — a σ-presentation, the K3 generator `g` (`σ = −16`), the forgetful `Φ` with
  `Φ[g] = k₀`, and the KT "only if" `hfwd : ∀ x, Φ x = 0 → 32 ∣ σ(x)`. Since `32 ∤ −16`
  (`not_thirtytwo_dvd_neg_sixteen`), `k₀ = Φ[g] = 0` would give `32 ∣ σ(g) = −16` — false. Hence
  `KTNonSplit prov` (`k₀ ≠ 0`, the ÷32-lower `σ(K3) = 16 ≢ 0 mod 32`). The datum EXCLUDES the split
  world (G8-3, where `k₀ = 0`) — that is precisely what `KTNonSplit` is for.

**Direction B — the "if" (`2·K3` Pin⁺-bounds) → `KummerWitness.1`/`SpinImageCyclic` (§B, §C).**
KT: `2·K3` Pin⁺-bounds, via the Enriques surface `E` (`π₁ = ℤ/2`, `w₂ ≠ 0`, `H²(E) = ℤ¹⁰ ⊕ ℤ/2`
with `w₂` the torsion image — the [Ha] facts); `y ∈ H¹(E;ℤ/2)` with `y² = w₂` (UCT); the line bundle
`L` (`w₁ = y`) has Pin⁻ total space, `∂(disc bundle) = K3`, so `K3` Pin⁻-bounds; the `Ω₃^{Pin⁺} ≅
ℤ/2` obstruction vanishes on `2·K3`.
* `EnriquesDatum` (§B): the leaf-packaged Enriques content — the [Ha] `σ(K3) = −16` fact + the empty-Σ
  (rank-0, spin) representative of `k₀` produced by the Pin⁺ bounding. ⟹ `KummerWitness.1`
  (`EmptySigmaRepresentable prov k₀`, `kummerWitness1_of_enriquesDatum`); the ÷32-UPPER `2·k₀ = 0`
  (`2·K3` bounds) is then FREE from the sector 2-torsion (`twoKummer_bounds_of_enriquesDatum`, via the
  SHARP `kernelRep_two_torsion_of_emptySigmaRep`, round-8 spec item 4).
* `KTSpinPresentationDatum` (§C): the SpinImageCyclic route, declared as round-9 spec item 3 **route
  (b) — geometric `Φ`**: the σ-presentation + the genuine geometric forgetful `Φ` (`hΦgeo`: every
  `Φ w` honestly-empty-Σ, `GeometricSpinRepresentable`) with `hΦrange`. It discharges `SpinImageCyclic`
  (`spinImageCyclic_of_ktSpinPresentationDatum`) AND CO-DISCHARGES the round-9 G8-5 overhang
  `SectorIsGeometric` (`sectorIsGeometric_of_ktSpinPresentationDatum`) from the SAME datum — the
  route-(b) co-obligation honored.

## Round-8/9 spec compliance
* Consumption unit = the TRIPLE (G8-1..G8-3): §D's `kt_equiv_zmod16_of_leaves` consumes all three
  leaves + `KernelReducesToSpin`; nothing here bounds a card / order from a proper subset.
* `SpinImageIsTwo` route (spec item 3 / G8-4): §C routes SIIT through the Lemma-5.3 cyclic
  classification (`spinImageIsTwo_of_cyclic_of_kummerRep`, SpinImageCyclic + `KummerWitness.1`), NOT a
  `∀ sector x, x = 0` collapse-smell.
* ÷32-upper consumers take `EmptySigmaRepresentable prov k₀` (the sharp hypothesis), not the full
  `KummerWitness` (spec item 4).
* Round-9: `KTSurgeryReduces` is consumed AS `KernelReducesToSpin` (§D takes it as a hypothesis, not
  re-derived); the `SpinImageCyclic` discharge declares route (b) + co-discharges `SectorIsGeometric`
  (item 3b); `hΦg` is never progress alone (the datum carries `hΦrange` + `hΦgeo`, the whole load).

Standing no-go compliance: the ÷32 content is honestly geometric (σ-doubling + Rokhlin, NOT a lattice
Arf — `nogo_lattice_arf_not_sigma8`); the 2-torsion of `k₀` is enhancement-tied on the rank-0 sector
(NOT universal `revStr`-triviality — `dataBordism_two_torsion_of_revStr_trivial`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTStepGate
import SKEFTHawking.PinPlusKTSurgeryTrace
import SKEFTHawking.SpinRokhlinInterface
import SKEFTHawking.SpinSigmaGenerator

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSectorGate
open SKEFTHawking.PinPlusKTStepGate

namespace SKEFTHawking.PinPlusKTLemma53Wave

variable {k : WithTop ℕ∞}

/-! ## §A. Direction A — the "only if": `32 ∣ σ` sharpness ⟹ `KTNonSplit`

The KT ÷32 forward direction. §A.1 banks the genuinely in-tree arithmetic (σ-doubling + Rokhlin),
with the K3 lattice as a concrete witness. §A.2 packages the carrier-level forward direction as a
leaf and derives `KTNonSplit`. -/

/-! ### §A.1. The in-tree ÷32 arithmetic core (BANKED, unconditional) -/

/-- **`32 ∤ −16`** — the ÷32-LOWER arithmetic fact (KT Lemma 5.3: `σ(K3) = ±16` is NOT divisible by
`32`, so K3 itself does not Pin⁺-bound). The single decidable arithmetic seed of `KTNonSplit`. -/
theorem not_thirtytwo_dvd_neg_sixteen : ¬ (32 : ℤ) ∣ (-16 : ℤ) := by decide

/-- **THE DUAL-SPIN-SUBMANIFOLD ÷32 DATUM** (Direction A, the in-tree arithmetic leaf). Packages the
KT "only if" σ-doubling step: `V` is the SPIN submanifold of `W⁵` dual to `w₁(W)` (as a
`SmoothSpinManifold4`, carrying its even-unimodular intersection form and the topological factor of
two), and `sigM` is the signature of the bounded `M` with the double-cover relation `σ(M) = 2·σ(V)`
(the boundary `∂E(V)` of `V`'s tubular neighbourhood is the orientation double cover). NO Rokhlin
field is carried — `16 ∣ σ(V)` is DERIVED in-tree from `V.rokhlin` (`SmoothSpinManifold4.rokhlin`).
Genuinely INHABITED (a `SmoothSpinManifold4` is a real structure and `sigM = 2·σ(V)` is satisfiable —
`k3BoundingDatum`). -/
structure Div32BoundingDatum where
  /-- the `w₁(W)`-dual SPIN submanifold `V ⊂ W`, with its even-unimodular intersection form. -/
  V : SmoothSpinManifold4
  /-- the signature of the bounded manifold `M`. -/
  sigM : ℤ
  /-- **the double-cover σ-doubling**: `σ(M) = σ(∂E(V)) = 2·σ(V)` (the orientation double cover). -/
  hdouble : sigM = 2 * V.sig

/-- **`32 ∣ σ(M)` from the datum** (the KT "only if" finish, in-tree): the Rokhlin `16 ∣ σ(V)`
(`SmoothSpinManifold4.rokhlin`, the E2 stack — Freedman–Kirby characteristic-surface Arf-vanishing)
composed with the σ-doubling `σ(M) = 2·σ(V)` gives `32 ∣ σ(M)`. Unconditional; the honest σ-doubling +
Rokhlin route, no leaf hypothesis. -/
theorem Div32BoundingDatum.thirtytwo_dvd_sigM (d : Div32BoundingDatum) :
    (32 : ℤ) ∣ d.sigM := by
  obtain ⟨c, hc⟩ := d.V.rokhlin
  exact ⟨c, by rw [d.hdouble, hc]; ring⟩

/-- **The K3 lattice as a `SmoothSpinManifold4`** — the concrete spin witness with `σ = −16`
(`k3Form`, the even-unimodular rank-22 K3 lattice `2·(−E₈) ⊕ 3·H`). Non-vacuity anchor: the ÷32
arithmetic is exhibited on the ACTUAL generator, not a toy. -/
noncomputable def k3Spin : SmoothSpinManifold4 where
  rank := 22
  form := k3Form
  even_unimod := k3Form_isEvenUnimodular
  topo := by rw [k3Form_latticeSig]; decide

@[simp] theorem k3Spin_sig : k3Spin.sig = -16 := k3Form_latticeSig

/-- **The concrete `2·K3` bounding datum** (non-vacuity of `Div32BoundingDatum`): `V = K3`
(`σ = −16`), `σ(M) = −32 = 2·σ(K3)`. Witnesses that the σ-doubling arithmetic is inhabited on the
real K3 lattice, and `thirtytwo_dvd_sigM` gives the honest `32 ∣ −32`. -/
noncomputable def k3BoundingDatum : Div32BoundingDatum where
  V := k3Spin
  sigM := -32
  hdouble := by rw [k3Spin_sig]; norm_num

/-- Non-vacuity check: the K3 bounding datum's `σ(M) = −32` is `32`-divisible via the general
`thirtytwo_dvd_sigM` — the σ-doubling + Rokhlin arithmetic on the genuine generator. -/
theorem k3BoundingDatum_thirtytwo_dvd : (32 : ℤ) ∣ k3BoundingDatum.sigM :=
  k3BoundingDatum.thirtytwo_dvd_sigM

/-! ### §A.2. The carrier-level forward direction ⟹ `KTNonSplit` (CONDITIONAL leaf) -/

section CarrierForward

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **THE CARRIER FORWARD DATUM** (Direction A, the carrier reduction leaf). Packages KT Lemma 5.3's
"only if" at the level of the CharPair carrier: a σ-presentation `R` of a spin carrier `ξ`
(`DataBordismGrp ξ = Ω₄^{Spin}`), the K3 generator `g` with `σ(g) = −16`, the forgetful map
`Φ : Ω₄^{Spin} → G` (the `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion) with `Φ[g] = k₀`, and the "only if"
implication `hfwd : ∀ x, Φ x = 0 → 32 ∣ σ(x)` — each instance of which is a `Div32BoundingDatum`
(§A.1): a `Φ x = 0` class bounds Pin⁺, its `w₁`-dual `V` doubles the signature, Rokhlin finishes.

**Vacuity / inhabitation** (round-10 seed): the genuine geometric `Φ` (the `Ω₄^{Spin} → Ω₄^{Pin⁺}`
inclusion) is UNBUILT in-tree, so this datum has zero in-tree inhabitants OFF the split world. In the
split world (`k₀ = 0`, kernel-trivial, G8-3) it IS inhabitable (`Φ = 0`, `hfwd` vacuous on `Φ x = 0`
only via the collapse), and there `ktNonSplit_of_dualSpinForwardDatum`'s conclusion `k₀ ≠ 0` FAILS —
i.e. no such datum exists in the split world (`hfwd[g]` would force `32 ∣ −16`). The datum EXCLUDES
exactly the split degenerate model, which is precisely `KTNonSplit`'s role in the triple. -/
structure DualSpinForwardDatum (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ξ : TangentialData X k' I') where
  /-- the σ-presentation of the spin carrier `ξ` (`DataBordismGrp ξ = Ω₄^{Spin}`). -/
  R : SpinSigmaPresentation ξ
  /-- the K3 generator. -/
  g : StrMfd ξ
  /-- `σ(K3) = −16` (the [Ha]/KT generator signature; ÷32-lower). -/
  hg : R.sig (DataBordismGrp.mk ξ g) = -16
  /-- the forgetful `Ω₄^{Spin} → Ω₄^{Pin⁺}` map to the CharPair carrier. -/
  Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov)
  /-- the K3 generator maps to the kernel representative `k₀ = 8 • [ℝP⁴]`. -/
  hΦg : Φ (DataBordismGrp.mk ξ g) = ktKernelRep prov
  /-- **KT Lemma 5.3 "only if"**: a Pin⁺-bounding spin class has `32 ∣ σ` (each instance a
      `Div32BoundingDatum`: `w₁`-dual `V`, σ-doubling, Rokhlin). -/
  hfwd : ∀ x, Φ x = 0 → (32 : ℤ) ∣ R.sig x

/-- **Direction A headline — `DualSpinForwardDatum ⟹ KTNonSplit`** (CONDITIONAL; discharges nothing
of the triple). If `k₀ = 0` then `Φ[g] = k₀ = 0`, so the "only if" gives `32 ∣ σ(g) = −16` — refuted
by `not_thirtytwo_dvd_neg_sixteen`. Hence `k₀ ≠ 0`: the ÷32-lower `σ(K3) = 16 ≢ 0 mod 32`, i.e. K3
does not Pin⁺-bound. This is `KummerWitness.2`, reduced to the (unbuilt) forgetful map + the KT "only
if" direction. -/
theorem ktNonSplit_of_dualSpinForwardDatum {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'} (d : DualSpinForwardDatum prov ξ) : KTNonSplit prov := by
  intro h0
  have hΦ0 : d.Φ (DataBordismGrp.mk ξ d.g) = 0 := by rw [d.hΦg]; exact h0
  have h32 := d.hfwd _ hΦ0
  rw [d.hg] at h32
  exact not_thirtytwo_dvd_neg_sixteen h32

end CarrierForward

/-! ## §B. Direction B — the "if": `2·K3` Pin⁺-bounds ⟹ `KummerWitness.1`

The Enriques construction, leaf-packaged. The load-bearing content is the empty-Σ (spin) representative
of `k₀`; the ÷32-upper `2·k₀ = 0` is then free from the sector 2-torsion. -/

/-- **THE ENRIQUES DATUM** (Direction B, the "if" leaf). Leaf-packages KT Lemma 5.3's Enriques
construction (do NOT build `E`): the [Ha] `σ(K3) = −16` fact, and the empty-Σ (rank-0, spin)
representative `p` of `k₀` that the Pin⁺ bounding produces (`K3 = ∂(disc bundle of L)` with `L` the
`w₁ = y`, `y² = w₂(E)` line bundle whose total space is Pin⁻; `2·K3` Pin⁺-bounds after the
`Ω₃^{Pin⁺} ≅ ℤ/2` obstruction vanishes on twice the class). The genuine spin carrier of `k₀` is the
open Kummer content.

**Vacuity / inhabitation** (round-10 seed): `hmk : [p] = k₀` with `hspin : p` rank-0 is the DEEP
`EmptySigmaRepresentable prov k₀` (`KummerWitness.1`) — a rank-0 representative of a possibly-nonzero
class. The empty structure represents `0` ONLY (`emptySigmaRepresentable_zero`), so this datum is
inhabited exactly when `k₀` is genuinely spin-representable: in the split/collapse world (`k₀ = 0`,
G8-2/G8-3) the empty structure inhabits it trivially; OFF that world it requires the unbuilt K3/Kummer
carrier. Hence `KummerWitness.1` alone is collapse-satisfiable and is consumed inside the triple. -/
structure EnriquesDatum (prov : CharPairWProviderPerOp (𝓡 4) k) where
  /-- the [Ha]/KT double-cover generator signature `σ(K3) = −16` (the ÷32-lower record). -/
  sigK3 : ℤ
  /-- `σ(K3) = −16`. -/
  hsigK3 : sigK3 = -16
  /-- the empty-Σ (rank-0, spin) representative of `k₀` produced by the Enriques Pin⁺ bounding. -/
  p : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- `p` is in the spin sector (rank-0 enhancement, empty characteristic surface). -/
  hspin : IsSpinSectorStr prov p
  /-- `[p] = k₀` — the spin representative realizes the kernel representative. -/
  hmk : T2DataBordismGrp.mk (pinPlusCharPairData prov) p = ktKernelRep prov

variable {prov : CharPairWProviderPerOp (𝓡 4) k}

/-- **The Enriques datum records the ÷32-lower** (the [Ha] sharpness): `σ(K3) = −16` is NOT divisible
by `32`. This is the arithmetic reason K3 itself does not Pin⁺-bound (the sharpness that makes `k₀`
nonzero); it ties Direction B's `σ(K3)` record to Direction A's `not_thirtytwo_dvd_neg_sixteen`. -/
theorem EnriquesDatum.k3_not_thirtytwo_dvd (d : EnriquesDatum prov) : ¬ (32 : ℤ) ∣ d.sigK3 := by
  rw [d.hsigK3]; exact not_thirtytwo_dvd_neg_sixteen

/-- **Direction B headline — `EnriquesDatum ⟹ KummerWitness.1`** (CONDITIONAL; discharges nothing of
the triple). The empty-Σ spin representative `p` of `k₀` IS the `EmptySigmaRepresentable prov k₀`
witness (`KummerWitness.1`). Reduces the ÷32-upper representability to the (unbuilt) Enriques carrier. -/
theorem kummerWitness1_of_enriquesDatum (d : EnriquesDatum prov) :
    EmptySigmaRepresentable prov (ktKernelRep prov) :=
  ⟨d.p, d.hspin, d.hmk⟩

/-- **`2·K3` Pin⁺-bounds — the ÷32-UPPER, FREE from the sector 2-torsion** (Direction B's KT "twice
the Kummer surface bounds a Pin⁺ manifold"). Given the Enriques spin representative of `k₀`, `k₀ + k₀
= 0` follows STRUCTURALLY (the sharp `kernelRep_two_torsion_of_emptySigmaRep`, taking only the
representability — round-8 spec item 4, NOT the full `KummerWitness`). The `σ(2·K3) = 32 ≡ 0 mod 32`
content, discharged from the sector alone. -/
theorem twoKummer_bounds_of_enriquesDatum (d : EnriquesDatum prov) :
    ktKernelRep prov + ktKernelRep prov = 0 :=
  kernelRep_two_torsion_of_emptySigmaRep prov (kummerWitness1_of_enriquesDatum d)

/-! ## §C. The SpinImageCyclic route — round-9 spec item 3 **route (b): geometric `Φ`** -/

section SpinImageRoute

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **THE SPIN-PRESENTATION DATUM** (Direction B, the `SpinImageCyclic` route, round-9 spec item 3
**route (b) — geometric `Φ`**). Packages the full `Ω₄^{Spin} ≅ ℤ` engine (`SpinSigmaPresentation` +
the two geometric freezes `hA`/`hB` + Rokhlin `hdvd` + the K3 generator `g`, `σ = −16`) together with
the GENUINE geometric forgetful map `Φ` (`hΦg : Φ[g] = k₀`; `hΦgeo`: every `Φ w` is honestly
empty-Σ — `GeometricSpinRepresentable`, the real `Ω₄^{Spin} → Ω₄^{Pin⁺}` inclusion; `hΦrange`: `Φ`
surjects onto the spin sector).

**Vacuity / inhabitation** (round-10 seed; the G9-4 self-locating fences apply): the genuine geometric
`Φ` is UNBUILT. A zero-`Φ` fake makes `hΦg` the split world (`0 = k₀`, refutes `KTNonSplit`) and
`hΦrange` exactly `SectorCollapsed` (G9-4) — the fenced worlds. A `k₀`-generated fake makes `hΦrange`
the conclusion itself; but `hΦgeo` (honestly-geometric range) is NOT satisfiable by such a fake for a
nontrivial sector. So the datum carries genuine content (the geometric inclusion), inhabited only off
the fenced worlds. -/
structure KTSpinPresentationDatum (prov : CharPairWProviderPerOp (𝓡 4) k)
    (ξ : TangentialData X k' I') where
  /-- the `Ω₄^{Spin} ≅ ℤ` σ-presentation. -/
  R : SpinSigmaPresentation ξ
  /-- freeze A — the `n·H` handle-trade realization (Benedetti 20.16/20.17). -/
  hA : R.RealizesSphereProducts
  /-- freeze B — `S²×S²` bounds. -/
  hB : R.SphereProductBounds
  /-- the K3 generator. -/
  g : StrMfd ξ
  /-- `σ(K3) = −16`. -/
  hg : R.sig (DataBordismGrp.mk ξ g) = -16
  /-- Rokhlin `16 ∣ σ` (the E2 stack). -/
  hdvd : ∀ x, (16 : ℤ) ∣ R.sig x
  /-- the genuine geometric forgetful `Ω₄^{Spin} → Ω₄^{Pin⁺}` map. -/
  Φ : DataBordismGrp ξ →+ T2DataBordismGrp (pinPlusCharPairData prov)
  /-- `Φ[K3] = k₀`. -/
  hΦg : Φ (DataBordismGrp.mk ξ g) = ktKernelRep prov
  /-- **route (b)**: `Φ`'s image is honestly geometric (every `Φ w` has an EMPTY-Σ representative). -/
  hΦgeo : ∀ w, GeometricSpinRepresentable prov (Φ w)
  /-- `Φ` surjects onto the spin sector. -/
  hΦrange : ∀ y, EmptySigmaRepresentable prov y → ∃ w, Φ w = y

/-- **`SpinImageCyclic` from the datum** (route (b)): the `Ω₄^{Spin} ≅ ℤ` engine writes every spin
class as `n • k₀` (`spinImageCyclic_of_presentation`). CONDITIONAL; discharges nothing of the triple
(the datum's geometric `Φ` is unbuilt). Per G9-3 this is the ≤-cyclic face of `SpinImageIsTwo`, not
independent progress. -/
theorem spinImageCyclic_of_ktSpinPresentationDatum {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'} (d : KTSpinPresentationDatum prov ξ) : SpinImageCyclic prov :=
  spinImageCyclic_of_presentation prov d.R d.hA d.hB d.g d.hg d.hdvd d.Φ d.hΦg d.hΦrange

/-- **The route-(b) co-obligation, DISCHARGED from the same datum** (round-9 spec item 3b): a
geometric `Φ` covering the broad sector (`hΦgeo` + `hΦrange`) FORCES the G8-5 characteristic-sphere
overhang `SectorIsGeometric` (`sectorIsGeometric_of_phiRange_geometric`). So this wave's geometric-`Φ`
route to `hΦrange` does NOT dodge the sphere-overhang reduction — it co-discharges it, honestly. -/
theorem sectorIsGeometric_of_ktSpinPresentationDatum {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'} (d : KTSpinPresentationDatum prov ξ) : SectorIsGeometric prov :=
  sectorIsGeometric_of_phiRange_geometric prov d.Φ d.hΦgeo d.hΦrange

/-- **`SpinImageIsTwo` via Lemma 5.3** (round-8 spec item 3 / G8-4 honest route): the SpinImageCyclic
route (§C datum) plus `KummerWitness.1` (the Enriques representability, §B) collapse `⟨k₀⟩` to `{0,
k₀}` through the 2-torsion (`spinImageIsTwo_of_cyclic_of_kummerRep`) — the Lemma-5.3 cyclic
classification, NOT a `∀ sector x, x = 0` collapse-smell. CONDITIONAL on both leaves. -/
theorem spinImageIsTwo_of_datums {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'} (dC : KTSpinPresentationDatum prov ξ) (dE : EnriquesDatum prov) :
    SpinImageIsTwo prov :=
  spinImageIsTwo_of_cyclic_of_kummerRep prov
    (spinImageCyclic_of_ktSpinPresentationDatum dC)
    (kummerWitness1_of_enriquesDatum dE)

end SpinImageRoute

/-! ## §D. The assembly — `G ≃+ ZMod 16` from the three leaves + `KernelReducesToSpin`

The coherence headline: all three sector directions, leaf-packaged, plus the KT §5 kernel-null
surgery (`KernelReducesToSpin`, = `KTSurgeryReduces`, the `AmbientSurgeryDatum` supply of
`PinPlusKTSurgeryTrace`), assemble the ℤ/16. Consumed AS the round-8 TRIPLE; discharges nothing (every
leaf + `KernelReducesToSpin` is open). -/

section Assembly

variable {X : Type*} [TopologicalSpace X] {k' : WithTop ℕ∞}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **`KummerWitness` from Directions A + B** — the ÷32 lower+upper localized to two leaves. The
Enriques representability (`KummerWitness.1`, §B) with the ÷32-lower non-split bit (`KTNonSplit`, §A)
IS `KummerWitness` (`= EmptySigmaRepresentable prov k₀ ∧ KTNonSplit prov`). CONDITIONAL on both
leaves; discharges nothing. -/
theorem kummerWitness_of_datums {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'} (dE : EnriquesDatum prov) (dA : DualSpinForwardDatum prov ξ) :
    KummerWitness prov :=
  ⟨kummerWitness1_of_enriquesDatum dE, ktNonSplit_of_dualSpinForwardDatum dA⟩

/-- **THE WAVE ASSEMBLY — `G ≃+ ZMod 16` from the three leaf directions + `KernelReducesToSpin`**
(CONDITIONAL; discharges NOTHING of the triple — every hypothesis is open). Composes:
* `KernelReducesToSpin` (the KT §5 kernel-null surgery, `KTSurgeryReduces` — `AmbientSurgeryDatum`
  supply, `PinPlusKTSurgeryTrace`) — taken as a hypothesis, consumed AS `KernelReducesToSpin`
  (round-9 spec item 1);
* `SpinImageIsTwo` — from `{KTSpinPresentationDatum, EnriquesDatum}` via the Lemma-5.3 cyclic route
  (§C `spinImageIsTwo_of_datums`);
* `KTNonSplit` — from `DualSpinForwardDatum` (§A `ktNonSplit_of_dualSpinForwardDatum`).
These are EXACTLY the triple `{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}` — the minimal honest
consumption unit (G8-1..G8-3) — fed to the sector assembly `kt_equiv_zmod16_of_sector`. The whole KT
Lemma 5.3 completeness content is thus reduced to the three named leaf-data structures + the surgery
supply, with nothing discharged. -/
theorem kt_equiv_zmod16_of_leaves {prov : CharPairWProviderPerOp (𝓡 4) k}
    {ξ : TangentialData X k' I'}
    (hKRS : KernelReducesToSpin prov)
    (dC : KTSpinPresentationDatum prov ξ) (dE : EnriquesDatum prov)
    (dA : DualSpinForwardDatum prov ξ) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_sector prov hKRS
    (spinImageIsTwo_of_datums dC dE)
    (ktNonSplit_of_dualSpinForwardDatum dA)

end Assembly

end SKEFTHawking.PinPlusKTLemma53Wave
