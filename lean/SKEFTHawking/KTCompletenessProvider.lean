/-
# Phase 5q.H W-D — THE KT §5 COMPLETENESS PROVIDER OPENER (the generic `AmbientSurgeryDatum` supply `H`)

⛔ HARD SCOPE: this module OPENS (does not close) the W-D completeness summit. It ships the
UNCONDITIONAL **algebraic head** of the generic `AmbientSurgeryDatum` construction and banks the
decomposition dossier for the remaining GEOMETRIC bricks. It discharges nothing of the round-8 triple
`{KernelReducesToSpin, SpinImageIsTwo, KTNonSplit}`; everything here composes into the SUPPLY of the
terminal hypothesis `H` consumed by `PinPlusKTSurgeryTrace.ktSurgeryReduces_of_ambientDatumSupply`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.

## The summit and its reduction (the lead's authority — `PinPlusKTSurgeryTrace.lean:189`)
The whole KT §5 completeness (`KernelReducesToSpin prov`, the "invariant = 0 ⟹ bounds" direction)
reduces — via the proven `kernelReducesToSpin_of_ambientDatumSupply` — to constructing, for EVERY
non-spin brown-0 representative `p`, the sharpest named geometric leaf:

  `H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,`
  `      charPairBrown prov (T2DataBordismGrp.mk _ p) = 0 → 0 < p.2.n → AmbientSurgeryDatum prov p`

`H` is EXACTLY what the summit consumes. So **completeness ⟺ a universal `AmbientSurgeryDatum`
supply**. `AmbientSurgeryDatum prov p` (`PinPlusKTSurgeryTrace.lean:116`) bundles seven fields; this
module makes the ALGEBRAIC three (`x`, `hx0`, `hxq`) unconditional and predicts the fourth (`hrank`),
leaving the GEOMETRIC three (`p'` as a full `StrMfd`, `b`, `hBor`) as the honest wall.

## THE DECOMPOSITION DOSSIER — the generic-`p` `AmbientSurgeryDatum` construction, brick by brick

Legend: 🟢 SHIPPED this wave · 🟡 form-level algebra banked, geometric lift open · 🔴 open geometric wall.

* **(i) Isotropic-class extraction — 🟢 SHIPPED (`exists_isotropicClass_of_charPairBrown_zero`).**
  For an ARBITRARY non-spin brown-0 `p`, produce a nonzero `x : Fin p.2.n → ZMod 2` with `p.2.q.q x = 0`
  — the datum's fields `x`/`hx0`/`hxq`, unconditionally. Reduces (via `charPairBrown_mk`) to the pure
  algebra `exists_isotropic_of_brown_zero`: a nondegenerate `Z4Quadratic ι` with `brown = 0` and
  `card ι > 0` has a nonzero isotropic vector. Machinery: the Gauss-sum real part — `brown = 0` forces
  `gaussSum4 Q.q = 2^(card/2)` (via `gaussSum4_eq_brownUnit` + `one_add_I_pow_two` + `I_pow_four` +
  the mod-4 phase collapse), whose real part is `≥ 2` when `card > 0`, while an anisotropic form
  (only `x = 0` isotropic) has real part `≤ 1` (each `zeta4(q x)` off `0` contributes `re ≤ 0`).
  No wall — this is the algebraic gateway, and it is closed.

* **(ii) The surgered representative `p'` — 🟡 form banked / 🔴 `StrMfd` lift open.** The KT surgery
  drops the enhancement rank by EXACTLY 2. FORM-level this is closed: `exists_finReduction` (banked in
  `PinPlusKTSurgeryTrace`) + `exists_finReduction_of_brown_zero` (this wave) give a reduced
  `Z4Quadratic (Fin m)` with `m + 2 = card` and SAME `brown`, UNCONDITIONALLY from `brown = 0` — the
  prediction the datum's `p'`/`hrank` must realize (`ambientDatum_matches_algebra`). 🔴 WALL: lifting
  the reduced FORM to a full `p' : StrMfd (pinPlusCharPairData prov).toTangentialData` — a carrier
  manifold `Σ'` + tangential data whose enhancement IS the reduced form. The capstone (#150–#178)
  built ONE such `p'`; the generic lift needs the provider `CharPairWProviderPerOp` to be CLOSED under
  isotropic surgery (supply a surgered carrier for every `p`, `x`). **This is the first hard geometric
  wall.** (`SmoothSurgeryChartDatum` / `SingularSurgeryManifold` / `HandleD5` / `ChartsConcrete` are
  the capstone's concrete instance; genericity needs them parameterized by `x`'s tubular data.)

* **(iii) The surgery-trace bordism `b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1` — 🔴 open.** The
  trace `W = M × I` with the membrane `Σ × [0,½] ∪ 2-handle ∪ Σ' × [½,1]`. Machinery to reuse:
  `PinPlusKTSurgeryTraceConsumers.ambientTraceBordism` / `surgeryTraceBordism` (build a `Bordism` from
  a `SmoothSurgeryChartDatum D`, singular ends, the boundary embedding `e`, its `ContMDiff`/injective/
  range hypotheses). 🔴 WALL: the `SmoothSurgeryChartDatum` and the handle-attachment carrier for a
  GENERIC `p`, `x` — i.e. the embedded surgery disk / tubular neighborhood of the circle representing
  `x` (KT §5's actual geometric input, "embedded-surgery-disk existence").

* **(iv) The weld/membrane tie `GeoRealizationTied` — 🔴 open.** The membrane `Q` charted over
  `MembraneModel` (dim 3), closed-embedded in `W`, with boundary-to-interior `H₁`-kernel `L` that is
  Taylor-leg-vanishing (`TaylorLegVanishes`) and jointly Lagrangian (`JointLagrangian`). Machinery:
  `GeoRealizationTied`, `GeoRealizationTied.toMembrane`, and the topology facts already banked at the
  `CharPairBorRealizedTethered` level (`surgeryTrace_membrane_charted`,
  `surgeryTrace_membrane_closedEmbeds`, `surgeryTrace_brown_eq_of_L`). 🔴 WALL: realizing the membrane
  geometrically (the trace surface as a charted 3-object) and its Lagrangian `H₁`-kernel.

* **(v) The genuine tether `hBor : Nonempty (CharPairBorRealizedTethered b p'.2 p.2)` — 🔴 open,
  assembly banked.** ASSEMBLY is closed: `PinPlusKTSurgeryTraceConsumers.ambientSurgeryDatum_of_weld`
  packs the whole datum from `x`/`hx0`/`hxq` (this wave, (i)) + `p'`/`hrank` ((ii)) + `b`/`hT2` ((iii))
  + `WAdmPinned b` + the tie `real` ((iv)) + the Taylor/Lagrangian kernel + the
  `HandleAttachment.Weld` + the glue equalities + the membrane `ChartedSpace` (via `borTetheredOfWeld`).
  🔴 WALL: the `WAdmPinned b`, the `HandleAttachment.Weld` + glue maps `glueσ`/`glueτ`, and `chartQ`
  for the generic surgery.

* **(vi) The `∀ p` assembly → `H` → completeness — 🟢 the tail is PROVEN.** Once (ii)–(v) supply a
  datum for each `p`, `H := fun p hb hn => ambientSurgeryDatum_of_weld …` and completeness is
  immediate: `kernelReducesToSpin_of_ambientDatumSupply H : KernelReducesToSpin prov` (already proven
  in `PinPlusKTSurgeryTrace`). No new wall beyond (ii)–(v).

## §4 — the algebraic head absorbed into the completeness supply (🟢 SHIPPED this wave)
Brick (i) is now propagated ALL THE WAY to the summit. The terminal completeness hypothesis is
sharpened from a full `AmbientSurgeryDatum` supply to the PURELY GEOMETRIC residual
`IsotropicSurgeryTrace prov p` (= `AmbientSurgeryDatum` minus its `x`/`hx0`/`hxq` head — the surgered
`p'`, the rank drop, the trace bordism `b`, the tether `hBor`, and nothing else). The two headlines
`kernelReducesToSpin_of_isotropicSurgeryTraceSupply` / `ktSurgeryReduces_of_isotropicSurgeryTraceSupply`
prove: a ∀-`p` supply of the geometric residual discharges `KernelReducesToSpin` / `KTSurgeryReduces`,
with the isotropic surgery class refilled internally (`IsotropicSurgeryTrace.toAmbientSurgeryDatum`,
via `exists_isotropicClass_of_charPairBrown_zero` + `ambientSurgeryDatum_of_traceWitness`). The
forgetful `AmbientSurgeryDatum.toIsotropicSurgeryTrace` witnesses that EXACTLY the algebraic three
fields were dropped. Net effect: the geometric program (bricks (ii)–(v)) no longer owes the isotropic
class — its whole remaining obligation is the geometric trace `⟨p', b, hBor⟩`.

## Foreseen hardest sub-wall
Brick (ii)'s `StrMfd` lift and brick (iii)'s `SmoothSurgeryChartDatum` for a GENERIC `p`, `x`: the
provider being closed under isotropic surgery, i.e. the embedded-surgery-disk / tubular-neighborhood
existence of KT §5 Thm 5.1. That is the genuine geometric content the completeness program must supply
next; everything algebraic upstream of it is now unconditional (bricks (i), (ii)-form, (vi)-tail).
-/
import Mathlib
import SKEFTHawking.PinPlusKTSurgeryTrace
import SKEFTHawking.PinPlusKTSurgeryTraceConsumers

open scoped Manifold
open Topology
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.RP4CharPairWitness
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSurgeryTrace

namespace SKEFTHawking.KTCompletenessProvider

/-! ## §1. The isotropic-class extraction — the unconditional algebraic gateway (brick (i)).

`brown = 0 ∧ rank > 0 ⟹ ∃ nonzero isotropic vector` for a nondegenerate `Z4Quadratic`. This is the
Brown/Arf-invariant-zero ⟹ isotropic-vector-exists fact, proved from the Gauss-sum real part:
`brown = 0` pins `gaussSum4 Q.q` to the positive real `2^(card/2)`, whose real part `≥ 2` is
incompatible with anisotropy (which caps the real part at `1`). -/

/-- Real part commutes with a finite `GaussianInt` sum. -/
lemma re_sum {ι : Type*} (s : Finset ι) (f : ι → GaussianInt) :
    (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.re_add, ih]

/-- Off `0`, the `ζ₄`-character has nonpositive real part (`re(i^k) ∈ {0,-1}` for `k ∈ {1,2,3}`). The
per-vector bound that caps an anisotropic Gauss sum's real part at the `x = 0` contribution. -/
lemma zeta4_re_nonpos (k : ZMod 4) (hk : k ≠ 0) : (zeta4 k).re ≤ 0 := by
  revert hk; revert k; decide

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-- **`brown = 0` pins the Gauss sum to the positive real `2^(card/2)`.** For a nondegenerate
`Z4Quadratic ι` with `brown Q = 0`, the dimension is even (`card = 2 m`) and `gaussSum4 Q.q = 2^m`
(the `ζ₈`-phase `brown` collapses to `0`). The seam feeding the isotropy count: `brown = 0` forces
`8 ∣ 2·brownUnit.val + card`, hence `card` even and `4 ∣ brownUnit.val + m`, killing the residual
`i`-phase (`I^4 = 1`). -/
lemma gaussSum4_eq_two_pow_of_brown_zero (hbrown : Q.brown = 0) :
    ∃ m : ℕ, Fintype.card ι = 2 * m ∧ gaussSum4 Q.q = (2 : GaussianInt) ^ m := by
  have hdvd : (8 : ℕ) ∣ (2 * Q.brownUnit.val + Fintype.card ι) := by
    have h := hbrown
    unfold Z4Quadratic.brown at h
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; convert h using 2
  have heven : 2 ∣ Fintype.card ι := by omega
  obtain ⟨m, hm⟩ := heven
  refine ⟨m, hm, ?_⟩
  have h4 : (4 : ℕ) ∣ (Q.brownUnit.val + m) := by omega
  have hgs := Q.gaussSum4_eq_brownUnit
  rw [hm] at hgs
  rw [hgs, pow_mul, one_add_I_pow_two, mul_pow]
  show I ^ Q.brownUnit.val * ((2 : GaussianInt) ^ m * I ^ m) = (2 : GaussianInt) ^ m
  rw [show I ^ Q.brownUnit.val * ((2 : GaussianInt) ^ m * I ^ m)
        = (2 : GaussianInt) ^ m * I ^ (Q.brownUnit.val + m) from by rw [pow_add]; ring]
  obtain ⟨k, hk⟩ := h4
  rw [hk, pow_mul, I_pow_four, one_pow, mul_one]

/-- **THE ALGEBRAIC GATEWAY (brick (i), form level).** A nondegenerate `Z4Quadratic ι` with Brown
invariant `0` and nonzero dimension has a nonzero isotropic vector (`q x = 0`, `x ≠ 0`). Proof: were
the form anisotropic (only `x = 0` isotropic), the Gauss sum's real part `∑ x (zeta4 (q x)).re` would
be `≤ 1` (the `x = 0` term contributes `1`, every other term `≤ 0` by `zeta4_re_nonpos`); but
`brown = 0` forces that real part to be `2^(card/2) ≥ 2` (`card > 0`) — contradiction. This is the
Brown-invariant-zero ⟹ isotropic-class-exists fact, the sharp input to `exists_finReduction`. -/
theorem exists_isotropic_of_brown_zero (hbrown : Q.brown = 0) (hpos : 0 < Fintype.card ι) :
    ∃ x : ι → ZMod 2, x ≠ 0 ∧ Q.q x = 0 := by
  by_contra hcon
  have hani : ∀ x : ι → ZMod 2, x ≠ 0 → Q.q x ≠ 0 := fun x hx hq => hcon ⟨x, hx, hq⟩
  obtain ⟨m, hm, hval⟩ := gaussSum4_eq_two_pow_of_brown_zero Q hbrown
  have hm1 : 1 ≤ m := by omega
  have hre : (gaussSum4 Q.q).re = (2 : ℤ) ^ m := by
    rw [hval, show (2 : GaussianInt) ^ m = ((2 ^ m : ℕ) : GaussianInt) by push_cast; ring,
      Zsqrtd.re_natCast]; push_cast; ring
  have hle : (gaussSum4 Q.q).re ≤ 1 := by
    unfold gaussSum4
    rw [re_sum]
    calc ∑ x, (zeta4 (Q.q x)).re
        ≤ ∑ _x : ι → ZMod 2, (if _x = (0 : ι → ZMod 2) then (1 : ℤ) else 0) := by
          apply Finset.sum_le_sum
          intro x _
          by_cases hx : x = 0
          · subst hx; rw [Q.q_zero, zeta4_zero]; simp
          · rw [if_neg hx]; exact zeta4_re_nonpos (Q.q x) (hani x hx)
      _ = 1 := by simp
  rw [hre] at hle
  have h2m : (2 : ℤ) ≤ 2 ^ m :=
    calc (2 : ℤ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm1
  omega

/-! ## §2. The composite gateway and the surgered-form prediction (brick (ii), form level).

Chaining the isotropic extraction into `exists_finReduction` closes the FORM leg of the datum's
`p'`/`hrank` UNCONDITIONALLY: from `brown = 0` alone (no isotropic vector supplied) the reduced
enhancement of rank `card − 2` with the SAME Brown invariant exists. -/

/-- **The unconditional form-level surgery reduction from `brown = 0` (brick (ii), form).** A
nondegenerate `Z4Quadratic (Fin n)` with `brown = 0` and `n > 0` surgers to a `Z4Quadratic (Fin m)`
with `m + 2 = n` (rank drops by exactly 2) and the SAME Brown invariant — with NO isotropic-vector
input (it is extracted internally via `exists_isotropic_of_brown_zero`). This is the algebraic
prediction the datum's `p'`/`hrank` must realize (`ambientDatum_matches_algebra`); its geometric lift
to a full `StrMfd` is brick (ii)'s open wall. -/
theorem exists_finReduction_of_brown_zero {n : ℕ} (Q : Z4Quadratic (Fin n))
    (hbrown : Q.brown = 0) (hn : 0 < n) :
    ∃ (m : ℕ) (R : Z4Quadratic (Fin m)), m + 2 = n ∧ R.brown = Q.brown := by
  obtain ⟨x, hx0, hxq⟩ :=
    exists_isotropic_of_brown_zero Q hbrown (by rw [Fintype.card_fin]; exact hn)
  exact exists_finReduction Q hxq hx0

/-! ## §3. The provider-level isotropic head — the datum's algebraic three fields, generically.

The `H`-hypothesis phrases the Brown condition as `charPairBrown prov (mk _ p) = 0`; `charPairBrown_mk`
identifies this with `p.2.q.brown = 0`, so the gateway of §1 delivers the isotropic surgery class
`x`/`hx0`/`hxq` — the datum's first three fields — for EVERY non-spin brown-0 representative `p`. -/

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}
variable {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **The generic ambient-surgery class (datum fields `x`/`hx0`/`hxq`, unconditional).** For every
non-spin (`0 < p.2.n`) representative `p` with vanishing computed grade
`charPairBrown prov (mk _ p) = 0`, there is a nonzero isotropic mod-2 `H₁`-class `x` with `p.2.q.q x = 0`
— the embedded surgery circle's homology class, the algebraic head of `AmbientSurgeryDatum prov p`
supplied unconditionally. What remains for the datum is the GEOMETRIC completion (bricks (ii)–(v)). -/
theorem exists_isotropicClass_of_charPairBrown_zero
    (hbrown : charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0)
    (hpos : 0 < p.2.n) :
    ∃ x : Fin p.2.n → ZMod 2, x ≠ 0 ∧ p.2.q.q x = 0 := by
  rw [charPairBrown_mk] at hbrown
  exact exists_isotropic_of_brown_zero p.2.q hbrown (by rw [Fintype.card_fin]; exact hpos)

/-- **The provider-level surgered-form prediction (brick (ii), form, `p`-level).** For every non-spin
brown-0 representative `p`, the reduced enhancement of rank `p.2.n − 2` with the SAME Brown invariant
exists — the algebraic target the datum's `p'` must realize. Composes
`exists_isotropicClass_of_charPairBrown_zero` with `exists_finReduction`. -/
theorem exists_reducedForm_of_charPairBrown_zero
    (hbrown : charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0)
    (hpos : 0 < p.2.n) :
    ∃ (m : ℕ) (R : Z4Quadratic (Fin m)), m + 2 = p.2.n ∧ R.brown = p.2.q.brown := by
  obtain ⟨x, hx0, hxq⟩ := exists_isotropicClass_of_charPairBrown_zero hbrown hpos
  exact exists_finReduction p.2.q hxq hx0

/-! ## §4. The geometric residual — the algebraic head absorbed into the completeness supply.

Brick (i) (§1–§3) makes the datum's algebraic head (`x`/`hx0`/`hxq`) UNCONDITIONAL for every non-spin
brown-0 `p`. This section propagates that all the way to the KT §5 completeness summit: the terminal
hypothesis shrinks from a full `AmbientSurgeryDatum` (which bundles the isotropic surgery class) to the
PURELY GEOMETRIC residual `IsotropicSurgeryTrace` — the surgered representative `p'`, the exact rank
drop, the surgery-trace bordism `b`, and the genuine Pin⁺ tether `hBor`. The isotropic surgery class is
no longer an obligation on the geometric program; it is supplied internally from
`exists_isotropicClass_of_charPairBrown_zero`. What remains is EXACTLY the geometric wall (dossier
bricks (ii)–(v)) — the surgered carrier `StrMfd`, the trace bordism, and the tether — with NO algebraic
residue. This is the honest sharp statement of the geometric leg (the algebra fully discharged); its
discharge is embedded-surgery-disk existence (KT §5 Thm 5.1), gated to the geometric construction wave. -/

/-- **The purely-geometric surgery residual at `p`** — `AmbientSurgeryDatum prov p` with its (now
unconditional, §3) algebraic head `x`/`hx0`/`hxq` dropped. Bundles the four geometric atoms the
completeness program must still supply for each non-spin brown-0 `p`: the surgered representative `p'`,
the exact rank-drop `hrank` (`n' + 2 = n`), the surgery-trace bordism `b` with Hausdorff carrier
(`hT2`), and the genuine Pin⁺ tether `hBor` realizing `[p'] = [p]`. This is the sharp terminal
hypothesis of the geometric leg — the honest wall (dossier bricks (ii)–(v)) with the algebraic leg
(brick (i)) absorbed. -/
structure IsotropicSurgeryTrace (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- the surgered representative (KT §5 genus/rank-drop-by-2 output). -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- the KT surgery drops the enhancement rank by EXACTLY 2. -/
  hrank : p'.2.n + 2 = p.2.n
  /-- the surgery-trace bordism `W` from `p'` to `p`. -/
  b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p'.1 p.1
  /-- its carrier is Hausdorff. -/
  hT2 : T2Space b.W
  /-- **the genuine tether**: the surgery-trace membrane realizes `[p'] = [p]` as a Pin⁺ bordism. -/
  hBor : Nonempty (CharPairBorRealizedTethered b p'.2 p.2)

/-- **The forgetful map** `AmbientSurgeryDatum → IsotropicSurgeryTrace`: dropping exactly the algebraic
head `x`/`hx0`/`hxq`. Witnesses that `IsotropicSurgeryTrace` is precisely `AmbientSurgeryDatum` minus
its (now free, §3) algebraic three fields — nothing geometric is lost or added. -/
def AmbientSurgeryDatum.toIsotropicSurgeryTrace (d : AmbientSurgeryDatum prov p) :
    IsotropicSurgeryTrace prov p :=
  ⟨d.p', d.hrank, d.b, d.hT2, d.hBor⟩

/-- **The geometric residual reconstitutes the full datum** for a non-spin brown-0 `p` (the algebraic
head refilled from brick (i), UNCONDITIONALLY). Given the brown-0 condition
(`charPairBrown prov (mk _ p) = 0`) and `0 < p.2.n`, the isotropic surgery class `x`/`hx0`/`hxq` is
extracted via `exists_isotropicClass_of_charPairBrown_zero` and welded to the geometric residual through
the banked `PinPlusKTSurgeryTraceConsumers.ambientSurgeryDatum_of_traceWitness`. So a geometric
`IsotropicSurgeryTrace` at a non-spin brown-0 `p` is EXACTLY as strong as a full `AmbientSurgeryDatum`
there — the algebraic gap is closed. -/
noncomputable def IsotropicSurgeryTrace.toAmbientSurgeryDatum
    (hbrown : charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0)
    (hpos : 0 < p.2.n) (G : IsotropicSurgeryTrace prov p) :
    AmbientSurgeryDatum prov p :=
  let hx := exists_isotropicClass_of_charPairBrown_zero (prov := prov) (p := p) hbrown hpos
  PinPlusKTSurgeryTraceConsumers.ambientSurgeryDatum_of_traceWitness
    hx.choose hx.choose_spec.1 hx.choose_spec.2 G.p' G.hrank G.b G.hT2 G.hBor

/-- **THE GEOMETRIC-LEG WAVE HEADLINE — `KernelReducesToSpin ⟸ (∀ non-spin brown-0 `p`,
`IsotropicSurgeryTrace`)** (CONDITIONAL; discharges nothing of the round-8 triple). A universal supply
of the PURELY GEOMETRIC surgery residual — one `IsotropicSurgeryTrace prov p` per non-spin brown-0
representative — discharges the deep KT §5 kernel-null binder `KernelReducesToSpin`. This is the
completeness summit with the ALGEBRAIC leg (brick (i)) fully absorbed: the isotropic surgery class is
supplied internally, so the residual `∀`-hypothesis is the sharpest purely-geometric statement — the
surgered carrier, the trace bordism, and the Pin⁺ tether (dossier bricks (ii)–(v)), and nothing
algebraic. Composes `IsotropicSurgeryTrace.toAmbientSurgeryDatum` with the banked
`kernelReducesToSpin_of_ambientDatumSupply`. -/
theorem kernelReducesToSpin_of_isotropicSurgeryTraceSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → IsotropicSurgeryTrace prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_ambientDatumSupply
    (fun p hbrown hpos => (H p hbrown hpos).toAmbientSurgeryDatum hbrown hpos)

/-- **The shallow-binder form — `KTSurgeryReduces ⟸ (geometric-residual supply)`** (CONDITIONAL;
discharges nothing of the triple). The same absorption at the `KTSurgeryReduces` level: a universal
geometric-residual supply discharges the single gated geometric surgery step, with the isotropic class
supplied internally (brick (i)). Composes `IsotropicSurgeryTrace.toAmbientSurgeryDatum` with
`ktSurgeryReduces_of_ambientDatumSupply`. -/
theorem ktSurgeryReduces_of_isotropicSurgeryTraceSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → IsotropicSurgeryTrace prov p) :
    KTSurgeryReduces prov :=
  ktSurgeryReduces_of_ambientDatumSupply
    (fun p hbrown hpos => (H p hbrown hpos).toAmbientSurgeryDatum hbrown hpos)

end SKEFTHawking.KTCompletenessProvider
