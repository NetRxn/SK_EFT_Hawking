/-
# Phase 5q.H (W-A arm 4, THE FLIP) — the live characteristic-pair CARRIER on the REALIZED `Bor`

`pinPlusCharPairData` (the faithful Pin⁺ instance, now on the membrane-REALIZED `Bor`) + its
computed mod-8 grade `charPairBrown` + the ℝP⁴ non-vacuity witness `rp4CharPairBundled`, plus the
type-former `charPairBundledMfd`.

**THE FLIP (2026-07-15):** `Bor` is `CharPairBorRealized` — every bordism witness carries a
GENUINE derived-basis geometric realization (`GeoRealizationTied`: real membrane topology `Q`,
per-object T2/Compact/closed-embedding certificates, bases DERIVED from the carried `basis`
through the UCT bridge), the substrate PINS (`pin14`/`pin23` — honest Steenrod, F3 fix), and the
Taylor-leg kernel `L = ker (transportedBInc real.toData)` COMPUTED from that topology (F1/F2 fix).
The provider is `CharPairWProviderPinned`. All eight op witnesses are the realized constructions
(`cyl/rev/neg/symmBorRealized` + `unit/comm/assocBorRealized` + `addBorRealized`). The synthetic-
`bInc` exploit family (`doubleKillerBorTied`, the §4.5 GateWD replay) is NOT constructible against
this `Bor` — the round-3/4.5 instance-level refutations are CONVERTED (see `PinPlusKTVacuityGateWD`
§5): the W-D binders `{KTKernelCard, KTNonSplit}` are now GENUINELY OPEN, not refuted.

Declarations live in `namespace SKEFTHawking.PinPlusCharPairData` (unchanged), so every downstream
fully-qualified name (`PinPlusCharPairData.pinPlusCharPairData`, `.charPairBrown`,
`.rp4CharPairBundled`, `.charPairBundledMfd`) keeps resolving.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairBorRealized
import SKEFTHawking.PinPlusCharPairBorRealizedOps
import SKEFTHawking.PinPlusCharPairAddRealization
import SKEFTHawking.PinPlusCharPairBorTethered
import SKEFTHawking.PinPlusWAdmPinnedCore

namespace SKEFTHawking.PinPlusCharPairData

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.T2TangentialBordism
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorRealized
open SKEFTHawking.PinPlusCharPairBorRealizedOps
open SKEFTHawking.PinPlusCharPairAddRealization
open SKEFTHawking.PinPlusCharPairBorTethered

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §11. The type-former `charPairBundledMfd` and the faithful `T2TangentialData` instance
`pinPlusCharPairData` (SPLIT OUT of `PinPlusCharPairData` §10–§11; the bundled op witnesses it
consumes — `charPairBundledEmpty`/`SumStr`/`RevStr` — stay there and are imported transitively). -/

/-- **The unblock, as a type.** `charPairBundledMfd` is a legitimate `Mfd`-family for a carrier at
universe 0 landing in `Type 1` — precisely the `SingularManifold.{0} X k I → Type 1` shape the generalized
`TangentialData.{0, 1}.Mfd` field now admits (`v = 1 ≠ u = 0`). Under the pre-generalization
`Mfd : SingularManifold.{u} → Type u` this very definition was a universe error (`Type 1 ≠ Type 0`); it now
type-checks, which IS the resolution of the §5 friction. -/
def charPairBundledMfd : SingularManifold.{0} PUnit k I → Type 1 :=
  fun s => CharPairStrBundled (k := k) I s

/-- **THE FAITHFUL Pin⁺ INSTANCE ON THE TETHERED `Bor`** (THE RE-FLIP, 2026-07-15, post
gate-round-6) — the certified characteristic-pair carrier as a `T2TangentialData.{0,1}`. `Bor`
is the **W-TETHERED** `CharPairBorRealizedTethered`: everything the realized `Bor` had (genuine
`GeoRealizationTied` with derived bases — F2; substrate pins — F3; computed Taylor-leg kernel —
F1) PLUS the round-6 tether: `ιW : C(Q, b.W)` a closed embedding with the pointwise glue tying
`real.ι`, the clopen identifications `homσ/homτ`, the ends' `emb`, and `b.e` — so the membrane
lives INSIDE this bordism's carrier specifically (fork `untethered-membrane-factors-relation`:
witnesses no longer transport across bordisms; the relation no longer factors ends-only) — plus
the `chartQ` membrane-model discipline. Parameterized by the PER-OP provider
`CharPairWProviderPerOp` (exactly the op-bordism family — the ∀-all-bordisms form was flagged
likely-uninhabitable, gate F6; the Track-2 `CylinderWAdmPinned` engine is its inhabitation
seam). The group `T2DataBordismGrp (pinPlusCharPairData prov)` is an `AddCommGroup` by the §2
replay. The W-D binders remain GENUINELY OPEN pending the round-7 gate. -/
noncomputable def pinPlusCharPairData (prov : CharPairWProviderPerOp I k) :
    T2TangentialData.{0, 1} PUnit k I where
  Mfd := charPairBundledMfd (k := k) (I := I)
  Bor := fun b σ τ => CharPairBorRealizedTethered b σ τ
  emptyStr := charPairBundledEmpty
  sumStr := fun σ τ => charPairBundledSumStr σ τ
  cylBor := fun σ => cylBorTethered prov σ
  addBor := fun β₁ β₂ => addBorTethered prov β₁ β₂
  symmBor := fun β => symmBorTethered β
  commBor := fun σ τ => commBorTethered prov σ τ
  assocBor := fun σ τ ρ => assocBorTethered prov σ τ ρ
  unitBor := fun σ => unitBorTethered prov σ
  revStr := fun σ => charPairBundledRevStr σ
  revBor := fun β => revBorTethered β
  negBor := fun σ => negBorTethered prov σ
  t2Str := fun m => m.toCharPairStr.t2

/-- **The certified characteristic-pair bordism GROUP fires as an `AddCommGroup`** — the whole point of
the faithful carrier: a genuine (T2-refined, Hausdorff) structured bordism group on the frozen instance,
its group law inherited from `T2TangentialBordism`'s §2 replay. -/
noncomputable example (prov : CharPairWProviderPerOp I k) :
    AddCommGroup (T2DataBordismGrp (pinPlusCharPairData prov)) := inferInstance

/-! ## §12. The computed mod-8 grade `charPairBrown` (W-C's abk8 opening) -/

/-- **THE COMPUTED mod-8 GRADE** `charPairBrown : Ω^{char-pair} →+ ZMod 8` — `abk8 := Brown ∘ q`,
computed from the carried enhancement's Brown/Gauss-sum invariant. Well-defined along the REALIZED
`Bor` because `CharPairBorRealized` FORCES `brown σ.q = brown τ.q` (the anti-collapse engine
`brown_eq_of_taylorLeg_lagrangian` via `CharPairBorRealized.brown_eq` — the realized membrane's
computed kernel is Taylor-vanishing and jointly Lagrangian), so no reading-(ii) torsor collapse
can disturb it. Additive via `sumStr = orthSum`-reindex (`reindex_brown` + `brown_orthSum`). This is
W-C's abk8 door opened directly on the honest faithful carrier. -/
noncomputable def charPairBrown (prov : CharPairWProviderPerOp I k) :
    T2DataBordismGrp (pinPlusCharPairData prov) →+ ZMod 8 where
  toFun := Quot.lift (fun p => p.2.q.brown)
    (fun _p _q h => by
      obtain ⟨_, _, ⟨str⟩⟩ := h
      exact CharPairBorRealized.brown_eq str.toRealized)
  map_zero' := by show (stdQuadratic 0).brown = 0; rw [brown_stdQuadratic, Nat.cast_zero]
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    show ((Z4Quadratic.orthSum p.2.q q.2.q).reindex finSumFinEquiv).brown
        = p.2.q.brown + q.2.q.brown
    rw [reindex_brown, brown_orthSum]

/-! ## §13. STRETCH — the ℝP⁴ characteristic-pair witness (non-vacuity, the odd generator) -/

open SKEFTHawking.RP2Manifold SKEFTHawking.RP4Manifold SKEFTHawking.RP4Unconditional
  SKEFTHawking.RP2EquatorialInclusion
  SKEFTHawking.RP4PointSet SKEFTHawking.RP2PointSet SKEFTHawking.RP4Witness
  SKEFTHawking.RP2IntersectionForm SKEFTHawking.SingularSurfaceIntersectionForm in
/-- **The ℝP⁴ characteristic-pair bundle** (the headline witness) — the bundled char-pair structure on
`ℝP⁴` (`rp4SM = rp4SM_k 0`) with characteristic surface `ℝP²` (`rp2SM_k 0`), the retained `w₂ = 0`
certificate `rp4_hcert`, and the **rank-1 odd enhancement** `stdQuadratic 1` (`q(gen) = 1 ∈ ZMod 4` —
the odd order-16 generator, `rp2_generator_value_not_two_torsion`; geometrically the `rp2H1EquivFun`
basis of `H₁(ℝP²;ℤ/2) ≅ ℤ/2`). The equatorial inclusion `embRP2 : ℝP² → ℝP⁴` (`continuous_embRP2`
shipped) supplies `emb`; its SMOOTHNESS (`ContMDiff (𝓡 2) (𝓡 4) 0`) and INJECTIVITY are taken as
HYPOTHESES here (`contMDiff_embRP2`/`embRP2_injective`, being proven in parallel on wt2/main — not yet
in this slot) — a hypothesis-parameterized def, NOT axioms. grade16-free; no completeness Prop is
stated (that is W-D/W-E). -/
noncomputable def rp4CharPairBundledK (k : WithTop ℕ∞)
    (embSmooth : ContMDiff (𝓡 2) (𝓡 4) k embRP2) (embInj : Function.Injective embRP2) :
    CharPairStrBundled (𝓡 4) (rp4SM_k k) where
  toCharPairStr :=
    { t2 := inferInstanceAs (T2Space RP4)
      cert := rp4_hcert_k
      n := 1
      q := stdQuadratic 1 }
  surf := rp2SM_k k
  surfT2 := inferInstanceAs (T2Space RP2)
  emb := embRP2
  embSmooth := embSmooth
  embInj := embInj
  surfClass := surfaceFundamentalClass (M := RP2)
  basis := rp2H1EquivFun
  hpolar := fun a b => by
    -- RHS is the ℝP² intersection form (definitional: `intersectionForm = μ ∘ cupH`, `μ = ⟨·,[ℝP²]⟩`)
    show (stdQuadratic 1).B (rp2H1EquivFun a) (rp2H1EquivFun b)
        = kroneckerH 2 (cupH a b) (surfaceFundamentalClass (M := RP2))
    rw [show kroneckerH 2 (cupH a b) (surfaceFundamentalClass (M := RP2))
          = intersectionForm (M := RP2) a b from rfl]
    -- both sides are ℤ/2-bilinear on the rank-1 `H¹(ℝP²)`; agree on the generator `xRP2`
    obtain ⟨c, rfl⟩ := h1_eq_smul_xRP2 a
    obtain ⟨d, rfl⟩ := h1_eq_smul_xRP2 b
    have hxeq : rp2H1EquivFun xRP2 = (fun _ => 1) := by
      funext i; fin_cases i
      rw [rp2H1EquivFun, ← rp2H1Basis_apply 0, Module.Basis.equivFun_self]; rfl
    have hLHS : ∀ c d : ZMod 2, (stdQuadratic 1).B (c • (fun _ => 1 : Fin 1 → ZMod 2))
        (d • (fun _ => 1 : Fin 1 → ZMod 2)) = c • d • (1 : ZMod 2) := by decide
    rw [map_smul, map_smul, hxeq, hLHS]
    simp only [map_smul, LinearMap.smul_apply, intersectionForm_xRP2_self]
    rw [smul_comm]
  hchar := fun a =>
    -- `⟨a, emb₊[ℝP²]⟩ = μ(a ⌣ x²)` (the discharged-crux pairing identity) then the cup-square
    -- bridge `μ(a ⌣ a) = μ(a ⌣ x²)` (rank-1 `H²`, `c² = c`).
    (SKEFTHawking.RP4CharSurfaceSmithNat.hchar_pairing a).trans
      (SKEFTHawking.RP4WuAssembly.mu_cupH24_self_eq_cupH24_xpow2 a).symm

open SKEFTHawking.RP2Manifold SKEFTHawking.RP4Unconditional SKEFTHawking.RP2EquatorialInclusion
  SKEFTHawking.RP4PointSet SKEFTHawking.RP2PointSet SKEFTHawking.RP4Witness in
/-- **The `C⁰` specialisation, unchanged** — the historical `k = 0` name, now a thin instantiation of
the regularity-generic `rp4CharPairBundledK`. Every pre-existing consumer keeps its exact type
(`rp4SM = rp4SM_k 0` by `rfl`); the generalisation is strictly conservative. -/
noncomputable def rp4CharPairBundled
    (embSmooth : ContMDiff (𝓡 2) (𝓡 4) 0 embRP2) (embInj : Function.Injective embRP2) :
    CharPairStrBundled (𝓡 4) rp4SM :=
  rp4CharPairBundledK 0 embSmooth embInj

end SKEFTHawking.PinPlusCharPairData
