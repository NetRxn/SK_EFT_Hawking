/-
# Phase 5q.H (W-A arm 4, THE SPLIT) — the live characteristic-pair CARRIER

`pinPlusCharPairData` (the faithful, membrane-TIED Pin⁺ instance) + its computed mod-8 grade
`charPairBrown` + the ℝP⁴ non-vacuity witness `rp4CharPairBundled`, plus the type-former
`charPairBundledMfd`.

These §11–§13 "live carrier" declarations were SPLIT OUT of `PinPlusCharPairData` — a PURE
REFACTOR, no semantic change — to sever the arm-4 import cycle. The KT-chain consumers
(`RP4CharPairWitness` / `PinPlusKTExtension` / `PinPlusKTVacuityGateWD`) need the instance, while the
membrane-realized chain that COMPUTES the tied `Bor` (`…BorRealized` / `…CylRealization` /
`…RealizationTied` / `…MembraneGeoRealization`) sits upstream of them. Placing the carrier in its
own module downstream of the realized chain (imports `PinPlusCharPairBorRealized` +
`PinPlusWAdmPinnedCore`) and re-pointing the consumers here breaks the cycle. Everything else stays in
`PinPlusCharPairData`; the frozen algebraic core, the bundled op witnesses (`CharPairStrBundled`,
`charPairBundledEmpty`/`SumStr`/`RevStr`), and the tied `Bor` (`CharPairBorTied`, §9.6) are consumed
transitively. `Bor` is UNCHANGED: `ULift (CharPairBorTied …)`.

Declarations live in `namespace SKEFTHawking.PinPlusCharPairData` (unchanged), so every downstream
fully-qualified name (`PinPlusCharPairData.pinPlusCharPairData`, `.charPairBrown`,
`.rp4CharPairBundled`, `.charPairBundledMfd`) keeps resolving.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairBorRealized
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

/-- **THE FAITHFUL Pin⁺ INSTANCE, MEMBRANE-TIED** (the arm-4 re-gate migration) — the certified
characteristic-pair carrier as a `T2TangentialData.{0,1}` (bundled `Type 1` `Mfd`, carrier at
universe 0). `Bor` is the **membrane-TIED** `CharPairBorTied` on the underlying algebraic cores
(`ULift`ed to `Type 1`): the Taylor-leg kernel `L` is COMPUTED from each op's membrane datum,
never carried free (no-go `free-membrane-kernel-kills-nonsplit`). The twelve op witnesses are the
§6/§9.6/§11 constructions. Parameterized by the W-admissibility provider `prov` (a hypothesis —
no axiom). The group `T2DataBordismGrp (pinPlusCharPairData prov)` is an `AddCommGroup` by the §2
replay. ⚠ The `bInc` geometric-realization residual (§9.6 header) is self-attacked in
`PinPlusKTVacuityGateWD`; the W-D binders remain FROZEN until the realization strengthening. -/
noncomputable def pinPlusCharPairData (prov : CharPairWProvider I k) :
    T2TangentialData.{0, 1} PUnit k I where
  Mfd := charPairBundledMfd (k := k) (I := I)
  Bor := fun b σ τ => ULift.{1} (CharPairBorTied b σ.toCharPairStr τ.toCharPairStr)
  emptyStr := charPairBundledEmpty
  sumStr := fun σ τ => charPairBundledSumStr σ τ
  cylBor := fun σ => ⟨charPairCylBorTied prov σ.toCharPairStr⟩
  addBor := fun β₁ β₂ => ⟨charPairAddBorTied prov β₁.down β₂.down⟩
  symmBor := fun β => ⟨charPairSymmBorTied β.down⟩
  commBor := fun σ τ => ⟨charPairCommBorTied prov σ.toCharPairStr τ.toCharPairStr⟩
  assocBor := fun σ τ ρ =>
    ⟨charPairAssocBorTied prov σ.toCharPairStr τ.toCharPairStr ρ.toCharPairStr⟩
  unitBor := fun σ => ⟨charPairUnitBorTied prov σ.toCharPairStr⟩
  revStr := fun σ => charPairBundledRevStr σ
  revBor := fun β => ⟨charPairRevBorTied β.down⟩
  negBor := fun σ => ⟨charPairNegBorTied prov σ.toCharPairStr⟩
  t2Str := fun m => m.toCharPairStr.t2

/-- **The certified characteristic-pair bordism GROUP fires as an `AddCommGroup`** — the whole point of
the faithful carrier: a genuine (T2-refined, Hausdorff) structured bordism group on the frozen instance,
its group law inherited from `T2TangentialBordism`'s §2 replay. -/
noncomputable example (prov : CharPairWProvider I k) :
    AddCommGroup (T2DataBordismGrp (pinPlusCharPairData prov)) := inferInstance

/-! ## §12. The computed mod-8 grade `charPairBrown` (W-C's abk8 opening) -/

/-- **THE COMPUTED mod-8 GRADE** `charPairBrown : Ω^{char-pair} →+ ZMod 8` — `abk8 := Brown ∘ q`,
computed from the carried enhancement's Brown/Gauss-sum invariant. Well-defined along the TIED `Bor`
because `CharPairBorTied` FORCES `brown σ.q = brown τ.q` (the anti-collapse engine
`brown_eq_of_taylorLeg_lagrangian` via `CharPairBorTied.brown_eq`), so no reading-(ii) torsor collapse
can disturb it. Additive via `sumStr = orthSum`-reindex (`reindex_brown` + `brown_orthSum`). This is
W-C's abk8 door opened directly on the honest faithful carrier. -/
noncomputable def charPairBrown (prov : CharPairWProvider I k) :
    T2DataBordismGrp (pinPlusCharPairData prov) →+ ZMod 8 where
  toFun := Quot.lift (fun p => p.2.q.brown)
    (fun _p _q h => by
      obtain ⟨_, _, ⟨str⟩⟩ := h
      exact CharPairBorTied.brown_eq str.down)
  map_zero' := by show (stdQuadratic 0).brown = 0; rw [brown_stdQuadratic, Nat.cast_zero]
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    show ((Z4Quadratic.orthSum p.2.q q.2.q).reindex finSumFinEquiv).brown
        = p.2.q.brown + q.2.q.brown
    rw [reindex_brown, brown_orthSum]

/-! ## §13. STRETCH — the ℝP⁴ characteristic-pair witness (non-vacuity, the odd generator) -/

open SKEFTHawking.RP2Manifold SKEFTHawking.RP4Unconditional SKEFTHawking.RP2EquatorialInclusion
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
noncomputable def rp4CharPairBundled
    (embSmooth : ContMDiff (𝓡 2) (𝓡 4) 0 embRP2) (embInj : Function.Injective embRP2) :
    CharPairStrBundled (𝓡 4) rp4SM where
  toCharPairStr :=
    { t2 := inferInstanceAs (T2Space RP4)
      cert := rp4_hcert
      n := 1
      q := stdQuadratic 1 }
  surf := rp2SM_k 0
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

end SKEFTHawking.PinPlusCharPairData
