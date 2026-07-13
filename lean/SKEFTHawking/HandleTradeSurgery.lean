/-
# Phase 5q.H (N1a) — the Freeze-A handle-trade at its terminal in-substrate grain

Attacks the last net-new geometric ask of Freeze A: `HandleTradeSplit`
(`SphereProductRealizationAtoms.lean`), the **form-free** single-`S²×S²` handle-trade (Benedetti
arXiv:1907.10297 Prop 20.16 / Lemma 20.17; DR route
`Lit-Search/Phase-5qH/Omega4Spin_Z_formalization_route_20260706.md` sub-piece (2')). Its output —
`∃ p', rank p' = m ∧ [p] = [S²×S²] + [p']` — is irreducibly geometric: it demands *constructing a
new structured manifold* `p'` (surgery on the embedded square-`0` sphere) together with a
*bordism-class equation* in `DataBordismGrp ξ`. Neither is derivable from the algebraic hypotheses;
both are exactly the handle-attachment / surgery constructions on `StrMfd` that the substrate
(`TangentialDataBordism.lean`; Mathlib `Bordism.lean`, definitional scaffolding only — DR finding #4)
does NOT provide. So `HandleTradeSplit` is NOT closable kernel-pure here — it needs a genuine manifold
surgery foundation.

What IS closable, kernel-pure, is the **last algebraic mile**: this module pins the residual at its
terminal in-substrate grain by naming the exact raw geometric object the discharge plan produces and
stripping ALL bordism-group algebra off it.

Benedetti's Lemma 20.17 handle-trade produces, from a hyperbolic-pair split `form p ≅ H ⊕ N'`, a
**single structured cobordism** `W : p ↝ (S²×S²) ⊔ p'` (attaching-circle standardization in a chart:
the square-`0` class `a` is an embedded `S²` with trivial normal bundle `S²×D²`; its handle trace,
composed with the connected-sum tube, is one cobordism to the disjoint union). The bordism-group
equation `[p] = [S²×S²] + [p']` is that cobordism's *shadow* under the quotient: `⊔` of representatives
is `+` of classes (`DataBordismGrp.add_mk`) and a single cobordism collapses under `Quot.sound`
(`DataBordismGrp.mk_eq_of_bordant`).

So we introduce `HandleTradeCobordism` — the raw single-cobordism surgery primitive (residual `p'` of
rank `m`, plus ONE `IsDataBordant ξ p (S²×S² ⊔ p')`) — and prove `HandleTradeCobordism → HandleTradeSplit`
kernel-pure, hence `HandleTradeCobordism → HyperbolicPeel → RealizesSphereProducts`. This is the
*terminal* grain statable in the disjoint-union substrate: it names precisely the one geometric object
(Benedetti's handle trace) that a future manifold-surgery foundation must build, decoupled from every
bit of `DataBordismGrp` algebra. The residual — a manifold-surgery foundation producing that
cobordism — is flagged for the lead (shared with the generic surgery substrate).

Does NOT modify `SphereProductRealization.lean` / `SphereProductRealizationAtoms.lean` /
`SpinSigmaRoute.lean` / `SpinSigmaRouteDoor.lean` (imports the atoms module). Kernel-pure
(`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SphereProductRealizationAtoms

namespace SKEFTHawking.SpinSigmaRoute

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open Matrix

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {ξ : TangentialData X k I}

namespace SpinSigmaPresentation

/-- **The terminal surgery primitive — the raw handle-trace cobordism** (Benedetti arXiv:1907.10297
Prop 20.16 / Lemma 20.17). Identical *inputs* to `HandleTradeSplit` (a structured manifold `p` whose
form splits off one hyperbolic plane `H` over a hyperbolic-standard complement `N'`), but the output
is the *raw geometric object* the handle-trade literally produces, before any bordism-group algebra:
a residual structured manifold `p'` of the complement's rank (`rank p' = m`) together with a
**single structured cobordism** `IsDataBordant ξ p ((S²×S²) ⊔ p')` — the trace of the handle
attachment (attaching-circle standardization in a chart), composed with the connected-sum tube, from
`p` to the disjoint union `S²×S² ⊔ p'`. No `Quot`-transitivity, no group `+`: exactly one cobordism.
This is the *terminal grain* statable in the disjoint-union substrate — the precise geometric object a
manifold-surgery foundation must build. -/
def HandleTradeCobordism (R : SpinSigmaPresentation ξ) : Prop :=
  ∀ (p : StrMfd ξ) (m : ℕ) (E : Fin 2 ⊕ Fin m ≃ Fin (R.rank p))
    (N' : Matrix (Fin m) (Fin m) ℤ) (_ : IsHyperbolicForm N'),
    IntCongr (R.form p) (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 N')) →
    ∃ p' : StrMfd ξ, R.rank p' = m ∧
      IsDataBordant ξ p ⟨R.s2s2.fst.sum p'.fst, ξ.sumStr R.s2s2.snd p'.snd⟩

/-- **The raw handle-trace cobordism discharges the form-free `HandleTradeSplit` (kernel-pure).**
Given the terminal surgery primitive `HandleTradeCobordism` (residual manifold + its rank + ONE
structured cobordism `p ↝ (S²×S²) ⊔ p'`), the group-level bordism equation
`[p] = [S²×S²] + [p']` of `HandleTradeSplit` is pure bordism-group algebra: the single cobordism
collapses under the quotient (`DataBordismGrp.mk_eq_of_bordant` = `Quot.sound`), and the disjoint
union of representatives is the sum of classes (`DataBordismGrp.add_mk`). So every bit of
`DataBordismGrp` algebra is stripped off the geometry — the net geometric ask drops from the
group-shadow `HandleTradeSplit` to the raw single cobordism. -/
theorem handleTradeSplit_of_cobordism (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) : R.HandleTradeSplit := by
  intro p m E N' hN' hcong
  obtain ⟨p', hrank, hbord⟩ := hCob p m E N' hN' hcong
  exact ⟨p', hrank,
    (DataBordismGrp.mk_eq_of_bordant ξ hbord).trans (DataBordismGrp.add_mk ξ R.s2s2 p').symm⟩

/-- **The single handle-trade reduces `HyperbolicPeel` (kernel-pure).** Composes the raw-cobordism
reduction `handleTradeSplit_of_cobordism` with the existing lattice-algebra reduction
`hyperbolicPeel_of_handleTradeSplit`: the terminal surgery primitive `HandleTradeCobordism` discharges
the full `HyperbolicPeel` atom (the residual's whole intersection form recovered by signature
bordism-invariance + σ=0 uniqueness). -/
theorem hyperbolicPeel_of_handleTradeCobordism (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) : R.HyperbolicPeel :=
  hyperbolicPeel_of_handleTradeSplit R (handleTradeSplit_of_cobordism R hCob)

/-- **Freeze-A discharge from the terminal surgery primitive + the rank-0 base (kernel-pure).**
Composes `hyperbolicPeel_of_handleTradeCobordism` with `realizesSphereProducts_of_peel_and_base`: the
raw handle-trace cobordism `HandleTradeCobordism` (Benedetti Prop 20.16 / Lemma 20.17) and the rank-0
nullbordism `HyperbolicBase` (Thm 20.14, itself a *consequence* of the freeze via
`hyperbolicBase_of_realizesSphereProducts`) together discharge the full `RealizesSphereProducts`
freeze. This pins the entire net-new geometric residual of Freeze A at its terminal in-substrate
grain: ONE structured handle-trace cobordism, with every bordism-group and lattice manipulation
stripped off into kernel-pure algebra. -/
theorem realizesSphereProducts_of_cobordism_and_base (R : SpinSigmaPresentation ξ)
    (hCob : R.HandleTradeCobordism) (hBase : R.HyperbolicBase) : R.RealizesSphereProducts :=
  realizesSphereProducts_of_peel_and_base R (hyperbolicPeel_of_handleTradeCobordism R hCob) hBase

end SpinSigmaPresentation

end SKEFTHawking.SpinSigmaRoute
