import SKEFTHawking.MolecularHamiltonian
import Mathlib.Analysis.Distribution.FourierMultiplier

/-!
# Essential self-adjointness criterion (Phase 6BB Wave 6 — discharge of `hkin`)

The Wave-1 `MolecularHamiltonian.lean` substrate proved the *basic criterion of self-adjointness*
(`IsSymmetricPMap.isSelfAdjoint_of_surjective`): a densely-defined symmetric `S` with `S ± iμ`
**surjective** is self-adjoint. That requires the full range `= ⊤`, which holds for an operator
defined on its maximal domain but **not** for a differential operator on a core (e.g. the kinetic
operator on Schwartz space), whose range is only *dense*.

This module supplies the **essential-self-adjointness criterion**: a densely-defined symmetric `S`
with `S ± iμ` having merely **dense range** has a self-adjoint *closure* (`S` is essentially
self-adjoint). The mechanism: `S.closure` is closed and symmetric; the range of `S.closure ± iμ` is
both closed (the Wave-1 closed-range argument needs only symmetry + a closed graph) and dense (it
contains the dense range of `S ± iμ`), hence `= ⊤`; the basic criterion then applies to `S.closure`.

This is the operator-theoretic half of discharging the disclosed `hkin` hypothesis of
`molecularHamiltonian_essSelfAdjoint`; the analytic half (dense range of the kinetic operator, via the
Fourier multiplier) consumes this criterion.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom;
no `maxHeartbeats`.
-/

namespace SKEFTHawking.DFT

open scoped InnerProductSpace
open LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Closed half of surjectivity for a closed symmetric operator.** If `T` is symmetric with a
*closed graph*, then for `μ ≠ 0` the range of `x ↦ T x - iμ·x` is topologically closed. (Generalizes
the Wave-1 `IsSelfAdjoint.isClosed_range_sub_I_smul`: that proof used only the symmetric lower bound
and closedness of the graph, never full self-adjointness.) -/
lemma IsSymmetricPMap.isClosed_range_sub_I_smul_of_isClosed [CompleteSpace H] {T : H →ₗ.[ℂ] H}
    (hT : IsSymmetricPMap T) (hTc : T.IsClosed) {μ : ℝ} (hμ : μ ≠ 0) :
    IsClosed {w : H | ∃ x : T.domain, (T x : H) - (Complex.I * (μ : ℂ)) • (x : H) = w} := by
  apply IsSeqClosed.isClosed
  intro w wlim hw_mem hw_lim
  choose x hx using hw_mem
  have hμpos : 0 < |μ| := abs_pos.mpr hμ
  have hCauchy : CauchySeq fun n => ((x n : H)) := by
    have hwc : CauchySeq w := hw_lim.cauchySeq
    rw [Metric.cauchySeq_iff] at hwc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hwc (|μ| * ε) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb := hT.mul_norm_le_norm_sub_I_smul μ (x m - x n)
    have hsub : (T (x m - x n) : H) - (Complex.I * (μ : ℂ)) • ((x m - x n : T.domain) : H)
        = w m - w n := by
      rw [LinearPMap.map_sub, AddSubgroupClass.coe_sub, smul_sub, sub_sub_sub_comm, hx m, hx n]
    rw [hsub] at hb
    rw [dist_eq_norm]
    have hlt := hN m hm n hn
    rw [dist_eq_norm] at hlt
    have hbb : |μ| * ‖(x m : H) - (x n : H)‖ ≤ ‖w m - w n‖ := by
      simpa [AddSubgroupClass.coe_sub] using hb
    nlinarith [norm_nonneg ((x m : H) - (x n : H))]
  obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hAx : Filter.Tendsto (fun n => (T (x n) : H)) Filter.atTop
      (nhds (wlim + (Complex.I * (μ : ℂ)) • x₀)) := by
    have heq : (fun n => (T (x n) : H)) = fun n => w n + (Complex.I * (μ : ℂ)) • (x n : H) := by
      funext n; rw [← hx n]; abel
    rw [heq]
    exact hw_lim.add (hx₀.const_smul _)
  have hgraph : (x₀, wlim + (Complex.I * (μ : ℂ)) • x₀) ∈ T.graph :=
    hTc.mem_of_tendsto (hx₀.prodMk_nhds hAx)
      (Filter.Eventually.of_forall fun n => T.mem_graph (x n))
  obtain ⟨y₀, hy₀_eq, hy₀_val⟩ := (LinearPMap.mem_graph_iff T).mp hgraph
  refine ⟨y₀, ?_⟩
  have hy_eq : (y₀ : H) = x₀ := hy₀_eq
  have hy_val : (T y₀ : H) = wlim + (Complex.I * (μ : ℂ)) • x₀ := hy₀_val
  rw [hy_val, hy_eq]; module

/-- The range set `{T x - iμ·x}` of a partial map, as a `Set H`. -/
private def rangeSubISmul (T : H →ₗ.[ℂ] H) (μ : ℝ) : Set H :=
  {w : H | ∃ x : T.domain, (T x : H) - (Complex.I * (μ : ℂ)) • (x : H) = w}

/-- The range of `S ± iμ` is contained in that of `S.closure ± iμ` (the closure extends `S`). -/
lemma rangeSubISmul_le_closure {S : H →ₗ.[ℂ] H} (μ : ℝ) :
    rangeSubISmul S μ ⊆ rangeSubISmul S.closure μ := by
  rintro w ⟨x, hx⟩
  exact ⟨⟨(x : H), (S.le_closure.1 x.2)⟩, by
    rw [← hx]; congr 1; exact (S.le_closure.2 rfl).symm⟩

/-- **Essential-self-adjointness criterion.** A densely-defined symmetric operator `S` whose
`S ± iμ` (for some `μ ≠ 0`) have **dense range** is essentially self-adjoint: its closure is
self-adjoint. The range of `S.closure ± iμ` is closed (the closed-graph argument above) and dense
(it contains the dense range of `S ± iμ`), hence all of `H`; the Wave-1 basic criterion then applies
to the closed symmetric `S.closure`. -/
theorem isSelfAdjoint_closure_of_dense_range [CompleteSpace H] {S : H →ₗ.[ℂ] H}
    (hS : IsSymmetricPMap S) (hdense : Dense (S.domain : Set H)) {μ : ℝ} (hμ : μ ≠ 0)
    (hpos : Dense (rangeSubISmul S μ)) (hneg : Dense (rangeSubISmul S (-μ))) :
    IsSelfAdjoint S.closure := by
  have hSsym : S.IsSymmetric := hS
  have hSunb : S.IsUnbounded := isUnbounded_of_dense_of_isSymmetric hdense hSsym
  have hScldense : Dense (S.closure.domain : Set H) := hSunb.closure.hasDenseDomain
  -- S.closure is symmetric: S.closure ≤ S† = (S.closure)†
  have hSleadj : S ≤ S.adjoint := (isSymmetric_iff_le_adjoint hdense).mp hSsym
  have hadj_closed : S.adjoint.IsClosed := adjoint_isClosed hdense
  have hScl_le_adj : S.closure ≤ S.adjoint := by
    have := hadj_closed.isClosable.closure_mono hSleadj
    rwa [hadj_closed.isClosable.isClosed_iff.mp hadj_closed] at this
  have hSclsym : S.closure.IsSymmetric :=
    (isSymmetric_iff_le_adjoint hScldense).mpr <| by
      rwa [hSunb.adjoint_closure_eq_adjoint]
  have hSclsymP : IsSymmetricPMap S.closure := hSclsym
  have hScl_closed : S.closure.IsClosed := hSunb.isClosable.closure_isClosed
  -- The range of `S.closure ± iμ` is closed (brick 1) and dense (⊇ dense range of `S ± iμ`), so `⊤`.
  have surj : ∀ ν : ℝ, ν ≠ 0 → Dense (rangeSubISmul S ν) →
      ∀ z : H, ∃ x : S.closure.domain, (S.closure x : H) - (Complex.I * (ν : ℂ)) • (x : H) = z := by
    intro ν hν hdν z
    have hclosed : IsClosed (rangeSubISmul S.closure ν) :=
      hSclsymP.isClosed_range_sub_I_smul_of_isClosed hScl_closed hν
    have hdense_cl : Dense (rangeSubISmul S.closure ν) :=
      hdν.mono (rangeSubISmul_le_closure ν)
    have htop : rangeSubISmul S.closure ν = Set.univ :=
      hclosed.closure_eq ▸ hdense_cl.closure_eq
    have : z ∈ rangeSubISmul S.closure ν := htop ▸ Set.mem_univ z
    exact this
  refine hSclsymP.isSelfAdjoint_of_surjective hScldense (surj μ hμ hpos) (fun z => ?_)
  obtain ⟨x, hx⟩ := surj (-μ) (neg_ne_zero.mpr hμ) hneg z
  exact ⟨x, by rw [← hx]; push_cast; module⟩

/-! ### Wave 2 — discharge of `hkin`: the kinetic operator is essentially self-adjoint.

`kineticOperator = ofReal (2m)⁻¹ • momentumSqOperator` (PhysLib `kineticOperator_eq`); real-scalar
invariance reduces `IsSelfAdjoint kineticOperator.closure` to `IsSelfAdjoint momentumSqOperator.closure`.
The latter is the Wave-1 criterion `isSelfAdjoint_closure_of_dense_range` applied to `momentumSqOperator`:
it is symmetric with dense (Schwartz) domain, and `momentumSqOperator ± i` has dense range because in
the Fourier representation it is multiplication by `s(ξ) = ℏ²(2π)²‖ξ‖² ≥ 0`, whose shifted inverse
`(s ± i)⁻¹` is a Schwartz-preserving (temperate) multiplier. -/

section Wave2
open QuantumMechanics SchwartzMap SpaceDHilbertSpace

variable {d : ℕ}

/-- `A.comp A` (with `A` mapping its domain into itself) is symmetric when `A` is symmetric. -/
lemma isSymmetricPMap_comp_self
    (A : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d) (hA : A.IsSymmetric)
    (hr : ∀ x : A.domain, A x ∈ A.domain) :
    (A.comp A hr).IsSymmetric := by
  intro x y
  exact (hA ⟨A x, hr x⟩ y).trans (hA x ⟨A y, hr y⟩)

/-- The momentum-square operator `∑ᵢ 𝓟ᵢ²` is symmetric. -/
lemma momentumSqOperator_isSymmetric :
    (momentumSqOperator (d := d)).IsSymmetric := by
  rw [momentumSqOperator_eq]
  exact LinearPMap.IsSymmetric.sum fun i =>
    isSymmetricPMap_comp_self (momentumOperator i) (momentumOperator_isSymmetric i)
      (momentumOperator_range i)

/-- The momentum-square operator has dense (Schwartz) domain. -/
lemma momentumSqOperator_hasDenseDomain :
    Dense ((momentumSqOperator (d := d)).domain : Set (SpaceDHilbertSpace d)) := by
  rw [momentumSqOperator_domain_eq]
  exact SpaceDHilbertSpace.SchwartzSubmodule.dense d MeasureTheory.volume

/-- **C1a (linchpin).** PhysLib's `momentumCLM i` is `-iℏ` times Mathlib's directional derivative
along `Space.basis i`; both unfold to `x ↦ fderiv ℝ ψ x (Space.basis i)`. -/
lemma momentumCLM_eq_smul_lineDeriv (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM i f = (-Complex.I * Constants.ℏ) • LineDeriv.lineDerivOp (Space.basis i) f := rfl

/-- The linear coordinate symbol `ξ ↦ ⟨ξ, basis i⟩` has temperate growth. -/
lemma innerBasis_hasTemperateGrowth (i : Fin d) :
    Function.HasTemperateGrowth (fun ξ : Space d => (inner ℝ ξ (Space.basis i) : ℝ)) := by
  fun_prop

/-- **C1b.** The momentum component is `2πℏ` times the Fourier multiplier with the (ℂ-cast) linear
symbol `⟨ξ, basis i⟩` (`(-iℏ)·(2πi) = 2πℏ`). -/
lemma momentumCLM_eq_fourierMultiplier (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM i f
      = (2 * Real.pi * Constants.ℏ : ℂ) •
        fourierMultiplierCLM ℂ (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ)) f := by
  rw [momentumCLM_eq_smul_lineDeriv, lineDeriv_eq_fourierMultiplierCLM,
    ← fourierMultiplierCLM_ofReal ℂ (innerBasis_hasTemperateGrowth i), smul_smul]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The ℂ-cast linear coordinate symbol has temperate growth. -/
lemma innerBasisC_hasTemperateGrowth (i : Fin d) :
    Function.HasTemperateGrowth (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ)) := by
  fun_prop

/-- **C1c.** The squared momentum component is `(2πℏ)²` times the Fourier multiplier with symbol
`⟨ξ, basis i⟩²`. -/
lemma momentumCLM_sq_eq_fourierMultiplier (i : Fin d) (f : 𝓢(Space d, ℂ)) :
    momentumCLM i (momentumCLM i f)
      = ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ) •
        fourierMultiplierCLM ℂ (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ) ^ 2) f := by
  have hsymb : (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ))
        * (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ))
      = (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ) ^ 2) := by
    funext ξ; simp [Pi.mul_apply, sq]
  simp only [momentumCLM_eq_fourierMultiplier]
  rw [_root_.map_smul, smul_smul,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (innerBasisC_hasTemperateGrowth i)
      (innerBasisC_hasTemperateGrowth i), hsymb]
  congr 1
  ring

/-- The squared ℂ-cast coordinate symbol has temperate growth. -/
lemma innerBasisCSq_hasTemperateGrowth (i : Fin d) :
    Function.HasTemperateGrowth (fun ξ : Space d => ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ) ^ 2) := by
  fun_prop

/-- **C1d.** The full momentum-square Schwartz action `∑ᵢ 𝐩ᵢ²` is `(2πℏ)²` times the Fourier
multiplier with symbol `‖ξ‖²`. -/
lemma momentumSq_schwartz_eq_fourierMultiplier (f : 𝓢(Space d, ℂ)) :
    (∑ i, momentumCLM i (momentumCLM i f))
      = ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ) •
        fourierMultiplierCLM ℂ (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) f := by
  have hsum : (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ))
      = (fun ξ : Space d => ∑ i, ((inner ℝ ξ (Space.basis i) : ℝ) : ℂ) ^ 2) := by
    funext ξ
    rw [← Space.basis.sum_sq_inner_left ξ]
    push_cast
    ring
  simp only [momentumCLM_sq_eq_fourierMultiplier]
  rw [← Finset.smul_sum]
  congr 1
  rw [← ContinuousLinearMap.sum_apply,
    ← fourierMultiplierCLM_sum ℂ (fun i _ => innerBasisCSq_hasTemperateGrowth i), ← hsum]

/-! #### C2 — the resolvent symbol `(s - iμ)⁻¹` has temperate growth.

No `HasTemperateGrowth.inv` exists in Mathlib, so we build it from temperate pieces. The inverse
growth is supplied by Mathlib's `hasTemperateGrowth_one_add_norm_sq_rpow` at exponent `-1`, applied
in **one real variable** `t` (so the denominator is quadratic in `t`), then composed with `‖·‖²`. -/

/-- `(1 + (a·t)²)⁻¹` (one real variable) has temperate growth — the inverse-growth building block. -/
lemma oneAdd_mulSq_inv_hasTemperateGrowth (a : ℝ) :
    Function.HasTemperateGrowth (fun t : ℝ => (1 + (a * t) ^ 2)⁻¹) := by
  have hbase := Function.hasTemperateGrowth_one_add_norm_sq_rpow ℝ (-1 : ℝ)
  have hlin : Function.HasTemperateGrowth (fun t : ℝ => a * t) := by fun_prop
  have hcomp := hbase.comp hlin
  have heq : (fun t : ℝ => (1 + (a * t) ^ 2)⁻¹)
      = (fun t : ℝ => (1 + ‖a * t‖ ^ 2) ^ (-1 : ℝ)) := by
    funext t; rw [Real.norm_eq_abs, sq_abs, Real.rpow_neg_one]
  rw [heq]; exact hcomp

/-- The real denominator inverse `(k²t² + μ²)⁻¹` (one variable) has temperate growth. -/
lemma denomInv1D_hasTemperateGrowth (k μ : ℝ) (hμ : μ ≠ 0) :
    Function.HasTemperateGrowth (fun t : ℝ => (k ^ 2 * t ^ 2 + μ ^ 2)⁻¹) := by
  have hb := (Function.HasTemperateGrowth.const (E := ℝ) ((μ ^ 2)⁻¹ : ℝ)).mul
    (oneAdd_mulSq_inv_hasTemperateGrowth (k / μ))
  have heq : (fun t : ℝ => (k ^ 2 * t ^ 2 + μ ^ 2)⁻¹)
      = (fun t : ℝ => (μ ^ 2)⁻¹ * (1 + (k / μ * t) ^ 2)⁻¹) := by
    funext t
    rw [← mul_inv]
    congr 1
    field_simp
    ring
  rw [heq]; exact hb

/-- The 1-D resolvent symbol `(↑(k·t) - iμ)⁻¹` has temperate growth (conjugate form). -/
lemma phi1D_hasTemperateGrowth (k μ : ℝ) (hμ : μ ≠ 0) :
    Function.HasTemperateGrowth
      (fun t : ℝ => (((k * t : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹) := by
  have hnum : Function.HasTemperateGrowth
      (fun t : ℝ => ((k * t : ℝ) : ℂ) + Complex.I * (μ : ℂ)) := by fun_prop
  have hden : Function.HasTemperateGrowth
      (fun t : ℝ => (((k ^ 2 * t ^ 2 + μ ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal
      (denomInv1D_hasTemperateGrowth k μ hμ)
  have heq : (fun t : ℝ => (((k * t : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹)
      = (fun t : ℝ => (((k * t : ℝ) : ℂ) + Complex.I * (μ : ℂ))
          * (((k ^ 2 * t ^ 2 + μ ^ 2)⁻¹ : ℝ) : ℂ)) := by
    funext t
    have hne : ((k * t : ℝ) : ℂ) - Complex.I * (μ : ℂ) ≠ 0 := by
      intro h
      apply hμ
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hwne : ((k * t : ℝ) : ℂ) + Complex.I * (μ : ℂ) ≠ 0 := by
      intro h
      apply hμ
      have him := congrArg Complex.im h
      simp at him
      linarith
    have hzw : (((k * t : ℝ) : ℂ) - Complex.I * (μ : ℂ))
        * (((k * t : ℝ) : ℂ) + Complex.I * (μ : ℂ)) = ((k ^ 2 * t ^ 2 + μ ^ 2 : ℝ) : ℂ) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [Complex.ofReal_inv, ← hzw]
    field_simp
  rw [heq]; exact hnum.mul hden

/-- **C2.** The resolvent symbol `(↑(k‖ξ‖²) - iμ)⁻¹` has temperate growth for `μ ≠ 0` (any real
`k`), since the denominator never vanishes (its imaginary part is `-μ`). Built by composing the
1-D resolvent `φ` with `‖·‖²`. -/
lemma resolventSymbol_hasTemperateGrowth (k μ : ℝ) (hμ : μ ≠ 0) :
    Function.HasTemperateGrowth
      (fun ξ : Space d => (((k * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹) :=
  (phi1D_hasTemperateGrowth k μ hμ).comp (Function.hasTemperateGrowth_norm_sq (H := Space d))

/-! #### C4 — transport of the Schwartz momentum-square action to the Hilbert space. -/

/-- `𝓟ᵢ` carries `schwartzEquiv G` to the L²-inclusion of `𝐩ᵢ G` (intertwining of the unbounded
operator with its Schwartz-space symbol). -/
lemma momentumOperator_schwartzEquiv (i : Fin d) (G : 𝓢(Space d, ℂ)) :
    (momentumOperator i (schwartzEquiv MeasureTheory.volume G) : SpaceDHilbertSpace d)
      = schwartzIncl MeasureTheory.volume (momentumCLM i G) := by
  rw [momentumOperator_apply, (schwartzEquiv MeasureTheory.volume).symm_apply_apply,
    SchwartzSubmodule.schwartzEquiv_apply_coe]

/-- `𝓟ᵢ` on any Schwartz-submodule element is the L²-inclusion of `𝐩ᵢ` applied to its Schwartz
preimage. -/
lemma momentumOperator_apply_coe (i : Fin d) (z : SchwartzSubmodule d) :
    (momentumOperator i z : SpaceDHilbertSpace d)
      = schwartzIncl MeasureTheory.volume
        (momentumCLM i ((schwartzEquiv MeasureTheory.volume).symm z)) := by
  rw [momentumOperator_apply, SchwartzSubmodule.schwartzEquiv_apply_coe]

/-- `schwartzEquiv.symm` of the canonical inclusion `⟨schwartzIncl G, _⟩` recovers `G`. -/
lemma schwartzEquiv_symm_mk (G : 𝓢(Space d, ℂ))
    (h : schwartzIncl MeasureTheory.volume G ∈ SchwartzSubmodule d) :
    (schwartzEquiv MeasureTheory.volume).symm ⟨schwartzIncl MeasureTheory.volume G, h⟩ = G := by
  rw [show (⟨schwartzIncl MeasureTheory.volume G, h⟩ : SchwartzSubmodule d)
      = schwartzEquiv MeasureTheory.volume G from
    Subtype.ext (SchwartzSubmodule.schwartzEquiv_apply_coe G).symm,
    (schwartzEquiv MeasureTheory.volume).symm_apply_apply]

/-- The Hilbert-space action of `momentumSqOperator` on a Schwartz element is the L²-inclusion of
the Schwartz-space momentum-square `∑ᵢ 𝐩ᵢ²`. -/
lemma momentumSqOperator_apply_eq (F : 𝓢(Space d, ℂ))
    (hmem : (schwartzEquiv MeasureTheory.volume F : SpaceDHilbertSpace d) ∈
      momentumSqOperator.domain) :
    (momentumSqOperator ⟨_, hmem⟩ : SpaceDHilbertSpace d)
      = schwartzIncl MeasureTheory.volume (∑ i, momentumCLM i (momentumCLM i F)) := by
  unfold momentumSqOperator
  rw [LinearPMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [LinearPMap.comp, LinearPMap.codRestrict, LinearMap.compPMap_apply, momentumOperator_apply,
    SchwartzSubmodule.schwartzEquiv_apply_coe]
  congr 2
  rw [(schwartzEquiv MeasureTheory.volume).symm_apply_eq]
  apply Subtype.ext
  exact (momentumOperator_apply_coe i _).trans
    (by simp only [SchwartzSubmodule.schwartzEquiv_apply_coe]; congr 2; exact schwartzEquiv_symm_mk F _)

/-! #### C3+C5 — dense range of `momentumSqOperator ± iμ`, hence essential self-adjointness. -/

/-- The shifted symbol `s(ξ) - iμ` (with `s` real) is nonzero for `μ ≠ 0`: its imaginary part is
`-μ`. -/
lemma momSqSymbol_sub_ne_zero (μ : ℝ) (hμ : μ ≠ 0) (ξ : Space d) :
    (((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ) ≠ 0 := by
  intro h
  apply hμ
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.I_re,
    Complex.ofReal_re, Complex.zero_im, one_mul, mul_zero, zero_sub, neg_eq_zero] at him
  linarith

/-- The resolvent symbol inverts the shifted symbol pointwise. -/
lemma momSqSymbol_mul_resolvent (μ : ℝ) (hμ : μ ≠ 0) (ξ : Space d) :
    ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))
      * ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹ = 1 :=
  mul_inv_cancel₀ (momSqSymbol_sub_ne_zero μ hμ ξ)

/-- Fourier multipliers subtract over their symbols. -/
lemma fourierMultiplierCLM_sub_apply {g₁ g₂ : Space d → ℂ} (hg₁ : g₁.HasTemperateGrowth)
    (hg₂ : g₂.HasTemperateGrowth) (f : 𝓢(Space d, ℂ)) :
    fourierMultiplierCLM ℂ g₁ f - fourierMultiplierCLM ℂ g₂ f
      = fourierMultiplierCLM ℂ (g₁ - g₂) f := by
  have hCLM : fourierMultiplierCLM ℂ g₁ - fourierMultiplierCLM ℂ g₂
      = fourierMultiplierCLM ℂ (g₁ - g₂) := by
    unfold fourierMultiplierCLM
    rw [SchwartzMap.smulLeftCLM_sub hg₁ hg₂, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub]
  rw [← ContinuousLinearMap.sub_apply, hCLM]

/-- The resolvent multiplier symbol `(s - iμ)⁻¹` for `s(ξ) = (2πℏ)²‖ξ‖²`. -/
noncomputable def resSym (μ : ℝ) : Space d → ℂ :=
  fun ξ => ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹

lemma resSym_hasTemperateGrowth (μ : ℝ) (hμ : μ ≠ 0) :
    (resSym (d := d) μ).HasTemperateGrowth :=
  resolventSymbol_hasTemperateGrowth ((2 * Real.pi * Constants.ℏ) ^ 2) μ hμ

/-- The ℂ-cast norm-square symbol `↑‖ξ‖²` has temperate growth. -/
lemma normSymC_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) :=
  Function.HasTemperateGrowth.comp Function.Complex.hasTemperateGrowth_ofReal
    (Function.hasTemperateGrowth_norm_sq (H := Space d))

/-- The combined resolvent symbol collapses to `1`: `(2πℏ)²·↑‖ξ‖²·r - iμ·r = 1`. -/
lemma resolvent_symbol_eq_one (μ : ℝ) (hμ : μ ≠ 0) :
    (((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ) • ((fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) * resSym μ)
      - (Complex.I * (μ : ℂ)) • resSym μ) = fun _ : Space d => (1 : ℂ) := by
  funext ξ
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, resSym]
  rw [show ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ)
          * (((‖ξ‖ ^ 2 : ℝ) : ℂ)
            * ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹)
        - Complex.I * (μ : ℂ)
          * ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹
      = ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))
          * ((((2 * Real.pi * Constants.ℏ) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) - Complex.I * (μ : ℂ))⁻¹
      from by push_cast; ring]
  exact momSqSymbol_mul_resolvent μ hμ ξ

/-- A constant scalar times a temperate function is temperate (in the `c • g` form). -/
lemma smul_hasTemperateGrowth {g : Space d → ℂ} (c : ℂ) (hg : g.HasTemperateGrowth) :
    Function.HasTemperateGrowth (c • g) :=
  (Function.HasTemperateGrowth.const c).smul hg

/-- **Operator identity.** `x := M[r]G` solves `(momentumSq − iμ)x = G` at the Schwartz level:
`(2πℏ)²·M[‖·‖²](M[r]G) − iμ·M[r]G = G`. -/
lemma resolvent_solves (μ : ℝ) (hμ : μ ≠ 0) (G : 𝓢(Space d, ℂ)) :
    ((2 * Real.pi * Constants.ℏ) ^ 2 : ℂ)
        • fourierMultiplierCLM ℂ (fun ξ : Space d => ((‖ξ‖ ^ 2 : ℝ) : ℂ))
          (fourierMultiplierCLM ℂ (resSym μ) G)
      - (Complex.I * (μ : ℂ)) • fourierMultiplierCLM ℂ (resSym μ) G = G := by
  have hr := resSym_hasTemperateGrowth (d := d) μ hμ
  have hn := normSymC_hasTemperateGrowth (d := d)
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply hn hr G,
    ← ContinuousLinearMap.smul_apply, ← fourierMultiplierCLM_smul (hn.mul hr),
    ← ContinuousLinearMap.smul_apply, ← fourierMultiplierCLM_smul hr,
    fourierMultiplierCLM_sub_apply (smul_hasTemperateGrowth _ (hn.mul hr))
      (smul_hasTemperateGrowth _ hr),
    resolvent_symbol_eq_one μ hμ, fourierMultiplierCLM_const]
  simp

/-- **Dense range.** `momentumSqOperator ± iμ` has dense range (it contains the dense Schwartz
submodule): for `w = schwartzIncl G`, the preimage `x = schwartzEquiv (M[r]G)` solves
`momentumSqOperator x − iμ·x = w`. -/
lemma dense_rangeSubISmul (μ : ℝ) (hμ : μ ≠ 0) :
    Dense (rangeSubISmul (momentumSqOperator (d := d)) μ) := by
  refine Dense.mono ?_ momentumSqOperator_hasDenseDomain
  intro w hw
  rw [SetLike.mem_coe, momentumSqOperator_domain_eq] at hw
  obtain ⟨G, rfl⟩ := hw
  have hmem : (schwartzEquiv MeasureTheory.volume (fourierMultiplierCLM ℂ (resSym μ) G) :
      SpaceDHilbertSpace d) ∈ momentumSqOperator.domain := by
    rw [momentumSqOperator_domain_eq]; exact (schwartzEquiv MeasureTheory.volume _).2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [momentumSqOperator_apply_eq _ hmem, SchwartzSubmodule.schwartzEquiv_apply_coe,
    ← _root_.map_smul, ← _root_.map_sub, momentumSq_schwartz_eq_fourierMultiplier,
    resolvent_solves μ hμ G]
  rfl

/-- **The momentum-square operator `∑ᵢ 𝐩ᵢ²` is essentially self-adjoint** (its closure is
self-adjoint): symmetric, dense Schwartz domain, and `± i` dense range (Wave-1 criterion). -/
theorem momentumSqOperator_isSelfAdjoint_closure :
    IsSelfAdjoint (momentumSqOperator (d := d)).closure :=
  isSelfAdjoint_closure_of_dense_range momentumSqOperator_isSymmetric
    momentumSqOperator_hasDenseDomain one_ne_zero
    (dense_rangeSubISmul 1 one_ne_zero) (dense_rangeSubISmul (-1) (by norm_num))

/-- **The molecular kinetic operator is essentially self-adjoint** — the discharge of `hkin`. The
kinetic operator is a positive real multiple of `momentumSqOperator`, whose closure is self-adjoint
(`momentumSqOperator_isSelfAdjoint_closure`); real-scalar invariance transfers self-adjointness. -/
theorem kineticOperator_isSelfAdjoint_closure (N : ℕ) (m : ℝ) (hm : 0 < m)
    (nuclei : Finset (Space 3 × ℝ)) :
    IsSelfAdjoint (molecularSystem N m hm nuclei).kineticOperator.closure := by
  have hm2 : (2 * (molecularSystem N m hm nuclei).m)⁻¹ ≠ 0 := by
    show (2 * m)⁻¹ ≠ 0; positivity
  rw [QuantumMechanics.SpaceDQuantumSystem.kineticOperator_eq,
    LinearPMap.closure_smul _ (Complex.ofReal_ne_zero.mpr hm2)]
  exact LinearPMap.IsSelfAdjoint.smul momentumSqOperator_isSelfAdjoint_closure
    (Complex.ofReal_ne_zero.mpr hm2) (Complex.conj_ofReal _)

/-- **Molecular Coulomb Hamiltonian essential self-adjointness with `hkin` discharged**, still
disclosing `hpot` and `hrel`. **Superseded** by the fully unconditional
`SKEFTHawking.DFT.molecularHamiltonian_essSelfAdjoint` (relocated to `CoulombRelativeBound.lean` once
`hrel` was discharged via `coulomb_isRelBounded`); kept here as the `hpot`+`hrel`-disclosing building
block. See also `_of_kinetic` (discharges `hpot` too). -/
theorem _root_.SKEFTHawking.DFT.molecularHamiltonian_essSelfAdjoint_of_hpot_hrel
    (N : ℕ) (m : ℝ) (hm : 0 < m)
    (nuclei : Finset (Space 3 × ℝ))
    (hpot : IsSymmetricPMap (molecularSystem N m hm nuclei).potentialOperator)
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hrel : IsRelBounded (molecularSystem N m hm nuclei).kineticOperator.closure
      (molecularSystem N m hm nuclei).potentialOperator a b) :
    IsSelfAdjoint ((molecularSystem N m hm nuclei).kineticOperator.closure
      + (molecularSystem N m hm nuclei).potentialOperator) :=
  spaceDQuantumSystem_hamiltonian_isSelfAdjoint _
    (kineticOperator_isSelfAdjoint_closure N m hm nuclei) hpot ha0 ha hb hrel

/-- **Molecular essential self-adjointness with `hkin` and `hpot` both discharged.** Only `hrel`
(Coulomb relative-boundedness `a < 1`) remains disclosed. -/
theorem _root_.SKEFTHawking.DFT.molecularHamiltonian_essSelfAdjoint_of_kinetic
    (N : ℕ) (m : ℝ) (hm : 0 < m) (nuclei : Finset (Space 3 × ℝ))
    {a b : ℝ} (ha0 : 0 ≤ a) (ha : a < 1) (hb : 0 ≤ b)
    (hrel : IsRelBounded (molecularSystem N m hm nuclei).kineticOperator.closure
      (molecularSystem N m hm nuclei).potentialOperator a b) :
    IsSelfAdjoint ((molecularSystem N m hm nuclei).kineticOperator.closure
      + (molecularSystem N m hm nuclei).potentialOperator) :=
  spaceDQuantumSystem_hamiltonian_isSelfAdjoint _
    (kineticOperator_isSelfAdjoint_closure N m hm nuclei)
    (molecularPotentialOperator_isSymmetric N m hm nuclei) ha0 ha hb hrel

end Wave2

end SKEFTHawking.DFT
