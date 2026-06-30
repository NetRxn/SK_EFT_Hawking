import SKEFTHawking.MolecularHamiltonian

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

end SKEFTHawking.DFT
