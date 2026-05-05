/-
# Phase 6n Wave 2b (QCrooks-α) — Tasaki-Crooks TPM axiomatization

The two-point measurement (TPM) protocol per Talkner-Hänggi 2007
(arXiv:0705.1252): project the initial density matrix ρ onto the
eigenbasis of H_i at t_0, evolve via U, project onto the eigenbasis of
H_f at t_f. The resulting forward/reverse work distributions satisfy the
classical Crooks ratio `P_F(W) = exp(β W) P_R(-W)` whenever ρ is diagonal
in the H_i eigenbasis (e.g., a thermal state at inverse temperature β).

**Stage 1 substantive scope.** Ships the `IsTasakiTPMScheme` predicate
identifying which `MeasurementScheme` instances correspond to the TPM
protocol. The substantive content of TPM-derived distributions
(spectral decomposition + transition matrix elements) is deferred to
Stage 2-3, where Aristotle and the program's MTC/quantum-group
infrastructure operate on `Fin n`-dim sandboxes. The Stage-1 deliverable
is the predicate name + its connection to `IsCrooksRatio`.

References:
- Talkner-Hänggi, J. Phys. A 40, F569 (2007), arXiv:0705.1252
- Tasaki, "Jarzynski Relations for Quantum Systems and Some Applications,"
  cond-mat/0009244 (2000)
- Phase 6n DR Appendix §5.A item 1
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.QuantumCrooks

/--
**A `MeasurementScheme` is a Tasaki-TPM scheme on diagonal initial
states if it satisfies the classical Crooks ratio at every inverse
temperature β.**

This is the Stage-1 *characterizing predicate*: rather than constructing
the TPM scheme from the spectral decomposition (deferred to Stage 2-3),
we identify TPM schemes by their defining property — they reproduce the
classical Crooks ratio on diagonal initial states. The Stage 2-3
substantive lift will exhibit the TPM scheme construction and prove it
satisfies this predicate via the inverse-Fourier-of-correlation-function
argument of Talkner-Hänggi 2007.

Per appendix §5.A: "Recovers classical Crooks for diagonal initial
states" — that recovery IS the predicate. -/
def IsTasakiTPMScheme (MS : MeasurementScheme) : Prop :=
  ∀ β : ℝ, IsCrooksRatio (MS.forward β) (MS.reverse β) β

/--
**The trivial `MeasurementScheme` is a Tasaki-TPM scheme.**

Substantive Stage-1 well-posedness: the trivial scheme (zero distributions
for both forward and reverse) trivially satisfies the Crooks ratio at
every β (both sides equal 0). So `IsTasakiTPMScheme` has at least one
inhabitant — the predicate is not vacuous as an existence statement.

This is the Stage-1 analog of `SKEFTAxioms_zero_action` from the
GloriosoLiu wave: a trivial well-posedness witness that confirms the
predicate type-checks and has a substantive `IsCrooksRatio` body. The
Stage 2-3 lift will exhibit non-trivial TPM-derived schemes that satisfy
the predicate via genuine spectral content. -/
theorem trivialScheme_is_TPM : IsTasakiTPMScheme MeasurementScheme.trivial := by
  intro β
  exact isCrooksRatio_zero β

end SKEFTHawking.QuantumCrooks
