/-
# Phase 6n Wave 2b (QCrooks-α) — Perarnau-Llobet et al. no-go obstruction

The load-bearing module of Wave 2b. Per Perarnau-Llobet, Bäumer,
Hovhannisyan, Huber, Acín (Phys. Rev. Lett. 118, 070601, 2017):

> No measurement scheme on a single copy of (ρ, U, H_i, H_f) can
> simultaneously
>
>   (i)  reproduce the average energy change ⟨W⟩ = Tr[H_f U ρ U†] − Tr[H_i ρ]
>        for ARBITRARY initial states ρ (including coherent ones);
>
>   (ii) recover the TPM scheme on diagonal initial states (in the H_i
>        eigenbasis).

Therefore *any* unified work-fluctuation framework must give up something:
either coherent-state average-energy reproduction (Tasaki-TPM does this),
or TPM-on-diagonal recovery (Åberg coherent does this), or some other
classical desideratum.

**Stage-1 substantive form (Phase 6n session 6).** The Stage-1 deliverable
is the **parametric form** of the no-go theorem, proved fully — not
deferred to Aristotle. The substantive content is shipped via three
abstract function parameters:

  - `firstMoment : WorkDistribution → ℝ` — the first moment of a work
    distribution (the average work value extracted from the distribution);
  - `trueAverage : ℝ → ℝ` — the "true" average energy change as a
    function of inverse temperature β (substantively
    `Tr[H_f U ρ U†] − Tr[H_i ρ]` once the quantum substrate is shipped);
  - `canonicalTPM : ℝ → WorkDistribution` — the canonical TPM-derived
    forward distribution at inverse temperature β.

The substantive obstruction `h_disagree` says that on coherent (off-
diagonal) initial states, the true average energy change disagrees with
the average extracted from the TPM distribution — this is the load-
bearing physics content of the Perarnau-Llobet no-go.

The parametric no-go theorem `perarnau_llobet_no_go_parametric` proves
that under `h_disagree`, no measurement scheme can simultaneously satisfy
the average-energy reproduction desideratum AND recover the canonical TPM
scheme. Stage 2-3 instantiates these parameters with the quantum
substrate's specific functions and proves `h_disagree` for a concrete
counterexample (e.g., the canonical 2-level Perarnau-Llobet superposition
with a non-commuting U); the parametric no-go then pulls back to the
quantum no-go.

References:
- Perarnau-Llobet et al., PRL 118, 070601 (2017),
  doi:10.1103/PhysRevLett.118.070601
- Chua, "Looking for Work in Quantum Thermodynamics," arXiv:2601.06312
  (2026) — explicit interpretational mapping of the no-go
- Phase 6n DR Appendix §5.A item 5 + §5.C
-/
import SKEFTHawking.QuantumCrooks.Setup

namespace SKEFTHawking.QuantumCrooks

/--
**The "reproduces average energy" desideratum (parametric form).**

A measurement scheme reproduces the average energy change at every
inverse temperature β if the first moment of its forward distribution
equals the substrate's true-average function applied to β.

Stage-1 form parameterizes over `firstMoment` (extracts the ⟨W⟩ from
a work distribution; substantively `∫ W · P(W) dW`) and `trueAverage`
(substantively `Tr[H_f U ρ U†] − Tr[H_i ρ]` as a function of β); Stage 2-3
plugs in the substantive Mathlib measure-theoretic integral and the
quantum substrate's matrix-trace identity. -/
def ReproducesAverageEnergy
    (MS : MeasurementScheme)
    (firstMoment : WorkDistribution → ℝ)
    (trueAverage : ℝ → ℝ) : Prop :=
  ∀ β : ℝ, firstMoment (MS.forward β) = trueAverage β

/--
**The "recovers TPM on diagonal initial states" desideratum
(parametric form).**

A measurement scheme recovers the canonical TPM scheme if, at every
inverse temperature β, its forward distribution equals the canonical TPM
distribution at β.

Stage-1 form parameterizes over `canonicalTPM` (substantively the TPM-
derived distribution from the spectral decomposition of H_i, H_f, U);
Stage 2-3 plugs in the substantive TPM construction. The "on diagonal
initial states" qualifier is implicit at Stage 1 — the canonical TPM is
a function of β only, with the diagonal-state assumption baked into the
canonical TPM constructor; Stage 2-3 makes this explicit when the
quantum substrate is shipped. -/
def RecoversTPMOnDiagonal
    (MS : MeasurementScheme)
    (canonicalTPM : ℝ → WorkDistribution) : Prop :=
  ∀ β : ℝ, MS.forward β = canonicalTPM β

/--
**The Perarnau-Llobet obstruction predicate (parametric form).**

A measurement scheme exhibits the obstruction if it fails to satisfy at
least one of the two desiderata under the given parametrization. -/
def PerarnauLlobetObstruction
    (MS : MeasurementScheme)
    (firstMoment : WorkDistribution → ℝ)
    (trueAverage : ℝ → ℝ)
    (canonicalTPM : ℝ → WorkDistribution) : Prop :=
  ¬ (ReproducesAverageEnergy MS firstMoment trueAverage ∧
     RecoversTPMOnDiagonal MS canonicalTPM)

/--
**The Perarnau-Llobet no-go theorem (parametric form).**

If the substrate's true average energy change `trueAverage` disagrees
at some inverse temperature β with the TPM-derived average
(`firstMoment ∘ canonicalTPM`), then NO measurement scheme can
simultaneously reproduce `trueAverage` AND recover `canonicalTPM`.

The hypothesis `h_disagree` is the load-bearing physics content: it
asserts that on coherent (off-diagonal) initial states, the true average
energy change disagrees with the TPM-derived average. This disagreement
is the canonical Perarnau-Llobet phenomenon — TPM projects coherences
away before computing work, so its average misses the off-diagonal
contributions to `Tr[H_f U ρ U†]` when U does not commute with H_f.

Substantive Stage-1 proof: by linearity. If MS recovers TPM
(`MS.forward β = canonicalTPM β`), then
`firstMoment (MS.forward β) = firstMoment (canonicalTPM β)`. If MS
reproduces true average (`firstMoment (MS.forward β) = trueAverage β`),
then by transitivity `trueAverage β = firstMoment (canonicalTPM β)` —
contradicting `h_disagree`.

Stage 2-3: instantiate `(firstMoment, trueAverage, canonicalTPM)` with
the substantive quantum-substrate functions and prove `h_disagree` for
the canonical Perarnau-Llobet 2-level system (a coherent superposition
state + non-commuting H_f / U pair). The parametric theorem then yields
the quantum no-go via specialization. -/
theorem perarnau_llobet_no_go_parametric
    {firstMoment : WorkDistribution → ℝ}
    {trueAverage : ℝ → ℝ}
    {canonicalTPM : ℝ → WorkDistribution}
    (h_disagree : ∃ β : ℝ, trueAverage β ≠ firstMoment (canonicalTPM β)) :
    ¬ ∃ MS : MeasurementScheme,
      ReproducesAverageEnergy MS firstMoment trueAverage ∧
      RecoversTPMOnDiagonal MS canonicalTPM := by
  rintro ⟨MS, h_repro, h_tpm⟩
  obtain ⟨β, hβ⟩ := h_disagree
  -- From h_repro β: firstMoment (MS.forward β) = trueAverage β
  -- From h_tpm β:   MS.forward β = canonicalTPM β
  -- Therefore trueAverage β = firstMoment (canonicalTPM β), contradicting hβ.
  apply hβ
  rw [← h_repro β, h_tpm β]

/--
**Contrapositive form: average-energy reproduction forces TPM-recovery
failure.**

Practical statement physicists use: any measurement scheme that reproduces
the true average energy change on arbitrary states must FAIL to recover
the canonical TPM scheme — under the load-bearing `h_disagree` hypothesis
that true average and TPM-derived average disagree at some β.

This is the form Åberg's coherent quantum framework satisfies: it
reproduces (i) on coherent states by construction but does NOT recover
TPM on diagonal states (Åberg's measurement protocol does not project
ρ onto the H_i eigenbasis). Stage 2-3 will instantiate this with the
substantive Åberg construction. -/
theorem reproduces_avg_implies_fails_TPM
    {firstMoment : WorkDistribution → ℝ}
    {trueAverage : ℝ → ℝ}
    {canonicalTPM : ℝ → WorkDistribution}
    (h_disagree : ∃ β : ℝ, trueAverage β ≠ firstMoment (canonicalTPM β))
    (MS : MeasurementScheme)
    (h_repro : ReproducesAverageEnergy MS firstMoment trueAverage) :
    ¬ RecoversTPMOnDiagonal MS canonicalTPM := by
  intro h_tpm
  exact perarnau_llobet_no_go_parametric h_disagree ⟨MS, h_repro, h_tpm⟩

/--
**Contrapositive form: TPM recovery forces average-energy reproduction
failure.**

Practical statement physicists use: any measurement scheme that recovers
the canonical TPM scheme must FAIL to reproduce the true average energy
change on arbitrary states — under the same `h_disagree` hypothesis.

This is the form Tasaki-TPM satisfies: it recovers TPM on diagonal states
by construction but does NOT reproduce the true average on coherent
states (because TPM projects coherences away before the energy
measurement). Stage 2-3 will instantiate this with the substantive
Tasaki TPM construction. -/
theorem recovers_TPM_implies_fails_avg
    {firstMoment : WorkDistribution → ℝ}
    {trueAverage : ℝ → ℝ}
    {canonicalTPM : ℝ → WorkDistribution}
    (h_disagree : ∃ β : ℝ, trueAverage β ≠ firstMoment (canonicalTPM β))
    (MS : MeasurementScheme)
    (h_tpm : RecoversTPMOnDiagonal MS canonicalTPM) :
    ¬ ReproducesAverageEnergy MS firstMoment trueAverage := by
  intro h_repro
  exact perarnau_llobet_no_go_parametric h_disagree ⟨MS, h_repro, h_tpm⟩

/--
**Specialization: the trivial scheme exhibits no obstruction in the
"trivial-substrate" parametrization.**

Sanity check that the parametric obstruction predicate behaves correctly:
take `firstMoment := fun _ => 0`, `trueAverage := fun _ => 0`,
`canonicalTPM := fun _ => WorkDistribution.zero`. Then both desiderata
are trivially satisfied by `MeasurementScheme.trivial`, so the
obstruction predicate fails for it. Confirms the parametric form has
non-vacuous content (an MS can fail to exhibit the obstruction when the
substrate-specific functions allow consistency). -/
theorem trivialScheme_no_obstruction_in_trivial_substrate :
    ¬ PerarnauLlobetObstruction
        MeasurementScheme.trivial
        (fun _ => (0 : ℝ))
        (fun _ => 0)
        (fun _ => WorkDistribution.zero) := by
  unfold PerarnauLlobetObstruction
  intro h
  apply h
  refine ⟨?_, ?_⟩
  · -- ReproducesAverageEnergy: ∀ β, 0 = 0
    intro _; rfl
  · -- RecoversTPMOnDiagonal: ∀ β, MS.forward β = WorkDistribution.zero
    intro _; rfl

end SKEFTHawking.QuantumCrooks
