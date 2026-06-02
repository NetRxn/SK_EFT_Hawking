import SKEFTHawking.QuantumNetwork.CPTPChannel

/-!
# General-state network monotonicity (Phase 6AG, Ask 3)

The repeater-network envelopes shipped so far (`swapChain_fidelity_envelope`, decay-inclusive,
distillation, …) are all phrased over the Werner / Bell-diagonal real-parameter model. This file
provides the **arbitrary density-matrix** network monotonicity that lifts the network past that
restriction: an end-to-end repeater is a *chain of CPTP operations* (entanglement swaps, LOCC
distillation steps, memory channels), and the data-processing inequality says the trace distance
between the actual end-to-end state and any target reference cannot increase as further CPTP
segments are applied. This is the operational meaning of "purification/swapping does not create
distinguishability from the ideal".

Built directly on the shipped CPTP data-processing inequality `traceDist_krausMap_le`. The
fidelity-domain analogue needs the fidelity data-processing inequality (not shipped); the
trace-distance version here is unconditional.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A **CPTP channel step** in the data-processing sense: a Hermitian-preserving, trace-distance
contractive operation on density operators. Every Kraus channel is one (`isChannelStep_krausMap`),
but the abstraction also covers compositions and any operation satisfying data processing. -/
structure IsChannelStep (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop where
  herm : ∀ {ρ : Matrix ι ι ℂ}, ρ.IsHermitian → (Φ ρ).IsHermitian
  contractive : ∀ {ρ σ : Matrix ι ι ℂ}, ρ.IsHermitian → σ.IsHermitian →
    traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ

/-- A Kraus channel (`∑ₖ Kₖ ρ Kₖᴴ` with `∑ₖ KₖᴴKₖ = 1`) is a CPTP channel step. -/
theorem isChannelStep_krausMap {m : ℕ} {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K) :
    IsChannelStep (krausMap K) where
  herm h := krausMap_isHermitian K h
  contractive hρ hσ := traceDist_krausMap_le hK hρ hσ

/-- Apply a chain of channel steps (a repeater/swap network), innermost segment first. -/
def applyChain (Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Φs.foldr (fun Φ acc => Φ acc) ρ

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem applyChain_nil (ρ : Matrix ι ι ℂ) : applyChain [] ρ = ρ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem applyChain_cons (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ)
    (Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)) (ρ : Matrix ι ι ℂ) :
    applyChain (Φ :: Φs) ρ = Φ (applyChain Φs ρ) := rfl

/-- A chain of Hermitian-preserving steps preserves Hermitianness. -/
theorem applyChain_isHermitian {Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)}
    (hΦs : ∀ Φ ∈ Φs, IsChannelStep Φ) {ρ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) :
    (applyChain Φs ρ).IsHermitian := by
  induction Φs with
  | nil => simpa using hρ
  | cons Φ rest ih =>
    rw [applyChain_cons]
    exact (hΦs Φ (List.mem_cons_self)).herm
      (ih fun Φ' h => hΦs Φ' (List.mem_cons_of_mem _ h))

/-- **General-state network data-processing monotonicity**: for ARBITRARY density-matrix states,
the trace distance between an actual state and a target reference does not increase under any chain
of CPTP channel steps (entanglement swaps / LOCC distillation / memory channels). -/
theorem traceDist_applyChain_le {Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)}
    (hΦs : ∀ Φ ∈ Φs, IsChannelStep Φ) {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDist (applyChain Φs ρ) (applyChain Φs σ) ≤ traceDist ρ σ := by
  induction Φs with
  | nil => simp
  | cons Φ rest ih =>
    have hrest : ∀ Φ' ∈ rest, IsChannelStep Φ' := fun Φ' h => hΦs Φ' (List.mem_cons_of_mem _ h)
    rw [applyChain_cons, applyChain_cons]
    refine le_trans ((hΦs Φ (List.mem_cons_self)).contractive
      (applyChain_isHermitian hrest hρ) (applyChain_isHermitian hrest hσ)) ?_
    exact ih hrest

/-- **One additional swap segment does not increase end-to-end distinguishability** (the single-step
specialization): prepending a CPTP segment `Φ` to the chain keeps the trace distance to the target
non-increasing. -/
theorem traceDist_step_le {Φ : Matrix ι ι ℂ → Matrix ι ι ℂ} (hΦ : IsChannelStep Φ)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    traceDist (Φ ρ) (Φ σ) ≤ traceDist ρ σ := hΦ.contractive hρ hσ

end SKEFTHawking.QuantumNetwork
