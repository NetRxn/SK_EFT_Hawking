import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact

/-!
# Diamond-norm network error budget (Phase 6AH, Wave 6AH.3)

The worst-case (diamond) analogue of the trace-distance chain bound. Channel composition in the
Kraus representation `composeKraus L K` (Kraus operators `Lⱼ Kᵢ`) realises `Φ_L ∘ Φ_K`, and the
diamond distance is contractive under composition with a fixed CPTP channel. Telescoping gives the
N-segment **error budget**: the worst-case end-to-end error of a composed channel network is bounded
by the sum of the per-segment diamond errors.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ}

/-- **Channel composition in the Kraus representation.** The Kraus operators of `Φ_L ∘ Φ_K` are the
products `Lⱼ Kᵢ` (indexed by `Fin b × Fin a ≃ Fin (b·a)`). -/
noncomputable def composeKraus (L : Fin b → Matrix ι ι ℂ) (K : Fin a → Matrix ι ι ℂ) :
    Fin (b * a) → Matrix ι ι ℂ :=
  fun idx => L (finProdFinEquiv.symm idx).1 * K (finProdFinEquiv.symm idx).2

/-- **`composeKraus` realises channel composition:** `krausMap (L∘K) = krausMap L ∘ krausMap K`. -/
theorem krausMap_composeKraus (L : Fin b → Matrix ι ι ℂ) (K : Fin a → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) :
    krausMap (composeKraus L K) ρ = krausMap L (krausMap K ρ) := by
  unfold krausMap composeKraus
  rw [finProdFinEquiv.symm.sum_comp
    (fun p : Fin b × Fin a => L p.1 * K p.2 * ρ * (L p.1 * K p.2)ᴴ), Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul]; noncomm_ring

/-- The composition of two CPTP channels is CPTP. -/
theorem isKrausChannel_composeKraus {L : Fin b → Matrix ι ι ℂ} {K : Fin a → Matrix ι ι ℂ}
    (hL : IsKrausChannel L) (hK : IsKrausChannel K) : IsKrausChannel (composeKraus L K) := by
  unfold IsKrausChannel composeKraus at *
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin b × Fin a => (L p.1 * K p.2)ᴴ * (L p.1 * K p.2)),
    Fintype.sum_prod_type]
  have hcol : ∀ i : Fin a, ∑ j, (L j * K i)ᴴ * (L j * K i) = (K i)ᴴ * (K i) := by
    intro i
    simp_rw [Matrix.conjTranspose_mul, show ∀ j, (K i)ᴴ * (L j)ᴴ * (L j * K i)
      = (K i)ᴴ * ((L j)ᴴ * L j) * K i from fun j => by simp only [Matrix.mul_assoc]]
    rw [← Finset.sum_mul, ← Matrix.mul_sum, hL, Matrix.mul_one]
  rw [Finset.sum_comm]; simp_rw [hcol]; exact hK

end SKEFTHawking.QuantumNetwork
