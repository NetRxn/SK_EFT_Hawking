import Mathlib
import SKEFTHawking.TopologicalBand.PrincipalBranch
import SKEFTHawking.TopologicalBand.FiniteTorus
import SKEFTHawking.TopologicalBand.FHSLatticeGauge

/-!
# D11-FHS Q4 (Lane A) — the sampled-band-frame → link adapter

The model-independent adapter from a **sampled band frame** on the finite torus to a `Circle`-valued
`LinkField`, feeding the Q2 `latticeChern`. Following the packet's admissibility design (and the
audit's §3.2/§3.3 corrections), we do **not** construct a global continuous eigenvector: a frame is
an arbitrary pointwise assignment of normalized states with an **explicit nonzero nearest-neighbor
overlap admissibility field** (a gap does not imply nonzero overlaps — §3.3). The link is the phase
of the overlap, `Uμ(k) = ⟨u(k), u(k+êμ)⟩ / |⟨u(k), u(k+êμ)⟩|`.

The headline is that the FHS integrality and gauge invariance of Q2 are inherited **for free**:
`blochLatticeChern F := latticeChern (linkOfFrame F)` is an exact integer, and it is invariant under
pointwise `Circle` rephasings of the frame (which induce the Q2 vertex gauge action).

This file is finite/data-level. No spectral law is used here (Lane A is model-independent); the
genuine `BlochBundle` spectral connection is in `BlochFHS.lean`.
-/

open Complex Real
open scoped BigOperators

namespace SKEFTHawking.TopologicalBand

/-! ### Phase normalization `ℂ → Circle` -/

/-- Phase normalization `phase z = z / |z|` for `z ≠ 0`, realised as the unit-circle element
`Circle.exp (arg z)`. -/
noncomputable def phase (z : ℂ) : Circle := Circle.exp (Complex.arg z)

@[simp] theorem phase_coe_circle (x : Circle) : phase (x : ℂ) = x := by
  unfold phase; exact Circle.exp_arg x

/-- `phase` is multiplicative on nonzero inputs (the `2π` branch corrections wash out under
`Circle.exp`'s periodicity). -/
theorem phase_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    phase (a * b) = phase a * phase b := by
  unfold phase
  rw [← Circle.exp_add]
  have h := arg_mul_branch_correction a b ha hb
  set n : ℤ := branchIndex (Complex.arg a + Complex.arg b) with hn
  have harg : Complex.arg (a * b)
      = (Complex.arg a + Complex.arg b) + ((-n : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast; linarith [h]
  rw [harg, Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- Complex conjugation sends a `Circle` element to its inverse. -/
theorem conj_coe_circle (x : Circle) : (starRingEnd ℂ) (x : ℂ) = ((x⁻¹ : Circle) : ℂ) := by
  rw [Circle.coe_inv]
  have h : (x : ℂ) * (starRingEnd ℂ) (x : ℂ) = 1 := by
    rw [Complex.mul_conj]; norm_cast; simp [Complex.normSq_eq_norm_sq]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

/-! ### Frame overlap (the Hermitian inner product on sampled states) -/

/-- The Hermitian overlap `⟨u, v⟩ = ∑ᵢ conj(uᵢ) vᵢ`. -/
noncomputable def frameOverlap {n : ℕ} (u v : Fin n → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (u i) * v i

theorem frameOverlap_smul_left {n : ℕ} (c : ℂ) (u v : Fin n → ℂ) :
    frameOverlap (fun i => c * u i) v = (starRingEnd ℂ) c * frameOverlap u v := by
  unfold frameOverlap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul]; ring

theorem frameOverlap_smul_right {n : ℕ} (c : ℂ) (u v : Fin n → ℂ) :
    frameOverlap u (fun i => c * v i) = c * frameOverlap u v := by
  unfold frameOverlap
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-! ### Admissible band frame and the induced link field -/

/-- A **sampled admissible band frame**: pointwise normalized states on the finite torus, with an
**explicit** nonzero nearest-neighbor overlap field (the admissibility that makes the phase link
well-defined — an honest field, not a gap-derived consequence; audit §3.3). -/
structure AdmissibleBandFrame (N₁ N₂ n : ℕ) where
  state : Torus N₁ N₂ → (Fin n → ℂ)
  normalized : ∀ k, frameOverlap (state k) (state k) = 1
  overlap_ne : ∀ (μ : Fin 2) (k : Torus N₁ N₂),
    frameOverlap (state k) (state (shift N₁ N₂ μ k)) ≠ 0

variable {N₁ N₂ n : ℕ}

/-- The `Circle`-valued link field induced by a frame:
`Uμ(k) = phase ⟨u(k), u(k+êμ)⟩ = ⟨u(k), u(k+êμ)⟩ / |⟨u(k), u(k+êμ)⟩|`. -/
noncomputable def linkOfFrame (F : AdmissibleBandFrame N₁ N₂ n) : LinkField N₁ N₂ :=
  fun μ k => phase (frameOverlap (F.state k) (F.state (shift N₁ N₂ μ k)))

/-- The FHS lattice Chern number of a sampled band frame. -/
noncomputable def blochLatticeChern [NeZero N₁] [NeZero N₂]
    (F : AdmissibleBandFrame N₁ N₂ n) : ℤ :=
  latticeChern N₁ N₂ (linkOfFrame F)

/-- **Inherited integrality (headline).** The band-frame FHS field strengths sum to `2π` times the
integer `blochLatticeChern` — the Q2 integrality theorem, for free. -/
theorem blochLatticeChern_integrality [NeZero N₁] [NeZero N₂]
    (F : AdmissibleBandFrame N₁ N₂ n) :
    ∑ k, plaquetteArg N₁ N₂ (linkOfFrame F) k = 2 * Real.pi * (blochLatticeChern F : ℝ) :=
  sum_plaquetteArg_eq_two_pi_mul_latticeChern N₁ N₂ (linkOfFrame F)

/-! ### Pointwise `Circle` rephasing induces the vertex gauge action -/

/-- Rephasing a frame pointwise by `φ : Torus → Circle`: `u(k) ↦ φ(k) · u(k)`. -/
noncomputable def rephase (φ : Torus N₁ N₂ → Circle) (F : AdmissibleBandFrame N₁ N₂ n) :
    AdmissibleBandFrame N₁ N₂ n where
  state := fun k i => (φ k : ℂ) * F.state k i
  normalized := by
    intro k
    rw [frameOverlap_smul_left, frameOverlap_smul_right, F.normalized, mul_one,
      conj_coe_circle, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  overlap_ne := by
    intro μ k
    rw [frameOverlap_smul_left, frameOverlap_smul_right]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ (F.overlap_ne μ k))
    · rw [conj_coe_circle]; exact Circle.coe_ne_zero _
    · exact Circle.coe_ne_zero _

/-- **State-gauge covariance (headline mechanism).** A pointwise `Circle` rephasing of the frame
induces exactly the Q2 vertex gauge transformation on the induced links. -/
theorem linkOfFrame_rephase (φ : Torus N₁ N₂ → Circle) (F : AdmissibleBandFrame N₁ N₂ n) :
    linkOfFrame (rephase φ F) = gaugeTransform N₁ N₂ φ (linkOfFrame F) := by
  funext μ k
  show phase (frameOverlap (fun i => (φ k : ℂ) * F.state k i)
      (fun i => (φ (shift N₁ N₂ μ k) : ℂ) * F.state (shift N₁ N₂ μ k) i))
    = (φ k)⁻¹ * phase (frameOverlap (F.state k) (F.state (shift N₁ N₂ μ k)))
      * φ (shift N₁ N₂ μ k)
  rw [frameOverlap_smul_left, frameOverlap_smul_right]
  have hO := F.overlap_ne μ k
  have hc : (starRingEnd ℂ) (φ k : ℂ) ≠ 0 := by rw [conj_coe_circle]; exact Circle.coe_ne_zero _
  have hφ : (φ (shift N₁ N₂ μ k) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [phase_mul _ _ hc (mul_ne_zero hφ hO), phase_mul _ _ hφ hO, conj_coe_circle,
    phase_coe_circle, phase_coe_circle]
  -- goal: (φ k)⁻¹ * (φ (shift μ k) * phase O) = (φ k)⁻¹ * phase O * φ (shift μ k)
  rw [mul_assoc]
  congr 1
  exact mul_comm _ _

/-- **Inherited gauge invariance (headline).** The band-frame lattice Chern number is invariant
under pointwise `Circle` rephasing of the frame — the Q2 gauge invariance, for free. -/
theorem blochLatticeChern_rephase [NeZero N₁] [NeZero N₂]
    (φ : Torus N₁ N₂ → Circle) (F : AdmissibleBandFrame N₁ N₂ n) :
    blochLatticeChern (rephase φ F) = blochLatticeChern F := by
  unfold blochLatticeChern
  rw [linkOfFrame_rephase]
  exact latticeChern_gaugeInvariant N₁ N₂ φ (linkOfFrame F)

end SKEFTHawking.TopologicalBand
