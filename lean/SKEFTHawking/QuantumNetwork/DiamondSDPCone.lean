import SKEFTHawking.QuantumNetwork.HermitianCarrier
import SKEFTHawking.QuantumNetwork.DiamondSDPAttainment
import Mathlib.Analysis.Convex.Cone.Dual

/-!
# The PSD proper cone on the diamond-SDP carrier (Phase 6AI — `≥` direction, cone infrastructure)

With the topology-diamond linchpin discharged (`HermCarrier`), the positive-semidefinite elements
form a genuine `ProperCone ℝ (HermCarrier ι)`: a closed, pointed (`ℝ≥0`-)cone. This is the object the
conic strong-duality engine (`ProperCone.hyperplane_separation`,
`geometric_hahn_banach_compact_closed`) consumes to close the zero-gap `≥` direction of
`diamondDist_eq_choiSDP`.

* `toMatₗ` / `continuous_toMat` — the carrier injects continuously and ℝ-linearly into `Matrix ι ι ℂ`
  (finite-dimensional ⇒ continuous), so the PSD set is closed in the carrier topology.
* `psdCarrierCone` / `psdProperCone` — the PSD `PointedCone` and its upgrade to a `ProperCone`.
* `convex_psdSet` — convexity of the PSD set (for the geometric-Hahn–Banach separation).

The route is geometric Hahn–Banach (route a), *not* `relative_hyperplane_separation` (route b):
`ProperCone.map` is the topological *closure* of the linear image, and cone images need a separate
closedness obligation; route (a) separates the already-closed PSD-feasible set from a compact set and
forms no image cone.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

namespace HermCarrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The carrier as an ℝ-linear map into `Matrix ι ι ℂ` (the underlying self-adjoint matrix). -/
noncomputable def toMatₗ : HermCarrier ι →ₗ[ℝ] Matrix ι ι ℂ where
  toFun A := A.toSA.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `A ↦ A.toSA.1` is continuous (a linear map out of a finite-dimensional space). -/
theorem continuous_toMat : Continuous (fun A : HermCarrier ι => A.toSA.1) :=
  toMatₗ.continuous_of_finiteDimensional

/-- **The positive-semidefinite `PointedCone`** on the carrier: closed under addition, nonnegative
real scaling, and containing `0`. -/
def psdCarrierCone : PointedCone ℝ (HermCarrier ι) where
  carrier := {A | A.toSA.1.PosSemidef}
  add_mem' := by rintro A B (hA : A.toSA.1.PosSemidef) (hB : B.toSA.1.PosSemidef); exact hA.add hB
  zero_mem' := by
    show (0 : HermCarrier ι).toSA.1.PosSemidef
    rw [zero_toSA]; simpa using (PosSemidef.zero : (0 : Matrix ι ι ℂ).PosSemidef)
  smul_mem' := by
    rintro c A (hA : A.toSA.1.PosSemidef)
    show ((c • A).toSA.1).PosSemidef
    have h : (c • A).toSA.1 = ((c : ℝ) : ℂ) • A.toSA.1 := by
      rw [← Nonneg.coe_smul c A, smul_toSA, selfAdjoint.val_smul]
      ext i j; simp [Matrix.smul_apply, Complex.real_smul]
    rw [h]; exact hA.smul (by rw [Complex.zero_le_real]; exact c.2)

/-- The PSD set is closed in the carrier topology (preimage of the closed matrix PSD set under the
continuous injection `toMat`). -/
theorem isClosed_psdCarrierCone :
    IsClosed ((psdCarrierCone : PointedCone ℝ (HermCarrier ι)) : Set (HermCarrier ι)) :=
  isClosed_posSemidef.preimage continuous_toMat

/-- **The positive-semidefinite `ProperCone ℝ (HermCarrier ι)`** — the cone the conic strong-duality
engine consumes. -/
noncomputable def psdProperCone : ProperCone ℝ (HermCarrier ι) :=
  ⟨psdCarrierCone, isClosed_psdCarrierCone⟩

@[simp] theorem mem_psdProperCone {A : HermCarrier ι} :
    A ∈ psdProperCone ↔ A.toSA.1.PosSemidef := Iff.rfl

/-- The PSD set is convex (for the geometric-Hahn–Banach separation). -/
theorem convex_psdSet : Convex ℝ {A : HermCarrier ι | A.toSA.1.PosSemidef} := by
  intro A hA B hB a b ha hb _
  show ((a • A + b • B).toSA.1).PosSemidef
  rw [add_toSA, smul_toSA, smul_toSA, AddSubgroup.coe_add, selfAdjoint.val_smul,
    selfAdjoint.val_smul]
  have e1 : a • A.toSA.1 = ((a : ℂ)) • A.toSA.1 := by
    ext i j; simp [Matrix.smul_apply, Complex.real_smul]
  have e2 : b • B.toSA.1 = ((b : ℂ)) • B.toSA.1 := by
    ext i j; simp [Matrix.smul_apply, Complex.real_smul]
  rw [e1, e2]
  exact (hA.smul (by rw [Complex.zero_le_real]; exact ha)).add
    (hB.smul (by rw [Complex.zero_le_real]; exact hb))

end HermCarrier

open scoped Matrix.Norms.L2Operator

/-- **Primal value as a Choi pairing.** For ANY input density `ρ`, the output trace distance equals
the real-trace pairing of the Choi difference `C` with the contraction of the optimal output
projector `P = posProj T` (`T` = output difference): `traceDist(Φ₁ρ, Φ₂ρ) = Re tr(C · M(P,ρ))`.
This is the head of the weak-duality chain (`diamondDist_le_dual_witness`) extracted as a reusable
identity — the bridge from the diamond distance to the Choi/`choiContraction` quantities the
strong-duality separation argument pairs against. -/
theorem traceDist_eq_re_trace_choiContraction_posProj {m n : ℕ} [NeZero n]
    {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ} (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂)
    (ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ)
    (hTh : (krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ).IsHermitian) :
    traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ)
      = ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) *
          choiContraction (posProj hTh) ρ).trace.re := by
  have hT0 : (krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ).trace.re = 0 := by
    rw [Matrix.trace_sub, trace_krausMap (isKrausChannel_tensorKraus hK₁),
      trace_krausMap (isKrausChannel_tensorKraus hK₂), sub_self, Complex.zero_re]
  have hchain : eigPosSum hTh
      = ((choiMatrix (krausMap K₁) - choiMatrix (krausMap K₂)) *
          choiContraction (posProj hTh) ρ).trace.re := by
    rw [eigPosSum_eq_re_trace_posProj]
    show (((posProj hTh) *
        (krausMap (tensorKraus K₁) ρ - krausMap (tensorKraus K₂) ρ)).trace).re = _
    rw [trace_mul_krausMap_sub]
  unfold traceDist
  rw [traceNorm_hermitian_eq hTh, hT0, sub_zero,
    show (1 : ℝ) / 2 * (2 * eigPosSum hTh) = eigPosSum hTh by ring]
  exact hchain

end SKEFTHawking.QuantumNetwork
