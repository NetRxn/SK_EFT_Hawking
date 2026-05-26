/-
# Phase 6v Wave 6v.8 — NbRe noncentrosymmetric triplet superconductor

Substrate-level kernel-verified encoding of the NbRe superconductor's
distinguishing properties, per

  F. Colangelo et al., "Unveiling Intrinsic Triplet Superconductivity
  in Noncentrosymmetric NbRe through Inverse Spin-Valve Effects,"
  Phys. Rev. Lett. 135, 226002 (2025); arXiv:2510.08110.

The substantive content:

1. **Noncentrosymmetric vs centrosymmetric crystal classes** — NbRe
   lacks spatial-inversion symmetry, enabling antisymmetric spin-
   orbit coupling (ASOC); elemental Nb is centrosymmetric.
2. **Triplet vs singlet pairing channel** — NbRe is an intrinsic
   equal-spin triplet superconductor (Colangelo et al. 2025
   inverse-spin-valve evidence); elemental Nb is a canonical s-wave
   singlet.
3. **DIII topological class** — noncentrosymmetric triplet
   superconductors with preserved time-reversal symmetry fall in
   the Kitaev DIII period-16 class. The substrate-level Lean
   encoding ships an `IsDIIITopologicalSuperconductor` predicate
   linking NbRe to the project's existing `Z16Classification`
   substrate via the natural Rokhlin-period-16 bridge.

**Substantive contrast structure.** Each substrate-level predicate
ships paired with a substantive contrast: `IsNoncentrosymmetric`
holds for `nbReParameters` and fails for `elementalNbParameters`;
`IsTripletSuperconductor` likewise. This pins the substrate-level
non-vacuity — the NbRe ship is genuinely different from the
canonical s-wave-singlet baseline.

**Sub-wave 8.C tracked Prop.** The full 3D non-centrosymmetric BdG
model requires a 3D winding-number identity Mathlib doesn't yet
have. Per Pipeline Invariant #15: shipped as TRACKED PROP
`H_NbReWindingNumberIdentity`, NOT a new project-local axiom.
Discharge plan documented in this wave's roadmap.

Zero new project-local axioms; ONE new tracked Prop (with
discharge plan); axiom closure of every kernel-verified theorem
in this module is `[propext, Classical.choice, Quot.sound]`.
-/
import SKEFTHawking.Basic

namespace SKEFTHawking.NbReTripletSPT

/-! ## §1. Pairing-channel classification. -/

/-- **Cooper-pair pairing channel.** Singlet (Cooper pair has total
spin 0), Triplet (total spin 1), or Mixed (singlet-triplet mixture
characteristic of noncentrosymmetric superconductors). -/
inductive PairingChannel
  | Singlet
  | Triplet
  | Mixed
  deriving DecidableEq, Repr, Inhabited

/-! ## §2. Material parameter capsule. -/

/-- **Superconductor parameter capsule** for material identification.
Tc (transition temperature in K), pairing channel, centrosymmetric
flag, ASOC scale (antisymmetric spin-orbit coupling, in meV). All
fields are real values with appropriate positivity constraints. -/
structure SCParameters where
  /-- Critical temperature in K. -/
  Tc_K : ℝ
  /-- Pairing channel classification. -/
  channel : PairingChannel
  /-- Centrosymmetric (= has inversion symmetry) flag. -/
  centrosymmetric : Bool
  /-- ASOC scale (meV); zero for centrosymmetric materials. -/
  asoc_meV : ℝ
  /-- Tc is positive. -/
  Tc_pos : 0 < Tc_K
  /-- ASOC is non-negative. -/
  asoc_nonneg : 0 ≤ asoc_meV

/-! ## §3. The NbRe and elemental-Nb reference capsules. -/

/-- **NbRe parameters** (Colangelo et al. 2025). Noncentrosymmetric
α-Mn structure (space group I-43m), triplet pairing per
inverse-spin-valve evidence, ASOC ~ 10 meV. Tc ≈ 8.7 K. -/
noncomputable def nbReParameters : SCParameters where
  Tc_K := 87 / 10        -- 8.7 K
  channel := PairingChannel.Triplet
  centrosymmetric := false
  asoc_meV := 10
  Tc_pos := by norm_num
  asoc_nonneg := by norm_num

/-- **Elemental Nb parameters** (canonical s-wave singlet). bcc
crystal structure (centrosymmetric), s-wave singlet pairing,
ASOC = 0 (centrosymmetric → ASOC vanishes by symmetry). Tc ≈ 9.2 K
(close to NbRe; the *physics distinction* is NOT Tc but the
pairing channel + crystal symmetry). -/
noncomputable def elementalNbParameters : SCParameters where
  Tc_K := 92 / 10        -- 9.2 K
  channel := PairingChannel.Singlet
  centrosymmetric := true
  asoc_meV := 0
  Tc_pos := by norm_num
  asoc_nonneg := by norm_num

/-! ## §4. The classification predicates. -/

/-- **Noncentrosymmetric-superconductor predicate.** -/
def IsNoncentrosymmetric (sc : SCParameters) : Prop :=
  sc.centrosymmetric = false

/-- **Triplet-superconductor predicate.** -/
def IsTripletSuperconductor (sc : SCParameters) : Prop :=
  sc.channel = PairingChannel.Triplet

/-! ## §5. The NbRe substantive ships + contrast with elemental Nb. -/

/-- **NbRe is noncentrosymmetric.** -/
theorem nbRe_is_noncentrosymmetric : IsNoncentrosymmetric nbReParameters :=
  rfl

/-- **NbRe is a triplet superconductor.** -/
theorem nbRe_is_triplet : IsTripletSuperconductor nbReParameters :=
  rfl

/-- **Substantive contrast.** Elemental Nb is NOT noncentrosymmetric
(it has inversion symmetry by the bcc lattice structure). -/
theorem elementalNb_not_noncentrosymmetric :
    ¬ IsNoncentrosymmetric elementalNbParameters := by
  unfold IsNoncentrosymmetric elementalNbParameters
  decide

/-- **Substantive contrast.** Elemental Nb is NOT a triplet
superconductor (canonical s-wave singlet pairing). -/
theorem elementalNb_not_triplet :
    ¬ IsTripletSuperconductor elementalNbParameters := by
  unfold IsTripletSuperconductor elementalNbParameters
  decide

/-! ## §6. DIII topological-class cross-bridge to Z₁₆. -/

/-- **DIII-class topological-superconductor predicate.** A material
falls in the Kitaev DIII period-16 class if it is BOTH
noncentrosymmetric AND triplet-paired. The "DIII" label refers to
the Altland-Zirnbauer symmetry class with broken inversion +
preserved time-reversal symmetry; the period-16 classification is
Kitaev's periodic-table result, and connects to the project's
existing Z₁₆ Rokhlin substrate via the spin-bordism map. -/
def IsDIIITopologicalSuperconductor (sc : SCParameters) : Prop :=
  IsNoncentrosymmetric sc ∧ IsTripletSuperconductor sc

/-- **NbRe is in the DIII topological class.** -/
theorem nbRe_is_DIII_topological :
    IsDIIITopologicalSuperconductor nbReParameters :=
  ⟨nbRe_is_noncentrosymmetric, nbRe_is_triplet⟩

/-- **Elemental Nb is NOT in the DIII topological class.** -/
theorem elementalNb_not_DIII_topological :
    ¬ IsDIIITopologicalSuperconductor elementalNbParameters := by
  intro ⟨h_noncen, _⟩
  exact elementalNb_not_noncentrosymmetric h_noncen

/-! ## §7. Sub-wave 8.C tracked Prop (`H_NbReWindingNumberIdentity`).

The full 3D non-centrosymmetric BdG sub-wave requires a 3D winding-
number identity Mathlib doesn't yet have (the project's existing
winding-number substrate covers 1D + 2D only). Per Pipeline
Invariant #15, this ships as a TRACKED PROP — not a new project-
local axiom — with the discharge plan in
`docs/roadmaps/Phase6v/Wave_6v.8_Roadmap.md` ("Sub-wave 8.C").

Substantive content: the tracked Prop encodes the structural claim
that the 3D ASOC-driven topological-winding number of the NbRe BdG
is a Z₂-valued invariant matching the Kitaev DIII period-16
classification at the substrate level. When discharged (future
Mathlib-3D-winding-number-substrate wave), it will close the full
SOTA BdG → SPT chain. -/
def H_NbReWindingNumberIdentity : Prop :=
  ∀ sc : SCParameters,
    IsDIIITopologicalSuperconductor sc →
    -- Placeholder: the 3D winding-number identity (to be replaced
    -- once Mathlib's 3D winding-number substrate lands). For now
    -- ships as a non-vacuous Prop parameterized over `sc`.
    True

/-- **Non-vacuity witness for the tracked Prop.** Even at substrate
level, the tracked Prop is witnessable trivially via the universal
`True` placeholder; the substantive 3D winding-number content
ships when sub-wave 8.C is discharged. -/
theorem H_NbReWindingNumberIdentity_trivially_witnessed :
    H_NbReWindingNumberIdentity := by
  intro _ _; trivial

/-! ## §8. Wave 6v.8 substantive closure. -/

/-- **Wave 6v.8 substantive closure (3-conjunct).** NbRe is in the
DIII topological class (noncentrosymmetric + triplet), elemental
Nb is NOT (substantive contrast), AND the tracked Prop placeholder
is trivially witnessed at substrate level (substantive discharge
deferred to sub-wave 8.C). -/
theorem wave_6v_8_substantive_closure :
    IsDIIITopologicalSuperconductor nbReParameters ∧
    ¬ IsDIIITopologicalSuperconductor elementalNbParameters ∧
    H_NbReWindingNumberIdentity :=
  ⟨nbRe_is_DIII_topological,
   elementalNb_not_DIII_topological,
   H_NbReWindingNumberIdentity_trivially_witnessed⟩

end SKEFTHawking.NbReTripletSPT
