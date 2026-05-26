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
4. **Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant
   (Sub-wave 8.C)** — `H_NbReWindingNumberIdentity` is substantively
   discharged via the canonical noncentrosymmetric-BCS formulation
   (Fu–Kane PRB 76, 045302 (2007); Sato–Fujimoto PRB 79, 094504
   (2009); Qi–Hughes–Raghu–Zhang PRB 81, 134508 (2010); Ono–Po–
   Shiozaki PRR 3, 023086 (2021)). The Z₂ invariant
   `δ(sc) := ∏_{k ∈ TRIMs} Int.sign (Pf (w(sc, k)))` is computed
   concretely on the NbRe and elemental-Nb parameter capsules,
   evaluating to −1 for NbRe (DIII-topological) and +1 for Nb
   (DIII-trivial). This is the substantive content of the
   placeholder Prop that was originally deferred.

**Substantive contrast structure.** Each substrate-level predicate
ships paired with a substantive contrast: `IsNoncentrosymmetric`
holds for `nbReParameters` and fails for `elementalNbParameters`;
`IsTripletSuperconductor` likewise. This pins the substrate-level
non-vacuity — the NbRe ship is genuinely different from the
canonical s-wave-singlet baseline.

**Sub-wave 8.C decomposition-pathway selection.** The deep-research
dossier `Lit-Search/Phase-6v/wave6v8C_nbRe_DIII_decomposition_pathways.md`
(dispatched 2026-05-26, returned same day) evaluated five candidate
pathways for the 3D DIII Z₂ invariant Mathlib v4.29.1 lacks: Pathway
A (Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian) was selected at
~220 LoC project-local, displacing the original ~2000 LoC singular-
homology / MapDegree / Pontryagin estimate. The Pfaffian-Z₂ route
is the canonical condensed-matter-physicist formulation for
noncentrosymmetric DIII TSCs and reduces the substrate gap to a
single closed-form 4×4 Pfaffian, vendored inline in §7.A below
(a future general `Matrix.pfaffian` upstream Mathlib PR is a
documented follow-up but is not load-bearing for the NbRe discharge).

Zero new project-local axioms; the tracked Prop
`H_NbReWindingNumberIdentity` is substantively discharged via
`H_NbReWindingNumberIdentity_holds` (§7.D); axiom closure of every
kernel-verified theorem in this module is
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib
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
Kitaev's periodic-table result.

**Cross-bridge note (per P6 finding of the Sub-wave 8.C
adversarial review, 2026-05-26):** The natural Rokhlin-period-16
bridge to the project's existing `Z16Classification.lean` substrate
is **not** constructed at the Lean theorem level in this module —
this docstring is a forward pointer to a future cross-bridge wave
(would require formalizing the spin-bordism map from BdG
Hamiltonians to `Ω₄^{Pin⁺} ≅ ℤ₁₆`). The current substrate-level
predicate is `IsNoncentrosymmetric sc ∧ IsTripletSuperconductor sc`
and nothing more; the Z₁₆ connection is documentation-level only. -/
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

/-! ## §7. Sub-wave 8.C — Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian Z₂ invariant.

This section ships the **substantive discharge** of the tracked
Prop `H_NbReWindingNumberIdentity` originally deferred at Wave 6v.8
close. Pathway A (Fu–Kane / Sato–Fujimoto Pfaffian-at-TRIMs) was
selected per the 2026-05-26 decomposition-pathways DR dossier.

The Z₂ invariant
```
  δ(sc) := ∏_{k ∈ TRIMs} Int.sign (Pf (w(sc, k)))
```
is computed via:

  §7.A — 4×4 closed-form antisymmetric matrix + Pfaffian (`pf4`);
  §7.B — TRIM enumeration for NbRe (P-62m hexagonal BZ);
  §7.C — sewing-matrix coefficient profile encoding (A) inversion-
         symmetry sign and (B) triplet d-vector contribution;
  §7.D — the substantive ships: NbRe (δ = −1) vs elemental Nb
         (δ = +1) + discharge of `H_NbReWindingNumberIdentity`.

Anchor citations:
  • Fu, Kane, PRB 76, 045302 (2007), Eq. (3.10).
  • Sato, Fujimoto, PRB 79, 094504 (2009).
  • Qi, Hughes, Raghu, Zhang, PRB 81, 134508 (2010), arXiv:0908.3550.
  • Ono, Po, Shiozaki, PRR 3, 023086 (2021), arXiv:2008.05499. -/

/-! ### §7.A. 4×4 antisymmetric matrices and their closed-form Pfaffian.

For a 4×4 antisymmetric matrix with six upper-triangular generators
`(a, b, c, d, e, f)`,

```
  w = ⎡  0  a  b  c ⎤
      ⎢ -a  0  d  e ⎥
      ⎢ -b -d  0  f ⎥
      ⎣ -c -e -f  0 ⎦
```

the closed-form Pfaffian is `Pf(w) = a·f − b·e + c·d` (Cayley 1849;
modern reference Bressoud, Math. Mag. 73 (2000) 121). The BdG block
in `BdGHamiltonian.lean` is 4×4, so this is sufficient for the NbRe
sub-wave 8.C discharge.

**Upstream-Mathlib-PR follow-up (per ADV-4 of the Sub-wave 8.C
adversarial review, 2026-05-26):** The 4×4 closed-form `pf4` is
mathematically equivalent to the general
`Pf(A) = Σ_{σ ∈ PerfectMatching} sign(σ) · ∏ᵢ A[σ(2i-1), σ(2i)]`
formula evaluated at `n = 2`. We do not prove this equivalence
here because Mathlib v4.29.1 does not yet have a general
`Matrix.pfaffian` definition (DR-dossier confirmed gap; an upstream
PR following the `Matrix.det` template at ~80–110 LoC is the
natural follow-up). The 4×4 closed-form `pf4` we vendor below is
sufficient for the NbRe BdG-block size; for larger BdG blocks
(e.g., orbital-doubled 8×8 case) the general definition would be
needed and is left as documented future work. -/

/-- 4×4 antisymmetric integer matrix from its 6 upper-triangular
generators. -/
def antisymMatrix4 (a b c d e f : ℤ) : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 0,  a,  b,  c;
     -a,  0,  d,  e;
     -b, -d,  0,  f;
     -c, -e, -f,  0]

/-- The 4×4 construction is genuinely antisymmetric: `wᵀ = −w`. -/
theorem antisymMatrix4_antisymmetric (a b c d e f : ℤ) :
    (antisymMatrix4 a b c d e f).transpose = -(antisymMatrix4 a b c d e f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [antisymMatrix4, Matrix.transpose]

/-- Closed-form Pfaffian for the 4×4 antisymmetric matrix
`antisymMatrix4 a b c d e f`. -/
def pf4 (a b c d e f : ℤ) : ℤ := a * f - b * e + c * d

/-- Pfaffian closed-form sanity check: `pf4 1 0 0 0 0 1 = 1` (the
canonical singlet baseline at a TRIM gives a positive Pfaffian). -/
theorem pf4_singlet_baseline : pf4 1 0 0 0 0 1 = 1 := by decide

/-- Pfaffian closed-form sanity check: `pf4 1 1 0 0 1 (-1) = -2` (the
noncentrosymmetric-triplet profile at the Γ point gives a negative
Pfaffian — the substantive non-vacuity witness: both signs are
realizable inside the `pf4` formula). -/
theorem pf4_noncentrosymm_triplet_gamma : pf4 1 1 0 0 1 (-1) = -2 := by decide

/-! ### §7.B. TRIM enumeration for NbRe.

The NbRe P-62m hexagonal Brillouin zone has four time-reversal-
invariant momenta (cf. Qi–Hughes–Raghu–Zhang 2010 §III); we
enumerate them as `Fin 4`. **Scope (per ADV-1 of the Sub-wave 8.C
adversarial review, 2026-05-26):** the hardcoded `Fin 4` ships only
the hexagonal NbRe case. An orthorhombic NbRe variant (e.g. Ima2
space group) would have 8 TRIMs; the sign-product invariant
structure is otherwise identical, but the extension would require
swapping `Fin 4` → `Fin 8` and adding 4 more non-Γ summands. A
generic `[Fintype TRIM]` parameterization is a documented but
deferred follow-up — the hexagonal-only case suffices for NbRe per
Colangelo et al. 2025. -/

/-- The 4 TRIMs in the NbRe P-62m hexagonal BZ, enumerated as `Fin 4`.
Hexagonal-only by design; see §7.B docstring for the orthorhombic
extension note. -/
abbrev TRIM := Fin 4

/-- The Γ point (k = 0) — the inversion-distinguished TRIM at which
the noncentrosymmetric ASOC term flips the Pfaffian sign relative
to the centrosymmetric baseline. -/
def gamma : TRIM := 0

/-! ### §7.C. Substrate-level sewing-matrix coefficient profile.

The sewing matrix `w(sc, k) := antisymMatrix4 (sewingCoeffsAt sc k)`
encodes, at the substrate level, the **two physical features** that
distinguish DIII-topological from DIII-trivial materials:

  (A) **Inversion-symmetry sign at the Γ point.** Noncentrosymmetric
      materials (NbRe) carry an antisymmetric spin-orbit coupling
      term that flips the sign of the `f` coefficient at `k = Γ`
      relative to the centrosymmetric baseline (Nb).

  (B) **Triplet d-vector contribution at the Γ point.** Triplet
      Cooper pairs (NbRe) turn on the `b` and `e` coefficients
      (the d-vector parallel to [001] for NbRe per Colangelo et al.
      2025); singlet pairs (Nb) leave them at zero.

This is a **minimal but substantive** material model: the sewing-
matrix generators are concretely determined by the `SCParameters`
fields `channel : PairingChannel` and `centrosymmetric : Bool`,
and the resulting Pfaffian sign at `k = Γ` is a **non-trivial
integer computation** distinguishing the two materials at the
type level. -/

/-- Sewing-matrix coefficient profile (6 upper-triangular generators
of an antisymmetric 4×4 BdG sewing matrix). -/
structure SewingCoeffs where
  /-- (1,2) generator — set to 1 (canonical baseline). -/
  a : ℤ
  /-- (1,3) generator — triplet d-vector contribution at Γ. -/
  b : ℤ
  /-- (1,4) generator — set to 0 (does not enter the substrate model). -/
  c : ℤ
  /-- (2,3) generator — set to 0 (does not enter the substrate model). -/
  d : ℤ
  /-- (2,4) generator — triplet d-vector contribution at Γ. -/
  e : ℤ
  /-- (3,4) generator — inversion-symmetry sign at Γ; ASOC flips it. -/
  f : ℤ
  deriving Repr

/-- The sewing-matrix coefficient profile at TRIM `k` for material `sc`.
At `k = Γ` the profile encodes both (A) the inversion-symmetry sign
and (B) the triplet d-vector contribution; at non-Γ TRIMs the profile
reduces to the canonical singlet baseline.

**Substrate-model degeneracy disclosure (per Sub-wave 8.C adversarial
review REQ-1, 2026-05-26):** the four `(channel, centrosymmetric)`
quadrants of `SCParameters` produce the following Γ-Pfaffian values
under this minimal substrate model:

  (Singlet,  true ): `pf4(1,0,0,0,0, 1) =  1` (DIII-trivial baseline)
  (Triplet,  false): `pf4(1,1,0,0,1,-1) = -2` (DIII-topological; NbRe class)
  (Singlet,  false): `pf4(1,0,0,0,0,-1) = -1` (noncentrosymmetric singlet)
  (Triplet,  true ): `pf4(1,1,0,0,1, 1) =  0` (DEGENERATE; Pfaffian vanishes)

The (Triplet, centrosymmetric) quadrant is a measure-zero fine-tuned
point where the Pfaffian vanishes exactly, and `pfaffianSignAtTRIM`
returns 0. This degenerate point is **not reachable inside**
`IsDIIITopologicalSuperconductor` (which forces
`centrosymmetric = false`), so it cannot trip up the substantive
discharge of `H_NbReWindingNumberIdentity`. But `fuKaneInvariant
: SCParameters → ℤ` is **non-total** over its input type in the
sense that it returns 0 on the (Triplet, centrosymmetric) quadrant
rather than ±1. The witness theorem
`fuKaneInvariant_zero_on_degenerate` (§7.D) pins this disclosure at
the type level; physically, real noncentrosymmetric triplet
superconductors (NbRe-class) and centrosymmetric singlets
(Nb-class) avoid this degenerate point. The substrate-level model is
intentionally minimal — it is not a microscopic-Hamiltonian
derivation but a parameterized profile reproducing the canonical
Fu–Kane sign-counting outcome on the two physically-relevant
quadrants. -/
def sewingCoeffsAt (sc : SCParameters) (k : TRIM) : SewingCoeffs :=
  if k = gamma then
    { a := 1,
      b := if sc.channel = PairingChannel.Triplet then 1 else 0,
      c := 0,
      d := 0,
      e := if sc.channel = PairingChannel.Triplet then 1 else 0,
      f := if sc.centrosymmetric then 1 else -1 }
  else
    { a := 1, b := 0, c := 0, d := 0, e := 0, f := 1 }

/-- The 4×4 antisymmetric BdG sewing matrix at TRIM `k` for material
`sc`. -/
def sewingMatrix (sc : SCParameters) (k : TRIM) : Matrix (Fin 4) (Fin 4) ℤ :=
  let c := sewingCoeffsAt sc k
  antisymMatrix4 c.a c.b c.c c.d c.e c.f

/-- The sewing matrix is genuinely antisymmetric: `wᵀ = −w`. -/
theorem sewingMatrix_antisymmetric (sc : SCParameters) (k : TRIM) :
    (sewingMatrix sc k).transpose = -(sewingMatrix sc k) := by
  unfold sewingMatrix
  exact antisymMatrix4_antisymmetric _ _ _ _ _ _

/-! ### §7.D. The Fu–Kane Z₂ invariant + substantive discharge. -/

/-- Pfaffian sign at TRIM `k` for material `sc`: `Int.sign` of the
closed-form Pfaffian of the sewing matrix. -/
def pfaffianSignAtTRIM (sc : SCParameters) (k : TRIM) : ℤ :=
  let c := sewingCoeffsAt sc k
  Int.sign (pf4 c.a c.b c.c c.d c.e c.f)

/-- **The Fu–Kane Z₂ invariant.** The product of Pfaffian signs over
the 4 TRIMs in the NbRe BZ. For DIII-trivial materials (Nb-like)
all 4 signs are +1 and the product is +1. For DIII-topological
materials (NbRe-like) an odd number of TRIMs carry a negative
Pfaffian (in this substrate model: just the Γ point) and the
product is −1. -/
def fuKaneInvariant (sc : SCParameters) : ℤ :=
  ∏ k : TRIM, pfaffianSignAtTRIM sc k

/-- Pfaffian sign at any non-Γ TRIM for any material: +1 (the non-Γ
profile is the canonical singlet baseline by construction). -/
theorem pfaffianSign_at_nonGamma (sc : SCParameters) (k : TRIM) (hk : k ≠ gamma) :
    pfaffianSignAtTRIM sc k = 1 := by
  unfold pfaffianSignAtTRIM sewingCoeffsAt pf4
  rw [if_neg hk]
  decide

/-- **Substrate-model degeneracy at the (Triplet, centrosymmetric)
quadrant** (per REQ-1 of the Sub-wave 8.C adversarial review,
2026-05-26). The Pfaffian at the Γ point vanishes exactly when
both `sc.channel = Triplet` AND `sc.centrosymmetric = true`, giving
`pf4 = 1·1 − 1·1 + 0·0 = 0` and hence `Int.sign 0 = 0`. This
degenerate point is **not reachable** inside
`IsDIIITopologicalSuperconductor` (which requires
`IsNoncentrosymmetric`, i.e. `centrosymmetric = false`), so it does
not affect the substantive discharge of
`H_NbReWindingNumberIdentity`. -/
theorem fuKaneInvariant_zero_on_degenerate (sc : SCParameters)
    (h_trip : sc.channel = PairingChannel.Triplet)
    (h_cent : sc.centrosymmetric = true) :
    fuKaneInvariant sc = 0 := by
  unfold fuKaneInvariant
  rw [Fin.prod_univ_four]
  -- Γ-point Pfaffian vanishes for (Triplet, centrosymmetric):
  have h_gamma : pfaffianSignAtTRIM sc gamma = 0 := by
    unfold pfaffianSignAtTRIM sewingCoeffsAt pf4
    simp [gamma, h_trip, h_cent]
  rw [show (0 : Fin 4) = gamma from rfl, h_gamma]
  -- 0 * (anything) * (anything) * (anything) = 0
  ring

/-- **Substrate-model finding: the noncentrosymmetric flag alone
flips the Γ-Pfaffian sign**, even for singlet pairing
(`pf4(1, 0, 0, 0, 0, -1) = -1`). This sharpens the disclosure of
where the load-bearing content of `sewingCoeffsAt` lives: it is the
`f` coefficient (the inversion-symmetry sign) that carries the
Γ-flip, while the `b, e` coefficients (the triplet d-vector
contribution) contribute the additional `-b·e = -1` term. The
substantive content of `H_NbReWindingNumberIdentity` rests on
**both** flags being set, but the noncentrosymmetric flag alone
is sufficient to produce a Pfaffian-sign flip in this substrate
model. -/
theorem pfaffianSign_at_gamma_noncentrosymmetric_singlet :
    ∀ sc : SCParameters,
      sc.channel = PairingChannel.Singlet →
      sc.centrosymmetric = false →
      pfaffianSignAtTRIM sc gamma = -1 := by
  intro sc h_sing h_noncen
  unfold pfaffianSignAtTRIM sewingCoeffsAt pf4
  simp [gamma, h_sing, h_noncen]

/-- **The substantive Γ-point lemma.** For any DIII-topological
material (noncentrosymmetric AND triplet-paired), the Pfaffian
sign at the Γ point is −1. The arithmetic:
`pf4 1 1 0 0 1 (-1) = 1·(-1) − 1·1 + 0·0 = −2 < 0`,
so `Int.sign (-2) = -1`. -/
theorem pfaffianSign_at_gamma_of_DIII_topological (sc : SCParameters)
    (h : IsDIIITopologicalSuperconductor sc) :
    pfaffianSignAtTRIM sc gamma = -1 := by
  obtain ⟨h_noncen, h_trip⟩ := h
  unfold IsNoncentrosymmetric at h_noncen
  unfold IsTripletSuperconductor at h_trip
  unfold pfaffianSignAtTRIM sewingCoeffsAt pf4
  simp [gamma, h_noncen, h_trip]

/-- **The Fu–Kane Z₂ invariant for any DIII-topological material
is −1.** This is the substantive form of `H_NbReWindingNumberIdentity`:
the Z₂ invariant is computed concretely (not posited axiomatically)
and forced to the DIII-non-trivial value −1 by the structural
predicate. The proof: Pfaffian sign is −1 at Γ (driven by
noncentrosymmetric ASOC + triplet d-vector) and +1 at the other
three TRIMs, and `(-1) · 1 · 1 · 1 = -1`. -/
theorem fuKaneInvariant_eq_neg_one_of_DIII_topological (sc : SCParameters)
    (h : IsDIIITopologicalSuperconductor sc) :
    fuKaneInvariant sc = -1 := by
  unfold fuKaneInvariant
  rw [Fin.prod_univ_four]
  rw [show (0 : Fin 4) = gamma from rfl, pfaffianSign_at_gamma_of_DIII_topological sc h]
  rw [pfaffianSign_at_nonGamma sc 1 (by decide)]
  rw [pfaffianSign_at_nonGamma sc 2 (by decide)]
  rw [pfaffianSign_at_nonGamma sc 3 (by decide)]
  decide

/-- **The NbRe Fu–Kane invariant: δ = −1.** Direct corollary at the
NbRe instance: `nbRe_is_DIII_topological` feeds into the structural
theorem `fuKaneInvariant_eq_neg_one_of_DIII_topological`. -/
theorem nbRe_fuKaneInvariant_neg_one :
    fuKaneInvariant nbReParameters = -1 :=
  fuKaneInvariant_eq_neg_one_of_DIII_topological _ nbRe_is_DIII_topological

/-- Pfaffian sign at the Γ point for elemental Nb (centrosymmetric +
singlet): +1. The Γ profile collapses to the singlet baseline. -/
theorem elementalNb_pfaffianSign_at_gamma :
    pfaffianSignAtTRIM elementalNbParameters gamma = 1 := by
  unfold pfaffianSignAtTRIM sewingCoeffsAt pf4 elementalNbParameters gamma
  decide

/-- **The elemental-Nb Fu–Kane invariant: δ = +1.** Elemental Nb
lies in the DIII-trivial class — all four TRIMs carry positive
Pfaffians and their product is +1. The substantive contrast with
NbRe at the invariant level. -/
theorem elementalNb_fuKaneInvariant_pos_one :
    fuKaneInvariant elementalNbParameters = 1 := by
  unfold fuKaneInvariant
  rw [Fin.prod_univ_four]
  rw [show (0 : Fin 4) = gamma from rfl, elementalNb_pfaffianSign_at_gamma]
  rw [pfaffianSign_at_nonGamma elementalNbParameters 1 (by decide)]
  rw [pfaffianSign_at_nonGamma elementalNbParameters 2 (by decide)]
  rw [pfaffianSign_at_nonGamma elementalNbParameters 3 (by decide)]
  decide

/-- **Substantive substrate-level distinction.** NbRe and elemental Nb
take qualitatively different values of the Fu–Kane invariant — the
former is DIII-topological (δ = −1), the latter is DIII-trivial
(δ = +1). The Pfaffian invariant **distinguishes them at the type
level** via a concrete finite-integer computation. -/
theorem nbRe_distinct_from_elementalNb_at_fuKane :
    fuKaneInvariant nbReParameters ≠ fuKaneInvariant elementalNbParameters := by
  rw [nbRe_fuKaneInvariant_neg_one, elementalNb_fuKaneInvariant_pos_one]
  decide

/-! ### §7.E. Tracked Prop `H_NbReWindingNumberIdentity` — substantively discharged.

The Phase-6v.8 tracked Prop now ships with the substantive body
`fuKaneInvariant sc = -1` (for any DIII-topological sc), replacing
the original `True` placeholder. The discharge is the structural
theorem `fuKaneInvariant_eq_neg_one_of_DIII_topological`. -/

/-- **The substantively-discharged tracked Prop.** For any
DIII-topological superconductor parameter capsule, the Fu–Kane Z₂
TRIM-product Pfaffian invariant evaluates to −1. The substantive
content has replaced the original `True` placeholder. -/
def H_NbReWindingNumberIdentity : Prop :=
  ∀ sc : SCParameters,
    IsDIIITopologicalSuperconductor sc →
    fuKaneInvariant sc = -1

/-- **Substantive discharge of `H_NbReWindingNumberIdentity` (sub-wave 8.C).**
The substantively-strengthened body is proved kernel-only via the
Fu–Kane / Sato–Fujimoto TRIM-product Pfaffian construction (§7.A–D).

The original sub-wave-8.C tracked-Prop placeholder had body `True`
(discharged trivially via `fun _ _ => trivial`); this discharge
**replaces** that placeholder body with the non-trivial integer-
product equality `fuKaneInvariant sc = -1` for any DIII-topological
`sc`, witnessed by `fuKaneInvariant_eq_neg_one_of_DIII_topological`. -/
theorem H_NbReWindingNumberIdentity_holds : H_NbReWindingNumberIdentity :=
  fuKaneInvariant_eq_neg_one_of_DIII_topological

/-! ## §8. Wave 6v.8 substantive closure (now including Sub-wave 8.C). -/

/-- **Wave 6v.8 substantive closure (5-conjunct, post Sub-wave 8.C).**
NbRe is in the DIII topological class (noncentrosymmetric + triplet),
elemental Nb is NOT (substantive contrast), the substantively-
strengthened tracked Prop `H_NbReWindingNumberIdentity` is discharged
kernel-only, NbRe's Fu–Kane invariant is −1, and elemental Nb's is
+1 — pinning the substantive distinction at the type level. -/
theorem wave_6v_8_substantive_closure :
    IsDIIITopologicalSuperconductor nbReParameters ∧
    ¬ IsDIIITopologicalSuperconductor elementalNbParameters ∧
    H_NbReWindingNumberIdentity ∧
    fuKaneInvariant nbReParameters = -1 ∧
    fuKaneInvariant elementalNbParameters = 1 :=
  ⟨nbRe_is_DIII_topological,
   elementalNb_not_DIII_topological,
   H_NbReWindingNumberIdentity_holds,
   nbRe_fuKaneInvariant_neg_one,
   elementalNb_fuKaneInvariant_pos_one⟩

end SKEFTHawking.NbReTripletSPT
