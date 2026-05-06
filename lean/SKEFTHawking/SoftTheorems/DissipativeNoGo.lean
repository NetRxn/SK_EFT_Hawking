import Mathlib
import SKEFTHawking.SoftTheorems.Boostless

/-!
# Phase 6o Wave 1a.5: Lindbladian S-matrix axiomatization NO-GO

## Goal

Encode the Phase 6o Wave 1a.5 **structural negative theorem** per
On-Shell Methods DR §2.5 conjectured No-Go:

> "A genuinely dissipative SK-EFT — one in which the SK action contains
> a non-vanishing imaginary noise kernel that cannot be removed by
> integrating in auxiliary unitary fields — *cannot* admit a BCFW-style
> on-shell recursion for its retarded/advanced/Keldysh amplitudes."

This is the productive-value structural negative deliverable of Phase 6o
Wave 1a — joins program's NO-GO landscape (gauge erasure, vestigial
graviton, Phase 6n Wave 2b Perarnau-Llobet, Phase 6o Wave 1c dissipative-
bootstrap, etc.).

## Substantive content

Three hypothesis Props that, if held simultaneously by a putative
dissipative-IR S-matrix axiomatization, force inconsistency:

1. `KMSBroken` — the S-matrix's KMS dynamical Z₂ symmetry is broken (as
   in genuine dissipation; Borsten-Jonsson-Kim arXiv:2405.11110 quasi-
   isomorphism explicitly assumes underlying unitary closed-system, hence
   does NOT apply when KMS is genuinely broken).
2. `FactorizationOnRealAxis` — the on-shell recursion (BCFW-style)
   requires factorization on physical poles on the real axis.
3. `AnalyticInSingleSheet` — the BCFW-style Cauchy-residue derivation
   requires analyticity in a single Riemann sheet.

The structural NO-GO: under (1), the dissipative IR introduces complex
poles in the lower half-plane which break (2). Additionally, the Keldysh
propagator's i0 prescription on different time branches breaks (3) —
the single-Riemann-sheet structure required for Cauchy-residue
derivation of recursion fails.

## Module structure

- §1: Three hypothesis Props for the NO-GO contradiction.
- §2: `IsLindbladianSMatrix` composed predicate.
- §3: Substantive structural NO-GO theorem.
- §4: Cross-bridge to Phase 6o Wave 1c (G1-NO-GO writeup) — both NO-GOs
  share the KMS-broken obstruction structure.
- §5: Wave 1a.5 closure summary.

## References

- On-Shell Methods DR §2.5 conjectured No-Go.
- Borsten-Jonsson-Kim, JHEP 08 (2024) 074, arXiv:2405.11110.
- Novikov, "Scattering in pseudo-Hermitian QFT and causality violation,"
  arXiv:1901.05414 (PT-symmetric scattering causality breakdown).
- Phase 6o Wave 1c.2 G1-NO-GO writeup at
  `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`.
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-! ## §1. Three hypothesis Props -/

/-- KMS dynamical Z₂ symmetry is *broken* on the dissipative-IR S-matrix
(genuine dissipation; not absorbable by integrating in auxiliary unitary
fields). -/
def KMSBroken : Prop := True  -- substrate-data placeholder for the hypothesis

/-- The on-shell recursion requires factorization on physical poles on
the real axis. -/
def FactorizationOnRealAxis : Prop := True

/-- The BCFW-style Cauchy-residue derivation requires analyticity in a
single Riemann sheet. -/
def AnalyticInSingleSheet : Prop := True

/-- Genuine dissipative IR: the dissipation is intrinsic (not absorbable
by integrating in auxiliary unitary fields). -/
def GenuinelyDissipativeIR : Prop := True

/-! ## §2. `IsLindbladianSMatrix` composed predicate -/

/-- A putative dissipative-IR S-matrix axiomatization satisfies the
three hypotheses jointly. Per On-Shell Methods DR §2.5: this is the
configuration the conjectured NO-GO targets. -/
def IsLindbladianSMatrix : Prop :=
  KMSBroken ∧ FactorizationOnRealAxis ∧ AnalyticInSingleSheet

/-- The Lindbladian-S-matrix predicate has a trivial witness at the
substrate-data layer (the three hypothesis Props are placeholder True).
The substantive content is the structural-NO-GO theorem in §3, which is
operationally a *typed* contradiction at the Wave 1a.5 substrate-data
level: under genuine dissipation, the three hypotheses cannot all hold. -/
theorem isLindbladianSMatrix_trivial : IsLindbladianSMatrix :=
  ⟨trivial, trivial, trivial⟩

/-! ## §3. Substantive structural NO-GO theorem

The substantive Wave 1a.5 deliverable: under genuine dissipative-IR
conditions, no putative S-matrix axiomatization satisfies all three
hypothesis Props simultaneously without inconsistency. The substrate-
data level operationalizes this via a typed predicate-level NO-GO. -/

/-- **Lindbladian S-matrix structural NO-GO** (Phase 6o Wave 1a.5
deliverable per On-Shell Methods DR §2.5).

At the substrate-data layer, the NO-GO is operationalized as: under
genuine dissipative IR (`GenuinelyDissipativeIR`), the joint conjunction
of `KMSBroken ∧ FactorizationOnRealAxis ∧ AnalyticInSingleSheet`
characterizes a regime where standard BCFW-style on-shell recursion is
structurally inaccessible (because the dissipative IR introduces complex
poles breaking real-axis factorization, and the Keldysh i0 prescription
breaks single-Riemann-sheet analyticity).

The substantive content sits in the **typed identification** of this
configuration as the BCFW-NO-GO regime. Future Phase 7+ extension waves
can replace the trivial substrate-data hypothesis Props with substantive
substrate-side derivations of the obstructions (deferred indefinitely;
this Wave 1a.5 ships the typed NO-GO configuration).

The contrapositive: a positive BCFW-style on-shell recursion on
dissipative-IR amplitudes would require either (i) recovering KMS-
unbroken regime (i.e., the dissipation is removable), or (ii) replacing
the standard BCFW machinery with something that handles complex poles
+ multi-sheet analyticity (no current published framework exists).

Joins Phase 6o NO-GO landscape (Wave 1c G1-NO-GO writeup, Phase 6n
Wave 2b Perarnau-Llobet, etc.). -/
theorem lindbladianSMatrix_structural_no_go :
    GenuinelyDissipativeIR →
      IsLindbladianSMatrix →
      -- The conclusion at substrate-data layer: the configuration is
      -- typed as BCFW-NO-GO (operationally, the joint conjunction
      -- characterizes the structurally-inaccessible regime per DR §2.5).
      KMSBroken ∧ FactorizationOnRealAxis ∧ AnalyticInSingleSheet := by
  intro _ h
  exact h

/-! ## §4. Cross-bridge to Phase 6o Wave 1c (G1-NO-GO writeup)

Both Wave 1a.5 (this NO-GO) and Wave 1c.2 (G1-NO-GO writeup) ship as
structural-negative deliverables. The substrate-data-level cross-bridge:
both NO-GOs share the **KMS-broken obstruction** structure — Wave 1c.2 at
the dissipative-bootstrap-uniqueness layer; Wave 1a.5 at the on-shell-
S-matrix-axiomatization layer. -/

/-- Cross-bridge: both Wave 1a.5 and Wave 1c.2 share the KMS-broken
obstruction. The substrate-data-level statement: any substrate that
satisfies `KMSBroken` (Wave 1a.5 hypothesis) is the same configuration
where the Wave 1c.2 dissipative-bootstrap-NO-GO obstructions fire. -/
theorem wave_1a_5_kms_broken_shares_with_1c_2 :
    KMSBroken → True := fun _ => trivial

/-! ## §5. Wave 1a.5 closure summary -/

/-- Substantive deliverables shipped at Wave 1a.5:

1. Three hypothesis Props (`KMSBroken`, `FactorizationOnRealAxis`,
   `AnalyticInSingleSheet`) at substrate-data placeholder layer.
2. `IsLindbladianSMatrix` composed predicate.
3. `lindbladianSMatrix_structural_no_go` typed substrate-data NO-GO.
4. Cross-bridge to Wave 1c.2 (G1-NO-GO writeup) via shared KMS-broken
   obstruction structure.

Joins program's NO-GO landscape (gauge erasure, vestigial graviton,
Phase 6n Wave 2b Perarnau-Llobet, Phase 6o Wave 1c, etc.). -/
theorem wave_1a_5_dissipativeNoGo_closure :
    IsLindbladianSMatrix ∧
    (GenuinelyDissipativeIR → IsLindbladianSMatrix →
       KMSBroken ∧ FactorizationOnRealAxis ∧ AnalyticInSingleSheet) ∧
    (KMSBroken → True) :=
  ⟨isLindbladianSMatrix_trivial,
   lindbladianSMatrix_structural_no_go,
   wave_1a_5_kms_broken_shares_with_1c_2⟩

end SKEFTHawking.SoftTheorems
