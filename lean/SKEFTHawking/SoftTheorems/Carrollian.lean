import Mathlib
import SKEFTHawking.SoftTheorems.Boostless

/-!
# Phase 6o Wave 1a.3: Strominger triangle on analog horizons (memory↔soft edge)

## Goal

Encode the Strominger-triangle structure (soft theorem ↔ asymptotic
symmetry Ward identity ↔ memory effect) on the program's analog-Hawking
backgrounds, per On-Shell Methods DR §3–§4 and Datta-Fischer acoustic
gravitational memory (arXiv:2011.05837).

## Substantive content (R-01 remediation, 2026-07-20)

**GENUINELY BUILT — the memory ↔ soft-theorem edge.** The mathematical
core of the Strominger triangle that does NOT require Carrollian/BMS
geometry is the *memory = soft-charge* identity: the permanent net
displacement of the condensate after a burst (the memory effect) equals
the zero-frequency (ω → 0, soft) mode of the flux, i.e. its
time-integral. We build this on a concrete acoustic-memory burst and prove
it by the fundamental theorem of calculus:

* `AcousticMemoryBurst` — a C¹ strain waveform `h` whose derivative is the
  acoustic `flux` (Datta-Fischer BEC acoustic memory).
* `AcousticMemoryBurst.memory` = `h b − h a` (permanent net displacement).
* `AcousticMemoryBurst.softCharge` = `∫ flux` (the DC / ω→0 soft mode).
* `memory_eq_softCharge` — **the genuine Ward identity** `memory =
  softCharge`, proved via FTC. This is the memory-vertex ↔ soft-theorem-
  vertex edge of the Strominger triangle, made concrete.

Non-vacuity: `identityBurst` has genuine non-zero memory
(`identityBurst_memory_ne_zero`), so the memory vertex is genuinely
witnessed (not the previous `True`).

## Documented GAP — the Carrollian-boundary geometry vertex (category 3)

The THIRD vertex — the existence of the Carrollian null-boundary 3-manifold
at acoustic null infinity carrying the asymptotic charges (Mason-Ruzziconi-
Yelleshpur Srikant arXiv:2312.10138; Penna membrane-paradigm arXiv:1508.06577)
— genuinely requires a Carrollian / BMS geometry formalization that
**Mathlib does not have** (On-Shell DR §4.3: "no paper proves a BMS theorem
for an acoustic/BEC analog black hole"; §8.2: "Mathlib does not yet have the
Lorentz group as a formal Lie group … no spinor-helicity, no contour
machinery for BCFW"). Building it would require: (i) a degenerate
(Carrollian) boundary-metric + null-vector-field structure; (ii) the BMS₃/₄
asymptotic-symmetry algebra with supertranslation charges; (iii) the
charge-conservation Ward identity tying (i)–(ii) to the soft charge above.
None of these exist in Mathlib and each is a substantial formalization
project. This module therefore ships the two tractable vertices/edges
(soft theorem via `Boostless.lean`; memory↔soft here) and documents the
Carrollian-boundary vertex as the precise remaining gap — it is NOT shipped
as a `True` placeholder.

## References

- Mason-Ruzziconi-Yelleshpur Srikant, JHEP 05 (2024) 012, arXiv:2312.10138.
- Agrawal-Nguyen, arXiv:2504.10577 (soft theorems ↔ spontaneous symmetry breaking; the
  supertranslation Ward identity ↔ soft-mode-insertion equivalence). [Attribution corrected
  2026-07-20 per the C0 scout — formerly misattributed to Have-Nguyen-Prohazka-Salzer,
  whose paper is arXiv:2402.05190, massive carrollian fields at timelike infinity.]
- Datta-Fischer, arXiv:2011.05837 (BEC acoustic gravitational memory).
- Penna, "BMS invariance and the membrane paradigm," arXiv:1508.06577.
- On-Shell Methods DR §3, §4, §4.3, §8.2.
-/

noncomputable section

namespace SKEFTHawking.SoftTheorems

/-! ## §1. Analog-Hawking background enum -/

/-- The three analog-Hawking backgrounds the program supports for the
boostless / Carrollian soft-theorem track. Parallels the
`SKEFTHawking.APSEta.Substrate` enum but at the soft-theorem substrate-data
layer. -/
inductive AnalogBackground
  | BECDrainingBathtub  -- Phase 4 BdG / Phase 5w transonic substrate
  | ADWSchwarzschild    -- Phase 5d Wave 11 ADW emergent-graviton-Schwarzschild
  | PolaritonSonicHorizon -- Phase 5y polariton substrate
  deriving DecidableEq, Repr

/-! ## §2. Acoustic memory burst + the genuine memory↔soft edge -/

/-- An acoustic-memory burst (Datta-Fischer arXiv:2011.05837): a strain /
condensate-phase waveform `h` on the real time line whose time-derivative
is the acoustic `flux`. The permanent net displacement of `h` across the
burst is the acoustic analogue of the (nonlinear) gravitational memory
effect. -/
structure AcousticMemoryBurst where
  /-- Condensate strain / phase waveform. -/
  h : ℝ → ℝ
  /-- Acoustic flux = dh/dt. -/
  flux : ℝ → ℝ
  /-- Start of the burst window. -/
  a : ℝ
  /-- End of the burst window. -/
  b : ℝ
  /-- `flux` is the time-derivative of the strain everywhere. -/
  hderiv : ∀ t, HasDerivAt h (flux t) t
  /-- The flux is continuous (so it is interval-integrable). -/
  hcont : Continuous flux

/-- **The memory**: permanent net displacement of the condensate strain
across the burst window. -/
def AcousticMemoryBurst.memory (B : AcousticMemoryBurst) : ℝ := B.h B.b - B.h B.a

/-- **The soft charge**: the zero-frequency (ω → 0, DC) mode of the flux,
i.e. its time-integral over the burst window. -/
def AcousticMemoryBurst.softCharge (B : AcousticMemoryBurst) : ℝ :=
  ∫ t in B.a..B.b, B.flux t

/-- **Strominger-triangle memory ↔ soft-theorem edge** (genuine Ward
identity). The acoustic memory (permanent displacement) equals the soft
charge (the ω → 0 / DC mode of the flux). Proved by the fundamental theorem
of calculus. This is the memory-vertex ↔ soft-theorem-vertex relation of the
Strominger triangle, on a concrete acoustic-memory burst. -/
theorem memory_eq_softCharge (B : AcousticMemoryBurst) :
    B.memory = B.softCharge := by
  unfold AcousticMemoryBurst.memory AcousticMemoryBurst.softCharge
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => B.hderiv t)
      (B.hcont.intervalIntegrable _ _)]

/-! ## §3. The genuine memory + Ward vertices -/

/-- The acoustic-memory vertex: the burst carries a genuine *non-zero*
permanent memory (distinguishing a memory-producing burst from a transient
pulse that returns to its initial value). -/
def IsAcousticMemoryVertex (B : AcousticMemoryBurst) : Prop := B.memory ≠ 0

/-- The asymptotic-symmetry Ward identity, operationalized (Have et al.
arXiv:2504.10577): the soft charge equals the memory. This is a THEOREM —
it holds for every burst — via `memory_eq_softCharge`. -/
def SatisfiesWardIdentity (B : AcousticMemoryBurst) : Prop :=
  B.softCharge = B.memory

theorem burst_satisfies_ward (B : AcousticMemoryBurst) :
    SatisfiesWardIdentity B :=
  (memory_eq_softCharge B).symm

/-! ## §4. Non-vacuity: a burst with genuine non-zero memory -/

/-- A concrete acoustic-memory burst with a constant unit flux and linear
(ramp) strain `h(t) = t` on `[0,1]`: the memory is `1 − 0 = 1 ≠ 0`. -/
def identityBurst : AcousticMemoryBurst :=
  { h := id
  , flux := fun _ => 1
  , a := 0
  , b := 1
  , hderiv := fun t => by simpa using hasDerivAt_id t
  , hcont := continuous_const }

theorem identityBurst_memory : identityBurst.memory = 1 := by
  simp [AcousticMemoryBurst.memory, identityBurst]

/-- The concrete burst carries genuine non-zero memory: the memory vertex is
non-vacuously witnessed. -/
theorem identityBurst_memory_ne_zero : IsAcousticMemoryVertex identityBurst := by
  unfold IsAcousticMemoryVertex
  rw [identityBurst_memory]; norm_num

/-! ## §5. Strominger triangle (the two tractable vertices) -/

/-- **The Strominger triangle on the emergent-IR sector** — the two
formalizable vertices: the burst has a genuine memory vertex (non-zero
permanent displacement) AND satisfies the memory↔soft Ward identity.

The third vertex (Carrollian null-boundary geometry carrying the asymptotic
charge) is the documented gap — see the module docstring — so it is not a
conjunct here. -/
def StromingerTriangleClosed (B : AcousticMemoryBurst) : Prop :=
  IsAcousticMemoryVertex B ∧ SatisfiesWardIdentity B

/-- The two tractable vertices of the Strominger triangle close for the
concrete `identityBurst`. -/
theorem stromingerTriangleClosed_identityBurst :
    StromingerTriangleClosed identityBurst :=
  ⟨identityBurst_memory_ne_zero, burst_satisfies_ward identityBurst⟩

/-! ## §6. Boostless bootstrap predicate (composed) -/

/-- **Boostless bootstrap predicate** (Wave 1a.3 composed deliverable):
a `SoftAmplitude` satisfying the Wave 1a.2 boostless leading-soft-factor
predicate (the soft-theorem vertex), living together with an acoustic-memory
burst on which the memory↔soft Strominger edge closes. -/
def BoostlessBootstrapPredicate {n : ℕ}
    (M : SoftAmplitude n) (B : AcousticMemoryBurst) : Prop :=
  IsBoostlessLeadingSoftFactor M ∧ StromingerTriangleClosed B

/-- The boostless bootstrap predicate has a genuine witness: the toy
boostless soft amplitude together with the non-zero-memory burst. -/
theorem boostlessBootstrap_existence :
    ∃ (n : ℕ) (M : SoftAmplitude n) (B : AcousticMemoryBurst),
      BoostlessBootstrapPredicate M B :=
  ⟨2, trivialSoftAmplitude, identityBurst,
   trivialSoftAmplitude_satisfies_boostless,
   stromingerTriangleClosed_identityBurst⟩

/-! ## §7. Wave 1a.3 closure summary -/

/-- Substantive deliverables shipped at Wave 1a.3 (R-01 remediation):

1. `AnalogBackground` enum (BEC + ADW + polariton).
2. `AcousticMemoryBurst` + `memory` + `softCharge` + **`memory_eq_softCharge`**
   (the genuine FTC-proved memory↔soft Ward edge of the Strominger triangle).
3. `IsAcousticMemoryVertex` (non-zero memory) + `SatisfiesWardIdentity`
   (proved for every burst) + `identityBurst` non-vacuous witness.
4. `StromingerTriangleClosed` (the two tractable vertices) +
   `BoostlessBootstrapPredicate` composed with the boostless soft factor.

The third vertex — the Carrollian null-boundary geometry — is documented as
the precise remaining gap (Mathlib lacks Carrollian/BMS geometry). -/
theorem wave_1a_3_carrollian_closure :
    -- The genuine memory↔soft Ward edge holds for every burst
    (∀ B : AcousticMemoryBurst, B.memory = B.softCharge) ∧
    -- The two tractable Strominger vertices close on the concrete burst
    StromingerTriangleClosed identityBurst ∧
    -- The boostless bootstrap predicate has a genuine witness
    (∃ (n : ℕ) (M : SoftAmplitude n) (B : AcousticMemoryBurst),
       BoostlessBootstrapPredicate M B) :=
  ⟨memory_eq_softCharge,
   stromingerTriangleClosed_identityBurst,
   boostlessBootstrap_existence⟩

end SKEFTHawking.SoftTheorems
