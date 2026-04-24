# Architecture Scope — Three-Layer Predictive Boundary

**Last updated:** 2026-04-23 (Phase 5y closure)

This document defines the **predictive scope** of the SK-EFT Hawking
research program's three-layer architecture — what the architecture
commits to predicting, and what is explicitly outside its tested scope.

---

## The three layers

The SK-EFT Hawking program is organized around a three-layer emergent-physics
architecture:

| Layer | Target physics                              | Canonical modules              |
|-------|---------------------------------------------|--------------------------------|
| 1     | Discrete lattice Hamiltonian + fermions     | `LatticeHamiltonian`, `FermionBag4D` |
| 2     | Coarse-grained effective field theory (SK)  | `AcousticMetric`, `SKDoubling`, `SecondOrderSK` |
| 3     | Emergent gauge fields + gravity (ADW+etc.)  | `ADWMechanism`, `GaugeErasure`, `ChiralityWall`, `VestigialGravity` |

---

## Predictive scope by layer

### Layer 3: SM + GR sector (IN SCOPE)

The architecture commits to **Standard Model + General Relativity
emergent physics** under the tested mechanisms:
- **ADW tetrad condensation** producing emergent gravity (Phase 3
  Wave 3)
- **Gauge erasure** producing `U(1)` from non-Abelian lattice
  (Phase 3 Wave 2)
- **Fracton hydrodynamics** producing subdiffusive emergent currents
  (Phase 4 Wave 2-3)
- **Vestigial gravity** as a distinct intermediate ordering
  (Phases 4, 5w, 5y; H4 structural content)

Layer-3 predictions in this sector are falsifiable, formalized
(currently ~3728 Lean theorems, zero sorry, 1 axiom), and actively
tested against laboratory platforms (BEC, polariton, graphene Dirac
fluid) in phases 5u/5w/5d.

### Dark-sector physics (OUT OF SCOPE under tested mechanisms)

**Phase 5y closure verdict (2026-04-23):** After six deep-research
rounds of Volovik-family dark-energy mechanisms (q-theory in four
realizations + vestigial gravity EOS + second-sound graviton), all
returned **NO-GO** for DESI DR2 compatibility. The structural obstruction
is formalized in:
- `GibbsDuhemTheorem.lean` — any single-scalar self-tuning emergent-vacuum
  framework with Gibbs-Duhem equilibrium locks `w_vac = −1`
- `QTheoryNoGoTheorem.lean` — the obstruction is realization-independent
  across the four tested KV q-theory constructions
- `DarkEnergyObstructionPrinciple.lean` — four-factor orthogonality
  (Gibbs-Duhem ∩ `c_s² ≥ 0` ∩ natural `T_c` ∩ MICROSCOPE) diagnoses
  why vestigial gravity also fails

**Predictive-scope recalibration:** Layer 3 is scoped to produce
SM+GR-sector emergent physics cleanly. The dark-energy sector is
**outside the architecture's tested predictive scope** under the
Volovik-family mechanisms explored in Phase 5y. This is a sharpening
of scope, not a retreat: the architecture remains intact for SM+GR
physics; it is explicit about not predicting cosmological-constant-type
physics under mechanisms currently tested.

### What this does NOT claim

Phase 5y's closure **does not** claim:
- q-theory is falsified as a vacuum-stability framework (only as a
  late-time dark-energy framework; q-theory as equilibrium or
  inflation-era framework remains untested / intact)
- Vestigial gravity is ruled out as a concept (the H4 framework
  PARTIAL verdict remains — the ordering and Z₄ structure are
  mathematically consistent and may find applications elsewhere)
- No emergent dark energy is possible (obstruction covers
  Volovik-family mechanisms specifically; entropic gravity,
  causal-set approaches, Jacobson-type thermodynamic GR are outside
  the tested scope)
- The three-layer architecture is falsified (only the dark-sector
  predictive claim is scoped out; Layer-3 SM+GR-sector claims are
  unaffected)

---

## Cross-phase non-inheritance

Phase 5y's NO-GO verdicts do **not** propagate to the following
parallel/subsequent phases:

| Phase | Inheritance     | Status             |
|-------|-----------------|--------------------|
| 5u (polariton Hawking)   | No inheritance | Tier A, continues independently |
| 5d (RHMC ADW fermion)    | No inheritance | Orthogonal physics, continues |
| 5w (graphene Dirac fluid)| No inheritance | Orthogonal physics, continues |
| 5x (dark matter)         | No inheritance | Different mechanisms, continues |

Cross-phase impact memos are in `docs/stakeholder/Phase5y_Impact_on_*.md`
(Wave 9 deliverables).

---

## Architectural implications

1. **Program value preserved.** The Lean backbone of the program
   continues to build cleanly. 3728+ theorems (Phase 5t baseline) plus
   ~109 new theorems from Phase 5y closure across 7 new modules + 3
   extensions.

2. **Scope explicit.** The predictive-scope boundary is now
   formally stated in Lean (`ClassificationTableDark.lean`) and
   documented here. Future Phase 5/6 architectural conversations can
   reference this scope explicitly without ambiguity.

3. **GO/NO-GO methodology validated.** Phase 5y demonstrated that
   the program can execute a six-round deep-research probe, land a
   structural NO-GO, and harvest the result as formal content without
   reopening or re-scoping the underlying decision. This is a reusable
   methodology for future high-leverage bets.

4. **No publication overhead.** Phase 5y deliberately produces no
   papers (user-stated preference). The harvest is entirely Lean +
   architectural documentation + cross-phase memos. This keeps the
   program oriented around formal-verification output during the
   current period.

---

## References

- **Roadmap:** `docs/roadmaps/Phase5y_Roadmap.md` (terminal revision
  2026-04-24)
- **Classification:** `temporary/working-docs/phase5y_classification_table_dark.md`
  + `lean/SKEFTHawking/ClassificationTableDark.lean`
- **Deep research:** `Lit-Search/Phase-5y/` (6 rounds, all complete)
- **Wave execution:** `docs/WAVE_EXECUTION_PIPELINE.md`

---

*Phase 5y terminal closure artifact. Supersedes no prior architecture
document — this is the first explicit `ARCHITECTURE_SCOPE.md` for the
program.*
