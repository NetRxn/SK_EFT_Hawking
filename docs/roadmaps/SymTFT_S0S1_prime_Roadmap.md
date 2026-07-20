# SymTFT S0/S1′: Honest Finite Toric-Boundary Classification — the Adopted Fable-Targets Lane

## Technical Roadmap — July 2026 (follow-on; the SymTFT semantic-strengthening lane's in-repo status ledger)

*Prepared 2026-07-20 as the SymTFT lane opener. The DETAILED execution authority remains the
scouted packet `temporary/working-docs/brainstorm/Fable-Targets/SymTFT/` (README +
`SYMTFT_SEMANTIC_STRENGTHENING_ROADMAP.md` (milestones S0–S7) + `SYMTFT_SUBSTRATE_AUDIT.md`) — this
file is the in-repo status ledger + gate record, per the `Phase6CA_prime_Roadmap.md` /
`Phase6o_prime_Roadmap.md` follow-on convention. Portfolio context:
`Fable-Targets/REMAINING_PRIORITY_PORTFOLIO.md` (SymTFT = "principal substrate program; finite
truth-serum before uniqueness"; Wave A item 1 = "SymTFT S0/S1 statement and semantic carrier
freeze"). This lane is the semantic-strengthening SUCCESSOR to `Phase6r_prime_Roadmap.md`
("Substantive Discharge of Phase 6r SymTFT Tracked Props") — it does NOT modify that lane's
predicates; it ships an honest v2 API beside them.*

**Project rules (inherited):** no PM/time estimates (task-count reference classes only);
kernel-purity `{propext, Classical.choice, Quot.sound}` with a fresh `#print axioms` per headliner;
preemptive-strengthening + non-vacuity pins on every carrier (a positive term AND a negative
fixture); the portfolio gates (current-HEAD re-validation at each wave launch; statement semantics
frozen before fan-out; data-level / categorical / object / continuum claims strictly separated; no
converting absent infrastructure into a free hypothesis hidden inside a structure). Architecture
rule (packet §3.1): **versioned API first** — the high-fanout legacy predicates (`Is3DTQFT`,
`IsLagrangianAlgebra`, `IsLagrangianAlgebraFPdimRefined`, `HasLagrangianAlgebra`,
`IsDMNOBiconditional`, `IsGappedTopologicalBoundary`) are NOT edited in place; honest v2 types live
in a new leaf. Off-limits (this lane): the live 16-convergence Pin⁺ files (`PinPlusKT*`,
`SphereProd*`, `Kummer*`, `PinPlusBordism4`, `PinPlusManifold4`) — the SymTFT Pin⁺/`ZMod 16`
adapter is packet §S7 downstream, never a prerequisite, and must never rebuild the retired
signature-mod-16 surrogate.

---

## Status ledger

| Gate/Wave | Status | Evidence (`SKEFTHawking.SymTFT` unless noted; headliners `#print axioms`-pure) |
|---|---|---|
| **Packet validation** (current-HEAD drift check) | ✅ 2026-07-20 | All 7 load-bearing audit defects re-confirmed at HEAD `141f5757` via slot LSP: `Is3DTQFT := Nonempty (BraidedCategory B)` (`Basic.lean:105`); `IsLagrangianAlgebra := IsConnectedAlgebra ∧ IsEtaleAlgebra` — FPdim omitted (`LagrangianAlgebra.lean:108-110`); `IsLagrangianAlgebraFPdimRefined` carries `globalFPdimSquared` as a **free per-use parameter** (`:142-147`); `IsDMNOBiconditional := Is3DTQFTBraided B ↔ HasLagrangianAlgebra B` — braidedness on the left, not Witt-triviality (`:214-216`); `IsGappedTopologicalBoundary B C := Is3DTQFT B ∧ HasLagrangianAlgebra B` — `C` ignored (`GappedBoundary.lean:74-77`); `A5LagrangianCenterUnit` makes the unit **weakly** Lagrangian (the regression target); `ToricCodeLagrangianAnyons` two-element classification + fermion falsifier proven and reusable. **No KERNEL_NOGO collision** — every registered no-go is Pin⁺/5qH bordism (bug-eyed non-Hausdorff, comp-twist, membrane-T2, taylor-leg, free-L KT, e₈ graph); the categorical toric side is untouched. **No 16-conv-lane collision** — no Pin⁺ file edited. Packet core premise (not-greenfield; semantic interfaces weak; toric anyon classification a reusable gift) **HOLDS**. |
| **Statement freeze (S0)** | ✅ 2026-07-20 | `SymTFT/SkeletalModularModel.lean` — honest v2 carriers frozen BESIDE the legacy façade: **`SkeletalModularModel`** (object-free finite abelian modular model: finite simple `Label`s + FPdim weight + unital fusion + monodromy phase + FPdim axioms; packet §2.1 "concrete/skeletal carrier") with **`globalFPdimSquared := ∑ FPdim²` DERIVED** — the antidote to the free-parameter kill criterion (§7). **`LagrangianSupport M`** — the condensable-boundary datum whose carrier appears in three LAWS (`fusion_closed`, `braiding_trivial`, `fpdim_lagrangian`), the last **reading the model's own `globalFPdimSquared`** — repairing both the unused-`C` and the free-`globalFPdimSquared` defects in one shape. |
| **S1 — finite core + non-vacuity + falsifiers + first classification** | ✅ 2026-07-20 | Same module. `toricSkeletalModel` (non-vacuity of the carrier from the existing `ToricCodeCenter` + `FrobeniusPerronDim` substrate); `toricSkeletalModel_globalFPdimSquared_eq_four` (derived dim = 4, reusing `toricGlobalFPdimSquared_eq_sum` — dimension is genuinely model-derived). Positive TERMS (not tracked Props): `toricElectricSupport`, `toricMagneticSupport`. Falsifier 1 (decisive unit falsifier): `unitOnly_fails_fpdim_lagrangian` + `no_unitOnly_lagrangianSupport` (`FPdim(1)² = 1 ≠ 4`; the honest law excludes what the legacy weak predicate admits). Falsifier 2 (braiding independently load-bearing): `fermionSet_passes_fpdim_lagrangian` (fermion PASSES FPdim) + `fermion_passes_fpdim_but_no_lagrangianSupport` (but fails `monodromy ε ε = 1`). Generic object-level negative (packet §1.5): `unit_not_isLagrangianAlgebraFPdimRefined` (unit fails the legacy FPdim-refined predicate in any bulk of global dim ≠ 1). S4-preview: `toric_lagrangianSupport_classification` (every honest support = electric ∨ magnetic — the FPdim law forces `card = 2`, then the existing exhaustive theorem applies). `toric_boundary_pilot_closure` bundles non-vacuity + both falsifiers + classification. **6 headliners `#print axioms`-pure `{propext, Classical.choice, Quot.sound}`; slot build green (module 8258 jobs; full library `SKEFTHawking` 10126 jobs).** |
| **S2 — object-level electric algebra** | 🚧 GATED (post-S1; object-level, multi-session) | Define multiplication **componentwise** on the `vacuum ⊞ electric` carrier via the four biproduct summands + `A5VacuumPlusElectric.electric_squared_iso_vacuum` (REPLACE the degenerate projection-through-vacuum multiplication, do NOT patch it — packet §S2 + audit §1.7). Prove `MonObj`/`ComonObj`/left+right Frobenius/separability/connectedness, `FPdim² = 4`, support `= {vacuum, electric}`. Non-vacuity target: the electric object is a TERM, decategorifying to `lagrangianElectricSet`. |
| **S3 — magnetic object + EM inequivalence** | 🚧 GATED | Mirror `1 ⊞ m` directly OR transport via an electric-magnetic braided autoequivalence (run both as short spikes; keep the cleaner). Inequivalence must be more than label inequality, with the quotient/labeling convention explicit (packet §S3; record if a bulk automorphism exchanges them). |
| **S4 — object/support bridge + exhaustive object classification** | 🚧 GATED (highest bounded-program risk) | Support map from the algebra presentation to `Finset ToricAnyon`; lift `toric_lagrangianSupport_classification` from the support level to object-equivalence classes, OR take an honest scope fallback (enumerate a finite presentation type / record algebra-structure uniqueness as the next named gap; packet §S4 — do NOT smuggle a general semisimple-decomposition theorem into a structure field). |
| **S5 — finite bulk-boundary correspondence pilot** | 🚧 GATED | `ToricBoundaryClass ≃ Fin 2` capstone with maps from the electric/magnetic presentations + inverse laws + support characterization (packet §S5). First milestone allowed a strong "boundary/Lagrangian-algebra correspondence" label. |
| **S6 / S7 — finite-abelian generalization / honest SymTFT–SM integration** | 🚧 GATED (downstream; never prerequisites) | S6 = the `Finite-Abelian-Drinfeld/` packet, owned as SymTFT S6 (maximal-isotropic-subgroup ↔ condensable-support). S7 = keep the three components separate (`ZMod 24` modular arithmetic ≠ categorical boundary ≠ physical realization); Pin⁺/`ZMod 16` + SM data enter only as narrow **adapter** modules with stable theorem signatures (packet §S7). |

## Wave-discipline notes

- **Versioned API first (packet §3.1).** No legacy SymTFT predicate was modified; the honest v2 carriers
  live in the new leaf `SymTFT/SkeletalModularModel.lean` (registered once in `SKEFTHawking.lean`).
  Canonical renames/deprecations of the Phase-6r façade are deferred to the S5 decision memo.
- **Global dimension is DERIVED model data, never a free per-use argument** — this directly discharges the
  packet's post-S1 kill criterion ("global dimension remains an arbitrary per-use argument").
- **Two independent falsifiers at first pass.** The unit fails the FPdim law; the fermion passes FPdim but
  fails braiding-triviality. Both conditions are therefore proven load-bearing, satisfying the
  strengthening discipline's non-vacuity + negative-fixture requirement without a retroactive pass.
- **Validate-first held, twice.** (i) The packet's audit was accurate at HEAD — the SymTFT categorical
  files are unchanged since the June-17 checkout, so no defect drifted. (ii) The existing
  `ToricCodeLagrangianAnyons.isLagrangianAnyonSet_classification` was a reusable gift: the honest support
  classification bridges to it in ~6 lines (the FPdim law ⇒ `card = 2`) rather than re-deriving the
  exhaustive enumeration.
- **Scope honesty.** This lane ships at the **support / skeletal** level only. No functorial TQFT, no
  general fusion/modular tensor library, no general DMNO proof, no object-level algebra (S2), and no
  Pin⁺/`ZMod 16` or SM-boundary bridge are claimed. Every module docstring states the scope boundary.
- **Off-limits respected.** No Pin⁺/16-convergence file was touched; no kernel no-go was re-entered; the
  retired signature-mod-16 surrogate was not rebuilt.
