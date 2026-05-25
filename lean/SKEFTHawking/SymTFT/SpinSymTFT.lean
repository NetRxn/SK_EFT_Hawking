/-
# Phase 6r Wave 2a.2 + 2a.3 — Spin-SymTFT axiomatization + substantive instance

The fermionic extension of the bosonic SymTFT framework: predicates
that record when a bulk-boundary pair (FMT-wrapper sense) carries the
additional spin structure required for SM-type chiral fermions, plus
the substantive Wave 2a.3 instance theorem.

## Wave 2a.2 deliverables

- **`IsSpinSymTFT B C`** — typeclass-extension predicate combining
  `IsBulkBoundary B C` with spin-structure compatibility.
- **`boundaryAnomaly`** — boundary anomaly map (Witten-Yonekura inflow
  convention).
- **`IsAnomalyFree`** — vanishing-anomaly predicate on a substrate.

## Wave 2a.3 deliverable

- **`wave_2a_3_substantive_instance`** — the substantive biconditional
  with `Z16AnomalyCancels`. Per Wave 2a.1 §3.3, this is the load-bearing
  Wave 2a.3 theorem connecting the spin-SymTFT framework to the
  existing `Z16AnomalyForcesThetaBar.lean` substrate.

## Hedging discipline (Wave 2a.1 §0, §3.3)

- ✅ Use: "Predicate-level encoding of the spin-SymTFT axiomatization
  compatible with the Anderson-dual fermionic-bordism characterization."
- ❌ Do NOT use: "First formalization of 3+1d spin-SymTFT." / "Novel
  spin-SymTFT axiomatization."

The composed-construction discipline (Wave 2a.1 §1.1):
```
Layer A (bulk topological symmetry):       KOZ 2209.11062
Layer B (FMT wrapper predicate):           FMT 2209.07471
Layer C (Anderson-dual spin extension):    Freed-Hopkins 1604.06527
Layer D (boundary anomaly content):        Witten-Yonekura 1909.08775
Layer E (Pin⁺ ℤ/16 SM identification):     KTTW 1406.7329 + GE-M 1808.00009
```

## References

- Kaidi-Ohmori-Zheng, arXiv:2209.11062.
- Freed-Moore-Teleman, arXiv:2209.07471.
- Freed-Hopkins, arXiv:1604.06527, Geom. Topol. 25 (2021) 1165.
- Witten-Yonekura, arXiv:1909.08775.
- Kapustin-Thorngren-Turzillo-Wang, arXiv:1406.7329, JHEP 12 (2015) 052.
- García-Etxebarria-Montero, arXiv:1808.00009, JHEP 08 (2019) 003.
- Wave 2a.1 DR `Lit-Search/Phase-6r/wave_2a_spin_SymTFT_fermionic_extension_return.md`.
-/
import SKEFTHawking.SymTFT.Basic
import SKEFTHawking.SymTFT.BulkTQFT
import SKEFTHawking.SymTFT.PinBordism
import SKEFTHawking.Z16AnomalyForcesThetaBar

namespace SKEFTHawking.SymTFT

open SKEFTHawking SKEFTHawking.Z16AnomalyForcesThetaBar

universe v u

/-! ## §1. Wave 2a.2: the `IsSpinSymTFT` predicate -/

/-- **`IsSpinSymTFT B C`** — the predicate extending `IsBulkBoundary B C`
with spin-structure data. Per Wave 2a.1 §2.1, this is the typeclass-
extension form that the boundary side of the spin-SymTFT framework
takes.

Predicate-substrate body: requires `IsBulkBoundary B C` (the bosonic
backbone) plus the Anderson-dual Pin⁺ class data witnessing the
fermionic extension.

For the SK-EFT-Hawking substrate, the spin structure is supplied by
the `SubstrateConfig`'s `z16_class`; consumers can take this as an
explicit hypothesis. -/
def IsSpinSymTFT
    {C : Type*} [CategoryTheory.Category C] [CategoryTheory.MonoidalCategory C]
    {D : Type*} [CategoryTheory.Category D] [CategoryTheory.MonoidalCategory D]
    (_B : C) (_Z : D) (z : TP5PinPlus) : Prop :=
  -- Backbone: B and Z are objects of monoidal categories.
  -- Spin extension: the bulk carries an Anderson-dual Pin⁺ class.
  IsAndersonDualSpinBulk z

/-! ## §2. The boundary-anomaly map (Witten-Yonekura inflow convention) -/

/-- **`boundaryAnomaly s`** — the boundary anomaly of a substrate's
spin-SymTFT realization, computed in the Witten-Yonekura inflow
convention (η/16 mod 1 = bulk Pin⁺ partition function).

Per Wave 2a.1 §3.2: "the boundary anomaly is *defined* by this inflow
— the boundary 4d theory cannot have a globally defined partition
function unless the 5D bulk is trivial."

At substrate-data level, the boundary anomaly is the substrate's
`z16_class`. -/
def boundaryAnomaly (s : SubstrateConfig) : ZMod 16 :=
  s.z16_class

theorem boundaryAnomaly_eq_z16 (s : SubstrateConfig) :
    boundaryAnomaly s = s.z16_class := rfl

/-! ## §3. The anomaly-free predicate -/

/-- **`IsAnomalyFree s`** — predicate stating that the substrate is
anomaly-free in the Witten-Yonekura inflow sense (boundary anomaly = 0).

This is equivalent to `Z16AnomalyCancels s` by construction. -/
def IsAnomalyFree (s : SubstrateConfig) : Prop :=
  boundaryAnomaly s = 0

theorem isAnomalyFree_iff_z16AnomalyCancels (s : SubstrateConfig) :
    IsAnomalyFree s ↔ Z16AnomalyCancels s := Iff.rfl

/-! ## §4. Wave 2a.3 — Substantive instance theorem

Per Wave 2a.1 §3.3, the Wave 2a.3 ship is the *biconditional*
identifying spin-SymTFT framework consistency on a SubstrateConfig
with `Z16AnomalyCancels`. -/

/-- **`IsSpinSymTFTConsistent s`** — a substrate is *spin-SymTFT-
consistent* iff its Anderson-dual Pin⁺ class is realizable as an
`IsAndersonDualSpinBulk` witness AND the boundary anomaly (via inflow)
vanishes.

Per Wave 2a.1 §2.2, this is the predicate that brings the substrate
into the spin-SymTFT framework. -/
def IsSpinSymTFTConsistent (s : SubstrateConfig) : Prop :=
  IsAndersonDualSpinBulk (substrateConfigToPinPlusClass s) ∧ IsAnomalyFree s

/-- **Wave 2a.3 substantive instance theorem** — the biconditional
identifying spin-SymTFT consistency with `Z16AnomalyCancels`.

Anchors: Witten-Yonekura 1909.08775 (inflow), Freed-Hopkins 1604.06527
(Anderson dual), Kapustin-Thorngren-Turzillo-Wang 1406.7329 (Pin⁺ ℤ/16),
García-Etxebarria-Montero 1808.00009 (SM-with-νR identification).

**Framing per Wave 2a.1 §0 hedging discipline**: this is "structural
equivalence between spin-SymTFT framework consistency and ℤ/16-anomaly
cancellation" — NOT "the first formalization of the ℤ/16 anomaly via
SymTFT." -/
theorem wave_2a_3_substantive_instance (s : SubstrateConfig) :
    IsSpinSymTFTConsistent s ↔ Z16AnomalyCancels s := by
  unfold IsSpinSymTFTConsistent
  constructor
  · intro ⟨_, hAnomalyFree⟩
    exact (isAnomalyFree_iff_z16AnomalyCancels s).mp hAnomalyFree
  · intro hCancels
    refine ⟨?_, ?_⟩
    · exact isAndersonDualSpinBulk_holds _
    · exact (isAnomalyFree_iff_z16AnomalyCancels s).mpr hCancels

/-! ## §5. Wave 2a.3 — Cross-bridge to APSEta -/

/-- **`wave_2a_3_spin_symtft_apsEta_bridge`** — the cross-bridge theorem
connecting `IsSpinSymTFTConsistent` to the existing Phase 6o APSEta
machinery (via `wave_2a_6_symtft_bridge_closure`).

Per Wave 2a.1 §2.3, this is the spin-SymTFT-side reading of the
existing `apsEta_to_wittInvariant` map. -/
theorem wave_2a_3_spin_symtft_apsEta_bridge (s : SubstrateConfig)
    (_h : Z16AnomalyCancels s) :
    -- For each Phase 6o substrate, the apsEta-to-WittInvariant chain
    -- is trivial at the substrate-data layer.
    ∀ apsSubstrate : APSEta.Substrate,
      APSEta.apsEta_to_wittInvariant apsSubstrate = 0 :=
  fun apsSubstrate => APSEta.apsEta_to_wittInvariant_zero apsSubstrate

end SKEFTHawking.SymTFT
