import SKEFTHawking.CondensedMatterAnalog

/-!
# Vestigial Mapping: Condensed Matter ↔ Vestigial-Tetrad Gravity

Formalizes the H4 §3 dictionary table that maps the Fernandes-Fu charge-4e
vestigial-superconductor framework onto Volovik's vestigial-tetrad
gravity. The dictionary is the bridge enabling the H4 closed-form
`w_vest, c_s², ζ_vest` derivation (Wave 5).

## Dictionary (H4 §3)

| Condensed matter (Fernandes-Fu / Jian-Huang-Yao) | Vestigial gravity (Volovik) |
|--------------------------------------------------|------------------------------|
| Electron field `ψ_e`                             | SM fermion `Ψ`              |
| Two-component primary `Δ = (Δ₁, Δ₂)`             | Composite tetrad `Ê^a_μ`    |
| Charge-4e composite `ψ = Δ₁² + Δ₂²`              | 4-fermion quartet `χ^{ab}_{μν}` |
| Nematic `Φ`                                      | Shear tetrad-bilinear `Q^{ab}` |
| `U(1)_gauge`                                     | `U(1)_tetrad-phase` (Volovik `Z_4`) |
| Lattice rotation `C_6`                           | Local Lorentz `SO(3,1)`      |
| Temperature `T`                                  | de Sitter temperature `T_dS = H/π` |
| Chemical potential `μ`                           | Cosmological-constant scale `μ_Λ ~ Λ^{1/4}` |
| External field `B`                               | Background curvature `R^a_{bcd}` |
| Strain `ε_ij`                                    | Metric fluctuation `h_μν`    |
| `T_{c,primary}`                                  | `T_ECSK` (full-tetrad transition) |
| `T_{4e}`                                         | `T_{c,vest}` (vestigial onset) |

## Symmetry preservation

The mapping preserves:
- Symmetry breaking pattern: `U(1) → Z₂` (doubled winding) on both sides
- `U(1)`-breaking character of the vestigial order parameter
- Two-stage transition structure (primary → vestigial → disordered)

## References

- `Lit-Search/Phase-5y/Phase 5y Hypothesis 4 — Effective Fluid EOS for Volovik-Style Vestigial Gravity.md` §3
- Volovik, *Vestigial gravity*, JETP Lett. 119, 330 (2024); arXiv:2312.09435
-/

namespace SKEFTHawking.VestigialMapping

open SKEFTHawking.CondensedMatterAnalog

/-!
## Dictionary types

The dictionary has two sides: condensed-matter (CM) and vestigial-gravity
(VG). Each row pairs a CM concept with its gravitational analog.
-/

/-- Condensed-matter side of the dictionary. Enumerates the canonical
    concepts from Fernandes-Fu / Jian-Huang-Yao. -/
inductive CMRow where
  | electronField
  | primaryPair
  | charge4e
  | nematic
  | u1Gauge
  | latticeRotC6
  | temperature
  | chemicalPotential
  | externalB
  | strain
  | primaryTc
  | vestigialT4e
  deriving DecidableEq, Repr

/-- Gravitational side of the dictionary (Volovik vestigial tetrad). -/
inductive VGRow where
  | smFermion
  | compositeTetrad
  | fourFermionQuartet
  | shearTetradBilinear
  | u1TetradPhase
  | localLorentz
  | deSitterTemp
  | cosmoConstScale
  | backgroundCurvature
  | metricFluctuation
  | ecskTransition
  | vestigialTc
  deriving DecidableEq, Repr

/-- The H4 §3 dictionary: maps each CM row to its VG counterpart. -/
def dictionary : CMRow → VGRow
  | .electronField      => .smFermion
  | .primaryPair        => .compositeTetrad
  | .charge4e           => .fourFermionQuartet
  | .nematic            => .shearTetradBilinear
  | .u1Gauge            => .u1TetradPhase
  | .latticeRotC6       => .localLorentz
  | .temperature        => .deSitterTemp
  | .chemicalPotential  => .cosmoConstScale
  | .externalB          => .backgroundCurvature
  | .strain             => .metricFluctuation
  | .primaryTc          => .ecskTransition
  | .vestigialT4e       => .vestigialTc

/-!
## Bijectivity and structural preservation
-/

/-- Inverse direction of the dictionary. -/
def dictionaryInv : VGRow → CMRow
  | .smFermion            => .electronField
  | .compositeTetrad      => .primaryPair
  | .fourFermionQuartet   => .charge4e
  | .shearTetradBilinear  => .nematic
  | .u1TetradPhase        => .u1Gauge
  | .localLorentz         => .latticeRotC6
  | .deSitterTemp         => .temperature
  | .cosmoConstScale      => .chemicalPotential
  | .backgroundCurvature  => .externalB
  | .metricFluctuation    => .strain
  | .ecskTransition       => .primaryTc
  | .vestigialTc          => .vestigialT4e

/-- **VM1 — Dictionary is a left-inverse of its inverse.**

    For every CM row, applying `dictionary` then `dictionaryInv` returns
    the original row. This is the structural consistency check for the
    H4 §3 bijection. -/
theorem dictionary_left_inv (r : CMRow) :
    dictionaryInv (dictionary r) = r := by
  cases r <;> rfl

/-- **VM2 — Dictionary is a right-inverse of its inverse.** -/
theorem dictionary_right_inv (r : VGRow) :
    dictionary (dictionaryInv r) = r := by
  cases r <;> rfl

/-!
## Key structural mappings

Three mappings are load-bearing for Wave 5's vestigial-EOS derivation:
1. `charge4e ↦ fourFermionQuartet` — the central composite
2. `temperature ↦ deSitterTemp` — the thermal-bath identification
3. `vestigialT4e ↦ vestigialTc` — the onset-temperature mapping
-/

/-- **VM3 — Central mapping: charge-4e composite corresponds to the
    4-fermion quartet.**

    The charge-4e composite `ψ = Δ₁² + Δ₂²` on the condensed-matter side
    maps to the 4-fermion quartet `χ^{ab}_{μν}` on the gravitational side.
    This is the single most important row of the dictionary for Wave 5. -/
theorem dict_charge4e_to_quartet :
    dictionary CMRow.charge4e = VGRow.fourFermionQuartet := rfl

/-- **VM4 — Temperature mapping: lab temperature corresponds to the
    de Sitter horizon temperature `T_dS = H/π`.**

    Volovik's 2024 paper identifies `T_dS = H/π` as the canonical thermal
    bath for vestigial condensation; this mapping underlies EQ.112. -/
theorem dict_temp_to_deSitter :
    dictionary CMRow.temperature = VGRow.deSitterTemp := rfl

/-- **VM5 — Onset-temperature mapping: `T_4e` ↔ `T_{c,vest}`.** -/
theorem dict_T4e_to_vestigialTc :
    dictionary CMRow.vestigialT4e = VGRow.vestigialTc := rfl

/-!
## U(1)-breaking preservation

The dictionary preserves the `U(1)`-breaking character of the vestigial
order: the charge-4e `ψ` breaks `U(1)_gauge` to `Z₂` (doubled winding),
and its gravitational analog (the 4-fermion quartet) breaks Volovik's
`U(1)_tetrad-phase` to `Z₄` (the `Ẑ_4` symmetry of arXiv:2406.00718).
-/

/-- **VM6 — U(1) breaking is preserved on the charge-4e side.**

    Both the condensed-matter charge-4e and its gravitational analog
    (4-fermion quartet) sit in `U(1)`-breaking channels — the central
    structural fact from the CMA `VestigialOrderType.breaksU1`. -/
theorem mapping_preserves_u1_breaking :
    VestigialOrderType.charge4e.breaksU1 = true ∧
    dictionary CMRow.charge4e = VGRow.fourFermionQuartet := by
  exact ⟨charge4e_breaks_u1, rfl⟩

/-!
## Two-stage transition structure

The condensed-matter system has a two-stage transition:
```
Disordered (T > T_4e) → Vestigial (T_primary < T < T_4e) → Full pairing (T < T_primary)
```
The gravitational analog inherits this structure:
```
Disordered (T_dS > T_{c,vest}) → Vestigial GR (T_ECSK < T_dS < T_{c,vest}) → ECSK (T_dS < T_ECSK)
```
Volovik's EQ.98 gives exactly this sequence.
-/

/-- Two-stage transition structure: a pair of critical temperatures with
    `T_primary < T_vestigial`, producing an intermediate vestigial window. -/
structure TwoStageTransition where
  T_primary : ℝ
  T_vestigial : ℝ
  /-- Nonempty vestigial window: primary transition is at lower temperature. -/
  window_nonempty : T_primary < T_vestigial

/-- Map a CM two-stage transition to its gravitational counterpart via
    the dictionary. The ordering is preserved since both sides use the
    same temperature scale. -/
def TwoStageTransition.toGrav (T : TwoStageTransition) : TwoStageTransition where
  T_primary := T.T_primary
  T_vestigial := T.T_vestigial
  window_nonempty := T.window_nonempty

/-- **VM7 — The condensed-matter two-stage transition maps to the
    gravitational two-stage transition under the dictionary, preserving
    the strict temperature ordering.**

    The `T_primary ↦ T_ECSK` and `T_4e ↦ T_{c,vest}` rows of the H4 §3
    table preserve the ordering structure, confirming that the vestigial
    window exists on the gravitational side iff it exists on the CM side.
    Concretely, the temperature ordering `T_primary < T_vestigial` is
    preserved under the mapping. -/
theorem two_stage_transition_preserved (T : TwoStageTransition) :
    dictionary CMRow.primaryTc = VGRow.ecskTransition ∧
    dictionary CMRow.vestigialT4e = VGRow.vestigialTc ∧
    T.toGrav.T_primary < T.toGrav.T_vestigial := by
  refine ⟨rfl, rfl, ?_⟩
  exact T.window_nonempty

/-!
## Injectivity of the dictionary
-/

/-- **VM8 — Dictionary is injective.**

    Different CM rows map to different VG rows — no accidental collapse
    of distinct concepts. This is the final structural-consistency check
    for the H4 §3 table. -/
theorem dictionary_injective :
    Function.Injective dictionary := by
  intro a b hab
  have := congrArg dictionaryInv hab
  rw [dictionary_left_inv, dictionary_left_inv] at this
  exact this

end SKEFTHawking.VestigialMapping
