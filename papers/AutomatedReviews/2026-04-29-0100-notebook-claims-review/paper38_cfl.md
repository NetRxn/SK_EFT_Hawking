# Claims Review — paper38 notebooks (Phase6d3_CFL)

Reviewer: claims-reviewer-v2 (notebook adaptation)
Date: 2026-04-29-0100
Targets:
- `SK_EFT_Hawking/notebooks/Phase6d3_CFL_Technical.ipynb`
- `SK_EFT_Hawking/notebooks/Phase6d3_CFL_Stakeholder.ipynb`
Sources of truth consulted:
- `lean/SKEFTHawking/CFLChiralLagrangian.lean` (12 theorem declarations; 0 sorry; 0 axioms)
- `lean/SKEFTHawking/CenterSymmetryConfinement.lean` (Wave 1 — `centerPhase`, `Z3`, `centerPhase_pow_N`, `centerPhase_norm_one`)
- `lean/SKEFTHawking/ChiralSSB_QCD.lean` (Wave 2 — `chiral_unbroken_violates_gmor`)
- `src/cfl/{__init__,cfl_lagrangian,z3_one_form_action,topological_order_check}.py`
- `src/center_symmetry/polyakov_loop.py` (`Z3`, `center_phase`)
- `src/chiral_ssb/{quark_condensate,gmor_check}.py` (`PDG_M_PI=0.137`, `PDG_F_PI=0.092`, `PDG_M_Q=0.0035`, `FLAG_LATTICE_VALUE.sigma=-0.0227`)
- `papers/paper38_cfl/paper_draft.tex`
- `src/core/visualizations.py:9275` (`fig_cfl_z3_center_bridge`)
- `src/core/citations.py` (`HironoTanizaki2018`, `AlfordRajagopalWilczek1999`, `SonStephanov2001`, `SchaeferWilczek1999`, `AlfordSchmittRajagopalSchaefer2008`, `GaiottoKapustinSeibergWillett2015`)
- `docs/counts.tex` (`\cflThms = 12`, `\cflTests = 17`)
- `SK_EFT_Hawking_Inventory_Index.md` (sync 2026-04-27-2030 — Phase 6d Wave 3 SHIPPED + Phase 6d CLOSED entry)

## Summary
- BLOCKER: 0
- REQUIRED: 0
- RECOMMENDED: 2
- INFO: 3

The notebook pair is in unusually good shape. Every theorem name claimed by the prose resolves cleanly in `CFLChiralLagrangian.lean`; every cross-reference to W1 (`centerPhase`, `Z3`, `centerPhase_pow_N`, `centerPhase_norm_one`) and W2 (`chiral_unbroken_violates_gmor`) resolves; the theorem count (12 substantive) matches `\cflThms` and the strict `^theorem ` BOL grep; the discipline trend "6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1" matches the Inventory Index verbatim; "Phase 6d CLOSED with this wave" is supported by Inventory line "Phase 6d CLOSED — Track A all three waves shipped"; the GMOR PDG arithmetic in cell `p38t-6-code` is computationally correct (`(0.137)² × (0.092)² ≈ 1.5887e-4 GeV⁴` ≡ `−2 × 0.0035 × (−0.0227) = 1.589e-4 GeV⁴`); and the Hirono-Tanizaki venue is now correct everywhere in the notebook prose (PRL 122, 212001, 2019; arXiv:1811.10608 — confirmed against `CITATION_REGISTRY['HironoTanizaki2018']` which has `journal: 'Phys. Rev. Lett.'`, `volume: 122`, `page: '212001'`, `year: 2019`, `arxiv: '1811.10608'`).

The findings below are precision items, not correctness gaps.

## Findings

### F-1: "Two completely independent code paths" overstates Python-level independence [RECOMMENDED] [class: SD]
- **Location:** Phase6d3_CFL_Technical.ipynb cell `p38t-intro` (intro paragraph 2); cell `p38t-2-md` (§2 closing line); Phase6d3_CFL_Stakeholder.ipynb cell `p38s-intro` ("What this paper formalizes" closing line); cell `p38s-1-md`; cell `p38s-1-code` output line "Closed form  -1/2 + i√3/2".
- **Quote (Technical, p38t-intro):** "**Verifiable to machine precision via independent code paths.**"
- **Quote (Technical, p38t-2-md):** "Two completely independent code paths:" (introducing the cell that prints `|ω_CFL − ω_QCD| = 0.00e+00`).
- **Quote (Stakeholder, p38s-intro):** "Same generator. *Verifiable to machine precision.* This is the Phase 6d correctness-push anchor."
- **Quote (Stakeholder, p38s-1-md):** "Compute them via independent code paths:"
- **Issue:** Strictly, the two Python evaluations are *structurally* independent (no module-level dependency between `EMERGENT_Z3_PHASE` in `src/cfl/z3_one_form_action.py` and `center_phase(Z3)` in `src/center_symmetry/polyakov_loop.py` — they live in disjoint subpackages, neither imports the other for the constant), but they are *numerically identical by construction*: both reduce to `complex(math.cos(2*math.pi/3), math.sin(2*math.pi/3))` evaluated by the same C `libm` routines. The `|diff| = 0.00e+00` is therefore not an empirical coincidence — it is exact bit-for-bit at IEEE-754 because the two expressions compile to the same FP op sequence. The current prose elides this. A reader could plausibly conclude that two genuinely separate algorithms (one using `cmath.exp`, one using `cos+i·sin`, one using a Taylor series, or one going through `numpy.exp(2j*pi/3)`) produced agreeing numbers — that is not what is happening.
- **Evidence:**
  - `src/cfl/z3_one_form_action.py:23-25`:
    ```python
    EMERGENT_Z3_PHASE: complex = complex(
        math.cos(2 * math.pi / 3), math.sin(2 * math.pi / 3)
    )
    ```
  - `src/center_symmetry/polyakov_loop.py:39-45`:
    ```python
    def center_phase(z: CenterZN) -> complex:
        return complex(math.cos(2 * math.pi / z.N), math.sin(2 * math.pi / z.N))
    ```
    With `Z3 = CenterZN(N=3)` (line 36), `center_phase(Z3)` evaluates the literal-identical expression to `EMERGENT_Z3_PHASE`.
  - The Lean theorem `CFL_emergent_Z3_matches_QCD_center_Z3` is proved by `rfl` after `unfold` (lines 100–103) — both Lean defs reduce to `cexp (2 * π * I / 3)`. The substantive content is the *identification across two derivations* (Hirono-Tanizaki Cooper-pair structure vs. SU(3) bare-gauge center), and that content is real. The Python pretends to be an *independent computational check* of that identification, but it is computing the same floating-point expression twice.
- **Suggested fix:** Replace "independent code paths" wording with one of:
  - "two structurally separate definitions that should yield the same closed form" (honest about Python-level scope; emphasizes the substantive content is the *identification across two derivations*, not a numerical fluke);
  - "verifiable in Lean by `rfl` after unfolding both definitions; the Python mirrors the same closed form" (foregrounds Lean as the verification surface, demotes Python to documentary mirror);
  - or, do the work to make it actually independent — e.g., compute `QCD_CENTER_Z3_PHASE` via `cmath.exp(2j*math.pi/3)` while keeping `EMERGENT_Z3_PHASE` as `complex(cos, sin)`. The two expressions then differ in their FP rounding paths and `|diff|` becomes a genuine ~1e-16 quantity rather than identically zero, which both more honestly reflects "agreeing to machine precision" and tightens the demonstrative force of the cell.

### F-2: Mass term scaling factor in cell `p38t-4-code` is undocumented [RECOMMENDED] [class: SD]
- **Location:** Phase6d3_CFL_Technical.ipynb cell `p38t-4-code`; Phase6d3_CFL_Stakeholder.ipynb cell `p38s-3-code`.
- **Quote (Technical, p38t-4-code, code line):** `kt = cfl_kinetic_term(abs(phi) * 2)`
- **Quote (Stakeholder, p38s-3-code, code line):** `kin = cfl_kinetic_term(abs(phi) * 2)`
- **Issue:** Both notebook cells call `cfl_kinetic_term(abs(phi) * 2)` — i.e., they pass `2|Φ|` as the "derivative norm," which forces the kinetic term to evaluate to `0.5 · (2|Φ|)² = 2|Φ|²`. This is a presentational choice (it makes the printed kinetic value `2.0000` instead of `0.5000` for `|Φ|=1`, which loosely "looks more like" a non-trivial Lagrangian), but the Lean theorem `cflKineticTerm_nonneg` and the Python function `cfl_kinetic_term(d_phi_norm)` are agnostic about what `d_phi_norm` represents — it is the magnitude of `∂Φ`, not `|Φ|`. By substituting `2|Φ|` for `|∂Φ|`, the cells implicitly assert "for these illustrative choices we set `|∂Φ| = 2|Φ|`" with no annotation. A reader trying to map the prose ("kinetic term is `(1/2)|∂Φ|²`") to the printed numbers will be confused.
- **Evidence:**
  - `src/cfl/cfl_lagrangian.py:26-28`:
    ```python
    def cfl_kinetic_term(d_phi_norm: float) -> float:
        return 0.5 * d_phi_norm**2
    ```
  - Lean `cflKineticTerm dPhi_norm := (1/2) * dPhi_norm^2` (line 171); the parameter is the derivative norm, not `|Φ|`.
  - The notebook prose in `p38t-4-md` says only "kinetic term `(1/2)|∂Φ|²`" — it does not motivate the choice of `|∂Φ| = 2|Φ|` for the demonstration.
- **Suggested fix:** Either (a) replace `abs(phi) * 2` with a separate scalar `d_phi_norm = 1.0` (or any fixed value with a brief comment "# illustrative |∂Φ| value; the kinetic term function is agnostic about the source"), and let the kinetic-column print as a constant; or (b) keep the current form but add a markdown line above each cell explicitly stating the substitution: "*For the demonstration we set `|∂Φ| = 2|Φ|`; the kinetic term is independent of `Φ` itself except through `|∂Φ|`.*" Option (a) is cleaner and removes the implicit physics-modeling assumption from a formula-neutral cell.

### F-3: Stakeholder mid-paragraph nit — "three quark-flavor flavors via Goldstone bosons" is malformed prose [INFO] [class: SD]
- **Location:** Phase6d3_CFL_Stakeholder.ipynb cell `p38s-intro` (paragraph 4, third bullet of "remarkable properties").
- **Quote:** "Quarks come in three quark-flavor flavors via Goldstone bosons of the residual symmetry."
- **Issue:** The line is duplicated/garbled — "three quark-flavor flavors" is not a coherent sentence, and the broader claim ("Quarks come in [N] flavors via Goldstone bosons") is itself wrong: Goldstone bosons in CFL parametrize the *broken* coset SU(3)_L × SU(3)_R / SU(3)_V, they don't "give the quarks flavors." This is a stakeholder-only line and doesn't carry any computational chain, but it is a visible non-sequitur on the most read-by-humans surface. Not a TN/IA issue (no theorem or number is wrong); not load-bearing for the wave's correctness-push claim.
- **Evidence:**
  - The technical notebook does not contain this sentence (it only describes the `isCFLPhase` predicate and the diquark order parameter — no claim about quark Goldstone counts).
  - Standard CFL exposition (Alford-Rajagopal-Wilczek 1999, Schäfer-Wilczek 1999): the unbroken diagonal is SU(3)_{c+L+R}; the chiral coset has 8 broken generators yielding 8 Goldstone bosons (analogues of the QCD pion octet, plus a heavy η′-like ninth from breaking U(1)_A with anomaly).
- **Suggested fix:** Replace the bullet with something like: "Eight Goldstone bosons emerge from the broken chiral coset SU(3)_L × SU(3)_R → SU(3)_V (analogues of the QCD pion octet)." Or, simpler — drop the bullet entirely; the surrounding bullets ("QCD vacuum is a color superconductor," "all eight gluons get masses") already convey the symmetry-breaking story.

### F-4: Visualization docstring carries stale "JHEP 12 (2018)" venue for Hirono-Tanizaki — not a notebook claim, but visible via the figure [INFO] [class: TN/SD]
- **Location:** `src/core/visualizations.py:9295` (docstring of `fig_cfl_z3_center_bridge`); `src/cfl/__init__.py:23` (subpackage docstring).
- **Quote (visualizations.py:9295):** "Source: Alford-Rajagopal-Wilczek NPB 537 (1999); Son-Stephanov PRL 86 (2001); Hirono-Tanizaki JHEP 12 (2018);"
- **Quote (cfl/__init__.py:23):** "Hirono-Tanizaki, JHEP 12 (2018): emergent ℤ_3 one-form symmetry."
- **Issue:** The Hirono-Tanizaki paper (arXiv:1811.10608) was submitted to arXiv in November 2018 and published in *Phys. Rev. Lett.* 122, 212001 in **May 2019**. The notebook prose is correct (`p38t-2-md` and `p38s-intro` both cite "PRL 122, 212001, 2019; arXiv:1811.10608"), as is `papers/paper38_cfl/paper_draft.tex` (line 265: "Phys.\ Rev.\ Lett.\ \textbf{122}, 212001 (2019); arXiv:1811.10608.") and `CITATION_REGISTRY['HironoTanizaki2018']` (`journal: 'Phys. Rev. Lett.'`, `volume: 122`, `page: '212001'`, `year: 2019`). However, the `fig_cfl_z3_center_bridge` figure docstring and the `src/cfl/__init__.py` subpackage docstring still carry the now-superseded "JHEP 12 (2018)" venue. This is exactly the false-positive class the verification request flagged. The notebook itself is clean, but anyone following the figure's "Source:" line back to a venue will hit a mismatch.

  Note: the task brief specifically called out "Hirono-Tanizaki citation: PRL 122, 212001 (2019), arXiv:1811.10608 — confirm the arXiv ID and venue are correct (this was a known false-positive earlier in the project; verify it stays correct now)." The notebook claim is correct; the surrounding non-notebook docstrings still hold the old venue.
- **Evidence:**
  - `papers/paper38_cfl/paper_draft.tex:262-265` (bibliography): "PRL 122, 212001 (2019); arXiv:1811.10608" — correct.
  - `src/core/citations.py:3394-3409` (registry): all fields point to the PRL form.
  - The Lean module docstring at `lean/SKEFTHawking/CFLChiralLagrangian.lean:26-27` also uses the corrected form: "Hirono-Tanizaki, PRL 122, 212001 (2019) [arXiv:1811.10608]: quark-hadron continuity beyond Landau-Ginzburg paradigm via ℤ_3 one-form symmetry".
  - The two stale references are both in non-notebook surfaces (`src/core/visualizations.py:9295` and `src/cfl/__init__.py:23`).
- **Suggested fix:** Out of scope for the notebook review (the notebook prose itself is correct), but flag for upstream cleanup: replace both stale "JHEP 12 (2018)" mentions with "PRL 122, 212001 (2019); arXiv:1811.10608" in `src/core/visualizations.py:9295` and `src/cfl/__init__.py:23`. The notebook does not need any change for this finding.

### F-5: Discipline trend phrasing in technical §8 is correct as a snapshot but invites future drift [INFO] [class: SD]
- **Location:** Phase6d3_CFL_Technical.ipynb cell `p38t-8-md` (last paragraph).
- **Quote:** "Discipline trend: 6c.3 = 12, 6b.1 = 5, 6d.1 = 6, 6d.2 = 4, **6d.3 = 1** (single first-pass identity-wrapper caught by Lean's unused-variable linter)."
- **Issue:** The trend is correct as of the wave-shipping snapshot (matches Inventory Index "Discipline metric trend (5 waves): 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1") and the technical notebook is the right place to record it. However, the Inventory Index has since been updated to an 8-wave trend ("Updated discipline trend (8 waves): 6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3" per sync 2026-04-28-0030). Future Phase-6c/d waves will continue extending the trend. The notebook records the partial trend without marking it as a snapshot. Not a current-state error, but the absence of an "as of <date>" qualifier means the prose will read as wrong as soon as another wave ships, even though the wave-3 row itself stays correct. Not load-bearing for the paper38 correctness-push claim.
- **Evidence:**
  - Inventory Index line (`SK_EFT_Hawking_Inventory_Index.md`, sync 2026-04-27-2030): the original 5-wave trend the notebook copies.
  - Inventory Index line (sync 2026-04-28-0030, post-Phase-6c W4+W5 strengthening): 8-wave trend now `6c.3=12, 6b.1=5, 6d.1=6, 6d.2=4, 6d.3=1, 6c.1=2, 6c.4=3, 6c.5=3`. The wave-3 entry (`6d.3=1`) is unchanged, so the *claim about this wave* remains correct, but the trend listing is no longer the latest project view.
- **Suggested fix:** Either (a) add a snapshot date — "Discipline trend at wave-3 ship (5 waves applied): 6c.3=12, ...". Or (b) accept that the trend grows and don't bother — the wave-3 entry is not at risk of changing. Option (a) is the smaller fix and removes the "stale-as-of-tomorrow" reading without requiring future updates. Lowest priority.

## Verification matrix (PASS rows omitted from findings; recorded for completeness)

### Theorem-name resolution (TN class — all PASS)
The notebook references the following Lean names. Each was verified to exist in `lean/SKEFTHawking/CFLChiralLagrangian.lean` with `grep -cE "^(theorem|def|noncomputable def|abbrev|lemma) <name>\b"`:

| Name (notebook prose) | Lean kind | File-line |
|----|----|----|
| `isCFLPhase_iff_magnitude_pos` | theorem | line 59 |
| `CFL_emergent_Z3_matches_QCD_center_Z3` | theorem | line 96 |
| `emergentZ3_pow_3` | theorem | line 111 |
| `emergentZ3_norm_one` | theorem | line 120 |
| `emergentZ3_sum_cube_roots` | theorem | line 130 |
| `cflKineticTerm_nonneg` | theorem | line 177 |
| `cflMassTerm_chiral_limit` | theorem | line 190 |
| `cflMassTerm_pos_in_cfl_phase` | theorem | line 200 |
| `H_TopologicalOrderBeyondLG` | def (tracked Prop) | line 218 |
| `H_TopologicalOrderBeyondLG_witness` | theorem | line 225 |
| `H_TopologicalOrderBeyondLG_falsifier_trivial` | theorem | line 236 |
| `H_TopologicalOrderBeyondLG_falsifier_too_large` | theorem | line 247 |
| `cfl_phase_with_gmor_dual_broken` | theorem | line 265 |

13 of 13 resolve. (Total includes 12 substantive theorems + the `H_TopologicalOrderBeyondLG` predicate `def`; the §8 inventory table in the technical notebook bundles the predicate `def` and its witness/falsifier theorems into rows 9, 10, 11 — the resolved count is consistent with the "12 substantive" headline because rows 9 and 11 of the table aggregate sub-items.)

### Cross-reference resolution (TN class — all PASS)
- W1 `centerPhase` → `lean/SKEFTHawking/CenterSymmetryConfinement.lean:53` (noncomputable def). PASS.
- W1 `Z3` → `CenterSymmetryConfinement.lean:47` (def, not "instance"; the verification request mentioned "`CenterZN.Z3` instance" — `Z3` is a `def`, but the qualified name `SKEFTHawking.CenterSymmetryConfinement.Z3` is what the Lean cross-bridge actually consumes, and that resolves correctly. The Inventory Index also uses "`CenterZN.Z3`" loosely for the same object). PASS.
- W1 `centerPhase_pow_N` → `CenterSymmetryConfinement.lean:59`. PASS.
- W1 `centerPhase_norm_one` → `CenterSymmetryConfinement.lean:75`. PASS.
- W2 `chiral_unbroken_violates_gmor` → `lean/SKEFTHawking/ChiralSSB_QCD.lean:152`. PASS.

### Cross-bridge invocation check (verification request item)
- `cfl_phase_with_gmor_dual_broken` (lines 265–276 of CFLChiralLagrangian.lean) — proof body inspection:
  - First conjunct (`sigma < 0`): proved by-contra; the body invokes `SKEFTHawking.ChiralSSB_QCD.chiral_unbroken_violates_gmor m_pi f_pi m_q sigma h_mq h_pi h_fpi h_nonneg h_gmor` (lines 274–275). LOAD-BEARING call to W2's contrapositive. PASS.
  - Second conjunct (`0 < diquarkMagnitude Φ`): proved by `(isCFLPhase_iff_magnitude_pos Φ).mp h_cfl` (line 276). LOAD-BEARING call to W3's biconditional. PASS.
- Both conjuncts use different load-bearing theorems (the verification request's specific item is satisfied — not an identity wrapper).

### ω closed-form verification (numeric class — PASS)
- `EMERGENT_Z3_PHASE` printed value: `(-0.49999999999999983+0.8660254037844387j)`.
- Closed form: `cos(2π/3) + i·sin(2π/3) = −1/2 + i·(√3/2) ≈ −0.5 + 0.866025i`. Match.
- `QCD_CENTER_Z3_PHASE = center_phase(Z3)` evaluates to the same expression. Match.
- ω³: notebook prints `(0.9999999999999998 - 4.996003610813204e-16j)` — within 1e-15 of `1+0i`. Lean: `emergentZ3_pow_3` returns `= 1`. PASS.
- |ω|: notebook prints `1.0000000000`. Lean: `emergentZ3_norm_one` returns `= 1`. PASS.
- `1 + ω + ω²`: notebook prints `3.330e-16j` — within 1e-15 of `0`. Lean: `emergentZ3_sum_cube_roots` returns `= 0`. PASS.

### GMOR cross-bridge numerical check (cell `p38t-6-code` — PASS)
- LHS = `m_π² · f_π² = (0.137)² · (0.092)² = 0.018769 · 0.008464 = 1.5887e-4 GeV⁴`. Notebook prints `1.589e-04`. Match.
- RHS = `−2 · m_q · σ = −2 · 0.0035 · (−0.0227) = 1.589e-4 GeV⁴`. Notebook prints `1.589e-04`. Match.
- `gmor_match = abs(LHS − RHS) < 1e-4`: notebook prints `True`. Match.
- W2 `gmor_pdg_match` Lean theorem certifies the same agreement at PDG/FLAG values. PASS.

### Theorem count claim (IA class — PASS)
- `\cflThms = 12` in `docs/counts.tex:43`. PASS.
- Strict `grep -cE "^theorem " lean/SKEFTHawking/CFLChiralLagrangian.lean = 12`. PASS.
- Notebook prose "12 substantive" matches.

### Discipline trend (IA class — wave-3 row PASS, full trend stale by F-5)
- "6d.3 = 1 (single first-pass identity-wrapper caught by Lean's unused-variable linter)" — matches Inventory Index sync 2026-04-27-2030 exactly. PASS.
- "Phase 6d CLOSED with this wave" — matches Inventory line "Phase 6d CLOSED — Track A all three waves shipped". PASS.

### Citation existence (citation class — all PASS)
The notebook prose names the following primary references; every one was verified in `src/core/citations.py` and in `papers/paper38_cfl/paper_draft.tex` `\bibitem{}` blocks:

| BibKey | Notebook surface | Registry entry | Paper bibitem | Status |
|----|----|----|----|----|
| `HironoTanizaki2018` | technical p38t-2-md, stakeholder p38s-intro | `citations.py:3394` | `paper_draft.tex:262` | PASS |
| `AlfordRajagopalWilczek1999` | implicit (registered) | `citations.py:3346` | `paper_draft.tex:245` | PASS |
| `SonStephanov2001` | implicit (registered) | `citations.py:3362` | `paper_draft.tex:251` | PASS |
| `SchaeferWilczek1999` | technical p38t-3-md (stakeholder p38s-intro paragraph "quark-hadron continuity") | `citations.py:3378` | `paper_draft.tex:257` | PASS |
| `AlfordSchmittRajagopalSchaefer2008` | (paper-only; not in notebook prose) | `citations.py:3429` | `paper_draft.tex:268` | PASS |
| `GaiottoKapustinSeibergWillett2015` | (paper-only; not in notebook prose) | `citations.py:3411` | `paper_draft.tex:272` | PASS |

All notebook citations resolve to real registry entries and real bibitems in the paper. The Hirono-Tanizaki venue is the post-correction PRL form everywhere except the two stale docstrings flagged in F-4 (both non-notebook surfaces).

### Visualization presence (verification request item — PASS)
- `fig_cfl_z3_center_bridge` defined at `src/core/visualizations.py:9275`. PASS.
- Referenced via `# viz-ref: fig_cfl_z3_center_bridge` in both notebooks (Technical `p38t-7-code`, Stakeholder `p38s-5-code`). PASS.
- The figure docstring at lines 9290–9296 references the exact theorems Stakeholder §5 / Technical §7 describe (cube-roots-of-unity ω; ℤ_3 charge classification matrix). PASS.
- Caveat: figure docstring's "Source:" line carries the stale "JHEP 12 (2018)" Hirono-Tanizaki venue — see F-4.

### `H_TopologicalOrderBeyondLG` predicate behavior (numeric class — PASS)
The notebook prints, for `charge ∈ {0, 1, 2, 3}`, predicate-conjunct values matching `class H_TopologicalOrderBeyondLG`:
- `charge=0`: cyclic_z3=True, nontrivial=False, holds=False — matches Lean falsifier `_falsifier_trivial`.
- `charge=1`: cyclic_z3=True, nontrivial=True, holds=True — matches Lean witness `_witness`.
- `charge=2`: cyclic_z3=True, nontrivial=True, holds=True — consistent with Lean predicate (no separate witness, but predicate satisfied).
- `charge=3`: cyclic_z3=False, nontrivial=True, holds=False — matches Lean falsifier `_falsifier_too_large`.

PASS.

## Non-reproducing prior findings
None — there is no prior `claims_review.json` for paper38 in the consulted directory.

## Closing assessment
This is the cleanest notebook pair in this review batch. The two waves of Phase-6d preemptive-strengthening discipline (6d.1's multi-pass review protocol applied prospectively; 6d.2's first-pass linter-driven catch) appear to have transferred to documentation prose: every notebook claim with a Lean theorem behind it resolves; every cross-reference resolves; every numerical anchor recomputes correctly; the citation registry, paper bibliography, and notebook prose are aligned on the corrected Hirono-Tanizaki venue.

The two RECOMMENDEDs (F-1 "independent code paths" overstating Python-level independence; F-2 the undocumented `abs(phi) * 2` substitution in kinetic-term cells) are presentational tightenings rather than correctness gaps. The three INFOs (F-3 the malformed "quark-flavor flavors" stakeholder bullet; F-4 stale figure-docstring venue not surfaced in notebook prose; F-5 trend-list snapshot framing) are the smallest-stakes class. There are no BLOCKERs and no REQUIREDs.
