# Claims Review — paper32 notebooks (Phase6c1_StrongCPDarkEnergy)

**Reviewer:** claims-reviewer (notebook adaptation)
**Run date:** 2026-04-29-0100
**Targets:**
- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/notebooks/Phase6c1_StrongCPDarkEnergy_Technical.ipynb`
- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/notebooks/Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb`

**Sources of truth consulted:**
- `lean/SKEFTHawking/StrongCPTopologicalDE.lean` (8 substantive theorems, 0 sorry, 0 axioms — confirmed)
- `lean/SKEFTHawking/Z16AnomalyComputation.lean` (`sm_anomaly_with_nu_R`)
- `lean/SKEFTHawking/ModularInvarianceConstraint.lean` (`framing_anomaly_constraint`)
- `src/strong_cp_de/{__init__,zhitnitsky_eval,combined_de_consistency}.py`
- `src/core/visualizations.py:9134` (`fig_zhitnitsky_de_theta_scan`)
- `src/core/visualizations.py:45-65` (`COLORS` dict)
- `src/core/citations.py` (`CITATION_REGISTRY`)
- `papers/paper32_strong_cp_de/paper_draft.tex`
- `docs/counts.tex` (`\strongCpDeThms = 8`, `\strongCpDeTests = 14` — match notebook claims)

## Summary
- BLOCKER: 0
- REQUIRED: 1
- RECOMMENDED: 4
- INFO: 3

Both notebooks are substantively clean: every Lean theorem cited resolves to an existing non-`sorry` declaration; the 8-theorem total + 0-sorry + 0-new-axioms claims match `grep` against the Lean file; the central numerical results (`240×`, `~120 orders`, `6.71e-9 eV⁴`, `2.8e-11 eV⁴`, the unit-conversion factor `6.71e-3 eV⁴/GeV⁶`) reproduce when the imported `src/strong_cp_de` code is executed; cross-bridge calls to `Z16AnomalyComputation.sm_anomaly_with_nu_R` and `ModularInvarianceConstraint.framing_anomaly_constraint 24` exist as named Lean theorems. The findings below are mostly small color/figure-prose drift and one acknowledgement-of-precision IA item.

## Findings

### F-1: Stakeholder caption mis-describes observed-bar color as "dissipative-blue" [REQUIRED] [class: SD]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-5-md` (Section 5, "Visualizing the prediction")
- **Quote:** "Three vacuum-energy scales side-by-side on a log axis: the Planck-natural $M_P^4 \approx 10^{112}$ eV⁴ (top, amber), Zhitnitsky's $\sim 10^{-9}$ eV⁴ (middle, blue), and observed $\sim 10^{-11}$ eV⁴ (bottom, **dissipative-blue**)."
- **Issue:** The observed-band bar in `fig_zhitnitsky_de_theta_scan` is rendered using `COLORS["dissipative"]`, which is defined as **amber/tan** `#D4A843`, not blue.
- **Evidence:**
  - `src/core/visualizations.py:50` — `"dissipative": "#D4A843", # Amber — new correction (our result, colorblind-safe)`
  - `src/core/visualizations.py:9242` — `colors_right = [COLORS["amber"], COLORS["steel_blue"], COLORS["dissipative"]]`
  - The figure therefore shows amber (top), steel-blue (middle), amber-tan (bottom) — not "dissipative-blue".
- **Suggested fix:** Replace "dissipative-blue" with "amber-tan" or simply "amber" to match the rendered figure. Alternatively, if the intent is colour-class semantics, write "(bottom, amber — same hue family as the dissipative-correction palette used elsewhere)".

### F-2: Hard-coded `M_P^4 ≈ 1.0e+112 eV⁴` is off by ~2.2× from the actual Planck-mass-fourth [RECOMMENDED] [class: IA]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-1-code` (Section 1 print) and `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-3-code` (Section 3, the `orders_below_planck = 112 - math.log10(rho_zhitnitsky)` line)
- **Quote (cell 1):** `print(f'Planck-natural M_P⁴            ≈ 1.0e+112 eV⁴ (vacuum-energy naturalness scale)')`
- **Issue:** $(1.22 \times 10^{28}\,\mathrm{eV})^4 = 2.21 \times 10^{112}\,\mathrm{eV}^4$, not $1.0 \times 10^{112}$. The technical notebook's literal `1.0e+112` understates the actual value by a factor 2.2. The same value `1.0e112` is then used as the top bar of `fig_zhitnitsky_de_theta_scan` at `src/core/visualizations.py:9241` (`values = [1.0e112, ...]`), and as the divisor in the inline formula `orders_below_planck = 112 - math.log10(rho_zhitnitsky)` (which hard-codes $\log_{10}M_P^4 = 112$ instead of $112.345$).
- **Evidence:**
  - The stakeholder notebook computes the same quantity with full precision: cell `p32s-1-code` uses `M_P_EV = 1.22e28; M_P4_EV4 = M_P_EV ** 4` and prints `M_P⁴ ≈ 2e+112` correctly.
  - Recomputation: `(1.22e28)**4 = 2.215e+112` (2.2× the hard-coded value).
  - The qualitative claim "$\sim$120 orders below Planck-natural $M_P^4$" survives — the more accurate computation gives 120.5 orders, the hard-coded computation gives 120.2 orders, both round to 120. So this is an internal-consistency / display-precision issue rather than a load-bearing physics drift.
- **Suggested fix:** Either (a) replace the hard-coded `1.0e+112` with `2.2e+112` (or computed `(1.22e28)**4`) for consistency with the stakeholder notebook, or (b) explicitly label the value as an order-of-magnitude shorthand (e.g., `~10^{112}`). Same fix needed in `src/core/visualizations.py:9241` for `fig_zhitnitsky_de_theta_scan` right-panel data and Section 3 `orders_below_planck = 112 - math.log10(...)` formula. Recommended: switch the figure data and the print statement to compute `M_P_EV**4` and use that consistently.

### F-3: Stakeholder Section 1 quotes "ratio is $\sim 10^{-120}$" but the actual observed/$M_P^4$ ratio is closer to $10^{-123}$ [RECOMMENDED] [class: IA]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-1-md`
- **Quote:** "Planck satellite + DESI Year-1 measurements give $\Lambda \approx 2.8 \times 10^{-11}$ eV⁴. **The ratio is $\sim 10^{-120}$.** This is the worst fine-tuning in all of physics".
- **Issue:** $\rho_{\rm obs}/M_P^4 = 2.8\times 10^{-11} / 2.21 \times 10^{112} \approx 1.27 \times 10^{-123}$, i.e. ~123 orders of magnitude. The "$10^{-120}$" number is the conventional textbook shorthand and is widely-used, but it doesn't equal the actual ratio computed from the numbers the notebook itself supplies.
- **Evidence:** Recomputation: `2.8e-11 / (1.22e28)**4 = 1.264e-123`, $\log_{10} \approx -122.9$.
- **Suggested fix:** Either (a) state "approximately $10^{-120}$" or "~120 orders" consistently as a textbook shorthand and note this is the conventional CC-problem framing; or (b) be precise: "$\sim 10^{-123}$" / "$\sim 123$ orders". Choosing (a) is consistent with how the technical notebook, paper draft, and figure caption all use "~120 orders" elsewhere; the stakeholder section 3 print statement `121 orders below natural scale` would then also benefit from the same harmonisation.

### F-4: Stakeholder Section 3 print computes "121 orders below natural scale" but every other anchor in the project says "120" [RECOMMENDED] [class: IA]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-3-code` (the `f'{-math.log10(ratio_to_planck):.0f}'` print)
- **Quote (output):** `prediction / M_P⁴          ≈ 3e-121    (121 orders below natural scale)`
- **Issue:** The actual computed value of `-log10(ratio_to_planck)` is $120.52$, which `:.0f` rounds to `121`. Every other place in the corpus — the technical notebook ("$\sim$120 orders"), the paper draft ("approximately 120 orders"), the visualization docstring ("~120 orders"), the Lean theorem docstring at line 117–118 ("~120 orders") — uses 120. The stakeholder running output displays "121", which contradicts its own surrounding prose ("The visible gap … represents the $\sim 120$-order suppression").
- **Evidence:**
  - `lean/SKEFTHawking/StrongCPTopologicalDE.lean:118` — "Numerical: ρ_predicted ≈ 6.71e-9 eV⁴; Planck-natural ρ_vacuum_naive ~ M_P^4 ≈ 1e112 eV⁴" → 120 orders.
  - `papers/paper32_strong_cp_de/paper_draft.tex` — "approximately $120$ orders of magnitude below the Planck-natural" (multiple occurrences).
  - `src/core/visualizations.py:9145-9147` — "~120 orders of magnitude below the Planck-natural M_P^4".
  - Recomputation: $-\log_{10}(\rho_{\rm Zhit}/M_P^4) = 120.52$, which rounds up to 121 with `:.0f` but truncates to 120 with `:d` of the floor.
- **Suggested fix:** Change `:.0f` to `:.1f` (so the print shows `120.5 orders`) or use `int(-math.log10(ratio_to_planck))` (truncation → 120) — either resolves the cosmetic mismatch with the surrounding "$\sim 120$" prose. Note the underlying physics is fine; this is purely a display-rounding inconsistency.

### F-5: Technical-notebook narration for `IsAnomalyMatchingCompatible_no_planck_theta` glosses what the theorem proves [RECOMMENDED] [class: TN-adjacent]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-4-md`
- **Quote:** "any vacuum at $\theta = 1$ structurally fails (Lean: `IsAnomalyMatchingCompatible_no_planck_theta`)."
- **Issue:** The Lean theorem actually has signature `(tv : ThetaVacuum) (h_planck : tv.theta = 1) : False` — i.e. it proves you cannot construct a `ThetaVacuum` with `θ = 1` at all (the structure invariant `theta_small : |theta| ≤ 1e-9` is violated). It does *not* "evaluate the three pillars and find they fail"; it short-circuits at the EDM-bound invariant. The phrase "structurally fails" is loose but defensible — the more precise statement is "**cannot exist** as a `ThetaVacuum`".
- **Evidence:** `lean/SKEFTHawking/StrongCPTopologicalDE.lean:168-174` — body is `linarith` against `tv.theta_small`, never touches pillars (a) or (c).
- **Suggested fix:** Tighten phrasing to: "any putative $\theta = 1$ vacuum cannot satisfy the EDM-bound invariant carried by the `ThetaVacuum` structure (Lean: `IsAnomalyMatchingCompatible_no_planck_theta`, which derives `False` from `tv.theta = 1`)." This is consistent with the analogous Lean theorem `theta_planck_natural_violates_edm_bound` already discussed in Section 2.

### F-6: `H_BothActiveGivesInconsistency` is a tracked-`Prop`, but the notebooks don't flag this [INFO] [class: HD]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-5-md` and `Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-4-md`
- **Quote (technical):** "The Lean theorem `combined_zhitnitsky_qtheory_exceeds_observation` proves this for any positive $\rho_{q}$."
- **Issue:** The theorem's conclusion is `H_BothActiveGivesInconsistency (zhitnitskyDE_eV4 0.1 + rho_qtheory)`, which is a *tracked-hypothesis predicate* (`def H_BothActiveGivesInconsistency rho := rho > zhitnitskyDE_eV4 0.1`). The Lean module docstring at lines 178-190 explicitly labels it a "Tracked hypothesis: BOTH the Zhitnitsky mechanism … AND a residual q-theory DE contribution … are simultaneously active. The structural inconsistency is that the combined contribution strictly exceeds the Zhitnitsky-alone prediction at PDG Λ_QCD". Both notebooks describe the result accurately at the *content* level (the combined-mechanism scenario fails the saturation threshold) but neither says "this conclusion is wrapped in a tracked-`Prop` named `H_BothActiveGivesInconsistency` that downstream consumers must explicitly accept; the threshold choice (`> zhitnitskyDE_eV4 0.1`) is itself a modelling choice from the project's correctness-push protocol".
- **Evidence:**
  - `lean/SKEFTHawking/StrongCPTopologicalDE.lean:178-205` — `H_BothActiveGivesInconsistency` defined as a `Prop`, not a structural inequality on physical observables; the threshold is `> zhitnitskyDE_eV4 0.1` not `> RHO_DE_OBSERVED_EV4`.
  - The technical notebook in cell `p32t-5-code` does run `H_BothActiveGivesInconsistency(zhitnitsky_de_eV4(LAMBDA_QCD_GEV) + 1e-10)` and reports `.holds = True`, so the *behaviour* is exposed. What's missing is the disclosure that the predicate is a tracked-`Prop` (i.e. that the threshold "$>$ Zhitnitsky-alone-saturation-at-PDG" is a project-internal modelling choice, not a derived constraint).
- **Suggested fix:** Add a sentence in cell `p32t-5-md` (and equivalently `p32s-4-md`) such as: "The threshold against which `H_BothActiveGivesInconsistency` triggers is set to the Zhitnitsky-alone saturation point at PDG $\Lambda_{QCD}$ — a project modelling choice motivated by the Phase 6c.1 correctness-push protocol; see `lean/SKEFTHawking/StrongCPTopologicalDE.lean:178-190` for the rationale." This is a soft HD finding because the underlying theorem is fully proved without `sorry` and the tracked-`Prop` is *self-consistent*; the disclosure gap is about the modelling-choice threshold rather than a hidden axiom.

### F-7: Citation `KlinkhamerVolovik2010` registry title differs from the q-theory framing in stakeholder Section 4 [INFO] [class: SD-adjacent]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-4-md`
- **Quote:** "Klinkhamer and Volovik proposed an earlier topological dark-energy mechanism in 2010 (q-theory: a self-tuning scalar from a 4-form gauge field)."
- **Issue:** The `CITATION_REGISTRY['KlinkhamerVolovik2010']` entry resolves to `arXiv:0907.4887` / JETP Lett. 91, 259 (2010) titled "Cosmological constant from gravitating Skyrmions", not a q-theory 4-form-gauge-field paper. The notes field in the registry says `'q-theory equilibrium relaxation mechanism for cosmological constant'` so the *project intent* is "Klinkhamer-Volovik q-theory framework". This is an INFO-level finding because the citation key is in the registry, the Lean module's references list calls it "q-theory DE" (line 24), and the stakeholder narration is consistent with the registry's notes; but a strict reader looking up arXiv:0907.4887 will see the Skyrmion paper, not q-theory.
- **Evidence:** `src/core/citations.py` — the `KlinkhamerVolovik2010` entry has title "Cosmological constant from gravitating Skyrmions"; arxiv `0907.4887`. Klinkhamer-Volovik q-theory is generally cited via the JETP 2008 paper or arXiv:0806.2805 / 1003.1396 in the literature.
- **Suggested fix:** Out-of-scope for the notebook claims review; flag for the citation-verification pass. Either (a) update the `KlinkhamerVolovik2010` registry entry to point to the canonical q-theory paper, or (b) add a separate `KlinkhamerVolovikQtheory` entry. The notebook prose itself does not need to change once the registry is correct.

### F-8: Notebook intro asserts `lean_verify` axiom-closure result without reproducing the verification [INFO] [class: HD-adjacent]
- **Location:** `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-intro`
- **Quote:** "Lean module: `lean/SKEFTHawking/StrongCPTopologicalDE.lean` (8 substantive theorems, 0 sorry, 0 new axioms; verified `propext, Classical.choice, Quot.sound` only via `lean_verify`)."
- **Issue:** The "0 sorry, 0 new axioms" portion is verified directly: `grep -c "^  sorry" lean/SKEFTHawking/StrongCPTopologicalDE.lean = 0`, `grep -c "^axiom " lean/SKEFTHawking/StrongCPTopologicalDE.lean = 0`. The "8 substantive theorems" portion matches `\strongCpDeThms = 8` in `docs/counts.tex`. The "verified `propext, Classical.choice, Quot.sound` only via `lean_verify`" portion is a meta-claim that this reviewer did not reproduce in this run (running `lean_verify` requires LSP/REPL invocation which is out of scope for a static notebook claims review). The claim is plausible because (a) the module declares no `axiom` directly, (b) all proofs use only standard Mathlib tactics (`linarith`, `norm_num`, `decide`, `simp`, `unfold`, `ring`, `positivity`), and (c) the project's typical 0-axiom modules close under that triple. Flagging as INFO so the reviewer trail records that the claim was not independently rerun.
- **Suggested fix:** None blocking. Optionally, the notebook could store the `lean_verify` output as a hashed reference (e.g., a stamp file `lean/.verify_stamps/StrongCPTopologicalDE.txt` with the closure list) so the claim becomes mechanically reproducible by future reviewers.

## Items checked and PASSED (no findings)

The following claims were verified and resolved cleanly:

- **TN-class (theorem-name resolution)**: All 8 Lean theorem names referenced in the technical notebook table (cell `p32t-8-md`) exist as non-`sorry` declarations in `lean/SKEFTHawking/StrongCPTopologicalDE.lean`:
  `theta_planck_natural_violates_edm_bound` (L66), `zhitnitskyDE_positive` (L95), `zhitnitsky_DE_at_lambda_qcd_within_3_orders` (L111), `zhitnitsky_DE_far_below_planck` (L124), `IsAnomalyMatchingCompatible_witness` (L154), `IsAnomalyMatchingCompatible_no_planck_theta` (L168), `combined_zhitnitsky_qtheory_exceeds_observation` (L200), `sm_framing_anomaly_consistent_with_strong_cp_bound` (L220).
- **Cross-module call sites**: `Z16AnomalyComputation.sm_anomaly_with_nu_R` exists at `lean/SKEFTHawking/Z16AnomalyComputation.lean:73`; `ModularInvarianceConstraint.framing_anomaly_constraint` exists at `lean/SKEFTHawking/ModularInvarianceConstraint.lean:103`. Both are non-`sorry`.
- **IA-class (numerical anchors)**: Recomputed independently:
  - `zhitnitsky_de_eV4(0.1) = 6.710e-9` eV⁴ ✓ matches notebook print and Lean comment.
  - `(2.3e-3)**4 = 2.798e-11` eV⁴ ≈ `RHO_DE_OBSERVED_EV4 = 2.8e-11` ✓.
  - Ratio `prediction/observed = 6.71e-9 / 2.8e-11 = 239.6×`, rounded to `240×` ✓.
  - Coefficient `1/M_P^2` in eV⁻² × `(eV/GeV)^6` conversion: `1/(1.22e19)^2 × 1e36 = 6.72e-3 eV⁴/GeV⁶` ✓ (notebook & Lean use `6.71e-3`, agreement to 0.1%).
  - "$\sim 120$ orders below $M_P^4$": $\log_{10}(M_P^4) - \log_{10}(\rho_{\rm Zhit}) = 112.35 - (-8.17) = 120.52$, rounds to 120 ✓ (qualitatively).
  - Z₁₆ anomaly arithmetic per generation: `(6+3+3+2+1+1) % 16 = 0` ✓ matches `lean/SKEFTHawking/Z16AnomalyComputation.lean:68` particle-content comment; `(6+3+3+2+1) % 16 = 15 ≡ -1 mod 16` ✓ matches `sm_anomaly_is_neg_one` (L104).
  - `H_BothActiveGivesInconsistency` triggering: `True` for `+1e-12, +1e-10, +1e-9, +rho_obs` excess ✓ verified by direct Python execution.
  - Modular phase `exp(2πi · 24/24) = 1 + 0i` ✓ (within 1e-15 numerical error).
- **TP-class (toolchain pin drift)**: No literal toolchain version mention in either notebook. The Lean module compatibility is implicit via the project pin (`lean-toolchain` = `leanprover/lean4:v4.29.0`); no drift to flag.
- **HD-class (hypothesis disclosure)**: The technical notebook explicitly mentions "tracked-`Prop`-style" disclosure for `H_BothActiveGivesInconsistency` (cell `p32t-5-md` paragraph, "load-bearing tracked hypothesis"); the stakeholder notebook discloses the falsifiability mechanism ("project must commit to ONE dark-energy mechanism, not both") in cell `p32s-4-md`. Hypothesis disclosure is adequate at the prose level; F-6 is a soft refinement, not a blocker.
- **SD-class (cardinality drift)**: All cardinality claims pass — 8 substantive theorems matches `\strongCpDeThms = 8` (counts.tex line 33), 14 tests matches `\strongCpDeTests = 14` (counts.tex line 34), 3 pillars of the anomaly-matching predicate matches the Lean `IsAnomalyMatchingCompatible` definition (3 conjuncts), 5 references in cell `p32s-7-md` match the registry/paper bibliography.
- **Citation registry membership**: All five cited references (`Pendlebury2015`, `VanWaerbeke2025`, `Planck2018`, `DESI2024`, `KlinkhamerVolovik2010`) exist in `CITATION_REGISTRY`. All are `doi_verified: None` (consistent with the wider project state per memory `feedback_citation_verification_required.md` — out-of-scope for this review).
- **Stakeholder docs cross-references**: `docs/stakeholder/Phase6c_Implications.md` and `docs/stakeholder/Phase6c_Strategic_Positioning.md` both exist (referenced from `p32s-7-md`).
- **Companion-notebook & paper cross-references**: `papers/paper32_strong_cp_de/paper_draft.tex` exists; `Phase6c1_StrongCPDarkEnergy_Technical.ipynb` is the file under review; both notebooks correctly cite each other.

## Recommendation

The two notebooks are publication-quality after addressing F-1 (color label correction) and the cosmetic IA items F-2/F-3/F-4 (display-precision harmonisation). F-5 is a soft-language tightening; F-6 is an optional disclosure-strengthening; F-7 is a citation-registry follow-up out of scope here; F-8 is an audit-trail informational. **No BLOCKER issues; one REQUIRED fix (F-1) is the only item that materially affects the figure description.**
