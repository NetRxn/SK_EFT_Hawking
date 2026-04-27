---
paper: paper38_cfl
target: notebooks (Phase6d3_CFL_Technical.ipynb, Phase6d3_CFL_Stakeholder.ipynb)
reviewer: adversarial-reviewer (notebook-adapted)
model: claude-opus-4-7
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper38_cfl notebooks

## Summary

Fresh-context audit of `Phase6d3_CFL_Technical.ipynb` and `Phase6d3_CFL_Stakeholder.ipynb` against the source-of-truth quintuple (paper draft, Lean module, Python source, upstream W1, upstream W2). Six citations verified live on arXiv (cache-cold fetch); all match the bibitems including the previously-suspect Hirono-Tanizaki 2018/2019 entry. The 12-substantive-theorem / 0-sorry / 0-new-axiom counts match the Lean source. The correctness-push claim is honestly disclosed in BOTH notebooks as a definitional alias once both sides commit to `exp(2πi/3)`; the substantive content is the *modeling choice* on each side, not a non-trivial algebraic theorem. The cube-roots-sum identity proof is substantive (factorization + sin(2π/3) > 0). The cross-bridge `cfl_phase_with_gmor_dual_broken` is genuinely double-load-bearing (W2 contrapositive + W3 magnitude positivity, both required). Phase 6d "CLOSED" claim is consistent with `RESEARCH_STATUS_OVERVIEW.md` and `Inventory_Index.md` (Track A roadmap-scoped). Discipline trend (6d.3 = 1) confirmed in Inventory.

**Findings: 0 BLOCKER, 1 REQUIRED, 4 RECOMMENDED. Notebooks are submission-track-acceptable** modulo the REQUIRED finding (a Stakeholder-notebook scope gap that risks misrepresenting what the Lean tracked-Prop establishes).

## Findings

### 1.1 — 🔵 RECOMMENDED — Bibkey `Hatsuda2008` is misleading; underlying paper has no Hatsuda authorship

- **Gate:** CitationIntegrity
- **Location:** `papers/paper38_cfl/paper_draft.tex:267-270` (cited from notebook intros indirectly via paper-draft pointers)
- **Observed:** Bibkey `\bibitem{Hatsuda2008}` resolves to "M.~G.~Alford, A.~Schmitt, K.~Rajagopal, and T.~Sch\"afer, ``Color superconductivity in dense quark matter,'' Rev.\ Mod.\ Phys.\ \textbf{80}, 1455 (2008); arXiv:0709.4635."
- **Evidence:** WebFetch arXiv 0709.4635 confirms author list is Alford-Schmitt-Rajagopal-Schäfer. No author named Hatsuda. The bibkey is a misnomer (likely a leftover from an earlier draft pointing to a Hatsuda et al. RMP). The CITATION_REGISTRY entry at `src/core/citations.py:3428-3438` correctly lists the actual authors but keeps the Hatsuda2008 key.
- **Expected:** Bibkey aligned with author list (e.g., `AlfordSchmittRajagopalSchaefer2008` or `ColorSuperconductivityRMP2008`).
- **Fix:** Rename the bibkey across `paper_draft.tex` and `src/core/citations.py`. Notebooks do not directly cite the bibkey, so they are not affected; this is a paper-draft hygiene issue surfaced during cross-reference scan.
- **Cache:** fresh-fetch (arXiv 0709.4635, verdict: match-on-content, key-mismatch)

### 2.1 — 🟡 REQUIRED — Stakeholder notebook §4 implies the Lean module formalizes "different topological sectors with same local order parameter," but `H_TopologicalOrderBeyondLG` does not

- **Gate:** AssumptionDisclosure
- **Location:** `notebooks/Phase6d3_CFL_Stakeholder.ipynb` cell `p38s-4-md` ("Topological order beyond Landau-Ginzburg")
- **Observed:** Stakeholder prose: *"CFL with the same local diquark VEV magnitude can sit in different topological sectors labeled by ℤ_3 charges. The non-trivial sectors {1, 2} are topologically ordered; the trivial sector 0 is plain Landau-Ginzburg, and 3 is outside the cyclic group entirely."* This implies the Lean theorem distinguishes two configurations with the same `|Φ|` but different topological charge.
- **Evidence:** Lean source `lean/SKEFTHawking/CFLChiralLagrangian.lean:218-219` shows `def H_TopologicalOrderBeyondLG (charge : ℕ) : Prop := charge < 3 ∧ charge ≠ 0`. The predicate constrains `charge ∈ {1, 2}`. It is a tracked Prop (assumption) — it does not formalize the local-probe-invisibility content of Hirono-Tanizaki, only that there exist non-trivial ℤ_3 charges in {1, 2}. The Lean docstring (line 210-217) discloses this honestly: *"the predicate enforces charge < 3 (cyclic ℤ_3) AND charge ≠ 0 (nontrivial sector)"* — but the Stakeholder notebook overstates the scope. The Technical notebook §5 correctly identifies it as a "tracked-Prop", but the Stakeholder version does not.
- **Expected:** Stakeholder §4 should disclose that the topological-order content (invisibility to local probes per Hirono-Tanizaki) is encoded as a *tracked-hypothesis assumption*, not derived from a deeper structural fact. A one-sentence honest-scope addition would close this finding (e.g., "The Lean theorem assumes the Hirono-Tanizaki framing as a structural Prop; the topological-order content is consumed, not derived.").
- **Fix:** Add a clarifying sentence to `p38s-4-md` (or to §6 "Honest scope") explicitly noting that `H_TopologicalOrderBeyondLG` is a tracked Prop (assumption) rather than a derived theorem.
- **Cache:** N/A (Lean source verification).

### 3.1 — 🔵 RECOMMENDED — Technical notebook §3 caption claim "Lean emergentZ3_sum_cube_roots (distinguishes Z_3 from Z_2)" is correct but the proof depth is not surfaced

- **Gate:** LeanProofSubstance
- **Location:** `notebooks/Phase6d3_CFL_Technical.ipynb` cell `p38t-3-code` (numerical output annotation)
- **Observed:** The cell annotates `1 + ω + ω² = 0` as "Lean emergentZ3_sum_cube_roots (distinguishes Z_3 from Z_2)". A reader could interpret the Lean theorem as a definitional unfolding of `cexp` arithmetic.
- **Evidence:** Lean source lines 130-165 show the proof uses (i) factorization $z^3 - 1 = (z-1)(z^2+z+1)$ via `ring`, (ii) $\omega \neq 1$ via $\sin(2\pi/3) > 0$ from `Real.sin_pos_of_pos_of_lt_pi`, (iii) `mul_eq_zero` to extract the quadratic factor, (iv) `linear_combination`. This is genuinely **substantive** — not a tautology. The Technical notebook §3 narrative correctly describes "distinguishes ℤ_3 from ℤ_2" but does not disclose that the proof is non-trivial (in contrast to `CFL_emergent_Z3_matches_QCD_center_Z3` which IS disclosed as definitional).
- **Expected:** Either (a) one-line note that the proof is via factorization + sine-positivity, OR (b) leave as-is — this is a low-severity polish issue, not a correctness issue.
- **Fix:** Optionally add a parenthetical "(proof via factorization $z^3-1 = (z-1)(z^2+z+1)$ + $\sin(2\pi/3) > 0$)" to the Technical §3 markdown. RECOMMENDED rather than REQUIRED because the proof IS substantive and the description IS accurate; only the depth disclosure is asymmetric vs the correctness-push.
- **Cache:** N/A (Lean source).

### 4.1 — 🔵 RECOMMENDED — "Phase 6d CLOSED" disclosed without enumerating Track-A scope deferrals

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6d3_CFL_Technical.ipynb` cell `p38t-8-md` (final sentence: "Phase 6d CLOSED with this wave — Track A (W1 + W2 + W3) all shipped end-to-end."); also `Phase6d3_CFL_Stakeholder.ipynb` cell `p38s-7-md` ("Phase 6d closure: all three waves shipped end-to-end").
- **Observed:** Both notebooks claim "Phase 6d CLOSED" without enumerating residual QCD items deferred per the roadmap.
- **Evidence:** `SK_EFT_Hawking_Inventory.md:19` (sync 2026-04-27-2030) and `RESEARCH_STATUS_OVERVIEW.md:312` confirm Phase 6d Track A is closed end-to-end. Inventory line 19 explicitly states: *"Per roadmap scope lock, residual QCD items (β-function, Wilson-loop, full hadron spectrum) deferred to HepLean/PhysLean."* The Stakeholder §6 ("Honest scope") does disclose three scope limitations (lattice QCD sign problem, quark-hadron continuity smooth interpolation not formalized, neutron-star observations) but does not enumerate the β-function / Wilson-loop / hadron-spectrum deferrals. The Technical notebook §8 just says "CLOSED".
- **Expected:** A one-sentence enumeration of the deferred items (β-function, Wilson-loop, full hadron spectrum) would strengthen the closure claim. The Phase 6c W4/W5 notebooks have analogous "Out-of-scope deferrals (per roadmap §A)" disclosures that this notebook lacks.
- **Fix:** Add to Technical §8: *"Per the Phase 6d roadmap scope lock, residual QCD items (β-function, Wilson loops, full hadron spectrum) are deferred to HepLean/PhysLean."* RECOMMENDED rather than BLOCKER because the closure claim is technically supported by the roadmap and the Stakeholder notebook does provide a partial honest-scope section.
- **Cache:** N/A (project documentation cross-check).

### 5.1 — 🔵 RECOMMENDED — Stakeholder intro: "without a thermodynamic phase transition" is a literature claim not anchored to a citation

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6d3_CFL_Stakeholder.ipynb` cell `p38s-intro` ("Quark-hadron continuity" subsection)
- **Observed:** Stakeholder intro: *"Schäfer and Wilczek (1999) made a striking observation: as you decrease density, the CFL phase smoothly evolves into the ordinary confined hadronic phase, without a thermodynamic phase transition."*
- **Evidence:** WebFetch confirms Schäfer-Wilczek 1999 (PRL 82, 3956, hep-ph/9811473) is "Continuity of Quark and Hadron Matter". The "smoothly evolves...without a thermodynamic phase transition" is the headline claim of that paper, and the citation is correct. However, this is a strong physics claim presented to a non-specialist audience without a parenthetical (Schäfer-Wilczek 1999) at point-of-claim. The Hirono-Tanizaki citation is similarly anchored later.
- **Expected:** A parenthetical citation at the claim point would tighten the prose. Lower-severity narrative-polish issue.
- **Fix:** Optional — add `(Schäfer-Wilczek 1999)` after "without a thermodynamic phase transition". RECOMMENDED-only.
- **Cache:** Cache-cold fetch of arXiv hep-ph/9811473, verdict match.

### 5.2 — 🔵 RECOMMENDED — Citations for AlfordRajagopalWilczek1999, SonStephanov2001, SchaeferWilczek1999, HironoTanizaki2018, GaiottoKapustinSeibergWillett2015, Hatsuda2008, Polyakov1978 all live-verified

- **Gate:** CitationIntegrity (positive finding, RECOMMENDED only as audit confirmation)
- **Location:** All paper38 bibitems (lines 245-282 of `paper_draft.tex`).
- **Observed:** Adversarial cross-checked each citation against arXiv / DOI / INSPIRE-HEP. All match.
- **Evidence (per bibitem):**
  1. `AlfordRajagopalWilczek1999` (NPB 537, 443, hep-ph/9804403) — fetched arXiv: title "Color-Flavor Locking and Chiral Symmetry Breaking in High Density QCD"; authors M. Alford, K. Rajagopal, F. Wilczek; NPB 537, pages 443-458, 1999. **Match.**
  2. `SonStephanov2001` (PRD 61, 074012, hep-ph/9910491) — fetched arXiv: title "Inverse meson mass ordering in color-flavor-locking phase of high density QCD"; authors D. T. Son, M. A. Stephanov; PRD 61, 074012, 2000. **Match** (the bibkey says "2001" but the paper-draft's `(2000)` year is correct; arXiv journal-ref is **PRD 61, not PRL 86**, despite the prompt's mention of "PRL 86 with corrections in 2001" — the prompt's hint about a PRL 86 alternative venue does NOT match arXiv 9910491; PRL 86 is a different paper. Citation as written is correct).
  3. `SchaeferWilczek1999` (PRL 82, 3956, hep-ph/9811473) — fetched arXiv: title "Continuity of Quark and Hadron Matter"; T. Schaefer, F. Wilczek; PRL 82, 3956-3959, 1999. **Match.**
  4. `HironoTanizaki2018` (PRL 122, 212001, 2019; arXiv:1811.10608) — fetched arXiv: title "Quark-hadron continuity beyond Ginzburg-Landau paradigm"; Y. Hirono, Y. Tanizaki; PRL 122, 212001, 2019. **Match.** (Previously-suspect from project memory; cleared this round.)
  5. `GaiottoKapustinSeibergWillett2015` (JHEP 02:172, arXiv:1412.5148) — fetched arXiv: title "Generalized Global Symmetries"; D. Gaiotto, A. Kapustin, N. Seiberg, B. Willett; JHEP 02, page 172, 2015. **Match.**
  6. `Hatsuda2008` (RMP 80, 1455, arXiv:0709.4635) — bibitem text correct (Alford-Schmitt-Rajagopal-Schäfer); only the bibkey name is misleading (see finding 1.1). **Content match.**
  7. `Polyakov1978` (PLB 72, 477, no arXiv) — fetched INSPIRE-HEP: A. M. Polyakov, "Thermal Properties of Gauge Fields and Quark Liberation", Physics Letters B 72, pages 477-480, 1978. **Match.**
- **Expected:** Citation integrity is clean.
- **Fix:** None required (positive audit confirmation).
- **Cache:** fresh-fetch (all 7 citations).

## QI Candidate

(none — the findings are localized to paper38 notebooks; no systemic pipeline issue surfaced.)

## Adversarial assessment summary

The notebooks are honest about the substantive content of the correctness-push: the equality `ω_CFL = ω_QCD` is **definitional after both sides commit to `exp(2πi/3)`**, NOT a non-trivial algebraic theorem. The Stakeholder intro discloses this explicitly: *"The Lean theorem... proves equality at the level of the closed-form expression (both reduce to the literal `e^(2πi/3)`); the substantive claim is the physical-derivation independence, not Python-level computational independence."* The Technical §3 says *"In Lean, both reduce definitionally to the same closed form. The substantive content is the identification across two independent derivations."* This level of disclosure is exactly what the project's strengthening-discipline doctrine requires for a P5/structural-tautology-adjacent theorem — the substantive content has been pushed into the *definitions* (which encode the modeling choices justified by literature on each side), and that fact is disclosed.

The downstream theorems (`emergentZ3_pow_3`, `emergentZ3_norm_one`) inherit the cross-module call structure: they invoke W1 lemmas through the correctness-push, so the cross-bridge integrity is structural. The cube-roots-sum identity proof is genuinely substantive (factorization argument, not refl). The W2 cross-bridge (`cfl_phase_with_gmor_dual_broken`) is double-load-bearing. The first-pass discipline-trend (6d.3 = 1, identity-wrapper caught by Lean's unused-variable linter) is consistent with `Inventory.md:19`.

**No BLOCKER findings.** The single REQUIRED finding (2.1) is a one-sentence Stakeholder-notebook clarification that the Hirono-Tanizaki topological-order-beyond-Landau-Ginzburg content is a tracked-Prop assumption rather than derived. The four RECOMMENDED findings are scope-disclosure polish items.
