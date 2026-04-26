---
paper: paper21_majorana_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-25T15:30:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper21_majorana_rung

## Summary

Stage-13 fresh-context sweep of paper 21 produced **9 findings (5 BLOCKER, 3 REQUIRED, 1 RECOMMENDED)**. The just-completed CitationIntegrity round caught all 15 *fresh* bibkey corrections but missed two pre-existing wrong-title bibitems for `WetterichSpinor2013` / `WetterichSpinor2022` that paper21 inherited from a (different, paper20 has them right) bibitem text — these are CitationIntegrity AND CrossPaperConsistency BLOCKERs. Three Lean-substance BLOCKERs found: `H_LeptonNumberViolated := True` makes the headlined no-go theorem `lepton_number_symmetry_obstructs_BCS_form` vacuous (the antecedent `¬ True` is uninhabitable); `IsDiracPMNS`/`IsMajoranaPMNS` defined as `True` make the `isMajoranaPMNS_of_majoranaRungData` "bridge" tautological; and three `DecouplingRegime` "failure-mode" predicates (`not_vestigial`, `not_cosmological`, `weakly_coupled_matter`) are all `True`-typed placeholders sold as semantic content in §6 prose. Paper21 flips from currently-yellow to **RED**: gates 1 (CitationIntegrity), 2 (CrossPaperConsistency), 5 (LeanProofSubstance) all flip to `blocked`.

## Findings

### 1.1 — 🔴 BLOCKER — `WetterichSpinor2013` bibitem title disagrees with arXiv:1201.2871

- **Gate:** CitationIntegrity
- **Location:** `paper21_majorana_rung/paper_draft.tex:540-541`
- **Observed:** Bibitem text `"Spinor gravity and gravitational anomaly"` for arXiv:1201.2871.
- **Evidence:** Fresh fetch of `https://arxiv.org/abs/1201.2871` returns title `"Spinor gravity and diffeomorphism invariance on the lattice"` (C. Wetterich, 2012; published as chapter 4 of LNP 863, DOI `10.1007/978-3-642-33036-0_4`). The cache entry for the same bibkey on `paper20_scalar_rung` already records the correct title (`citation_verifications.jsonl` line 3, `verdict: match`). Paper20's bibitem prints the correct title; paper21's does not.
- **Expected:** Replace with `\emph{Spinor gravity and diffeomorphism invariance on the lattice}` to match arXiv truth and paper20.
- **Fix:** Edit the `\bibitem{WetterichSpinor2013}` block to use the correct title; treat the bibkey as cross-paper-shared and do not retitle locally.
- **Cache:** fresh-fetch (Stage 13 confirmation, today 2026-04-25)

### 1.2 — 🔴 BLOCKER — `WetterichSpinor2022` bibitem title disagrees with arXiv:2101.11519

- **Gate:** CitationIntegrity
- **Location:** `paper21_majorana_rung/paper_draft.tex:543-545`
- **Observed:** Bibitem text `"Spinor gravity flow equations"` for arXiv:2101.11519.
- **Evidence:** Fresh fetch of `https://arxiv.org/abs/2101.11519` returns title `"Pregeometry and spontaneous time-space asymmetry"` (C. Wetterich, JHEP 06 (2022) 069). Cache entry (`citation_verifications.jsonl` line 4) and `paper20_scalar_rung/paper_draft.tex` both record this correct title. Paper21's bibitem alone retains the hallucinated `"Spinor gravity flow equations"` title.
- **Expected:** Replace with `\emph{Pregeometry and spontaneous time-space asymmetry}`.
- **Fix:** Edit the `\bibitem{WetterichSpinor2022}` block.
- **Cache:** fresh-fetch + cache-verified at paper20

### 1.3 — 🟡 REQUIRED — `KamLANDZen800` bibitem omits the journal publication (PRL 135, 262501, 2025)

- **Gate:** CitationIntegrity
- **Location:** `paper21_majorana_rung/paper_draft.tex:582-584`
- **Observed:** `"arXiv:2406.11438 (2024; v2 March 2026)"` — no journal reference. Registry similarly lists `journal: 'arXiv'`.
- **Evidence:** Fresh fetch of `https://arxiv.org/abs/2406.11438` and INSPIRE both report the paper is published as `Phys. Rev. Lett. 135, 262501 (2025)` (DOI `10.1103/jkf6-48j8`). The journal version exists and is the authoritative reference at the time of paper21 submission.
- **Expected:** `Phys. Rev. Lett. \textbf{135}, 262501 (2025); arXiv:2406.11438`.
- **Fix:** Update both the paper21 bibitem and the `KamLANDZen800` `CITATION_REGISTRY` entry; flip `journal/volume/page/year` to PRL values, keep arXiv as additional identifier.
- **Cache:** fresh-fetch

### 5.1 — 🔴 BLOCKER — `lepton_number_symmetry_obstructs_BCS_form` is vacuous: `H_LeptonNumberViolated := True`

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/MajoranaRung.lean:214` (definition) + `:248-253` (theorem); paper §4 prose lines 198-235.
- **Observed:** `def H_LeptonNumberViolated : Prop := True`. The theorem `lepton_number_symmetry_obstructs_BCS_form` takes `(h_no_LNV : ¬ H_LeptonNumberViolated)` as a hypothesis. Since `H_LeptonNumberViolated = True`, `¬ H_LeptonNumberViolated = ¬ True` is uninhabited; the theorem is vacuously true and discharges no obstruction.
- **Evidence:** The paper at L233-235 advertises this theorem as `"the cleanest no-go content available"` and asserts `"without LNV, the strong BCS hypothesis cannot hold."` But no caller can ever instantiate `h_no_LNV`. Compare this against `feedback_tracked_hypothesis_nontrivial.md` in MEMORY.md, which the project explicitly flags as the precise antipattern.
- **Expected:** `H_LeptonNumberViolated` must be a non-trivial `Prop` parameterized over substrate data — e.g., a predicate over the substrate Lagrangian asserting that some `ΔL=2` operator coefficient is non-zero, or, at minimum, a tracked `Prop` opaque to the substrate side and threaded as an explicit assumption argument throughout the module (not provable by `trivial`).
- **Fix:** Restate `H_LeptonNumberViolated` as `H_LeptonNumberViolated (s : SubstrateData) : Prop` with non-trivial content (e.g., `∃ Δ : ℝ, Δ ≠ 0 ∧ Δ encodes the L-violating coefficient`); rewrite the obstruction theorem to use a *parametric* hypothesis. Until then, the no-go content the paper claims does not exist.
- **Cache:** N/A (Lean substance, not citation)

### 5.2 — 🔴 BLOCKER — `IsDiracPMNS`, `IsMajoranaPMNS` defined as `True`; `isMajoranaPMNS_of_majoranaRungData` is structurally tautological

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/NeutrinoMixing.lean:119`, `:125`, `:132-135`. Paper §5 prose lines 270-272.
- **Observed:** `def IsDiracPMNS (_V : PMNSMatrix) : Prop := True`; `def IsMajoranaPMNS (_V : PMNSMatrix) : Prop := True`; `theorem isMajoranaPMNS_of_majoranaRungData ... := trivial`. Body is `trivial` on a definition that unfolds to `True`.
- **Evidence:** The paper §5 cites this Lean infrastructure as the formal Dirac-vs-Majorana distinction and the bridge to `MajoranaRung`. The Lean text encodes neither: both predicates are `True`, the bridge is vacuous. Per Pipeline Invariant 9, `True := trivial` constructs MUST NOT be referenced by paper claims; here they are referenced as if they were content.
- **Expected:** Either drop the predicates from the paper's prose (and treat them as scaffolding markers only, like `Wave2OpenManifest`), or supply genuine content — e.g., `IsMajoranaPMNS V := ∃ α₁ α₂, α₁ ≠ 0 ∨ α₂ ≠ 0` parameterized over the right-hand diagonal phase data, with the bridge theorem proved against that content.
- **Fix:** Reframe paper §5 to clarify that the Dirac/Majorana parametric markers are scope tags rather than physical-content theorems; alternatively, refactor the definitions to carry actual content.
- **Cache:** N/A

### 5.3 — 🔴 BLOCKER — `DecouplingRegime` failure-mode fields are all `True` placeholders advertised as physics

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/MajoranaRungDecoupling.lean:96-104` (structure fields `not_vestigial`, `not_cosmological`, `weakly_coupled_matter`). Paper §6 prose lines 369-374 ("plus three predicates excluding cosmological-scale failure modes").
- **Observed:** All three structure fields have `: True` type. The paper enumerates them as encoding three named physical regimes (Volovik 2024 vestigial; Klinkhamer-Volovik q-theory; Wetterich/Reuter-Saueressig FRG strong-coupling). The Lean encoding records nothing of the kind — they accept any inhabitant trivially.
- **Evidence:** `decouplingRegime_at_electroweak_scale` proves the regime predicate at `(80, 10^14)` by discharging the three failure-mode fields with `trivial`. The "all three are trivially satisfied" statement in paper §6 is technically true but only because they are *literally* `True` — not because the substrate physics rules them out.
- **Expected:** Either parameterize the fields over substrate data (e.g., `not_vestigial : Λ_QCD < E`, `not_cosmological : H_0 ≪ E`) so they actually encode the regime conditions, or remove the prose claim that the fields encode regime exclusions. The current prose is an overclaim about the formal artifact.
- **Fix:** Replace the three `True` fields with non-trivial inequality predicates over `SubstrateData` + `E`; reprove `decouplingRegime_at_electroweak_scale` against the new conditions; or, alternatively, soften paper §6 prose to "three placeholder fields reserved for future regime-exclusion content."
- **Cache:** N/A

### 5.4 — 🟡 REQUIRED — Two `: True := trivial` summary placeholders cited indirectly via theorem-count claims

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/NeutrinoMixing.lean:264` (`neutrino_mixing_structure_note_summary : True := trivial`); `lean/SKEFTHawking/MajoranaRungDecoupling.lean:281` (`wave2b_decoupling_summary : True := trivial`).
- **Observed:** Both are `True := trivial`. The paper's Table~\ref{tab:formal-summary} reports `NeutrinoMixing.lean = 9 theorems` and `MajoranaRungDecoupling.lean = 7 theorems`. Excluding these two `True := trivial` placeholders the substantive counts drop to 8 and 6 respectively. The abstract asserts "$14$ substantive theorems" for `MajoranaRung.lean` — that subset is not explicitly broken down for the two companion modules.
- **Evidence:** Pipeline Invariant 9: "Theorems proved as `True := trivial` ... MUST NOT be referenced by any other proof, formula, or paper claim." The paper claim is "(7 theorems)" / "(9 theorems)"; the substantive claim should subtract the placeholders. Currently the paper count and the table conflate substantive + placeholder.
- **Expected:** Either remove the two summary markers, or have the paper explicitly distinguish substantive vs. placeholder counts the way it does for `MajoranaRung.lean`.
- **Fix:** Replace `wave2b_decoupling_summary` and `neutrino_mixing_structure_note_summary` with substantive marker theorems (or delete them and rely on file-level documentation comments instead). Update Table 1 counts.
- **Cache:** N/A

### 2.1 — 🔴 BLOCKER — Same bibkey (`WetterichSpinor2013`, `WetterichSpinor2022`) carries different titles in paper20 vs paper21

- **Gate:** CrossPaperConsistency
- **Location:** `paper21_majorana_rung/paper_draft.tex:540-541` and `:543-545`; cf. `paper20_scalar_rung/paper_draft.tex` (correct titles).
- **Observed:** Paper20 bibitems have `"Spinor gravity and diffeomorphism invariance on the lattice"` (1201.2871) and `"Pregeometry and spontaneous time-space asymmetry"` (2101.11519). Paper21 bibitems for the same bibkeys have `"Spinor gravity and gravitational anomaly"` and `"Spinor gravity flow equations"`.
- **Evidence:** Direct grep diff between the two `.tex` files (see Finding 1.1, 1.2). A reader reaching the same bibkey from two project papers will see two different cited works for the same key — the canonical CrossPaperConsistency failure mode the gate exists to catch.
- **Expected:** Identical bibitem text for shared bibkeys. The pipeline-canonical truth is the `CITATION_REGISTRY` entry; paper-local bibitems must match.
- **Fix:** Resolve via 1.1 + 1.2 fixes (use registry/paper20 truth in paper21).
- **Cache:** fresh diff

### 3.1 — 🟡 REQUIRED — All 21 MAJORANA parameters lack `human_verified_date`

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py` MAJORANA.* keys (21 entries: M_R bounds, NuFit angles, Δm² values, m_ββ bands, Yukawa bounds, m_ν).
- **Observed:** All 21 entries have `llm_verified_date` populated (2026-04-26 for the new ones; 2026-04-01 for the four MAJORANA_J* / GAMMA_8x8 entries) but `human_verified_date = None` across the board.
- **Evidence:** Programmatic enumeration via `PARAMETER_PROVENANCE` import (this review). Per Gate 3 pass criterion: "Every parameter the paper depends on has llm_verified_date AND human_verified_date set." The latter is missing on every parameter the paper relies on.
- **Expected:** Each parameter human-verified via the provenance dashboard before submission.
- **Fix:** Run the provenance dashboard sign-off pass on each MAJORANA.* entry; populate `human_verified_date`. This is a draft-acceptable / submission-blocking finding (REQUIRED severity, per finding-class 2 protocol).
- **Cache:** N/A

### 6.1 — 🔵 RECOMMENDED — `Hill2024Bilocal` registry entry omits arXiv ID 2310.14750 (DOI verified, but bibliographic completeness lacking)

- **Gate:** AssumptionDisclosure / CitationIntegrity advisory
- **Location:** `src/core/citations.py` `Hill2024Bilocal` (`arxiv: None`) + `paper21_majorana_rung/paper_draft.tex:617-619`.
- **Observed:** Registry entry has `arxiv: None`; bibitem has no arXiv identifier. INSPIRE-HEP confirms the paper is `arXiv:2310.14750`.
- **Evidence:** WebFetch of `inspirehep.net/api/literature?q=Hill+bilocal+composite+scalar+entropy+2024` returns arXiv:2310.14750. The DOI is verified, but readers without journal access cannot reach the PDF without the arXiv ID.
- **Expected:** Add `arxiv: '2310.14750'` to registry; add `arXiv:2310.14750` to bibitem.
- **Fix:** Update both registry and bibitem.
- **Cache:** fresh-fetch

## QI Candidate

The pre-existing `WetterichSpinor2013` / `WetterichSpinor2022` wrong-title bibitems in paper21 reveal a systemic gap in the just-completed CitationIntegrity round: the round verified the **15 fresh bibkey CHANGES** (renames + corrections) but did not re-verify pre-existing-but-shared bibitems whose paper-local text drifted from the registry/paper20 canonical. Recommend: extend the CitationIntegrity round protocol to verify *every* bibkey in every paper against (a) the registry, (b) live arXiv/DOI, and (c) all other papers that share the same bibkey — not just the bibkeys that changed since the last round. The cache schema (`citation_verifications.jsonl`) already supports per-paper records (`paper` field on each entry); the gap is that the round only minted records for the renames, not the inherited bibitems. Closing this gap requires CrossPaperConsistency to be a first-class output of the CitationIntegrity round, not a separate finding-class 4 catch.

Additionally, the `H_LeptonNumberViolated := True` and `Is{Dirac,Majorana}PMNS := True` antipatterns surface a recurring failure mode (`feedback_tracked_hypothesis_nontrivial.md` documents the same antipattern). Recommend: a static-analysis lint rule in `validate.py` that flags any `def H_…X… : Prop := True` (or any `def H_…X… (args) : Prop := True`) and any `theorem … := trivial` whose statement-type unfolds to a plain `True` not under a binder. Such a rule would have caught all three Lean BLOCKERs in this report at Stage 12 rather than Stage 13.
