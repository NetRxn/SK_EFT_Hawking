# Current citation source-custody reconciliation

### 1.1 — Reconcile the actual held Dawson–Nielsen source and zero-headroom citation population

- **Severity:** minor
- **Lane:** infra
- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py`, `src/core/constants.py`, `docs/primary_sources_state.json`
- **Observed:** After transport of the independently accepted thirteen identity additions, the actual canonical check finds zero missing registry identities but remains red because DawsonNielsen2006 points at a missing abstract file. Its existing held Crossref JSON has the correct journal identity and DOI, contradicting the registry note denying any DOI. The same unchanged check measures76 undeclared entries against ceiling78.
- **Expected:** Record the actual held source and its version/fidelity through the canonical acquisition writer; preserve historical artifacts, all unrelated registry/state/parameter data and the original full-source scientific obligations. Keep the ratchet at the actual measured population without headroom.
- **Fix:** The existing acquisition writer fetched the full arXiv author preprint into Lit-Search and recorded current custody. Correct the registry path/DOI/notes; retain the 2005-preprint versus 2006-publication distinction. Tighten only the measured undeclared ceiling78 to76. No fabricated exemption or full-text inference from metadata.
- **Evidence:** Current canonical measurement, fetch stdout/stderr, PDF bytes/version/hash and complete source/state conservation receipts. D4 stage10 finding2.2 and D8 stage10 finding1.4 retain separate scientific attribution review; they are not closed by this data repair. Independent current composition review and actual Verify are required before this finding closes.
- **Verify:** `uv run --no-sync python -m pytest -m '' tests/test_d5_citations.py tests/test_phase6i_wave1.py tests/test_workspace_resolver.py -q`

- **Independent R1 residual:** New Dawson notes incorrectly said section3.3. Actual held v2 has Section3, Analysis, Eqs.(8)–(9), printed page7. ROOT checked the actual text and corrected this locator after the complete fresh R1 review. The claim is retained; independent current reassessment remains required.
