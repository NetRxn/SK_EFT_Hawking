# Reconciliation of four legacy citation findings

- Finding 5. The original [Volovik preprint](https://arxiv.org/abs/2312.09435)
  and the held source in Lit-Search identify the article as *Fermionic
  quartet and vestigial gravity*. Paper 6 already used that title. Paper 5
  adds it to the correct identifier. Paper 20 had a shortened title and
  now uses the same source identity.
- Finding 6. The [Nature version of record](https://www.nature.com/articles/s41586-024-08188-0)
  starts on page 80. Paper 3 already had the correct page. The registry
  points to its held arXiv preprint and records the version-of-record DOI
  and the distinct published title in the notes.
- Finding 10. The [JHEP version of record](https://link.springer.com/article/10.1007/JHEP07%282022%29001)
  confirms July 2022 and article 001. Papers 7 and 8 already use the
  journal year. The registry now records the actual author, title,
  article identifier and DOI. The held arXiv copy is v3 from May 2022.
- Finding 11. The held publisher PDF `Berti2024CRPhys25S2.pdf` in
  Lit-Search identifies volume 25, special issue S2 (2024), pages 181–216.
  It distinguishes online publication on January 20, 2025, from the
  issue date of October 27, 2026. Both affected bibliography entries
  now carry the journal issue and DOI, with Lennart Fernandes as
  second author. Paper 12 no longer contains a Berti citation. The
  registry still identifies its previously held
  arXiv preprint and names the distinct publisher PDF in the notes.
  [Publisher DOI](https://doi.org/10.5802/crphys.226).

The D4/D8 attribution work and the legacy Son action-source finding
retain their own scope. No full source is copied from Lit-Search.

Paper 2 also used unsupported Unicode checkmarks and a literal Greek
letter in its proof-summary list. Use the already loaded LaTeX math
symbols so the existing compiler can render the list.

Independent review accepted the four source identities, their distinct
Verify commands and the preserved manuscript scope. The title-drift
validator measured six high-confidence flags against the old ceiling of
seven. The refreshed ceiling is six. The citation suite passed 55 tests.
All four changed manuscripts compiled with no TeX errors or unresolved
references.
