# Independent I1 stage table review

**ACCEPT_SCOPED** for the three-path I1 stage table source and presentation repair, patch SHA-256 `334bb742e9c35f1504a39acd364e57d22fc929992b7b22f064b0347eff092c91`.

I exported the relevant files from exact PR118 commit `ddc320ec365a1f42fd5d8d81796ae07bc0bb029c`, applied the frozen all-eleven patch `f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516`, copied that scratch baseline, and applied the I1 patch with whitespace errors enabled. Author manifest, intake continuity, and terminal continuity verified. The pinned checkout remained clean.

An independent parser of the governing pipeline overview matched all 15 generated labels and gate text, including 3a and 3b and current Stage 4, 8, 9, 10 and 13 wording. Stage 14 is the sole advisory in the overview, and the new caption carries that distinction. The original input and label each occur once and remain the same. Two canonical renders reproduced the candidate stage file byte for byte. The neighboring finding-class table remains identical to the baseline and both rerenders.

I forced two canonical I1 compiles, with pdfTeX's recorder enabled in scratch. Both measured 37 pages and 41 overfull notices, with zero TeX errors, unresolved references or dropped class options. Both open the same two local table files. In the baseline, the active stage table is outside the spec. Both opens in the candidate belong to the canonical I1 spec. I inspected page 17 in both rendered PDFs. All 15 rows and the advisory are visible and fit within the page. The entire extracted text differs only on page 17. Scoped em-dash, reader-facing voice and manuscript-length checks passed for both forms.

This accepts I1's exact table provenance and presentation on the pinned candidate. The composed R3 checker, other publication gates, full I1 claims and final human approval remain separate. No tracked source, Lean slot or main integration changed.
