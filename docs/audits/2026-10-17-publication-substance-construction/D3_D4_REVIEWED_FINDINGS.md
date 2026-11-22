# D3 and D4 source reconciliation

These dispositions cover the original statements identified in the August
Stage 10 reports. They do not change either bundle’s charter or review state.

- D3 finding 2.1. The D3 redraft in `dc8ad3493` removed the claim that
  Glorioso and Liu's method avoids a pointwise null energy condition for
  horizon area. The remaining citation concerns the slow-mode effective
  theory obtained by integrating out fast modes, which the held paper
  explicitly describes. The D3 area-law claim gets no support from this
  citation correction.
- D3 finding 3.2. The displayed value of the leading heat-kernel coefficient
  follows from the definition of `HeatKernelExpansion.a0_dirac` and its
  spinor trace factor. D3 explicitly uses `a0_dirac_linear` for homogeneity
  and `a0_dirac_pos` for positivity. The metadata makes that distinction
  in `154ad49cb`; it is checked against the current declaration map.
- D4 finding 2.4. The redraft reports the Ising squared total dimension as
  four and the total dimension as two. The object dimension remains
  the square root of two. The original report independently verifies the
  correction and names the two Lean witnesses. The original check and a
  positive source readback are used together.
- D4 finding 2.6. The active apex annotation now describes what
  `GenericSU2.valid_branch_K_chain_le_K_compose_numeric_generic` certifies.
  The displayed bound is an explicit numerical inequality with the defined
  composition constant on its right. The manuscript already withdrew the
  unsupported earlier calibration numbers. The historical review note now
  identifies that withdrawal.

D3 finding 1.3 remains open. Existing tests distinguish a Crossref
bibliographic envelope from full-body JSON, and the production validator
reports the fidelity separately. The original finding also calls for
reconciling declared and discovered source paths. The current fidelity scan
still selects the strongest discovered file, while a separate leg checks
declared paths. Confirm the disposition of that remaining requirement
against the citation architecture before closing the full finding.
