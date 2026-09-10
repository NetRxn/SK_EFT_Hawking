# Reset-sensitive memory increment: independent review receipt

Candidate: `2c7887de`, compared with `ce194cdc4bf939b108c17edc9530a7f0a14565f9`.
Scope: [partial-interaction plan](../dev-loops/MemoryProcesses/PARTIAL_INTERACTION.md). Local-only substrate acceptance; no publication or hardware certification.

This lead-filed receipt records the fresh-context `memory_partial_integrated_review` agent's independent findings. It is not an additional review by the lead or a human approval.

## Verdict and evidence

No substantive findings. The reviewer reproduced 78 memory tests in 0.18 seconds with verified review-checkout imports. Independent checks covered 160 complex correlated-state Kraus/reset/control cases, 160 random common-channel/effect comparisons, and 289 exact rational parameter pairs covering 1,156 classical-path trajectories. The rational trajectory comparison found zero discrepancy.

Source inspection confirmed actual joint trajectories, the control's environment reset after the same imperfect system reset, arbitrary-density physicality, exact reset leakage, shared continuation and measurement quantifiers, and a nonempty strict regime. No scalar-only replacement or vacuous premises were found.

The reviewer verified 31 added extraction records with unchanged existing records, the 21 public and 11 private authored theorem counts, standard core axiom closures, aggregate import, and all plan/Python theorem references. The final explicit continuity snapshot remained fresh, and the reviewer made no file mutations.

## Root-owned validation

The aggregate kernel build passed through the controller at `ca9414ba`. Canonical extraction and counts/atlas refresh passed. All 31 new extracted records have no project axiom dependencies or dependency-extraction timeouts; core axioms are confined to `propext`, `Classical.choice`, and `Quot.sound`. The 11 private proof helpers are compiled with the module and consumed by the public theorem proofs.

`gate_precheck.py s13-lean` passed in 528.8 seconds: 70/89 checks passed overall, with 19 pre-existing paper-corpus failures reported separately under the owner-approved scope. The gate did not modify the candidate.

## Limits and disposition

The reviewer did not perform another kernel build; build evidence is root/controller-owned. Numerical tests do not certify floating-point error. The basis process admits classical memory, and probabilistic identity/SWAP composition is not coherent partial SWAP. A nonpositive margin is inconclusive, and retained-versus-control contrast alone is not the common-channel exclusion criterion.

The scoped increment is accepted locally after independent review. Public main and remote publication are outside this integration boundary. Existing paper readiness states and corpus failures remain unchanged.
