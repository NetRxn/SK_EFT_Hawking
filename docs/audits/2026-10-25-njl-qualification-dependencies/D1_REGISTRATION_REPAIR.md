# D1 second-order registration reconciliation

The historical lift in `d1f3700c` registered three topic labels. The reviewed replacement registers the owners of the exact declarations used by the current manuscript.

| Historical topic | Current owner and cited result |
|---|---|
| KMSOptimality | SKDoubling, firstOrder_KMS_optimal and firstOrder_altSign_uniqueness_test |
| SecondOrderPositivity | SecondOrderSK, combined_positivity_constraint distinct from fullSecondOrder_uniqueness |
| TransportCounting | SecondOrderSK, transport_coefficient_count and the finite and parity counts |

The existing append writers preserve all 13 original events and record the new owner registrations and retired labels. The manuscript, source manifest, lifecycle metadata and closure ledger are byte-identical. D1 remains stale with Stage 13 pending and redo required.

The live module reach check decreased from 185 to 182 against a ceiling of 147 and reported no contradicted or unjustified deregistration. Coverage and Stage-13 ordering tests returned 15 passes and one deselected known-red corpus ratchet. All 17 append section-policy tests passed. See the [independent readback](D1_REGISTRATION_READBACK.md). This is a registration correction, with scientific review and closure governed by their existing records.
