# Reverse mixed original N16 bounded witness preflight

This assignment was evaluated against primary `07d76dc9eede4a6455e30a27ae2a090178da5d47`.
It constructs two distinct targets for the previously refused reverse W:S4
Z:S2 mixed contact seed directions. A bounded target contains 22 exterior
generators, 23 anchored quaternion factors and shared `g2^3 g1 J`. Its
operand order is X, W, Z, contact, Y. The two contact seed operands d0 and
d1 identify the chosen lineage. The signed tests use the same full d0+d1
contact sum for both targets.

## Construction

The unsigned pass chooses X, contact and Y rows by their disjoint exterior
incidence, then fills W:S4 and Z:S2 against the remaining exterior bits.
For each of the four fixed X/Y frame pairs, it projects every selected
factor to the target. It subtracts the outer and contact exterior incidence
and exact anchored-symbol multiset and checks the ordered W/Z completion.
Its signature is the set of attainable selected-inner combined mask and
remaining multiset pairs. The other W/Z labels still participate in the
signed frame calculation.

All 2,048 seeds per direction had identical selected-inner signatures
under each single reflection, so this pass spent zero signed tests.
The pass used 14,643,315 charged operations under the 20,000,000 cap.
This is a measured obstruction for the unsigned selected-inner discriminator
on this roster, with no claim of universal reflection symmetry.

A new bounded run also screens the phase of the two actual local three-factor
outer products at the seed's X and Y incidences. Each has a nonzero
unreflected local contribution and nonzero sum with its reflected local
contribution before a signed witness is spent. This is a priority
heuristic. In controls it rejects one previously accepted forward mixed
case and admits the other. It correctly deprioritizes the two tested
previous reverse cancellation examples, but cannot determine the full
frame coefficient by itself.

The phase-prioritized run qualified direction 1 on structural attempt 22
and signed witness 6. The direction 0 search stopped on its 12th signed
witness at structural attempt 44. The phase run spent 776,816 charged
operations across both directions.

To qualify direction 0, hold the direction 1 X/W/Z/Y physical lineage
fixed and enumerate actual d0 contact rows that match its quaternion
chirality and are disjoint from the other factors' exterior incidence.
The successful direction 0 target used source row 18 and signed test 2.
The prior 16 contact rows overlap. The first eligible row yielded a
zero selected witness. The directed run spent 45,690 charged operations.
The phase-prioritized and directed runs each retain the same 12-test
and 2,048-attempt ceilings. These are separate measured search policies.

| Seed direction | Selected labelled coefficient | Fixed frame coefficients in base, X, Y, XY order | Four-frame sum |
| --- | --- | --- | --- |
| 0 | 1/262144 | (1/16384, 0, 1/16384, 0) | 1/8192 |
| 1 | −i/524288 | (−i/32768, −i/32768, −i/32768, −i/32768) | −i/8192 |

Both targets have nonzero base, base plus X, base plus Y and four-frame
sums. All four frame counts remain present even when some signed sums
cancel. The four previously accepted targets remain the exact byte prefix
of the candidate ledger, followed by the new reverse targets in direction
order. The 720 signed records remain the accepted prefix for eventual
original admission. Both new targets remain bounded witnesses before Haar
contraction and physical normalization.

## Resource and replay boundary

The existing limits remain 8,192 local and later records, 16,384 oracle
records, 20,000,000 charged operations and 2,048 signed output records.
The existing selected-witness and fixed-frame routines were reused.
`replay.py` independently rebuilds actual raw orientations and permutations
for the selected labels and all W/Z terms in the four fixed outer frame
pairs, using direct canonical exterior multiplication and exact target
projections. It also replays the established baseline identities and
all four prior bounded targets. An eventual full original run requires
separate independent admission and explicit ROOT authorization.

The fresh six-target replay and two raw fixed-frame controls completed at
1,364,293 charged operations. Both raw selected-label values and all eight
fixed-frame coefficients matched the grouped path exactly. The oracle peak
was 2,831 logical records, with raw local peaks 2,831 and 2,723. The contact
replacement pilot's reported 2,516-record peak plus a conservative count
of all 3,753 live phase JSON list/object containers is 6,269 under the
8,192 local envelope for this exact pilot.

The 20,178-byte candidate ledger has SHA-256
`84ca076d2ec7cb78975c921dfcbc25a98b6b7c469e6fe9e4083c66897f2bfdd0`.
Terminal continuity returned SAME. The candidate ledger is a preflight
handoff for a fresh independent admission review. Its full original
coefficient and physical acceptance boundaries remain open.
