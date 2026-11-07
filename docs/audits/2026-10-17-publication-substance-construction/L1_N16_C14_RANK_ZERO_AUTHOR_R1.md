# Exact original c14 rank-zero and rank-eight local closure

The authority is the original periodic closed source_C at clean primary
27012c18fa374e8341e124b510abbedeedb18d29. This cut acts on the zero-centered
(01,01,23,23) occupancy row. It uses the accepted exact star at rank 8
and the accepted shared-trace sewing. It keeps the open boundary
factored. The global exponential divisor 512 stays external.

## Exact source factors and open boundary

The existing axis-0 star tensor between ranks 8 and 0 already contains
two generators at rank 0. Each of the other three edges at rank 0
contains two coframe factors and two trace factors. The three exact
new edge tensors attach to ranks 4, 2, and 1 on axes 1, 2, and 3.
Each has 240 incidence-admissible degree-four Haar tuples and 14,208
nonzero sparse rows. Each row contains the rank-zero mask, remote
mask, two ordered source component indices, and two ordered trace
coordinates. The Gaussian integer coefficients have denominator 768.
The actual anchor, chirality and source occurrence interfaces are in
`edge-meta.json`. Each edge was verified against literal raw quarter
increments and an independent Kronecker pairing Haar comparator.

The rank-zero site has all 2,520 ordered partitions into four pairs.
The partitions include the existing shared axis-0 mask at rank 0
and each of the three other exact edge tensors. The rank-8 site keeps
its 240 existing signed partitions. The bridge joins them through
the two masks on the original axis-0 edge. The interface has 100
compatible mask pairs covering 73,440 pairs of signed partitions.
Each edge row has two generators at each endpoint. Apart from the
two sites being closed, the six exterior endpoints are disjoint.
All reordering signs involving entire two-generator blocks are even.
The complete top projection therefore uses the product of the two
local partition signs in the original 128-generator order.

Both original 01 S2 traces are attached through one shared exact
source table of 1,536 nonzero rows in 32 joint seam bins at
denominator 4. The occurrence slots remain distinct. The 01 trace
row keys are ordered `(q02,q03,a0,a1,r23,r12)`. The two first q labels
come from the new axes 2 and 3 on original anchors (0,2) and (0,3).
The two components come from the shared edge and new axis 1.
Residual anchored coordinates (2,3) and (1,2) remain open for each
occurrence. The already sewn 23 traces take both component indices
from the new axes 2 and 3 and their (0,1) coordinate from new axis 1.
Their residual (4,0) coordinate remains open in each occurrence.
All q codes 0–7 within each referenced anchor mean L0–L3 and R0–R3.

To evaluate any coefficient at the declared open boundary, sum over
bridge-compatible signed site partitions. Select the existing tile
of the four seam coordinates between the rank-8 axes 0 and 1 and
the two 23 traces. Multiply all seven exact edge factors, the two 23
trace factors, and the two 01 trace factors, matching every component
and q slot as described above. Sum over all internal component and
sewn coordinate labels; keep the two site signs. The fixed boundary
consists of the three old remote masks and their S4 component pairs,
three new remote masks, and the per-occurrence trace residual labels.
The combined denominator before reduction is 280,159,925,619,463,815,168.
No remaining S4 epsilon or unrelated source factor has been applied.

The sum is exact and factored. It retains boundary cancellation
without visiting the gross Cartesian expansion of
36,474,951,220,875,755,520 seven-edge row products before trace
restrictions. This number is a pre-filter visit count, not a
lower bound or an implementation cost prediction.

## Verification and capacity boundary

The serialized readback independently checks each signed local
partition, the entire bridge support and counts, and the gross
Cartesian visit total. The factor graph label map is in `graph.json`.

Three controls fix the two local partitions, the earlier tile and
the newly sewn quaternion coordinates, and distinct actual open
boundary assignments. Within each restriction all internal coframe
component labels are summed. A separate comparator traverses the
opposite edge order, re-extracts both types of original raw ordered
trace at the fixed residual coordinates, and computes the sign of
the complete literal 128-position wedge word. Both routes find 16
nonzero signed path contributions whose sum is zero for each control.
A deliberately reversed sign on one recorded contributing path
changes the three sums by +386,547,056,640, -386,547,056,640, and
-386,547,056,640 in numerator units. Transposing the first two
rank-zero generators also reverses the literal top-word sign.
The cancellation controls are exact on their declared restrictions.

An unrestricted fixed-boundary value has not been evaluated. Both
the ordinary indexed candidate and tighter restrictions reached the
same 4,000,000 work ceiling, refusing prospectively at operation
4,000,001 in the recorded projected joins. The work refusals and
the additional 300,001-row refusal of the initial search for a
nonzero sum are retained. The capped comparison was then narrowed
to the three explicitly restricted cancellations above. Their zero
sums supply no vanishing assertion for the unrestricted cut.

The three new edge runs in one process charged 575,896 operations
and 113,328 cumulative tracked insertions, using 58,023,936 accounting
bytes and 1,108,056 serialized bytes. The inherited 100,000-row cap
first refused prospectively at 100,001. The successful rerun set its
row cap to 120,000 before running and kept the original 64 MiB
accounting limit. Its sampled peak process RSS was 116,228,096 bytes.

The factored composition and comparison run charged 176,762 visits,
118,010 cumulative rows, 45,315,840 accounting bytes and 36,268
serialized bytes. Its sampled peak process RSS was 124,993,536 bytes.
The configured caps are recorded alongside the meters. Actual
RSS is sampled rather than OS-enforced. The table meters price
declared entries, excluding source constructors, secondary runtime
allocations and separate readback. The output byte meters cover the
enumerated JSONL tables. Exact complex arithmetic uses prospective
checked Gaussian-integer bounds for the coefficient routes.

## Continuation

First try to pair the signed component terms before any boundary
expansion. The observed cancellation restrictions can guide a test
of a sign-reversing involution, with its full scope checked separately.
The next independent edge cut is the still-open residual (4,0) edge, between
ranks 4 and 12. It contains two independent 23 trace occurrence
legs and the paired S4 coframes originating at rank 12. A conditional
edge contraction there can consume the remaining 23 q labels and
couple to two of the already open exterior boundaries. Check all
owners from the original roster before closing either next site.
The other two axis arrangements and the complete representative
coefficients, c14, c0, full denominator and normalization remain open.
