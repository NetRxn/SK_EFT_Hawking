# Independent normalized quaternion specialization review

**ACCEPT** exact sole-file worker commit
`adbb3a2919ced9ae33d06fc7bff49941ff11e952` against
`c75d4543292c5f754cb7c4877c6abf5b064b5280`.
The Lean module SHA-256 is
`5f8f2e0b3af6c991a44570aed23441f238a1fc69af1aa0a2c8bdc3429e7665a1`.
The diff is clean. All ten public statements were inspected and source
search found no `sorry`, `admit`, added axiom, `native_decide` or heartbeat
override. ROOT owns kernel and native replay.

## Source correspondence

The quaternion block matches all four plus-i entries of
`original_spin4_link`, with component 2 negated only in the lower
off-diagonal and component 3 entering the diagonal with opposite
imaginary signs. The real unit-sphere condition gives both determinant
one and unitary membership. Distinct site, direction, chiral block and
component indices reproduce independent Python link variables. The
symbolic dagger transposes and changes the sign of the imaginary
coefficient, leaving real q labels fixed. It evaluates to the actual
physical dagger.

All four ordered quarter products and their signs match
`original_coframe_blocks`, including addition when forward and
backward endpoints or anchors coincide. At each anchor the earlier
central twist matches the step sign in both direct and reversed terms.
The gamma permutation affects only the gamma label, preserving the
step direction and original link anchor. The two h and J families
use the Python flat matrix order. Arbitrary fixed complex J specializes
to constants while h stays symbolic. Matrix mapping preserves the
determinant. The selected raw-jet theorem composes the same equality
with existing first and second auxiliary derivatives, including a
repeated coordinate.

## Independent bounded checks

A fresh rational-complex oracle constructed signed quarter-block
scatters from modular neighbours and independently checked each real
unit quaternion's complex determinant and unitarity. On 18 finite
fixtures it checked 384 normalized chiral blocks and 2,496 matrix
entries. It compared default-symbolic Python h/J/q evaluations and
separately supplied exact fixed links with the independent scatter.
The cases cover extents one, two and three, three boundary patterns
and both gamma conventions. On the one-site cases direct signed
Leibniz expansion matched 144 selected raw determinant slots, with
72 nonzero second-order slots and both mixed and repeated coordinates.
The scratch oracle's first attempt had a missing complex subtraction
operator. Its corrected exact version and successful output are included.

## Scope and continuity

This is pointwise normalized quaternion specialization with independent
anchored unit tuples, followed by the selected derivative bridge. A
converse parametrization and pushforward equality for the Haar measure,
concrete Python sparse storage and resource admission, general
accelerated source paths, full scientific acceptance and publication
qualification remain separate.

The first continuity read observed an untracked transient matching MCP
snippet during ROOT replay. A retry after its normal removal and the
terminal check both returned SAME. The reviewer made no repository,
lease or slot writes.
