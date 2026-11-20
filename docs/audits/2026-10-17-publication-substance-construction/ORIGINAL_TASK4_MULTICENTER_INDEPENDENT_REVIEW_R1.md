# Independent original N16 two-center design and preflight review

**ACCEPT the source geometry, exact bounded preflight and low-power
two-center implementation design.** The proposed first package is
the three selected (S2 at w, S2 at z) requests plus an actual
identity-at-z restriction. Its implementation and original replay
require separate review and admission. The eventual 81 allocations
and 243 request identities remain in scope.

The intake and terminal continuity checks matched. The manifest and
predecessor input hashes verified. The primary changes from the author
pin c75d45432 are the quaternion Lean bridge and aggregate import;
the tracked original Python source inputs are unchanged. No tracked
files, remote state or slots were touched.

## Source and independently reproduced arithmetic

The closed-word source-C OriginalRegulator defaults are (2,2,2,2)
with all positive paired boundary signs. The four sites are x, x+e0,
x+e2 and x+e0+e2. Independent axis-toggle geometry reproduces every
entry of the six unordered site-pair intersections. Each site's
exterior star has five sites, coframes use eight directed anchors,
and the curvature support uses 16. In particular w and z share two
exterior sites, their two directed axis-0 coframe anchors, six
curvature anchors and eight combined anchors. Reciprocal directed
anchors remain distinct at extent two. The other factors around
the square can still use both kinds of shared support.

Independently built the actual T_w00 and T_z00 and recomputed their
complete coefficient map by all 4,096 ordered row pairs, explicit
exterior inversion counts, full masks and canonical symbol keys.
768 candidate pairs overlap. The remaining arithmetic yields 2,304
nonzero exact coefficients and agrees with the canonical exterior
product on the entire map. The repeated-coordinate coefficient at
the frozen key is -1/16. The specific distinct listed overlapping
rows are both present and their one-row product is exactly zero.

Independently rebuilt the two selected ordered closed plaquette
traces by explicit D†C†BA and gamma multiplication, with permutation
inversion signs and quarter weights. Each grouped trace has 128
terms and equals the sum of its four equal oriented contributions.
Looking up the frozen actual coframe and trace terms and applying
an independent signed ordering gives the repeated-anchor curvature
branch contribution +1/64. This is one source path. No complete
two-center target coefficient was evaluated here.

## Continuation contract

Original S2 uses two degree-two coframes and a degree-four trace.
S4 uses four coframes and no quaternion trace. Their coefficients
commute, and their exterior factors have even degree. Each coframe
consumes one bit of its own center, giving the nine power pairs
2a+4b≤8 at each center and 81 ordered allocations. Their product
has factorial weight 1/(a_w! b_w! a_z! b_z!). The full raw grade is
10+4A+8B exterior and 13+6A+4B quaternion for A=a_w+a_z and
B=b_w+b_z, with g2^(2+A) g1^B J. At both saturated centers a
reciprocal coframe cannot survive. In the unsaturated first package
that overlap and its signed surviving alternatives are real. The
raw odd quaternion grade does not license dropping live raw keys.

Use the existing x,w,z,contact,y factor order. With identity at z,
its empty mask, empty multiset and unit coefficient leave the exact
original x,w,contact,y word unchanged. Test that restriction against
already accepted actual (S2,1) targets and signed x/y groups, using
the same appropriate ordered or grouped path convention. New
lookalike seed targets alone would not establish continuity.

The first package should retain each actual target and a nonzero
fully labelled branch witness, then compare its complete signed
x/y table to an independently projected raw-oriented canonical
oracle. A known repeated anchored coordinate and an actual
overlapping branch make distinct controls. One overlapping branch
proves its own zero only. Claim a complete target zero only after
exhausting or otherwise excluding all contributing alternatives.
Maintain both mixed seed directions against the same d0+d1
observable. Predefine the role of the seed witness versus the total
when a nonzero complete coefficient is required.

Allocation metadata does not alter physical monomial keys. For
example (S2,S2), (S2²,1) and (1,S2²) share the same overall grade.
When complete sums are required, permit deliberate identical
physical targets across allocations, compare on those common keys
and reaggregate exact signed coefficients. Do not apply a global
target deduplication across allocation identities. The sorted
eventual schedule and chosen first low-power batch are distinct.

The safe last-use rule is sufficient. Retain exterior bits while
any unprocessed factor can touch them. Retain each quaternion
family while any member is used by any remaining factor. Raw target
multiplicities are evidence and survive last-use reasoning.
Only full Berezin projection and exact correlated Haar moments
can eliminate the relevant final family in their respective
calculations. The square and its shared anchors demonstrate
necessary retention, not a complete global schedule.

At the next admission keep prior 696 accepted signed records in
the 2,048 output cap, leaving 1,352 if there are no additional
accepted records. Enforce 8,192 live local rows and later paths,
16,384 prospective oracle rows, and 20 million charged work for
the one bounded batch. Count simultaneous index and projected
rows, charge signed fanout and all materialized scratch as
appropriate, and reuse cache-free seed draws. Preserve cap refusal,
identity controls and exact source evidence. The design provides
no certificate of fit before that implementation is independently
reviewed and run. Full all-center denominator/normalization,
physical response and publication remain open.

The sibling independent script and exact output preserve the
reproduced calculations.
