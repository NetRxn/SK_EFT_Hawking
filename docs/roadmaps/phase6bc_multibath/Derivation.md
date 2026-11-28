# Reachable fixed-dose channels for finitely many baths

Use n≥1 labelled normalized thermal targets T_i and nonnegative
prescribed doses d_i. The public Gibbs slice with dose t and target
T_i is the affine channel e^(-t) X+(1-e^(-t)) tr(X) T_i.
The argument uses this action on every complex input. It applies
to the existing diagonal reset slices. It also applies to any
density targets when the slice is defined by this same channel.

Put D=sum_i d_i and p=e^(-D). Read the schedule backward in
cumulative dose s from 0 to D. The positions assigned to bath i
form a finite union E_i of intervals of total length d_i. By the
public affine composition formula, the supported channel is

  X ↦ p X + tr(X) sum_i w_i T_i,
  w_i = integral_(E_i) e^(-s) ds.

Set F(t)=1-e^(-t). The exact set of weights is the polytope P given by

  sum_i w_i = F(D),
  sum_(i in S) w_i <= F(sum_(i in S) d_i) for every subset S.

This distinguishes target labels even if two target matrices agree.

## Necessary constraints and block-order convex hull

For a set E of total length t inside [0,D], its integral of the
decreasing e^(-s) is at most the integral over [0,t]. For example,
the portions of E outside [0,t] and missing from [0,t] have equal
length, and the integrand on the former is at most e^(-t) and
on the latter at least e^(-t). Apply this to the union of the
positions of S. Summing over the entire partition gives equality
for the full label set.

Write v^pi for the weight vector of one contiguous block per label
in backward order pi. For any real linear objective c·w, choose
pi with coefficients c_pi(1)≥...≥c_pi(n). Put S_j={pi(1),...,pi(j)}.
Summation by parts rewrites the objective as
c_pi(n) F(D) plus the sum of (c_pi(j)-c_pi(j+1)) w(S_j)
over j<n. The subset constraints bound that sum above.
The block order pi attains all its nested bounds at once.
The compact convex hull of the block-order weight vectors therefore
has the same support bound in every direction as P. A separating
linear functional would contradict that bound for a point of P
outside the hull. Thus P is exactly this convex hull.

## Realize convex combinations by finite, deterministic schedules

Write a target w as a convex combination of at most n block orders.
This count follows by affine dependence since every vertex has the
same coordinate sum. If more than n weights are positive, move
along a nontrivial affine dependence until one coefficient becomes
zero, preserving the represented point and nonnegativity.

Take the common interval refinement of the chosen backward block
orders. It has at most n(n-1)+1 nonempty cells. In each cell I the
convex combination assigns fixed fractions lambda_i to the labels,
summing to one. We now split that single cell into finitely many
coloured intervals so that colour i receives both lambda_i |I|
and lambda_i integral_I e^(-s) ds. No random choice of a schedule
is required.

To allocate a colour, compress the currently unassigned pieces of
the cell in dose order to an interval of length L. The inherited
integrand is still decreasing and integrable, with jumps allowed.
If the requested fraction of the remaining mass and length is h,
slide a window of length h L across the compressed interval.
Its integral is continuous in the left endpoint. The leftmost
window's average is at least the entire residual average and the
rightmost window's average is at most that average. Therefore one
window has exactly h times the residual integral. Give its
preimage to the selected colour, remove it, and renormalize the
remaining fractions. Fractions zero or one are immediate.
This converts at most two existing interval interiors into new
cut points at each colour allocation. The last colour takes the
remainder, so a cell has at most 2n-1 pieces. Summing cell lengths
and weighted integrals realizes the requested doses and weights.
Reversing the dose order yields a finite chronological schedule.

This proves a uniform bound (n(n-1)+1)(2n-1) on the number of slices.
It covers zero-length doses and coincident targets. At total dose
zero the empty schedule realizes the sole weight vector. An empty
label family has only the identity action. The bound
is constructive and makes no minimality claim.

## Exact error with a retained spectator

Fix a total dose and let T,T' denote the two unnormalized accumulated
targets for two reachable schedules. In the amplified channel
difference, the common p X cancels. On any joint input X with the
spectator in the second factor the difference is

  (T-T') tensor Tr_system X.

For a density input the spectator marginal has trace norm one.
Multiplicativity of trace norm on tensor products gives output
trace distance exactly ||T-T'||_1/2 for every density input and
every finite nonempty spectator. This value is therefore the
operational diamond distance used by DiamondNormSup. It is
attained by product and correlated inputs alike. On an arbitrary
complex joint matrix, trace-norm duality and ||I tensor B||=||B||
give ||Tr_system X||_1<=||X||_1 and the corresponding induced
trace-norm upper bound. Thus the same formula also gives the
usual half diamond norm, with attainment on a density.

## How many fixed scalar detectors identify the schedule action

If every labelled dose is positive, swapping adjacent block
labels i and j changes the weight vector by a nonzero multiple of
e_i-e_j. The positive multiplier in magnitude is
e^(-s)(1-e^(-d_i))(1-e^(-d_j)), where s is the preceding backward
dose. Hence P has affine dimension n-1. The accumulated-target
polytope has affine dimension
r=dim_R span{T_i-T_1}. Relative interiors are nonempty in the
respective affine hulls. Calibrate with a known trace-one input,
subtracting its known p X contribution. Real-linear readouts
give a linear map on the target affine hull. If fewer than r
readouts are fixed, a nonzero vector in its kernel yields two
distinct sufficiently close accumulated targets about an interior
point with identical data. Conversely r linear coordinates on
the direction span give injective readout. The recovered object
is the channel action, which need not identify the chronological
schedule or the label weights when the targets are dependent.
Zero-dose labels can be deleted for this dimension statement.

For the three-level targets
A=(1/2,1/4,1/4), B=(1/4,1/2,1/4), C=(1/4,1/4,1/2),
use three log-two doses. Chronological B,C,A and C,B,A have the
same A weight 1/2. The B/C weights are 1/8 and 1/4 and then
swapped. The level-A occupation readout agrees for the same
calibration input. The exact accumulated-target trace norm
difference is 1/16 and its diamond distance is 1/32. The level-B
occupation distinguishes the control. Taken together with the
common weight sum, the level-A and level-B occupations recover
all coefficients.

## Bounded noisy two-bath reconstruction

For two fixed bath doses write the reachable weight of B as
I=[l,u]. Let a known trace-one calibration and real-linear
detector give y(w)=y0+d w with d nonzero. For a datum y and
known bounded error epsilon, let z=(y-y0)/d and eta=epsilon/|d|.
The compatible weights form J=I intersect [z-eta,z+eta].
For actual data under the error model this interval is nonempty.
Its midpoint is a reachable schedule by the two-bath result.

The diamond distance between two weights is c times their
absolute difference, with c=||B-A||_1/2. The midpoint minimizes
the worst-case distance over the compatible interval. Every
alternative estimated channel has worst-case error at least
half the distance between the two endpoint channels, by the
triangle inequality. The midpoint attains this value, including
against estimators allowed to return channels outside the family.
Over all admissible data the exact minimax radius is
c min(eta,(u-l)/2). The center datum attains maximum compatible
interval length and supplies the matching lower bound.

Use the two positive targets from the clipped-channel control,
A=(3/4,1/4) and B=(1/4,3/4), with the same log-two doses and
first-level detector. Here choose the calibration input diag(1,0)
and datum 11/16. Then
I=[1/4,1/2], y(w)=13/16-w/2 and c=1/2.
At y=11/16 with error allowance 1/16 the interval is
[1/4,3/8]. Clipping the nominal weight gives 1/4 and worst-case
error 1/16. The compatible midpoint is 5/16 with worst-case
error 1/32. The endpoint channels and every distance in this
comparison have finite same-dose realizations.
