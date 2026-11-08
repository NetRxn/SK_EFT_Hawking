# Independent N16 zero-source denominator review

**ACCEPT_SCOPED.** The tighter denominator and sufficient CRT product bound apply to the full zero-source partition polynomial of the original periodic, closed N16 action at source `a72e9c41fd91c51a0e15dd1e5648203aaf3228c0`. The author manifest verifies and continuity matched at intake and terminal.

## Source and arithmetic review

The original regulator supplies 128 ordered Grassmann generators and 64 independently anchored Spin(4) links. Each link has two normalized SU(2) factors. The code retains each direction and anchor even when both periodic hops reach the same neighbor. The closed word is `D† C† B A`. Original link and gamma matrix entries have Gaussian-integer coefficients. The actual coframe consists of four signed quarter increments, each linear in the anchored quaternion variables and bilinear in the exterior generators. The 24 local S4 terms use four coframes and integer epsilon. The 384 local S2 terms use two coframes and an ordered trace of four links, with one action quarter. I checked these source paths directly in `src/core/formulas.py` and `src/vestigial/original_coefficients.py`, and reproduced their degree and integer-coefficient properties for the complete one-site roster and all 16 coframe labels.

For saturation at 128 generators, (8m+4n=128), so (2m+n=32). The action denominator (4^{4m+3n}) follows by multiplying the original quarters. Expansion of the two even action polynomials gives (m!n!), which divides (32!) by the integral multinomial quotient. Closed plaquette links contribute at most four quaternion powers per trace, so the whole degree is at most (4m+6n=2K) with (K=96-4m).

The grouped evaluator merges every repeated symbol at the same site, direction and chirality before applying the joint four-coordinate moment. For even powers with half-degree (k), its denominator divides (2^k(k+1)!). Odd powers in any coordinate give zero. Six exact controls distinguish a fourth power on one coordinate, two squared coordinates in one group and two squares at distinct chiralities or anchors. The latter moments are respectively (1/8), (1/24) and (1/16). The joint monomial degree gives (sum k_jle K) for all 128 factors.

Counting multiples of (p^r) in ((k+1)!) gives (v_p((k+1)!)=(k+1-s_p(k+1))/(p-1)). Since (s_p(k+1)ge1), summing over the chiral groups bounds the combined factorial exponent by (lfloor K/(p-1)
floor). The extra (2^{sum k_j}) divides (2^K). The refinement therefore gives the stated common denominator (32!4^{96}H(96)), with the per-coefficient denominator (m!n!4^{4m+3n}H(K)). The coordinatewise sharpness claim concerns the unreduced factorial envelope. It follows by allocating half-degree (p-1) to (lfloor K/(p-1)
floor) groups. The actual original support and odd double-factorial numerators may lower the required denominator.

I independently computed the exact LCM of the factorial denominators over all half-degree partitions by the recurrence (F(0)=1), (F(t)=operatorname{lcm}_{1le jle t}((j+1)!F(t-j))). All partitions fit the 128-group roster since (tle96). The LCMs are nested and reproduce all 17 per-coefficient bit counts, as well as the old and refined common denominators at 77,222 and 938 bits. Under the existing (2^{800}) absolute height bound, the old and refined strict reconstruction thresholds have 78,023 and 1,739 bits. The sufficient counts for distinct good primes above (2^{60}) are 1,301 and 29. These are product-size guarantees for the stated prime class.

The Gaussian-integer components must both survive each modular reduction. At a split prime, evaluating at both roots of (-1) recovers the components using the invertible determinant (2r) for root (r). At an inert prime, the rank-two field basis preserves them directly. Coordinatewise CRT then yields unique signed components once the product exceeds twice the component height. All primes above 97 avoid the common denominator. Neither the derivation nor the controls assume positivity of a finite-field value or infer a zero coefficient from an incomplete residue.

## Scope

This review certifies the denominator and reconstruction bound and the reported bounded controls. The accepted separate analytic proof gives (Z(2^{1717},1)>1) at its explicit original algebraic point. The pure-EHC coefficient (c_0), exact contraction support and feasibility, the full coefficient values, and physical normalization remain separate. No original evaluation, Lean operation or tracked edit occurred.
