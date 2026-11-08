# Original N16 partition coefficient denominator refinement

Use the accepted periodic closed N16 action, zero source, and the exact
top orientation from N16_SYMBOLIC_NORMALIZATION.md. For the coefficient
c_m, m counts S4 vertices and n=32-2m counts S2 vertices. The original
denominators before Haar divide m! n! 4^(4m+3n). The total quaternion
degree is at most 4m+6n = 2K, with K=96-4m. Only monomials whose
coordinates are all even contribute to the Haar integral. This use of
parity is on the completed word, after shared-link factors are multiplied.

For the original 128 chiral SU(2) factors, write k_j for their
half-degrees. Their normalized moments have integer numerators and
denominators 2^k_j (k_j+1)!. The sum of k_j is at most K. The factorial
valuation identity follows by counting multiples of powers of a prime p.
Writing s_p for base-p digit sum, the identity is

    v_p((k+1)!) = (k+1 - s_p(k+1))/(p-1) <= k/(p-1).

Sum over all chiral groups and use the integrality of each valuation.
The product of all moment denominators therefore divides

    H(K) = 2^K * product_{p prime <= K+1} p^floor(K/(p-1)).

This is uniform over arbitrary allowed assignments of exponents to actual
groups. It neither treats coordinates within a chiral group as independent
nor merges distinct anchors. The bound is coordinatewise sharp for the
unreduced factorial part if one allows all distributions of half-degree
at most K. Assign k=p-1 to floor(K/(p-1)) different groups; at most 96
groups are needed. Actual source support and numerator cancellations may
make a smaller denominator sufficient.

Thus m! n! 4^(4m+3n) H(K) clears c_m into Z[i], and
32! 4^96 H(96) is common for all 17 original coefficients, including the
separately proved zero odd-m slots. The accepted complex absolute bound
2^800 bounds each integer component after multiplication by the common
denominator. A complete coordinatewise CRT reconstruction needs a
product modulus strictly exceeding twice that integer bound, and a correct
Gaussian-integer representation at each prime. For p=1 mod 4 use both
embeddings or a full rank-two ring. For p=3 mod 4 the quadratic extension
retains both components. A zero residue is insufficient to show a zero
coefficient until the complete reconstruction bound is met.

The exact integer script reproduces the old 77,222-bit common denominator
and the new 938-bit common denominator. With the same coefficient height
bound, 29 distinct good primes each greater than 2^60 suffice by product
size, versus 1,301 under the previous conservative denominator. This
reduces the arithmetic reconstruction requirement. Each prime still
requires the full contraction of the same original coefficient, and no
state count, runtime feasibility, coefficient value or physical domain
is inferred here.

The script checks exact divisibility for all 17 coefficients and separately
recovers the maximal factorial valuation via dynamic programming over
all half-degree partitions. The accepted analytic result already proves
original Z>1 at its explicit algebraic point. This refinement addresses
exact coefficient reconstruction, including the still open pure-EHC c0.
