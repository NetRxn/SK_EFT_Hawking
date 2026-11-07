# Reflection pairs in the Hamiltonian coefficient

Executor01a1ac65, continuation of l1-nodal-hamiltonian-harmonic-r1 at `53765e44ee86bbc3e77d0dc208b7521346d34a1d`. This separately frozen supplement uses the original task snapshot. The following equality groups the nine assignments of the specified spin-one projection. Their signed integrals remain unevaluated.

Use the cycle `000,100,110,010,011,111,101,001` and back to `000`, with x_t indexed modulo eight as in the harmonic result. The cube permutation

`f(b1,b2,b3)=(1−b1,b3,b2)`

is a translation by the first spatial unit followed by exchange of spatial coordinates 2 and 3. Substitution into the eight listed vertices gives `f(x_t)=x_(1−t)`. It exchanges cycle parity classes, reverses the cycle and permutes the four matching edges. Every based moving and retained positive-direction anchor is relabelled to the corresponding based anchor of the image direction, because translation and permutation commute with the period-two neighbor relations. In particular the retained inverse-pair substitution is preserved. All moving and retained product Haar measures are preserved.

Relabel all spatial coordinates and world directions of the original action, leaving the internal Clifford basis and chirality fixed. This transports each complete projected vertex `A_(x,i)^χ` to `−A_(f(x),π(i))^χ`, where π swaps 2 and 3 and fixes time and direction 1. The minus sign is the odd world permutation of the EHC epsilon. No other sign comes from the two actual coframe orders or closed curvature words, which are transported with the same ordered labels. There are exactly 16 vertices in every term, giving total sign +1. The inherited Berezin top is unchanged because each permuted site block has eight generators and the transformation leaves the order inside each block intact. The spin-one cycle character is unchanged under reversal of the holonomy and cyclic change of base. Indeed it is a class function and the spin-one character takes the same real value on G and G^-1. Thus this change of variables preserves the value of each complete signed occupation contribution and its multinomial coefficient, carrying it to its image occupation contribution.

For the occupation parameters of the harmonic result, the even-site multiplicity becomes `a'=4−a`. The even-site forward curvature count becomes the old odd-site backward count, so `k'=4−a−(k+2−a)=2−k`. The involution `(a,k)→(4−a,2−k)` pairs the nine assignments as

- `(0,0)` with `(4,2)`
- `(1,0)` with `(3,2)`
- `(1,1)` with `(3,1)`
- `(2,0)` with `(2,2)`
- `(2,1)` with itself.

The full projected coefficient is therefore the sum of twice the first four representative contributions and once the last, each with its original multinomial. Five signed contractions suffice for this specified label. This symmetry gives equality inside each pair and leaves possible cancellations between representatives open. The full projected coefficient and P0 remain unevaluated. The argument is manual and uses the accepted closed-word and harmonic source conventions. Separate actual mathematical and original-source review is required.
