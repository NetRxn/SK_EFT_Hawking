# Pure-g₂ one-point selection on the common 2⁴ regulator

Use the covariant closed-order action and literal composite metric
source G_{μν}(x) = Σ_b T_μ^b(x) T_ν^b(x). This covers G₂₂, G₃₃,
G₂₃, G₃₂, and the fixed shear D = G₂₂ − G₃₃, at any site.
The source has exterior degree four.

Let S = γ₃ = [[0,I],[I,0]] in the actual Dirac basis of
l1_full_action_reference.py. It is involutive. Conjugate each link
by S and apply S to both barred and unbarred generators. Within
each four-entry block the two chiral pairs are exchanged, giving
the local permutation i → i XOR 2. Its determinant is +1 per
block. Thus the product Berezin top form is invariant. Product
Haar is invariant under exchange of its two equal SU(2) factors,
and identity tree links remain identity.

Write s_b = −1 for b=0,1,2 and s₃=+1. Then S γ_b S = s_b γ_b
and S γ₅ S = −γ₅. Each of the four coframe blocks in the full
action has a matrix of the form U^±1 γ_b or γ_b U^±1 in a
bilinear. Each acquires s_b under the combined link and generator
change, independently of the world axis, directed anchor, and
endpoint order. A metric insertion contracts two equal internal
labels and their signs multiply to one, even when the two source
links differ. The shear is invariant by linearity.

The transformed closed plaquette at any site is S P S, since
conjugation commutes with links, inverses and ordered products.
Cyclicity gives tr(S P S γ_b γ_c γ₅) = −s_b s_c tr(P γ_b γ_c γ₅).
The two frame signs multiply to s_b s_c. Each complete
curvature–coframe quartic vertex therefore changes sign. This
retains the world epsilon, action quarter, ordered vertices and
local frame orientation. A contribution conditioned on a
particular chiral probe may map to its swapped coordinate.
The zero follows after the complete invariant Haar sum.

There are 16 sites and eight odd generators per site. At pure
g₂, all action vertices and metric insertions are degree four.
Only 31 vertices contribute to a one-point coefficient, since
4(31+1)=128. For every ordered 31-vertex word with one such source,
the measure-preserving involution maps its integrand to its
negative. Its integrated Berezin top coefficient is exactly
zero. Summing words and retaining their factorials preserves zero.

The zero-source and two-source sectors use 32 and 30 vertices.
This symmetry supplies no sign or nonzero certificate for either.
If the full common-regulator coefficient Z₃₂ is nonzero and
g₂≠0, the normalized metric one-points vanish. For a declared
linear source the connected two-point is the full two-source
derivative-normalized numerator divided by g₂² Z₃₂. This uses
distinct labelled derivatives, or twice the raw repeated-source
coefficient [h²]. The signed numerator, the nonzero
denominator, and physical source/contact matching remain separate.
Mixed g₁/g₂ or another source family needs its own parity check.

The [companion polynomial replay](l1_pure_g2_one_point.py) checks the tracked frame functions,
actual chiral curvature coefficients L, directed anchors, top-form
sign and diagonal/off-diagonal composite sources. It evaluates
local tensors and does not contract a full 31-vertex word.

Independent review checked the full-word change of variables and
reran 512 frame, 544 source, and 96 curvature comparisons.
