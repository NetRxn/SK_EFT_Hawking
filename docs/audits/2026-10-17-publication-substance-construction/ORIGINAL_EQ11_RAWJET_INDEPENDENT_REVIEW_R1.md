# Independent finite determinant raw-jet correspondence review

**ACCEPT** exact source commit `7532bf3f4ec0ae7076aec8b52641245baa22a3af`
against `5a3946d008e42a2e92633c74078639682cfd92a2`. One 212-line
Lean file, SHA-256
`95925445487d6ff7b0f1ce3c7feb6a7256c4b2fa73ea7aa9d595de190744ddb3`.
The assigned continuity input was SAME before and after review. Exact
two-commit diff check passed. I read all 16 public statements and their
proofs; no source proof escape or added axiom was present. ROOT owns
the independent native replay and absorption.

The nested dual number entry has outer pair `((v, db), (da, dab))`.
The inner-outer coefficient is the sum of exactly the four positional
splits in Python `RawJet.__mul__`. For a repeated label both first
slots coincide but remain distinct positions in the multiplication,
so the cross term occurs twice. Neither the theorem nor its Python
model requires dividing by two. Addition, one, zero and the scalar
sign are accounted for. Python normalizes label order in storage and
access; formal polynomial iterated derivatives commute by the
monomial/additive proof.

The coefficient pair from an ordinary polynomial is a ring map because
orders zero and one in a product depend only on those orders in its
factors. Composing the two maps with independent perturbations gives
the entry's value, both first derivatives and undivided iterated
partial, also at repeated labels. Mapping the matrix entries through
this homomorphism commutes with determinant. The preceding accepted
mask DP gives the equality for the actual recurrence over this ring.
There is no invertibility assumption. A wholly missing coordinate is
the zero jet, individual missing slots default to zero, the empty
determinant is one, and repeated full jet rows vanish. Coincident value
rows alone can still have nonzero derivative outputs.

The independent rational oracle in `check.py` enumerates signed Leibniz
permutations, multiplies ordinary truncated Taylor polynomials without
using the source multiplication or recurrence, then converts the
diagonal coefficients to raw derivatives. On the actual Python entry
point it matched 1,000 raw coefficients of 200 fixtures across
dimensions 0–4 and 0–3 derivative labels. Inputs included sparse
individual planes, zero value matrices, value-only matrices, and
repeated full rows. Mixed acceleration keys were supplied reversed
and all output keys checked in both orientations. There were 257
nonzero second-order slots.

Acceptance covers a selected positional pair and exact commutative
value semantics, plus the polynomial determinant derivative theorem
when the supplied jet entries are the derivatives of the stated
polynomial matrix. Concrete Python containers, input validation,
runtime budgeting, original Dirac matrix assembly and scientific or
publication acceptance remain separate. The value-only no-label case
uses the previous plain determinant DP.
