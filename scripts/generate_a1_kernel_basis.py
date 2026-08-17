"""Generate kernel-basis certificates for d1, d2, d3 of the A(1) minimal free resolution.

Phase 5q.T. Replaces the last three `native_decide` uses in
`lean/SKEFTHawking/A1Resolution.lean` with a kernel-pure certificate.

The three theorems state a CARDINALITY, `Fintype.card {v // d.mulVec v = 0} = 2^k`,
not a rank. An RREF certificate of the kind used for d4/d5 proves a rank and does not,
by itself, reach a cardinality: getting there would need rank-nullity plus a cardinality
computation. So the certificate emitted here is the one the cardinality statement actually
wants -- an explicit bijection `(Fin k -> F2) ~= ker d`:

    B : n x k   columns are a basis of ker(d)
    C : k x n   coordinate projection, a left inverse of B on ker(d)
    X : n x m   the "vanishes on the kernel" cofactor

certified by three matrix identities, each an explicit Lean literal closed by
`decide +kernel`:

    (1)  d * B = 0            every column of B lies in ker(d)
    (2)  C * B = 1            B is injective, C recovers the coordinates
    (3)  B * C + 1 = X * d    B * C is the identity ON ker(d)

(3) is the crux and is what makes the bijection SURJECTIVE: for any v with d v = 0,
(B C + 1) v = X (d v) = 0, hence B (C v) = v over F2. Together with (2) these give
mutually inverse maps, so the kernel has exactly 2^k elements.

Such an X always exists: B*C + 1 annihilates ker(d), and over a field the space of
functionals annihilating ker(d) is exactly the row space of d, so every row of B*C + 1
is an F2-combination of rows of d.

*** This script is a WITNESS FINDER, not part of the proof. ***
Nothing it computes is trusted. Its entire output is Lean matrix literals whose defining
identities are re-derived from scratch by the Lean kernel via `decide +kernel`; a wrong
entry anywhere in B, C or X makes A1Resolution.lean fail to compile. The proof's trust
base is `{propext, Classical.choice, Quot.sound}` and does not include this file, numpy,
or Python.

Companion to scripts/generate_a1_homotopy.py (same house pattern, same SPEC transcription).
"""

import numpy as np

# --- differentials, transcribed from lean/SKEFTHawking/A1Resolution.lean -------------

SPEC = {
    "d1": ((8, 16), [(1, 0), (2, 8), (3, 2), (3, 9), (4, 2), (5, 3), (5, 4), (5, 10),
                     (6, 12), (7, 6), (7, 13)]),
    "d2": ((16, 16), [(1, 0), (3, 2), (3, 8), (4, 2), (5, 3), (5, 4), (6, 10), (7, 6),
                      (7, 11), (7, 12), (10, 8), (11, 9), (13, 10), (14, 12), (15, 13)]),
    "d3": ((16, 16), [(1, 0), (3, 2), (4, 2), (5, 3), (5, 4), (6, 8), (7, 6), (7, 9),
                      (11, 8), (14, 10), (15, 11), (15, 12)]),
}


def build(name):
    (m, n), entries = SPEC[name]
    M = np.zeros((m, n), dtype=np.uint8)
    for k, i in entries:
        M[k, i] = 1
    return M


def mm(A, B):
    return (A.astype(np.int64) @ B.astype(np.int64) % 2).astype(np.uint8)


# --- F2 linear algebra --------------------------------------------------------------

def rref(M):
    """Return (R, pivots, T) with R = T M in reduced row echelon form over F2."""
    M = M.copy() % 2
    m, n = M.shape
    T = np.eye(m, dtype=np.uint8)
    pivots = []
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, m):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        T[[r, piv]] = T[[piv, r]]
        for i in range(m):
            if i != r and M[i, c]:
                M[i] ^= M[r]
                T[i] ^= T[r]
        pivots.append(c)
        r += 1
        if r == m:
            break
    return M, pivots, T


def solve(A, B):
    """Solve A X = B over F2 (any particular solution). Raise if inconsistent."""
    m, n = A.shape
    aug = np.concatenate([A, B], axis=1) % 2
    R, pivots, _ = rref(aug)
    for p in pivots:
        if p >= n:
            raise ValueError("inconsistent system: column %d" % p)
    X = np.zeros((n, B.shape[1]), dtype=np.uint8)
    for row, p in enumerate(pivots):
        X[p] = R[row, n:]
    assert np.array_equal(mm(A, X), B % 2), "solve failed"
    return X


def kernel_certificate(d):
    """Return (B, C, X, k) certifying ker(d) ~= F2^k, as described in the module docstring."""
    m, n = d.shape
    R, pivots, _ = rref(d)
    free = [c for c in range(n) if c not in pivots]
    k = len(free)

    # B: standard nullspace basis. Column l has a 1 in free position free[l], and the
    # back-substituted values in the pivot positions.
    B = np.zeros((n, k), dtype=np.uint8)
    for l, f in enumerate(free):
        B[f, l] = 1
        for row, p in enumerate(pivots):
            B[p, l] = R[row, f]

    # C: read off the free coordinates. C B = I_k because column l of B is 1 at free[l]
    # and 0 at every other free position.
    C = np.zeros((k, n), dtype=np.uint8)
    for l, f in enumerate(free):
        C[l, f] = 1

    # X: solve X d = B C + I_n, i.e. d^T X^T = (B C + I_n)^T.
    M = mm(B, C) ^ np.eye(n, dtype=np.uint8)
    X = solve(d.T, M.T).T

    return B, C, X, k


# --- emit Lean ----------------------------------------------------------------------

def emit(name, M):
    rows, cols = M.shape
    ent = [(int(r), int(c)) for r in range(rows) for c in range(cols) if M[r, c]]
    lines = ["def %s : Matrix (Fin %d) (Fin %d) F2 := Matrix.of fun k i =>" % (name, rows, cols),
             "  match k.val, i.val with"]
    buf = ["| %d, %d => 1" % (r, c) for r, c in ent]
    for j in range(0, len(buf), 4):
        lines.append("  " + " ".join(buf[j:j + 4]))
    lines.append("  | _, _ => 0")
    return "\n".join(lines)


def main():
    out = []
    for name in ("d1", "d2", "d3"):
        d = build(name)
        m, n = d.shape
        B, C, X, k = kernel_certificate(d)
        r = len(rref(d)[1])

        # Re-check the three identities Lean will re-derive independently.
        ok1 = np.array_equal(mm(d, B), np.zeros((m, k), dtype=np.uint8))
        ok2 = np.array_equal(mm(C, B), np.eye(k, dtype=np.uint8))
        ok3 = np.array_equal(mm(B, C) ^ np.eye(n, dtype=np.uint8), mm(X, d))
        print("%s: rank=%d nullity=%d card=2^%d=%d  | d*B=0 %s | C*B=1 %s | B*C+1=X*d %s"
              % (name, r, k, k, 2 ** k, ok1, ok2, ok3))
        assert ok1 and ok2 and ok3 and r + k == n

        idx = name[-1]
        out.append(emit("kerB%s" % idx, B))
        out.append(emit("kerC%s" % idx, C))
        out.append(emit("kerX%s" % idx, X))

    print("\n-- ===== LEAN =====")
    for block in out:
        print(block)
        print()


if __name__ == "__main__":
    main()
