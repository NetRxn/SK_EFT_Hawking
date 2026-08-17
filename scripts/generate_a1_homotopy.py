"""Generate an F2 contracting homotopy for the augmented A(1) minimal free resolution.

Augmented complex (all over F2):
    F2 <-eps- P0(8) <-d1- P1(16) <-d2- P2(16) <-d3- P3(16) <-d4- P4(24) <-d5- P5(32)

We seek s_{-1}: F2 -> P0, s_n : P_n -> P_{n+1} with
    eps . s_{-1} = I_1
    d1 . s0  + s_{-1} . eps = I_8
    d_{n+1} . s_n + s_{n-1} . d_n = I_{dim P_n}   (n >= 1)

Its existence is equivalent to exactness; verifying the identities in Lean by
`decide +kernel` is a kernel-pure exactness certificate (no native_decide).
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
    "d4": ((16, 24), [(1, 0), (3, 2), (4, 2), (5, 3), (5, 4), (6, 8), (7, 6), (7, 9),
                      (9, 8), (11, 10), (12, 10), (13, 11), (13, 12), (14, 16), (15, 14),
                      (15, 17)]),
    "d5": ((24, 32), [(1, 0), (3, 2), (4, 2), (5, 3), (5, 4), (6, 8), (7, 6), (7, 9),
                      (9, 8), (11, 10), (12, 10), (13, 11), (13, 12), (14, 16), (15, 14),
                      (15, 17), (17, 16), (18, 24), (19, 18), (19, 25), (20, 18), (21, 19),
                      (21, 20), (21, 26), (22, 28), (23, 22), (23, 29)]),
}


def build(name):
    (m, n), entries = SPEC[name]
    M = np.zeros((m, n), dtype=np.uint8)
    for k, i in entries:
        M[k, i] = 1
    return M


d = {k: build(k) for k in SPEC}
eps = np.zeros((1, 8), dtype=np.uint8)
eps[0, 0] = 1  # augmentation = coefficient of e0


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
    # pivot in a B column => inconsistent
    for p in pivots:
        if p >= n:
            raise ValueError("inconsistent system: column %d" % p)
    X = np.zeros((n, B.shape[1]), dtype=np.uint8)
    for row, p in enumerate(pivots):
        X[p] = R[row, n:]
    assert np.array_equal(mm(A, X), B % 2), "solve failed"
    return X


def rank(M):
    return len(rref(M)[1])


# --- build the homotopy -------------------------------------------------------------

dims = {0: 8, 1: 16, 2: 16, 3: 16, 4: 24, 5: 32}

s = {}
# s_{-1} : F2 -> P0 with eps s_{-1} = I_1
s[-1] = solve(eps, np.eye(1, dtype=np.uint8))

# n = 0 : d1 s0 = I_8 - s_{-1} eps
t0 = (np.eye(8, dtype=np.uint8) ^ mm(s[-1], eps))
s[0] = solve(d["d1"], t0)

for n in (1, 2, 3, 4):
    dn = d["d%d" % n]
    dn1 = d["d%d" % (n + 1)]
    t = (np.eye(dims[n], dtype=np.uint8) ^ mm(s[n - 1], dn))
    s[n] = solve(dn1, t)

# --- verify -------------------------------------------------------------------------

ok = []
ok.append(("eps . s(-1) = I1", np.array_equal(mm(eps, s[-1]), np.eye(1, dtype=np.uint8))))
ok.append(("d1 s0 + s(-1) eps = I8",
           np.array_equal(mm(d["d1"], s[0]) ^ mm(s[-1], eps), np.eye(8, dtype=np.uint8))))
for n in (1, 2, 3, 4):
    lhs = mm(d["d%d" % (n + 1)], s[n]) ^ mm(s[n - 1], d["d%d" % n])
    ok.append(("d%d s%d + s%d d%d = I%d" % (n + 1, n, n - 1, n, dims[n]),
               np.array_equal(lhs, np.eye(dims[n], dtype=np.uint8))))
for name, good in ok:
    print(("OK   " if good else "FAIL ") + name)

print()
for n in ("d1", "d2", "d3", "d4", "d5"):
    print("rank(%s) = %d" % (n, rank(d[n])))
print("rank(eps) = %d" % rank(eps))


# --- emit Lean ----------------------------------------------------------------------

def emit(name, M, rows, cols):
    ent = [(int(k), int(i)) for k in range(M.shape[0]) for i in range(M.shape[1]) if M[k, i]]
    lines = []
    lines.append("def %s : Matrix (Fin %d) (Fin %d) F2 := Matrix.of fun k i =>" % (name, rows, cols))
    lines.append("  match k.val, i.val with")
    buf = []
    for k, i in ent:
        buf.append("| %d, %d => 1" % (k, i))
    # 4 per line
    for j in range(0, len(buf), 4):
        lines.append("  " + " ".join(buf[j:j + 4]))
    lines.append("  | _, _ => 0")
    return "\n".join(lines)


print()
print("-- ===== LEAN =====")
print(emit("s_neg1", s[-1], 8, 1))
print()
print(emit("s0", s[0], 16, 8))
print()
print(emit("s1", s[1], 16, 16))
print()
print(emit("s2", s[2], 16, 16))
print()
print(emit("s3", s[3], 24, 16))
print()
print(emit("s4", s[4], 32, 24))
