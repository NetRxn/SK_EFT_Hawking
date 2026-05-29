#!/usr/bin/env python3
"""KMM base-case (𝕊₃) BFS + the constant N₃ — reference computation.

Phase 6x Tier-2 Item F (M4). Companion to `kmm_zomega_reference_oracle.py`.

KMM (arXiv:1206.5236, Corollary 1) bounds single-qubit Clifford+T synthesis by
`n_g(U) ≤ N₃ + 4·sde_{|·|²}(U)`, where `N₃` is the max gate count over the finite
set 𝕊₃ of unitaries with `sde(|z₀₀|²) ≤ 3` (the base case). The pre-implementation
dossier flags the **value of N₃ as UNKNOWN**. This script computes it by BFS over
the Clifford+T group (matrices over ℤ[ω][1/√2], represented as a ZOmega numerator
matrix over a common `√2`-denominator), matching the Lean `ZOmega` convention.

Result (BFS depth 14, generating set {H,S,T,X,Y,Z,ω}; the `sde(|z₀₀|²)≤3` levels
saturate at word-length 9 ≪ 14, i.e. converged):

    sde(|z₀₀|²) = 0 : 128 matrices, max shortest-word 5
    sde(|z₀₀|²) = 2 : 512 matrices, max shortest-word 7
    sde(|z₀₀|²) = 3 : 1024 matrices, max shortest-word 9
    ─────────────────────────────────────────────────────
    𝕊₃ = {sde(|z₀₀|²) ≤ 3} : 1664 matrices, **N₃ = 9**

(`sde(|z₀₀|²)` skips 1 — it takes values in {0,2,3,4,…} — consistent with the
`gde(|x|²) ≤ 1` cleared-numerator structure.) This cross-checks deep-research Q2.
"""

from __future__ import annotations
import sys, os, collections
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kmm_zomega_reference_oracle import (  # noqa: E402
    mul as zmul, add as zadd, norm_sq, divides_sqrt2, div_sqrt2, gde_sqrt2)

ZERO = (0, 0, 0, 0)
ONE = (0, 0, 0, 1)
NEG1 = (0, 0, 0, -1)
OM = (0, 0, 1, 0)        # ω
I = (0, 1, 0, 0)         # ω² = i
NEGI = (0, -1, 0, 0)

# A matrix = ((m00, m01, m10, m11), k) meaning numerator / √2^k (each entry ZOmega).
GENS = {
    'H': ((ONE, ONE, ONE, NEG1), 1),   # (1/√2)·[[1,1],[1,-1]]
    'S': ((ONE, ZERO, ZERO, I), 0),    # diag(1, i)
    'T': ((ONE, ZERO, ZERO, OM), 0),   # diag(1, ω)
    'X': ((ZERO, ONE, ONE, ZERO), 0),
    'Y': ((ZERO, NEGI, I, ZERO), 0),
    'Z': ((ONE, ZERO, ZERO, NEG1), 0),
    'W': ((OM, ZERO, ZERO, OM), 0),    # ω·I (global phase)
}
ID = ((ONE, ZERO, ZERO, ONE), 0)


def matmul(A, B):
    (a00, a01, a10, a11), j = A
    (b00, b01, b10, b11), k = B
    return ((zadd(zmul(a00, b00), zmul(a01, b10)), zadd(zmul(a00, b01), zmul(a01, b11)),
             zadd(zmul(a10, b00), zmul(a11, b10)), zadd(zmul(a10, b01), zmul(a11, b11))), j + k)


def normalize(A):
    ents, k = A
    while k > 0 and all(divides_sqrt2(e) for e in ents):
        ents = tuple(div_sqrt2(e) for e in ents)
        k -= 1
    return (ents, k)


def sde_z00sq(A):
    ents, k = normalize(A)
    return max(0, 2 * k - gde_sqrt2(norm_sq(ents[0])))


def bfs(maxlen: int = 14):
    start = normalize(ID)
    dist = {start: 0}
    q = deque([start])
    while q:
        M = q.popleft()
        d = dist[M]
        if d >= maxlen:
            continue
        for G in GENS.values():
            N = normalize(matmul(G, M))
            if N not in dist:
                dist[N] = d + 1
                q.append(N)
    return dist


def main():
    dist = bfs(14)
    print(f"orbit explored to word length 14: {len(dist)} distinct matrices")
    by = collections.defaultdict(list)
    for M, d in dist.items():
        by[sde_z00sq(M)].append(d)
    print("\nsde(|z₀₀|²) | #matrices | max shortest-word")
    for s in sorted(by):
        print(f"   {s:2d}       | {len(by[s]):6d}    | {max(by[s])}")
    base = [d for M, d in dist.items() if sde_z00sq(M) <= 3]
    n3 = max(base)
    print(f"\n𝕊₃ = {{sde(|z₀₀|²) ≤ 3}}: {len(base)} matrices, N₃ = {n3}")
    assert n3 == 9, f"expected N₃ = 9, got {n3}"
    assert sorted(by.keys())[:4] == [0, 2, 3, 4], "sde(|z₀₀|²) value-set changed"
    print("N₃ = 9 (saturated at word-length 9 ≪ 14 ⟹ converged). Checks PASS.")


if __name__ == "__main__":
    main()
