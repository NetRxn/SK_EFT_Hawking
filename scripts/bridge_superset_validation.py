"""Validate the `bridge` native_decide BEFORE formalizing it.

bridge: realizable M, μ(M)=sde(|M00|²) ≤ 3  ⟹  kSO3 M ≤ 3.

Formalization plan: via column0_cleared_bounded, √2²·M00=of x, √2²·M10=of y with
(normSq x).d ≤ 4, (normSq y).d ≤ 4. Via realizable_col1, M01=-(ωᵏ·conj M10),
M11=ωᵏ·conj M00. So M = reconstruct(x,y,k) = ((x, -(ωᵏ·conj y), y, ωᵏ·conj x), 2).

The native_decide will quantify over the SUPERSET box:
    {(x,y,k) : norm_sq(x)+norm_sq(y) = (0,0,0,4),  |coords|≤2,  k∈0..7}
(the unitarity necessary condition normSq M00 + normSq M10 = 1, scaled by √2⁴=4).
This is a superset of genuinely realizable μ≤3 matrices (like ma_step's BᵀB=2ᵏI).

CLAIM TO CHECK: kSO3(reconstruct(x,y,k)) ≤ 3 for ALL (x,y,k) in the superset.
If 0 failures, the native_decide is safe. Also report box size + max kSO3, and
sanity-check the realizable 1664-orbit is covered.
"""
from __future__ import annotations
import sys, os
# this script lives in SK_EFT_Hawking/scripts/ alongside the ZOmega oracle modules
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from kmm_zomega_reference_oracle import (mul as zmul, add as zadd, conj as zconj_o,
                                         norm_sq, divides_sqrt2, gde_sqrt2)
from kmm_n3_bfs import GENS, ID, matmul, normalize, ONE, ZERO, OM, sde_z00sq
from kmm_ma_coverage_validation import kso3, adjoint  # reuse the validated kSO3

def zneg(z):
    return tuple(-c for c in z)

def zpow_om(k):
    """ω^k as ZOmega (mod ω⁴=-1, period 8)."""
    r = ONE
    for _ in range(k % 8):
        r = zmul(r, OM)
    return r

FOUR = (0, 0, 0, 4)  # = 4·ONE  (the scaled unitarity constant)

def reconstruct(x, y, k):
    """M = [[x, -(ωᵏ·conj y)], [y, ωᵏ·conj x]] / √2²  (realizable_col1 form)."""
    omk = zpow_om(k)
    m00 = x
    m10 = y
    m01 = zneg(zmul(omk, zconj_o(y)))
    m11 = zmul(omk, zconj_o(x))
    return ((m00, m01, m10, m11), 2)

# ── enumerate the superset box ────────────────────────────────────────────────
R = range(-2, 3)
zoms = [(a, b, c, d) for a in R for b in R for c in R for d in R]
# group by norm_sq for the coupling filter
from collections import defaultdict
by_ns = defaultdict(list)
for z in zoms:
    by_ns[norm_sq(z)].append(z)

count = 0
maxk = 0
failures = []
seen_pairs = 0
# pair x,y so that norm_sq(x)+norm_sq(y) = FOUR
for nsx, xs in by_ns.items():
    nsy_needed = tuple(FOUR[i] - nsx[i] for i in range(4))
    ys = by_ns.get(nsy_needed)
    if not ys:
        continue
    # μ(M) ≤ 3  ⟺  gde(norm_sq x) ≥ 1  ⟺  √2 | norm_sq x   (the dropped filter)
    if not divides_sqrt2(nsx):
        continue
    for x in xs:
        for y in ys:
            seen_pairs += 1
            for k in range(8):
                M = reconstruct(x, y, k)
                kk = kso3(M)
                count += 1
                if kk > maxk:
                    maxk = kk
                if kk > 3:
                    failures.append((x, y, k, kk))

print(f"superset box (x,y,k) tuples checked : {count}")
print(f"distinct (x,y) pairs with nsx+nsy=4  : {seen_pairs}")
print(f"max kSO3 over the superset           : {maxk}")
print(f"FAILURES (kSO3 > 3)                   : {len(failures)}")
for f in failures[:10]:
    print("   FAIL", f)

# ── sanity: every realizable μ≤3 matrix is in the superset & has kSO3≤3 ────────
# BFS the μ≤3 orbit, check each is reconstruct(x,y,k) for some box tuple, and kSO3≤3
from collections import deque
start = normalize(ID)
dist = {start: 0}
q = deque([start])
orbit = []
while q:
    M = q.popleft()
    orbit.append(M)
    for G in GENS.values():
        N = normalize(matmul(G, M))
        if N not in dist and sde_z00sq(N) <= 3:
            dist[N] = dist[M] + 1
            q.append(N)
orbit_bad = [M for M in orbit if kso3(M) > 3]
print(f"\nrealizable μ≤3 orbit size            : {len(orbit)}")
print(f"realizable orbit with kSO3 > 3        : {len(orbit_bad)}")
print("\nVERDICT:", "SAFE — native_decide claim holds over superset"
      if not failures else "UNSAFE — superset too loose, need tighter filter")
