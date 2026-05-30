"""Validate the `cliffordBase` discharge BEFORE formalizing.

cliffordBase: realizable M, kSO3 M = 0  ⟹  ∃ gs, interp gs = M ∧ gs.length ≤ 6.

kSO3 M = 0 ⟺ M is a single-qubit Clifford (up to global phase ωᵏ) = the 192
matrices ⟨H,S,X,Y,Z,ω⟩. Plan (mirrors the bridge): M = reconstruct x y k over the
bridge box; for the kSO3=0 subset look up a ≤6-gate Clifford word.

Checks:
  (1) kSO3=0 subset of the bridge box has size 192 (the Cliffords).
  (2) BFS over Clifford gens {H,S,X,Y,Z,W} reaches every kSO3=0 matrix in ≤6 gates.
  (3) the μ = sde(|z00|²) values on kSO3=0 (to decide how Lean gets the column box).
  (4) emit the (x,y,k) → word lookup for the Lean encoding.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from kmm_zomega_reference_oracle import (mul as zmul, conj as zconj_o, norm_sq, divides_sqrt2)
from kmm_n3_bfs import GENS, ID, matmul, normalize, ONE, OM, sde_z00sq
from kmm_ma_coverage_validation import kso3
from collections import deque, defaultdict

def zneg(z): return tuple(-c for c in z)
def zpow_om(k):
    r = ONE
    for _ in range(k % 8): r = zmul(r, OM)
    return r
FOUR = (0, 0, 0, 4)

def reconstruct(x, y, k):
    omk = zpow_om(k)
    return ((x, zneg(zmul(omk, zconj_o(y))), y, zmul(omk, zconj_o(x))), 2)

# ── BFS over Clifford gens to get minimal words ───────────────────────────────
CLIFF_GENS = ['H', 'S', 'X', 'Y', 'Z', 'W']   # W = ω·I (the `omega` gate)
GATE_NAME = {'H': 'H', 'S': 'S', 'X': 'X', 'Y': 'Y', 'Z': 'Z', 'W': 'omega'}

# interp gs = G1 * G2 * ... (matmul left-to-right, as in the Lean interp_cons)
def interp_word(gates):
    M = ID
    for g in gates:
        M = matmul(M, GENS[g])
    return normalize(M)

start = normalize(ID)
word = {start: []}
q = deque([start])
while q:
    M = q.popleft()
    if len(word[M]) >= 6:
        continue
    for g in CLIFF_GENS:
        N = normalize(matmul(M, GENS[g]))   # append g on the right: interp (word ++ [g])
        if N not in word:
            word[N] = word[M] + [g]
            q.append(N)

cliffords = {M for M in word if kso3(M) == 0}
print(f"Clifford matrices reachable ≤6 (kSO3=0)   : {len(cliffords)}")
print(f"max word length among them                : {max(len(word[M]) for M in cliffords)}")

# ── the kSO3=0 subset of the bridge box ───────────────────────────────────────
R = range(-2, 3)
zoms = [(a, b, c, d) for a in R for b in R for c in R for d in R]
by_ns = defaultdict(list)
for z in zoms:
    by_ns[norm_sq(z)].append(z)

box0 = []          # (x,y,k) with kSO3(reconstruct)=0
mus = []
uncovered = []
for nsx, xs in by_ns.items():
    nsy = tuple(FOUR[i] - nsx[i] for i in range(4))
    ys = by_ns.get(nsy)
    if not ys or not divides_sqrt2(nsx):
        continue
    for x in xs:
        for y in ys:
            for k in range(8):
                M = reconstruct(x, y, k)
                if kso3(M) != 0:
                    continue
                box0.append((x, y, k))
                mus.append(sde_z00sq(M))
                Mn = normalize(M)
                if Mn not in word or len(word[Mn]) > 6:
                    uncovered.append((x, y, k))

print(f"\nkSO3=0 box tuples (x,y,k)                  : {len(box0)}")
print(f"distinct Clifford matrices covered         : {len({normalize(reconstruct(*t)) for t in box0})}")
print(f"μ = sde(|z00|²) range on kSO3=0            : min={min(mus)} max={max(mus)}")
print(f"box tuples NOT covered by a ≤6 word        : {len(uncovered)}")

# ── universal μ vs kSO3 over the full μ≤3 orbit (to bound μ from kSO3 in Lean) ─
ob_start = normalize(ID)
dist = {ob_start: 0}; oq = deque([ob_start]); orbit = []
while oq:
    M = oq.popleft(); orbit.append(M)
    for G in GENS.values():
        N = normalize(matmul(G, M))
        if N not in dist and sde_z00sq(N) <= 3:
            dist[N] = dist[M] + 1; oq.append(N)
worst = max(sde_z00sq(M) - 2 * kso3(M) for M in orbit)
print(f"\nfull μ≤3 orbit size                        : {len(orbit)}")
print(f"max (μ − 2·kSO3) over orbit                : {worst}   (μ ≤ 2·kSO3 + {max(0,worst)} ?)")
print(f"max μ where kSO3=0                          : {max(sde_z00sq(M) for M in orbit if kso3(M)==0)}")

print("\nVERDICT:", "SAFE — all kSO3=0 box tuples have ≤6 Clifford words"
      if not uncovered else f"UNSAFE — {len(uncovered)} uncovered")
