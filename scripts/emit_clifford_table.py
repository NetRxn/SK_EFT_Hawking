"""Emit the 192-entry Lean Clifford lookup table for cliffordBase.

For each (x,y,k) in the kSO3=0 subset of the bridge box, BFS-find a minimal
Clifford word (gens {H,S,X,Y,Z,omega}) w with interp w = reconstruct(x,y,k),
and emit a Lean entry `(⟨a,b,c,d⟩, ⟨a,b,c,d⟩, k, [.G,...])`.

The native_decide `cliffordBase_box_core` re-verifies every word, so this emitter
is untrusted scaffolding.
"""
from __future__ import annotations
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kmm_zomega_reference_oracle import mul as zmul, conj as zconj_o, norm_sq, divides_sqrt2
from kmm_n3_bfs import GENS, ID, matmul, normalize, ONE, OM
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

CLIFF = ['H', 'S', 'X', 'Y', 'Z', 'W']
LEAN_GATE = {'H': '.H', 'S': '.S', 'X': '.X', 'Y': '.Y', 'Z': '.Z', 'W': '.omega'}

# BFS from ID: word[M] = minimal gate list with interp = M (matmul left-to-right)
start = normalize(ID); word = {start: []}; q = deque([start])
while q:
    M = q.popleft()
    if len(word[M]) >= 6: continue
    for g in CLIFF:
        N = normalize(matmul(M, GENS[g]))
        if N not in word:
            word[N] = word[M] + [g]; q.append(N)

# enumerate kSO3=0 box
R = range(-2, 3)
by_ns = defaultdict(list)
for a in R:
    for b in R:
        for c in R:
            for d in R:
                by_ns[norm_sq((a, b, c, d))].append((a, b, c, d))

entries = []
for nsx, xs in by_ns.items():
    nsy = tuple(FOUR[i] - nsx[i] for i in range(4))
    ys = by_ns.get(nsy)
    if not ys or not divides_sqrt2(nsx): continue
    for x in xs:
        for y in ys:
            for k in range(8):
                M = reconstruct(x, y, k)
                if kso3(M) != 0: continue
                Mn = normalize(M)
                assert Mn in word and len(word[Mn]) <= 6, (x, y, k)
                entries.append((x, y, k, word[Mn]))

def zlean(z): return f"⟨{z[0]}, {z[1]}, {z[2]}, {z[3]}⟩"
lines = []
for (x, y, k, w) in entries:
    gates = "[" + ", ".join(LEAN_GATE[g] for g in w) + "]"
    lines.append(f"  ({zlean(x)}, {zlean(y)}, {k}, {gates})")
body = ",\n".join(lines)
print(f"-- {len(entries)} entries; max word length {max(len(w) for *_, w in entries)}")
print("def cliffordTable : List (ZOmega × ZOmega × ℕ × List CliffordTGate) := [")
print(body)
print("]")
