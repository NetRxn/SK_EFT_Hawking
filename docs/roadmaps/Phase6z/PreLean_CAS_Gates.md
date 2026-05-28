# Phase 6z — Wave 0: Pre-Lean computer-algebra gates (HARD GATE)

*Progressive-disclosure detail doc for `Phase6z_Roadmap.md`. **Both gates MUST pass before any Lean
LoC is committed.** The second gate sets the entire phase budget. Source: DR2 §1.4 + §4 + Recommendations.*

Rationale (per CLAUDE.md "correctness over expediency" + DR2): the seed spectrum and the
conjugation-orbit dimension are **assumptions** in the Lean plan. A symbolic check is cheap (≈1 day
combined) and either confirms the plan or redirects it before sinking ~2,000 LoC. DR2 explicitly flags
both as unverified.

---

## Gate 1 — Confirm the seed spectrum (`verify_seed.py`)

**Commit output to `Lit-Search/Phase-6y/verify_seed.py` + its printed result.** Confirms the operative
seed `g₀ = (H⊗H⊗H · CCX)²` has char poly `(x−1)⁶·(x²−(3/2)x+1)`, eigenvalues `(3±i√7)/4`, and `det=1`
(so `g₀ ∈ SO(8) ⊂ SU(8)`, no phase correction).

```python
import sympy as sp
H1  = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
HHH = sp.kronecker_product(sp.kronecker_product(H1, H1), H1)
CCX = sp.eye(8); CCX.row_swap(6, 7)            # Toffoli: swap |110⟩,|111⟩  (index 6,7)
g0  = sp.simplify(HHH * CCX * HHH * CCX)
print(sp.factor(g0.charpoly().as_expr()))      # expect (x-1)^6 * (x^2 - 3*x/2 + 1)
print(sp.simplify(g0.det()))                   # expect 1
lam = sp.Rational(3, 4) + sp.I * sp.sqrt(7) / 4
print(sp.simplify(2*lam**2 - 3*lam + 2))       # expect 0  (minpoly 2x^2-3x+2, non-monic over ℤ)
print(sp.simplify(sp.Abs(lam) - 1))            # expect 0  (|λ|=1)
```

**Decision:**
- Matches → proceed to Gate 2 with `g₀`.
- **Differs → HALT.** Try backup words before adjusting budget: `(H₃·CCX)⁴` (squaring preserves the
  irrational eigenangle); mixed-Hadamard `(H₁·CCX·H₁·CCX)·(H₂·CCX·H₂·CCX)`; or DR1's `CCZ·(H⊗H⊗H)`
  (`tr=1/√2`, already Lean-proven in Phase A.1 `litSeed_trace` — a valid fallback, weaker eigenblock).
  The irrationality skeleton (`Phase6z/Mathlib_Decls.md` (b)) is robust to ANY short word with a
  non-monic-over-ℤ degree-2 minimal polynomial on the unit circle.

*(DR1/DR2 note both flag that a verbatim Shi-2002 extraction of this exact word+spectrum was not
obtained within search budget — hence this gate is the authoritative settle-the-question step.)*

---

## Gate 2 — Clifford-orbit dimension (sets the phase budget) — THE load-bearing check

**The single most consequential unverified claim:** does `Ad_{C₃}(X)` — the Clifford-group (`C₃ =
⟨H,S,CNOT⟩`, order 92,897,280) conjugation orbit of `X = i·log g₀` — **span `𝔰𝔲(8)` (63-dim)** by
itself, or is BCH/Trotter bracket closure also needed? DR2 flags the "Clifford-orbit spans" claim is
**mis-attributed to Aaronson–Gottesman 2004** (that paper is stabilizer *simulability*; it proves no
such transitivity theorem) — so **settle it by computation, not citation.**

Compute (Sage/Mathematica) `dim span{ Ad_U(X) : U ∈ ⟨H,S,CNOT⟩ generators, up to conjugation depth ~4 }`
where `X = i·log g₀` (the traceless skew-Hermitian generator on `g₀`'s 2-D eigenblock).

**Decision gate → sets Wave-4 scope:**
| Spanned dim | Case | Wave 4 raw LoC | Wave 3 (SU(d) Trotter) |
|---|---|---|---|
| `= 63` | **BEST** | ~400 | not needed |
| `∈ [30, 62]` | **TYPICAL** | ~900 | needed (1 BCH layer) |
| `< 30` | **WORST** | ~1800 | needed (multi-layer) — consider splitting as sub-spike 6z.4.x |

Commit the spanned-dimension result + the generator/depth used to `Lit-Search/Phase-6z/` (create the
directory). This number is referenced by the Phase 6z roadmap's Wave table.

---

## Outputs of Wave 0 (gate to Lean work)
1. `Lit-Search/Phase-6y/verify_seed.py` + confirmed char-poly/det output (Gate 1).
2. `Lit-Search/Phase-6z/orbit_dimension.{py,md}` + the spanned-dim result + chosen case (Gate 2).
3. Roadmap Wave-4 LoC + Wave-3 inclusion updated to the confirmed case.
**Only then** begin Wave 1 (`not_rootOfUnity_of_minpoly_not_int` is the recommended first Lean artifact —
highest leverage, independently reusable).
