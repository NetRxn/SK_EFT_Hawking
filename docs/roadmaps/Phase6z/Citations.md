# Phase 6z — Citation sheet (verified primary sources)

*Progressive-disclosure detail doc for `Phase6z_Roadmap.md`. Source: DR2 §Recommendations(8) + the
in-session BMPRV correction (`ec12f58`). Use these exact titles/IDs in module docstrings + any paper
output. Add each to `src/core/citations.py::CITATION_REGISTRY` if cited in a paper (per Tier-2 checks).*

## Universality of {Toffoli/CCZ, Hadamard} — the 6z headline's mathematical basis
- **Shi 2002** — Y. Shi, *"Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation,"* arXiv:**quant-ph/0205115** (2002). *(The {Toffoli, H} universality lives in the proof
  of Shi's Thm 3.2; Shi's Lemma 3.4 is attributed to Kitaev and is density-via-stabilizer.)*
- **Aharonov 2003** — D. Aharonov, *"A Simple Proof that Toffoli and Hadamard are Quantum Universal,"*
  arXiv:**quant-ph/0301040** (2003). *(Reduces {Toffoli, H} to Kitaev's set; defers SO(8)-density to
  Shi — does NOT itself exhibit an explicit irrational-angle seed word.)*
- **Brylinski–Brylinski 2001** — J.-L. Brylinski, R. Brylinski, *"Universal quantum gates,"*
  arXiv:**quant-ph/0108062** (2001); reprinted in *Mathematics of Quantum Computation*, Chapman &
  Hall/CRC 2002. *(Entangling-gate criterion: any non-primitive 2-qubit gate + all 1-qubit gates is
  universal; CCZ is non-primitive.)*

## Parallel-but-different basis (cite ONLY for Clifford+T, NOT for CCZ)
- **Boykin–Mor–Pulver–Roychowdhury–Vatan 1999** — *"On universal and fault-tolerant quantum computing:
  a novel basis and a new constructive proof of universality for Shor's basis,"* FOCS 1999, pp. 486–494,
  DOI **10.1109/SFFCS.1999.814621**; arXiv:**quant-ph/9906054**. **This is the Clifford+T / Shor's-basis
  paper** (`{H, σ_z^{1/4}=T, CNOT}`). Cite for Phase 6y's Clifford+T-at-SU(8) density; **do NOT cite for
  literal Clifford+CCZ universality** (that's Shi/Aharonov). *(In-session correction `ec12f58` fixed an
  earlier mis-attribution of CCZ universality to BMPRV.)*

## Irrationality
- **Niven 1956** — I. Niven, *Irrational Numbers*, Carus Mathematical Monographs no. 11, MAA. The
  cos-rationality classification is **Corollary 3.12** (NOT "Theorem 3.9" — a common mis-citation; do
  not propagate). *Used only as a cross-check;* **not** in the Lean proof (algebraic-integer route is
  cleaner, and Niven is absent from Mathlib).
- **Kronecker 1857** — algebraic integer with all conjugates on the unit circle ⇒ root of unity. The
  obstruction backing `not_rootOfUnity_of_minpoly_not_int`.

## DO NOT CITE for universality / Clifford-orbit transitivity
- **Aaronson–Gottesman 2004** — *"Improved Simulation of Stabilizer Circuits,"* Phys. Rev. A 70, 052328 /
  arXiv:quant-ph/0406196. This is the **CHP stabilizer-simulability** paper (§IV CHP simulator, §II
  stabilizer-Pauli preliminaries). It proves **no** universality theorem and **no** "Clifford conjugation
  spans `𝔰𝔲(8)`" transitivity theorem. The orbit-spanning claim must be settled by computer algebra
  (`PreLean_CAS_Gates.md` Gate 2), not by citing this. *(For Clifford-on-Pauli action / adjoint-action
  irreducibility, the correct lineage is the Gottesman thesis + Clifford-group representation theory,
  e.g. Nebe–Rains–Sloane.)*
