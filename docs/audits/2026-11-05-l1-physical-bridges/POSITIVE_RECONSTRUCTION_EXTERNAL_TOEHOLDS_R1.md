# External positive-reconstruction toeholds — r1

## Scope and authority

Task: `l1-positive-external-toeholds-r1`; parent Executor01a1ac65 / publication ROOT01a13f67. Read-only external source research only; this is not a roadmap change or physics acceptance. I read the assigned packet `/private/tmp/l1-positive-reconstruction-toehold-scout-scope-r1.md`, including its WEB scope and current-known-source/frontier inventory. Original obligations summarized there: finite 16-site periodic/128-odd, 64-independent compact Spin(4) anchor, independent Grassmann bars/psis, quarter-coframe and full determinant/EHC closed operator, exp(+S), two temporal interfaces and prescribed source/overlap/trajectory data. Physical positive domain/product/adjoint/polarization, dynamics/kernel sewing, and source/normalization correspondence remain open. I did not submit private material to public services or consult other scouts.

## Ranked primary-source candidates (body read)

### 1. M. Lüscher, “Construction of a Selfadjoint, Strictly Positive Transfer Matrix for Euclidean Lattice Gauge Theories” (DESY 76/54, 1976; journal CMP 54 (1977) 283)

Primary version: [DESY author preprint PDF](https://bib-pubdb1.desy.de/record/396349/files/7611148.pdf?version=1). I read the paper body, notably its model/setup at pp. 1–2, operator/Fock construction at pp. 6–9, strict-positivity proof at pp. 10–11, and reconstruction at pp. 12–14 (PDF text lines around 47–159, 219–429, 462–604, 662–731). Its lattice has SU(N) links and Grassmann Dirac fields with Wilson gauge/quark action. It constructs the time-zero Hilbert space as fermion Fock space tensor gauge (L^2), defines an explicit transfer operator, proves strict positivity under |K|<1/6 (the text notes the condition is inessential near the continuum value K≈1/8), and recovers Euclidean Schwinger functions with periodic gauge and anticyclic fermion time boundary conditions. Gauge-invariant states are characterized by invariance under the residual gauge transformations in its construction.

**Potentially helps:** concrete template for building a positive physical quotient/completion, transfer operator, Gauss-invariant subspace, and exact Grassmann-kernel/trace sewing with temporal boundary conditions. This is the strongest constructive analogy found for the requested physical state/kernel layer.

**Mismatch:** it begins with a canonical CAR Fock space and Wilson-type action/standard time-slice factorization. It does not derive CAR or a positive adjoint from the target’s independent ψ,̄ψ Berezin functional, quarter-coframe determinant, composite gravity kernel, unusual exp(+S), or its literal source conventions. Its anticyclic trace prescription is not proof of the target’s two-interface sewing. Transfer positivity must be reproved for the actual kernel; importing the CAR input would assume the disputed bridge.

### 2. Brydges–Fröhlich–Seiler, “On the Construction of Quantized Gauge Fields, I: General Results” (IHES/P/78/237, June 1978)

Primary version: [IHES author archive PDF](https://repo-archives.ihes.fr/FONDS_IHES/I_Prepublications/FROHLICH/1978-1980/P_78_237/P_78_237_web.pdf). Body read: abstract/introduction pp. 1–3 (lines 31–56), hypotheses on potentials and gauge actions pp. 23–24 (527–553), and Theorem 5.3/Corollary 5.4 with boundary hypotheses pp. 71–74 (2239–2315). The paper treats lattice gauge theories with minimally coupled scalar and Dirac matter. Its general potential conditions include translation/reflection covariance, summability, local gauge invariance, and a **reflection-negative** condition. Theorem 5.3 obtains OS positivity for the stipulated cutoff and reflection-positive boundary functional; Corollary 5.4 restricts it to gauge-invariant observables in any gauge, and the authors state existence of gauge/translation-invariant RP thermodynamic limits for the described setup. The paper explicitly warns the cutoff condition (5.21) is essential and the theorem would fail if it were violated; standard periodic/half-Dirichlet boundary conditions are given as RP examples.

**Potentially helps:** a genuine boundary-weight route: it identifies how matter/gauge interactions, a reflection-compatible UV cutoff, and boundary state weights can coexist with gauge-invariant OS positivity and controlled volume limits. This is a specific candidate for testing boundary-weighted positive kernels.

**Mismatch:** reflection negativity and RP boundary conditions are hypotheses, not consequences of a complex asymmetric composite action. Its bosonic a-priori measures plus Grassmann field algebra do not show that the signed Berezin integral is a positive bosonic measure. Regulator/coupling/field content differ; no target source, normalization, or gravitational composite map is established.

### 3. Lang–Liegener–Thiemann, “Hamiltonian Renormalisation I: Derivation from Osterwalder-Schrader Reconstruction” (arXiv:1711.05685v2; CQG 35 (2018) 245011)

Primary version: [arXiv v2 record and linked full text](https://arxiv.org/abs/1711.05685). I read the v2 abstract and publication/version metadata (body entry at lines 8–27). The paper’s stated construction inverts OS reconstruction: from reflection-positive measures it relates OS data (Hilbert space, Hamiltonian, ground state) to a non-perturbative operator-level renormalization flow, motivated for regulated complex gauge/gravity settings.

**Potentially helps:** a useful methodological route if a target-specific RP family can first be constructed: formulate regulator changes as maps on Hilbert/Hamiltonian data and test whether reconstruction commutes with the controlled limit.

**Mismatch:** it does not establish RP or positive reconstruction for this target. Its conditional “if resulting measure obeys OS axioms” is exactly the missing input; its Hamiltonian-renormalization setup does not supply the target’s Grassmann adjoint/CAR, finite Spin(4) action, boundary sew, or source normalization. This is an operator-flow framework, not evidence that the target lies in its domain.

### 4. M. Lüscher and P. Weisz, “Definition and general properties of the transfer matrix in continuum limit improved lattice gauge theories” (Nucl. Phys. B240 (1984) 349–361)

Primary version: [publisher article record](https://www.sciencedirect.com/science/article/abs/pii/0550321384902700). I read the publisher abstract/body summary. It proves a transfer matrix can still be defined after dimension-six improvements, but explicitly reports that physical positivity is generally lost: complex eigenvalues and negative spectral weights may occur.

**Potentially helps:** a counterexample boundary on the proposed “controlled regulator limit” route: a transfer matrix or formal continuation alone does not guarantee a positive physical Hilbert space. Any regulator family needs a positivity-preserving criterion or a proved limit theorem.

**Mismatch:** it studies particular improved lattice gauge actions, not this composite model, and is negative/diagnostic rather than a construction of the needed positive representation.

## Best deeper-read and falsifiable applicability test

**Best candidate: Lüscher 1977.** Read the complete canonical factorization and gauge-invariance argument (especially propositions around the explicit (T), strict positivity, and reconstruction), then try a finite-anchor analogue as a paper-only test: define from the *actual target* positive-time observable algebra and its stated two-interface kernel a sesquilinear form (Q(F,G)=langle Theta F,Gangle); derive an explicit factorization (Q(F,F)=|B F|^2) (or exhibit a negative-norm gauge-invariant (F)); prove the shift descends to a self-adjoint positive transfer operator and that the exact Grassmann/Berezin sewing reproduces the prescribed (Z) and source derivatives without assuming CAR. **Falsifier:** any gauge-invariant positive-time polynomial with (Q(F,F)<0), or any nonzero mismatch between the sewn transfer matrix’s generating functional and the target literal source/normalization/interface prescription. Passing would only establish the finite-anchor bridge under its explicitly matched hypotheses, not continuum/publication acceptance.

## Search and verification record

- First/final continuity packet check: first check returned `fresh: true`, `changed: []`; final check must be run by the parent/worker after report freeze per assignment.
- Browser tool: primary-source searches for OS reconstruction with gauge/fermions, positive transfer matrices, complex actions/contours, and Hamiltonian/constraint constructions; opened the complete Lüscher 1977 PDF, the relevant Brydges–Fröhlich–Seiler PDF theorem/hypothesis sections, and the arXiv v2 record for Lang–Liegener–Thiemann. Search snippets were used only to locate candidate identifiers; claims above are based on the opened primary-source body/abstract, not snippet-only.
- Lüscher 1977 full text was available through browser body read; no downloading performed. The 1984 publisher record was abstract-level only and is used solely as a cautionary counterexample.
- Uncertainty: I did not inspect Lit-Search or obtain/paywall-download copies; Menotti–Pelissetto/Osterwalder–Seiler were already represented in packet inventory, so not repeated as novel candidates. The older primary scan has OCR/math extraction imperfections; cross-check theorem wording against page images before relying on a formula. No theory-specific applicability has been accepted.
- No repository, notebook, code, Lean, build, slot, controller, or other scout files were edited. No physical premise adopted.
