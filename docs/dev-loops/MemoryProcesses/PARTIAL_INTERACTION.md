# Reset-sensitive finite-memory increment

Status: accepted locally after authoritative build, substrate checks and independent integrated review. Public feature branch remains local; no public push or main merge. Root owns integration and the machine-local notebook. Independent review precedes local acceptance; no remote push or PR publication is authorized for this public increment.

## Scientific contract

For t,p in [0,1], use the joint channel C_t(X)=(1-t)X+t SWAP(X). This is a probabilistic identity/SWAP channel, not a coherent partial-SWAP unitary. Prepare S=b, E=0, apply C_t, apply resetMixture p to S, apply C_t again, then measure binary system outcome. The control inserts perfect reset of E after the same imperfect S reset. Both histories use the same maps. The two channel applications compose fresh probabilistic mixtures; reusing a correlated hidden SWAP coin would define a different model.

Prove normalized Kraus realization and density preservation on arbitrary joint inputs. Derive post-reset reduced system states: history zero is zero; history one has outcome-one weight r=p(1-t). Prove exact trace distance r from the common zero reference, using the accepted diagonal fixture. Derive retained outcome-one separation A=t^2+p(1-t)^2, control separation B=p(1-t)^2, and A-B=t^2. Thus control need not erase all signal: residual system information can survive imperfect reset.

Apply the existing common-system-channel binary criterion with epsilon_0=0, epsilon_1=r. Prove A-r=t(t-p(1-t)), and a nonempty strict separation regime, with explicit interior examples and boundary cases. For example t=1/2,p=1/4 gives r=1/8,A=5/16,B=1/16 and excess 3/16. At p=1,t=1/2 the criterion is exactly inconclusive. A nonpositive excess is not a proof of absent memory. These basis dynamics admit a classical realization and imply no quantum advantage or unusual time.

## Deliverables and ownership

P1: Lean joint channel, exact trajectories, physicality, reduced-state distance and common-channel exclusion. One admitted slot worker owns the new QuantumNetwork/FiniteMemoryPartialInteraction.lean module; root owns aggregate imports and generated evidence.
P2: canonical formulas.py CPU reference and tests in tests/test_memory_partial_interaction.py, on a separate ordinary worktree. Compute the joint matrix trajectory, not only scalar closed forms; report reset leakage, retained/control separation and criterion margin. Test correlated-state channel behavior, endpoints, interior examples and invalid input. No clipping result is a formal numerical certificate.
P3: independent cross-layer review, authoritative build and axiom audit, focused tests and substrate gate, source-of-truth sync and local-only integration. Existing publication-corpus failures remain outside scope. No sampling inference, hardware, CUDA, general process tensor, new manuscript or full coarse-graining branch in this increment.

## Acceptance

No new sorry, native_decide or project-local axioms. Explicit exact statements must connect to the actual channel trajectory, not merely prove polynomial identities. Review verifies common-continuation premises and environment-reset control order. Source/semantic review and kernel validation are separate evidence. Keep CPU execution light and independent of the proof critical path. Scientific defects reopen their package.

## Implemented evidence

The new module is `SKEFTHawking.QuantumNetwork.FiniteMemoryPartialInteraction`, with 32 authored theorems (21 public and 11 private helpers). Its declarations remain under `SKEFTHawking.QuantumNetwork.FiniteMemoryProcess`:

- `partialInteractionKraus_eq`, `partialInteractionKraus_normalized`: exact joint channel realization and normalization.
- `partialPostReset_density`, `partialRetainedRun_density`, `partialControlRun_density`: physicality on arbitrary joint density inputs.
- `partialPostReset_basis`, `partialPostReset_marginal`, `partialPostReset_traceDist`: actual trajectory and exact residual-system budget.
- `partialRetained_probability`, `partialControl_probability`, `partial_control_gap`: measured probabilities and control contrast.
- `partial_common_channel_bound`, `partial_no_common_system_model`: the existing binary criterion applied to actual reset marginals and exclusion in the strict regime.
- `partialRetained_margin`, `partial_interior_example`, `partial_interior_exclusion`, `partial_zero_interaction`, `partial_full_interaction`, `partial_inconclusive_boundary`: quantitative and non-vacuity checks.

The canonical CPU functions are `memory_partial_interaction` and `memory_partial_interaction_reference`. They evaluate joint matrices and reduced states rather than returning only polynomial formulas. They return a numerical criterion margin, not an automatically certified verdict. The control can have nonzero separation, and a nonpositive margin does not establish absent memory.

Proof candidate `4a328f86` passed live diagnostics and six principal axiom-closure checks. CPU candidate `8f6a203e` passed 78 combined memory tests (43 new). Independent CPU review reproduced 78 tests, checked 40 complex correlated mixed states and 100 further parameter pairs, and found no substantive defects. The integrated root test run passed 78 tests in 0.18 seconds. Aggregate build at `ca9414ba` passed through the slot controller. Canonical extraction adds 31 records with no changed existing declarations: 21 public authored theorems, five definitions and five generated records. All new extracted closures use only standard core axioms, with no project axioms or dependency-extraction timeouts. The private helper proofs are included in the compiled module and consumed theorem closures. Counts and atlas were refreshed by the existing producers. The substrate gate passed in 528.8 seconds (70/89 overall, 19 pre-existing paper-corpus failures outside scope). Independent integrated review at `2c7887de` found no substantive findings; these records do not certify floating-point arithmetic, hardware behavior or publication readiness.

Completion evidence: [independent review receipt](../../audits/2026-09-09-memory-partial-interaction.md). P1–P3 are complete at the local integration boundary. Sampling-based inference and wider process/coarse-graining extensions remain subsequent increments, not implied deliverables here.

The separately accepted [fixed-sample inference increment](SAMPLING.md) now supplies the sampling bridge. Its evidence is owned by that plan and does not alter this increment's original acceptance scope.
