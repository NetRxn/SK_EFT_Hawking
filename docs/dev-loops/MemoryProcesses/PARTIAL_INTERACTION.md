# Reset-sensitive finite-memory increment

Status: authorized supervised implementation; local-only public branch. Root owns integration and the machine-local notebook. Independent review precedes local acceptance; no remote push or PR publication is authorized for this public increment.

## Scientific contract

For t,p in [0,1], use the joint channel C_t(X)=(1-t)X+t SWAP(X). This is a probabilistic identity/SWAP channel, not a coherent partial-SWAP unitary. Prepare S=b, E=0, apply C_t, apply resetMixture p to S, apply C_t again, then measure binary system outcome. The control inserts perfect reset of E after the same imperfect S reset. Both histories use the same maps.

Prove normalized Kraus realization and density preservation on arbitrary joint inputs. Derive post-reset reduced system states: history zero is zero; history one has outcome-one weight r=p(1-t). Prove exact trace distance r from the common zero reference, using the accepted diagonal fixture. Derive retained outcome-one separation A=t^2+p(1-t)^2, control separation B=p(1-t)^2, and A-B=t^2. Thus control need not erase all signal: residual system information can survive imperfect reset.

Apply the existing common-system-channel binary criterion with epsilon_0=0, epsilon_1=r. Prove A-r=t(t-p(1-t)), and a nonempty strict separation regime, with explicit interior examples and boundary cases. For example t=1/2,p=1/4 gives r=1/8,A=5/16,B=1/16 and excess 3/16. At p=1,t=1/2 the criterion is exactly inconclusive. A nonpositive excess is not a proof of absent memory. These basis dynamics admit a classical realization and imply no quantum advantage or unusual time.

## Deliverables and ownership

P1: Lean joint channel, exact trajectories, physicality, reduced-state distance and common-channel exclusion. One admitted slot worker owns the new QuantumNetwork/FiniteMemoryPartialInteraction.lean module; root owns aggregate imports and generated evidence.
P2: canonical formulas.py CPU reference and tests in tests/test_memory_partial_interaction.py, on a separate ordinary worktree. Compute the joint matrix trajectory, not only scalar closed forms; report reset leakage, retained/control separation and criterion margin. Test correlated-state channel behavior, endpoints, interior examples and invalid input. No clipping result is a formal numerical certificate.
P3: independent cross-layer review, authoritative build and axiom audit, focused tests and substrate gate, source-of-truth sync and local-only integration. Existing publication-corpus failures remain outside scope. No sampling inference, hardware, CUDA, general process tensor, new manuscript or full coarse-graining branch in this increment.

## Acceptance

No new sorry, native_decide or project-local axioms. Explicit exact statements must connect to the actual channel trajectory, not merely prove polynomial identities. Review verifies common-continuation premises and environment-reset control order. Source/semantic review and kernel validation are separate evidence. Keep CPU execution light and independent of the proof critical path. Scientific defects reopen their package.
