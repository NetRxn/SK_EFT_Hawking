# SK-EFT Hawking: Educational Companion Guide

SK-EFT Hawking began with a question about sound in fluids. How does
dissipation, the tendency for motion to lose energy into its surroundings,
change the radiation expected near an analog horizon? That question connects
laboratory models to a broader study of effective theories, condensed matter,
gravity, and quantum information.

## How can a fluid have a horizon?

Imagine sound trying to travel upstream. If the flow outruns sound, a sound
wave aimed upstream is still carried downstream. A transition between regions
with slower and faster flow can therefore act as a horizon for sound. It
provides a laboratory model for studying how waves behave near horizons.

The project studies how effects such as dissipation and dispersion change the
predicted signal. Dispersion means that waves of different wavelengths travel
at different speeds. Bose–Einstein condensates and fluids of light–matter
hybrids called polaritons provide different models for studying these effects.
A prediction for a particular device depends on its operating conditions and
on how its detector converts the signal into a measured quantity. See the
[analog-horizon drafts](../../papers/E1/) and the
[operator and transport study](../roadmaps/Phase6v/Wave_6v.10_Roadmap.md#scope-of-the-operator-and-transport-results).

## What does a checked result tell us?

A result is easiest to understand by asking what went into it and what
comes out:

- **Formal proof.** Lean checks that the conclusion follows from the stated
  hypotheses. For example, the [receiver kernel](../../lean/SKEFTHawking/DKMBootstrap/ReceiverKernel.lean)
  used in an idealized detector model has a proved normalization and bounds on
  its derivatives. Applying the model to an instrument requires evidence
  about what the instrument measures.
- **Numerical result.** Code computes a quantity for stated inputs and
  approximations. [Computational notebooks](../../notebooks/) show how
  calculations are set up and tested, and the
  [provenance guide](../KNOWLEDGE_GRAPH.md) explains how sources, parameters,
  code, and draft claims are linked.
- **Limit of a model.** A proof can show that a given set of assumptions rules
  out a proposed behavior. One [vacuum model](../../lean/SKEFTHawking/GibbsDuhemTheorem.lean)
  fixes the ratio of pressure to nonzero energy density at −1. Within that
  model the ratio cannot evolve over time, which sharply limits the range
  of behaviors it can explain.

The same approach extends to mathematical problems in quantum computation.
For example, [the gate-synthesis draft](../../papers/D8/) studies how to
approximate a continuous family of quantum operations using finite sequences
of gates. Tests of proposed physical mechanisms and proofs about quantum
algorithms have different evidence requirements. The
[project scope](../ARCHITECTURE_SCOPE.md#the-three-layers) describes how the
research areas fit together.

## Where to go next

- **Read a working paper.** Use the [bundle summary](../PAPER_STRATEGY.md#6-summary-table)
  to find a topic and the [readiness matrix](../../README.md#publication-readiness)
  to see its review status.
- **Follow the evidence.** The [provenance dashboard](../architecture/DASHBOARD.md#quick-start)
  helps trace a paper claim to supporting material. Use the
  [generated project counts](../counts.json) for library and code totals.
- **Try a proof or contribute.** The [contributor guide](../../CONTRIBUTING.md)
  has a short Lean example and paths into the library and numerical work.
