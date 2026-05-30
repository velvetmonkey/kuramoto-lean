# kuramoto-lean: Lean 4 Formalization of Kuramoto Synchronization

[![Lean 4](https://img.shields.io/badge/Lean-4.31.0--rc1-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-971b902-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-no%20sorry-brightgreen)](Kuramoto)
[![DOI](https://img.shields.io/badge/DOI-pending-lightgrey)](#cite-this-library)
[![Companion project](https://img.shields.io/badge/companion-flywheel--universe-d4af37)](https://github.com/velvetmonkey/flywheel-universe)
[![Live demo](https://img.shields.io/badge/demo-live-d4af37)](https://velvetmonkey.github.io/flywheel-universe/)

This library formally proves finite-N results about the Kuramoto model of coupled oscillators in Lean 4 / Mathlib. It takes a geometric approach on T^N, distinct from the Ott-Antonsen manifold approach in taejun-song/kuramoto-lean. The checked development contains no sorry, no admit, and no new axioms.

This repo is the formal proof spine for the companion project [flywheel-universe](https://github.com/velvetmonkey/flywheel-universe), which studies budgeted Hebbian Kuramoto dynamics for Max-Cut under coupling-resource constraints. The companion project includes a [live browser demo](https://velvetmonkey.github.io/flywheel-universe/) of Hebbian Kuramoto synchronisation across several graph topologies.

## Paper

**kuramoto-lean: A Sorry-Free Lean 4 Library for Finite-N Kuramoto Synchronisation Dynamics**  
Ben Cassie (2026). Zenodo.  
https://doi.org/10.5281/zenodo.20468619

## Background

The Kuramoto model describes N coupled oscillators whose phases evolve under mutual interaction. Originally proposed to model biological synchrony, it appears in power grid stability, distributed clocks, neural dynamics, and AI training. The model's key property is that coupling drives phases toward agreement; when coupling strength exceeds a critical threshold, global synchronisation emerges. This library formalises the mathematical foundations of that synchronisation, making the claims machine-checkable rather than proof-sketch-dependent.

## Why formal verification

A Lean 4 proof with zero sorry, zero admit, and zero new axioms is a machine-checked guarantee, not a human-readable argument. Every lemma name is verified to exist in the Mathlib version pinned in `lean-toolchain` before use. This means the theorems here cannot silently depend on incorrect API assumptions or plausible-but-wrong algebraic steps. The discipline is enforced by a `#check`-before-cite rule throughout development.

## Proof discipline

All proofs were developed using an explicit API verification step: every Mathlib lemma name was `#check`ed against the pinned Mathlib commit before appearing in a proof. Names that failed `#check` were reported and not used. This prevents the most common failure mode in AI-assisted Lean development: hallucinated API names that compile locally against a wrong version.

## Results

- `Kuramoto/OrderParameter.lean`: The Kuramoto order parameter satisfies `‖kuramotoR N θ‖ ≤ 1` for any positive number of oscillators and any phase configuration.

  ```lean
  theorem kuramotoR_norm_le_one (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ) :
      ‖kuramotoR N θ‖ ≤ 1
  ```

- `Kuramoto/GradientFlow.lean`: The uniform Kuramoto vector field is the negative gradient of the Kuramoto potential `V`; equivalently, each component satisfies `kuramotoF K N i θ = -(∂V/∂θ i)`.

  ```lean
  theorem kuramoto_gradient_identity
      (K : ℝ) (N : ℕ) (hN : 0 < N) (hK : 0 < K)
      (θ : Fin N → ℝ) (i : Fin N) :
      kuramotoF K N i θ =
        -(deriv (fun x => kuramotoV K N (Function.update θ i x)) (θ i))
  ```

- `Kuramoto/Contraction.lean`: Three contraction results: the `N = 2` relative velocity identity, `N = 2` pairwise contraction when the phase gap lies in `(0, π)`, and a general-N direct-coupling contraction theorem showing that a positive symmetric pair coupling pushes a pair together when the gap lies in `(0, π)`.

  ```lean
  lemma kuramoto_relative_velocity
      (K : ℝ) (θ : Fin 2 → ℝ) :
      kuramotoF K 2 0 θ - kuramotoF K 2 1 θ =
        -K * Real.sin (θ 0 - θ 1)

  theorem kuramoto_pairwise_contraction
      (K : ℝ) (hK : 0 < K) (θ : Fin 2 → ℝ)
      (hgap : 0 < θ 0 - θ 1) (hpi : θ 0 - θ 1 < Real.pi) :
      kuramotoF K 2 0 θ < kuramotoF K 2 1 θ

  theorem kuramoto_coupling_contraction
      (K : ℝ) (hK : 0 < K)
      (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
      (θ : Fin N → ℝ) (i j : Fin N)
      (hWpos : 0 < W i j)
      (hgap : 0 < θ i - θ j) (hpi : θ i - θ j < Real.pi) :
      K * W i j * Real.sin (θ j - θ i)
        - K * W j i * Real.sin (θ i - θ j) < 0
  ```

- `Kuramoto/Weighted.lean`: Weighted Kuramoto dynamics with symmetric coupling. It proves the weighted gradient identity, a symmetry cancellation lemma, and algebraic Lyapunov descent: the weighted system moves downhill in its potential without invoking ODE trajectory theory.

  ```lean
  lemma weighted_gradient_identity

  lemma weightedKuramotoV_symm_cancel

  theorem weighted_lyapunov_descent
  ```

- `Kuramoto/Hebbian.lean`: Hebbian phase-plus-weight dynamics. It proves the Hebbian weight gradient identity, the phase gradient identity for the joint Lyapunov function, and joint algebraic Lyapunov descent. This formally closes the centrepiece no-ODE descent claim of the Budgeted Hebbian Kuramoto Max-Cut paper.

  ```lean
  theorem hebbian_weight_gradient_identity

  theorem hebbian_phase_gradient_identity

  theorem hebbian_joint_lyapunov_descent
  ```

## Connections

- This library supports [flywheel-universe](https://github.com/velvetmonkey/flywheel-universe) and the Budgeted Hebbian Kuramoto Max-Cut paper: <https://zenodo.org/records/20303914>.
- In witness-theory terms, the gradient identities formalise observer-like coherence emerging from local gradient dynamics: local phase and weight updates jointly descend a shared Lyapunov landscape.

## Companion project: flywheel-universe

[flywheel-universe](https://github.com/velvetmonkey/flywheel-universe) is the experimental and conceptual companion to this proof library. It studies budgeted Hebbian Kuramoto dynamics with fixed sparsity support, symmetric weights, and symmetric-Frobenius projection: a constrained control/calibration algorithm for oscillator-based Ising-machine style systems. The original contribution is not a claim to beat classical Max-Cut solvers; it is the identification and testing of a joint phase-plus-weight descent mechanism under physical coupling-budget constraints, especially under amplitude heterogeneity.

This Lean repo makes the central mathematical spine of that project machine-checkable. `Weighted.lean`, `Hebbian.lean`, and `Connections.lean` prove that the weighted and Hebbian systems are negative-gradient/descent systems for explicit potentials, and that the joint phase-plus-weight Hebbian update descends the Lyapunov function algebraically without ODE machinery. In short: flywheel-universe supplies the model, experiments, and demo; this repo supplies the zero-sorry formal proof core.

Useful links:

- Project repo: <https://github.com/velvetmonkey/flywheel-universe>
- Live demo: <https://velvetmonkey.github.io/flywheel-universe/>
- Demo source: <https://github.com/velvetmonkey/flywheel-universe/blob/main/demos/hebbian-kuramoto.html>
- Zenodo paper: <https://zenodo.org/records/20303914>

## Related work

- `taejun-song/kuramoto-lean`: comprehensive Lean 4 formalisation via the Ott-Antonsen manifold; it studies the continuum-limit approach, while this library focuses on finite-N geometric and Lyapunov identities.
- `facebookresearch/atlas-lean`: ATLAS autoformalized textbook library; its `FourierAnalysis` module provides AddCircle scaffolding used in early exploration.
- [`velvetmonkey/flywheel-universe`](https://github.com/velvetmonkey/flywheel-universe): Budgeted Hebbian Kuramoto dynamics for Max-Cut; the `Hebbian.lean` and `Connections.lean` modules here formally close the centrepiece descent claim of the companion paper. See the [live demo](https://velvetmonkey.github.io/flywheel-universe/).
- Zenodo paper: <https://doi.org/10.5281/zenodo.20468619>

## Cite this library

Use the Zenodo record for the paper: <https://doi.org/10.5281/zenodo.20468619>.

## Build

```bash
# Requires elan / Lean 4
git clone https://github.com/velvetmonkey/kuramoto-lean
cd kuramoto-lean
lake exe cache get
lake build
```

## Toolchain

- Lean: `leanprover/lean4:v4.31.0-rc1`
- Mathlib: `971b90233bf92f8f8ac41f236bcac871e13b9f8e`

## Context

This project is part of the witness-theory research programme connecting gradient descent, synchronisation, and observer dynamics.
