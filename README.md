# kuramoto-lean: Lean 4 Formalization of Kuramoto Synchronization

This library formally proves finite-N results about the Kuramoto model of coupled oscillators in Lean 4 / Mathlib. It takes a geometric approach on T^N, distinct from the Ott-Antonsen manifold approach in taejun-song/kuramoto-lean. The checked development contains no sorry, no admit, and no new axioms.

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

- This library supports the flywheel-universe research line and the Budgeted Hebbian Kuramoto Max-Cut paper: <https://zenodo.org/records/20303914>.
- In witness-theory terms, the gradient identities formalise observer-like coherence emerging from local gradient dynamics: local phase and weight updates jointly descend a shared Lyapunov landscape.

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
