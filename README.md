# kuramoto-lean: Lean 4 Formalization of Kuramoto Synchronization

This library formally proves three results about the finite-N Kuramoto model of coupled oscillators in Lean 4 / Mathlib. It takes a geometric approach on T^N, distinct from the Ott-Antonsen manifold approach in taejun-song/kuramoto-lean. The checked development contains no sorry, no admit, and no new axioms.

## Results

- `Kuramoto/OrderParameter.lean`: The Kuramoto order parameter satisfies `‖R‖ ≤ 1` for any positive number of oscillators and any phase configuration.

  ```lean
  theorem kuramotoR_norm_le_one (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ) :
      ‖kuramotoR N θ‖ ≤ 1
  ```

- `Kuramoto/GradientFlow.lean`: The Kuramoto vector field is the negative gradient of the Kuramoto potential `V`; equivalently, each component satisfies `kuramotoF K N i θ = -(∂V/∂θ i)`.

  ```lean
  theorem kuramoto_gradient_identity
      (K : ℝ) (N : ℕ) (hN : 0 < N) (hK : 0 < K)
      (θ : Fin N → ℝ) (i : Fin N) :
      kuramotoF K N i θ =
        -(deriv (fun x => kuramotoV K N (Function.update θ i x)) (θ i))
  ```

- `Kuramoto/Contraction.lean`: For two identical oscillators with `K > 0`, if the phase gap is in `(0, π)`, the leading oscillator's rate is strictly less than the trailing one's, so the oscillators are converging.

  ```lean
  theorem kuramoto_pairwise_contraction
      (K : ℝ) (hK : 0 < K) (θ : Fin 2 → ℝ)
      (hgap : 0 < θ 0 - θ 1) (hpi : θ 0 - θ 1 < Real.pi) :
      kuramotoF K 2 0 θ < kuramotoF K 2 1 θ
  ```

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
