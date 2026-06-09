# kuramoto-lean: A Lean 4 Library for Finite-N Kuramoto Synchronisation Dynamics

Ben Cassie  
Independent Researcher  
bencassie@outlook.com  
ORCID: 0009-0004-1899-7627

Published on Zenodo. DOI: 10.5281/zenodo.20468619.

## Abstract

We present `kuramoto-lean`, a Lean 4 / Mathlib library for finite-$N$ Kuramoto oscillator dynamics. The library takes a finite-dimensional geometric approach on phase configurations, distinct from the Ott--Antonsen manifold and continuum-limit formalism used in complementary Kuramoto formalisation work. It contains 27 theorem statements, all machine-checked sorry-free, admit-free, and with no new axioms (axiom footprint `{propext, Classical.choice, Quot.sound}`). Fourteen results form the algebraic core (order-parameter boundedness, gradient and Lyapunov-descent identities, contraction sign facts, Hebbian phase-plus-weight descent); thirteen frontier results add ODE existence and uniqueness via Picard--Lindelof, Lyapunov stability along trajectories, and a full all-to-all convergence-to-synchrony theorem proving that from any open-semicircle initial condition the order-parameter norm tends to one. We describe the library contents, the convergence proof architecture, and the `#check`-before-cite development discipline used to avoid hallucinated API names during AI-assisted Lean development.

## 1. Introduction

The Kuramoto model is one of the standard mathematical models of synchronisation. It describes a population of coupled phase oscillators, each with phase $\theta_i$, whose velocities depend on phase differences with other oscillators. In its identical-frequency, all-to-all form, the model is often written

$$
\dot{\theta_i} = \frac{K}{N}\sum_{j=1}^N \sin(\theta_j-\theta_i),
$$

where $K$ is a global coupling strength. Positive coupling drives phases toward agreement, and the order parameter

$$
R(\theta) = \frac{1}{N}\sum_{j=1}^N e^{i\theta_j}
$$

measures the degree of coherence. The model and its variants appear in biological synchrony, neural dynamics, power-grid stability, distributed timing, and oscillator-based computing.

This paper is not a claim of new dynamical-systems theory. The mathematical facts formalised here are standard finite-dimensional identities or algebraic consequences of standard definitions. The contribution is instead a machine-checked proof artifact: a Lean 4 / Mathlib library in which these identities are represented precisely, compiled against a pinned toolchain, and verified without `sorry`, `admit`, or additional axioms. For dynamical systems, this distinction matters. Informal calculations involving finite sums, signs, derivatives, and symmetries are easy to state but can hide mismatched conventions or incorrect factors. A formal library exposes these choices explicitly.

The library differs in scope from `taejun-song/kuramoto-lean`, which develops Kuramoto stability results through continuum and Ott--Antonsen machinery. In a local inspection of that repository, files such as `ComplexOA.lean`, `ContinuumRigidity.lean`, and `KuramotoFinal.lean` show the continuum/Ott--Antonsen orientation. By contrast, `kuramoto-lean` works directly with finite index types `Fin N`, finite sums, explicit vector fields, and coordinate derivatives. Its main focus is finite-$N$ geometric structure: order-parameter boundedness, gradient identities, pairwise contraction contributions, weighted Lyapunov descent, and Hebbian phase-plus-weight descent.

The library also serves as the formal proof spine for the companion `flywheel-universe` project, which studies budgeted Hebbian Kuramoto dynamics for Max-Cut under coupling-resource constraints. The companion project supplies the experimental model, browser demo, and benchmark context; this library supplies a machine-checked formalisation of the unprojected algebraic descent core, together with a frontier layer that proves all-to-all convergence to synchrony for the unconstrained system. The companion paper is available at the Zenodo record <https://zenodo.org/records/20303914>. The present library does not formalise the full projected constrained dynamics, projected KKT stationarity, or trajectory-level convergence claims from that project.

The remainder of the paper is organised as follows. Section 2 describes the library module by module. Section 3 records the verified artifact and reproducibility information. Section 4 describes the development methodology, especially the `#check`-before-cite discipline. Section 5 situates the library relative to the companion project, witness-theory framing, ATLAS, and related Kuramoto formalisation work. Section 6 states the limitations and future work. Section 7 concludes.

## 2. The Library

The repository consists of a root import file, `Kuramoto.lean`, and seven theorem-bearing modules under `Kuramoto/`. The public result set contains 14 theorem or lemma statements. The following catalogue summarises the results without relying on a wide table, so that the rendered PDF remains readable.

- **Order parameter bound** (`kuramotoR_norm_le_one`, `OrderParameter.lean`): for $N>0$, $\|R_N(\theta)\|\le 1$. This is the basic geometric bound for finite phasor averages.
- **Uniform gradient identity** (`kuramoto_gradient_identity`, `GradientFlow.lean`): $F_i(\theta)=-\partial_i V(\theta)$. This identifies the uniform identical Kuramoto field as a negative gradient flow.
- **$N=2$ relative velocity** (`kuramoto_relative_velocity`, `Contraction.lean`): $F_0-F_1=-K\sin(\theta_0-\theta_1)$. This gives exact two-oscillator relative dynamics.
- **$N=2$ pairwise contraction** (`kuramoto_pairwise_contraction`, `Contraction.lean`): if $K>0$ and the phase gap lies in $(0,\pi)$, then $F_0<F_1$. The leading oscillator slows relative to the trailing one.
- **General direct-coupling contraction** (`kuramoto_coupling_contraction`, `Contraction.lean`): a positive symmetric direct coupling contributes negatively to relative velocity. This is a general-$N$ pairwise result, not a global synchronisation theorem.
- **Weighted gradient identity** (`weighted_gradient_identity`, `Weighted.lean`): for symmetric $W$, $F_i^W=-\partial_i V_W$. Weighted finite networks retain gradient structure.
- **Symmetry cancellation** (`weightedKuramotoV_symm_cancel`, `Weighted.lean`): $\sum_i F_i^2=-\sum_i F_i\partial_iV_W$. This is the algebraic cancellation underlying descent.
- **Weighted Lyapunov descent** (`weighted_lyapunov_descent`, `Weighted.lean`): $\sum_i F_i\partial_iV_W\le 0$. The potential decreases in the vector-field direction.
- **Hebbian weight gradient identity** (`hebbian_weight_gradient_identity`, `Hebbian.lean`): $G_{ij}=-\partial_{W_{ij}}L$. The weight update is the negative gradient of the joint Lyapunov function.
- **Hebbian phase gradient identity** (`hebbian_phase_gradient_identity`, `Hebbian.lean`): $F_i^W=-\partial_iL$. The phase update is the negative gradient of the same joint Lyapunov function.
- **Joint Hebbian descent** (`hebbian_joint_lyapunov_descent`, `Hebbian.lean`): phase and weight terms jointly contribute a non-positive directional derivative. This is the unprojected algebraic joint descent core.
- **Zero-regularisation connection** (`hebbianL_zero_lam_eq_weighted`, `Connections.lean`): $L_{K,0}=V_W$. The Hebbian Lyapunov function generalises the weighted Kuramoto potential.
- **Weight-entry convexity** (`hebbianL_convex_weight_entry`, `Connections.lean`): $\partial^2 L/\partial W_{ij}^2>0$ when $\lambda>0$. The quadratic regulariser gives entrywise strict convexity.
- **Barrier asymmetry toy result** (`barrier_asymmetry_direct`, `WitnessGeometry.lean`): unequal quadratic curvatures give unequal restoring-force magnitudes. This is a minimal witness-geometry force-asymmetry formalisation.

### 2.1 `OrderParameter.lean`

For $N$ oscillators with phases $\theta:\mathrm{Fin}\,N\to\mathbb{R}$, the library defines the complex Kuramoto order parameter

$$
R_N(\theta)=\frac{1}{N}\sum_{k:\mathrm{Fin}\,N}\exp(i\theta_k).
$$

The theorem states that the norm of this average of unit phasors is bounded by one whenever $N>0$.

```lean
noncomputable def kuramotoR (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (∑ k, Complex.exp (θ k * Complex.I)) / N

theorem kuramotoR_norm_le_one (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ) :
    ‖kuramotoR N θ‖ ≤ 1
```

The proof is the triangle inequality for a finite sum in $\mathbb{C}$. Each summand has norm one, established through Mathlib's circle exponential interface (`Circle.coe_exp` and `Circle.norm_coe`). The norm of the sum is therefore at most $N$, and division by the positive real coercion of $N$ gives the result.

### 2.2 `GradientFlow.lean`

For the identical all-to-all Kuramoto model, the library defines the potential

$$
V_K(\theta)=-\frac{K}{2N}\sum_i\sum_j\cos(\theta_j-\theta_i)
$$

and vector field

$$
F_i(\theta)=\frac{K}{N}\sum_j\sin(\theta_j-\theta_i).
$$

The main theorem states that each vector-field component is the negative coordinate derivative of the potential.

```lean
noncomputable def kuramotoV (K : ℝ) (N : ℕ) (θ : Fin N → ℝ) : ℝ :=
  -(K / (2 * N)) * ∑ i : Fin N, ∑ j : Fin N, Real.cos (θ j - θ i)

noncomputable def kuramotoF (K : ℝ) (N : ℕ) (i : Fin N) (θ : Fin N → ℝ) : ℝ :=
  (K / N) * ∑ j : Fin N, Real.sin (θ j - θ i)

theorem kuramoto_gradient_identity
    (K : ℝ) (N : ℕ) (hN : 0 < N) (hK : 0 < K)
    (θ : Fin N → ℝ) (i : Fin N) :
    kuramotoF K N i θ =
      -(deriv (fun x => kuramotoV K N (Function.update θ i x)) (θ i))
```

The proof differentiates a finite double sum term by term. Updating the $i$-th phase coordinate is represented by `Function.update θ i x`. The derivative of each cosine term is encoded by a local `pairDeriv`, and a finite-sum identity collapses the double sum to $2\sum_j\sin(\theta_j-\theta_i)$. The factor $2$ cancels the $1/(2N)$ in the potential, yielding the vector field.

### 2.3 `Contraction.lean`

The first contraction result specialises the uniform vector field to $N=2$. It proves the exact relative-velocity identity

$$
F_0(\theta)-F_1(\theta)=-K\sin(\theta_0-\theta_1).
$$

```lean
lemma kuramoto_relative_velocity
    (K : ℝ) (θ : Fin 2 → ℝ) :
    kuramotoF K 2 0 θ - kuramotoF K 2 1 θ =
      -K * Real.sin (θ 0 - θ 1)
```

The proof expands the two finite sums using `Fin.sum_univ_two`, eliminates diagonal sine terms with $\sin 0=0$, and rewrites $\sin(\theta_1-\theta_0)$ using oddness of sine.

The second result converts the identity into a strict contraction inequality. If $K>0$ and the phase gap lies in $(0,\pi)$, then $\sin(\theta_0-\theta_1)>0$, so $F_0-F_1<0$.

```lean
theorem kuramoto_pairwise_contraction
    (K : ℝ) (hK : 0 < K) (θ : Fin 2 → ℝ)
    (hgap : 0 < θ 0 - θ 1) (hpi : θ 0 - θ 1 < Real.pi) :
    kuramotoF K 2 0 θ < kuramotoF K 2 1 θ
```

The third result avoids claiming full general-$N$ synchronisation. Instead, it isolates the direct pairwise coupling contribution in a weighted system. For symmetric $W$, positive $W_{ij}$, and a gap in $(0,\pi)$, the direct contribution to $F_i-F_j$ is strictly negative:

$$
K W_{ij}\sin(\theta_j-\theta_i)-K W_{ji}\sin(\theta_i-\theta_j)<0.
$$

```lean
theorem kuramoto_coupling_contraction
    (K : ℝ) (hK : 0 < K)
    (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hWpos : 0 < W i j)
    (hgap : 0 < θ i - θ j) (hpi : θ i - θ j < Real.pi) :
    K * W i j * Real.sin (θ j - θ i)
      - K * W j i * Real.sin (θ i - θ j) < 0
```

This theorem is deliberately local. In a general network, other oscillators also contribute to $F_i-F_j$, so the theorem does not assert global contraction. It asserts that the direct positive symmetric pair coupling has the expected sign.

### 2.4 `Weighted.lean`

The weighted module generalises the uniform all-to-all potential to an arbitrary symmetric coupling matrix $W:\mathrm{Fin}\,N\to\mathrm{Fin}\,N\to\mathbb{R}$:

$$
V_W(\theta)=-\frac{K}{2}\sum_i\sum_j W_{ij}\cos(\theta_j-\theta_i),
$$

with vector field

$$
F_i^W(\theta)=K\sum_j W_{ij}\sin(\theta_j-\theta_i).
$$

```lean
noncomputable def weightedKuramotoV (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) : ℝ :=
  -(K / 2) * ∑ i : Fin N, ∑ j : Fin N, W i j * Real.cos (θ j - θ i)

noncomputable def weightedKuramotoF (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (i : Fin N) (θ : Fin N → ℝ) : ℝ :=
  K * ∑ j : Fin N, W i j * Real.sin (θ j - θ i)

lemma weighted_gradient_identity
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i : Fin N) :
    weightedKuramotoF K N W i θ =
      -(deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i))
```

The symmetry assumption is essential. Without $W_{ij}=W_{ji}$, differentiating the full double sum produces the symmetrised coupling rather than the stated vector field. The formal proof repeats the finite-sum derivative structure from the uniform case, but the collapse lemma uses symmetry to combine the $W_{ij}$ and $W_{ji}$ terms.

The module then proves an algebraic cancellation identity and a descent inequality:

```lean
lemma weightedKuramotoV_symm_cancel
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i : Fin N, weightedKuramotoF K N W i θ * weightedKuramotoF K N W i θ =
    -(∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i))

theorem weighted_lyapunov_descent
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) ≤ 0
```

Mathematically, substituting $F_i^W=-\partial_iV_W$ gives

$$
\sum_i F_i^W\,\partial_iV_W
=-\sum_i (F_i^W)^2\le 0.
$$

This is an algebraic directional-descent statement, not a theorem about ODE solutions.

### 2.5 `Hebbian.lean`

The Hebbian module introduces a joint phase-and-weight Lyapunov function

$$
L_{K,\lambda}(\theta,W)
=V_W(\theta)+\frac{\lambda}{2}\sum_i\sum_j W_{ij}^2,
$$

and an unprojected Hebbian weight field

$$
G_{ij}(\theta,W)=\frac{K}{2}\cos(\theta_j-\theta_i)-\lambda W_{ij}.
$$

The coordinate update helper `hebbianUpdateWeight W i j x` replaces the single weight entry $W_{ij}$ with $x$.

```lean
noncomputable def hebbianL (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) : ℝ :=
  weightedKuramotoV K N W θ + (lam / 2) * ∑ i : Fin N, ∑ j : Fin N, W i j * W i j

noncomputable def hebbianWeightF (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) : ℝ :=
  (K / 2) * Real.cos (θ j - θ i) - lam * W i j

theorem hebbian_weight_gradient_identity
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    hebbianWeightF K lam N W θ i j =
      -(deriv (fun x => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j))
```

The proof differentiates $L$ with respect to a single weight coordinate. The potential part contributes $-(K/2)\cos(\theta_j-\theta_i)$; the quadratic regulariser contributes $\lambda W_{ij}$. Negating their sum gives the stated weight field.

The phase-side theorem states that, for symmetric $W$, the weighted phase vector field is also the negative coordinate derivative of the same joint Lyapunov function:

```lean
theorem hebbian_phase_gradient_identity
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) (i : Fin N) :
    weightedKuramotoF K N W i θ =
      -(deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i))
```

The quadratic weight regulariser is constant with respect to phase coordinates, so the result reduces to the weighted gradient identity.

The central Hebbian result is the joint algebraic descent theorem:

```lean
theorem hebbian_joint_lyapunov_descent
    (K lam : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    (∑ i : Fin N, weightedKuramotoF K N W i θ *
        deriv (fun x => hebbianL K lam N W (Function.update θ i x)) (θ i))
      + (∑ i : Fin N, ∑ j : Fin N, hebbianWeightF K lam N W θ i j *
        deriv (fun x => hebbianL K lam N (hebbianUpdateWeight W i j x) θ) (W i j)) ≤ 0
```

The theorem says that the phase contribution and weight contribution together are non-positive. Substituting the two negative-gradient identities gives

$$
-\sum_i (F_i^W)^2-\sum_{i,j}G_{ij}^2\le 0.
$$

This closes the unprojected algebraic joint descent core of the companion Hebbian Kuramoto claim. It does not formalise projection onto a constrained coupling polytope, projected-gradient flow, KKT stationarity, or trajectory convergence.

### 2.6 `Connections.lean`

The connections module proves two simple but useful relationships. First, with zero weight regularisation, the Hebbian Lyapunov function is exactly the weighted Kuramoto potential under the full double-sum convention used in the library:

$$
L_{K,0}(\theta,W)=V_W(\theta).
$$

```lean
lemma hebbianL_zero_lam_eq_weighted
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    hebbianL K 0 N W θ = weightedKuramotoV K N W θ
```

No factor of $1/2$ appears in this statement, because both definitions use the same full double sum. Earlier informal descriptions using an upper-triangular convention would require a different normalisation.

Second, when $\lambda>0$, the weight landscape is strictly convex in each individual weight coordinate at fixed phase:

$$
\frac{\partial^2}{\partial W_{ij}^2}L_{K,\lambda}(\theta,W)>0.
$$

```lean
lemma hebbianL_convex_weight_entry
    (K lam : ℝ) (hlam : 0 < lam) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ : Fin N → ℝ) (i j : Fin N) :
    0 < deriv (fun x => deriv (fun y => hebbianL K lam N (hebbianUpdateWeight W i j y) θ) x)
              (W i j)
```

The proof reuses the weight-gradient identity to identify the first derivative as an affine function $\lambda x-(K/2)\cos(\theta_j-\theta_i)$, then differentiates once more.

### 2.7 `WitnessGeometry.lean`

The witness-geometry module contains a small direct algebraic theorem about asymmetric quadratic restoring forces. It does not prove a theorem about the derivative of a piecewise-defined potential. Instead, it proves that if two positive curvatures $a$ and $b$ are unequal, then equal displacements on the two sides of a minimum produce unequal force magnitudes:

$$
\left|-2a(-x)\right|\ne \left|-2b x\right|
\quad\text{for }a,b,x>0,\ a\ne b.
$$

```lean
theorem barrier_asymmetry_direct
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (x : ℝ) (hx : 0 < x) :
    |(-2 * a * (-x))| ≠ |(-2 * b * x)|
```

The proof reduces the absolute values using the signs of the two expressions and then uses arithmetic to show that equality would imply $a=b$, contradicting the hypothesis. The result is included as a minimal formal bridge to the witness-theory interpretation of asymmetric potentials; it is not used in the Kuramoto proofs.

### 2.8 `Frontier.lean`

The frontier module moves from algebraic identities to trajectory-level dynamics. It contains thirteen theorem statements, all proved sorry-free: smoothness of the Kuramoto vector field, ODE existence and uniqueness via Mathlib's Picard--Lindelof infrastructure, Lyapunov derivative identities and monotonicity along trajectories, semicircle extremal contraction, phase-diameter non-expansion, a synchrony characterisation of the order parameter, a Lyapunov lower bound, and the capstone, full all-to-all convergence to synchrony.

The capstone theorem states that for all-to-all coupling ($W_{ij}=1$ for $i\ne j$, zero diagonal), positive coupling $K>0$, $N\ge 2$ oscillators, any trajectory $\theta(t)$ solving the Kuramoto ODE, and any initial configuration confined to an open semicircle ($|\theta_a(0)-\theta_b(0)|<\pi$ for all $a,b$), the order-parameter norm converges to one:

```lean
theorem allToAll_convergence_to_synchrony
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi) :
    Filter.Tendsto (fun t => ‖kuramotoR N (θ t)‖) Filter.atTop (nhds 1)
```

The proof is structured to avoid waiting on Mathlib's LaSalle-invariance and $\omega$-limit infrastructure, which were not available in usable form under the pinned toolchain. It is assembled from four parts.

First, a Lyapunov--Barbalat step. The weighted Lyapunov function $V$ satisfies $\dot V = -\sum_i F_i(\theta)^2$ along trajectories, and $V$ is bounded below, so $\sum_i F_i^2$ is the derivative of a function bounded above. A Lipschitz-form Barbalat lemma (`barbalat_of_nonneg_lipschitz`: a non-negative Lipschitz function whose antiderivative is bounded above tends to zero) then yields $\sum_i F_i(\theta(t))^2 \to 0$, hence each $F_i \to 0$ and $\sum_i |F_i| \to 0$.

Second, uniform semicircle confinement (`semicircle_preserved`). The phase diameter starts strictly below $\pi$ and a strict extremal-contraction argument, combined with a finite-family maximum-barrier principle (`finite_max_stays_below`), keeps every pairwise difference below a single constant $C = (D_0+\pi)/2 < \pi$ for all forward time. This uniform bound is exposed as `semicircle_preserved_uniform`; the uniformity (as opposed to a merely pointwise $<\pi$ bound) is exactly what the final analysis step requires.

Third, a phase-diameter squeeze (`phase_diffs_tend_to_zero`). Writing $D(t)$ for the phase diameter (the supremum of signed pairwise differences), the off-diagonal sine terms of the minimum-phase oscillator are all non-negative, and its $F$-value bounds $K\sin(D(t))$ from below. Combined with $F_{\min} \le \sum_i |F_i| \to 0$, this gives $0 \le K\sin(D(t)) \le \sum_i |F_i(t)| \to 0$, so $\sin(D(t)) \to 0$. Notably the minimising and maximising oscillator indices may change with time; this is harmless, because the bound is applied pointwise to the scalar quantity $\sin(D(t))$ and no continuity of the index selection is required.

Fourth, an analysis core (`diam_tendsto_zero_of_sin_tendsto_zero`). If $\sin(D(t)) \to 0$ and $D(t)$ is eventually confined to $[0,C]$ with $C<\pi$, then $D(t)\to 0$. The upper branch of $\sin$ near $\pi$ is excluded by $C<\pi$, so the positive compact minimum of $\sin$ on $[\varepsilon,C]$ forces $D(t)<\varepsilon$ once $\sin(D(t))$ is small. The diameter therefore vanishes, every pairwise difference is squeezed to zero, and a continuity-of-exponential argument (`R_norm_of_phase_convergence`) lifts this to $\|R\|\to 1$.

The complete theorem depends only on the axioms `{propext, Classical.choice, Quot.sound}`; it uses no `sorry`, no `admit`, no `native_decide`, and no new axioms.

## 3. Verified Artifacts

The repository is available at:

<https://github.com/velvetmonkey/kuramoto-lean>

The artifact reviewed for this paper had commit:

```text
2da1ca063229a6ffd3b718193f76bfb9e4fe2cb8
```

The Lean toolchain is pinned to:

```text
leanprover/lean4:v4.31.0-rc1
```

Mathlib is pinned in `lakefile.toml` to:

```text
971b90233bf92f8f8ac41f236bcac871e13b9f8e
```

The library root is:

```lean
-- Kuramoto synchronisation library: root import
import Kuramoto.OrderParameter
import Kuramoto.GradientFlow
import Kuramoto.Contraction
import Kuramoto.Weighted
import Kuramoto.Hebbian
import Kuramoto.Connections
import Kuramoto.WitnessGeometry
import Kuramoto.Frontier
```

The verification commands are:

```bash
lake exe cache get
lake build
rg "sorry|admit|axiom" Kuramoto/
```

At the reviewed commit, `lake build` succeeds, and the `rg` command returns no matches. The theorem-bearing Lean modules contain 1486 lines in `Kuramoto/*.lean`. They expose 27 public theorem statements (14 in the algebraic core, 13 in the frontier module), supported by additional private lemmas. A `#print axioms allToAll_convergence_to_synchrony` reports the dependency set `{propext, Classical.choice, Quot.sound}`, confirming no `sorry`, no `admit`, and no new axioms reach the capstone theorem.

## 4. Development Methodology

The library was developed with an explicit `#check`-before-cite discipline. Before a Mathlib lemma name was used in a proof, the name was checked against the pinned Mathlib version. Names that failed to elaborate were not used. This rule is simple, but it addresses a common failure mode in AI-assisted Lean development: plausible API names that do not exist in the local version of Mathlib.

The importance of this rule became visible during development. Several expected names were absent or unsuitable under the pinned toolchain, and some informal theorem statements required correction after Lean exposed a sign or normalisation issue. For example, the general pairwise contraction expression must use a subtraction to represent the contribution to relative velocity; using a plus sign would cancel to zero under symmetry. Similarly, the zero-regularisation connection between `hebbianL` and `weightedKuramotoV` is equality, not equality up to a factor of two, because both definitions use full double sums.

A second methodological constraint was scoped target selection. Each proof attempt was framed around a concrete theorem statement and a proof strategy before proof search began. This reduced the search space and kept the development focused on finite algebraic identities rather than broader ODE claims. The result is a library of narrow but reliable facts: derivative identities, sign inequalities, and finite-sum descent statements.

Version pinning is also essential. Lean and Mathlib APIs evolve quickly, especially around analysis, derivatives, finite sums, and coercions. The pinned `lean-toolchain` and Mathlib revision make the artifact reproducible. A theorem that compiles against this commit has a precise dependency context; a theorem that merely appears plausible in prose does not.

Finally, zero-sorry verification should be interpreted correctly. The absence of `sorry`, `admit`, and new axioms means that the stated Lean theorems are fully checked from the imported foundations. It does not mean that the theorems imply more than they state. The algebraic core proves gradient and Lyapunov-descent identities; the frontier module proves ODE existence and uniqueness, Lyapunov stability along trajectories, and all-to-all convergence to synchrony from open-semicircle initial data. What remains outside the library is broader still: convergence from arbitrary (non-semicircle) initial conditions, synchronisation under general (non-all-to-all) coupling, and the constrained projected dynamics of the companion Max-Cut model. The convergence theorem is precisely scoped by its hypotheses and should be read as exactly that statement, not as a general Kuramoto synchronisation result.

## 5. Connections

### 5.1 Companion `flywheel-universe` project

The companion project `flywheel-universe` studies budgeted Hebbian Kuramoto dynamics for Max-Cut under coupling-resource constraints. It includes an experimental benchmark suite and a live browser demo:

- Project: <https://github.com/velvetmonkey/flywheel-universe>
- Live demo: <https://velvetmonkey.github.io/flywheel-universe/>
- Companion paper record: <https://zenodo.org/records/20303914>

The companion paper frames the Hebbian rule as a robustness primitive for heterogeneous-amplitude oscillator arrays rather than as a state-of-the-art Max-Cut solver. Its model includes symmetric weights, fixed support, row-sum budgets, and projection onto a constrained coupling set. The Lean library here does not formalise that full constrained projected system. Instead, `hebbian_joint_lyapunov_descent` proves the unprojected algebraic descent core:

$$
dL[F,G]\le 0
$$

for the finite-dimensional phase-plus-weight vector field defined in the library. This is the part of the argument where the phase gradient identity and the weight gradient identity combine into a shared Lyapunov descent statement. Projection, tangent cones, Moreau decompositions, and KKT stationarity remain outside the present formalisation.

### 5.2 Witness-theory framing

The witness-theory connection is interpretive rather than a dependency of the Lean proofs. In that programme, observer-like coherence is modelled as descent on a loss or potential landscape. The Kuramoto gradient identity formalises one concrete instance of this pattern: local phase interactions can be represented as negative-gradient dynamics of a global potential. The Hebbian extension adds a second adaptive layer: weights as well as phases descend a joint Lyapunov function. The Lean contribution is to make this descent structure precise in a finite algebraic setting.

### 5.3 ATLAS and Mathlib context

The ATLAS project (`facebookresearch/atlas-lean`) is a large autoformalised Lean corpus. In exploratory work for this library, its Fourier-analysis material, especially the AddCircle scaffolding, was relevant as background for phase-circle reasoning. However, ATLAS did not supply the finite-dimensional Kuramoto dynamics or Lyapunov machinery needed here. The useful lesson is not that ATLAS is inadequate, but that domain-specific dynamical-systems libraries still require targeted formalisation beyond general mathematical scaffolding.

Mathlib itself provides the foundations used throughout this library: finite sums, complex numbers, real trigonometry, derivatives, norms, and order reasoning. The proofs here repeatedly exercise patterns that could be useful as future library contributions, especially around coordinate updates with `Function.update`, derivatives of finite sums, and finite-dimensional vector-field notation.

### 5.4 Related Kuramoto formalisation work

The most directly related Lean repository is `taejun-song/kuramoto-lean`, described on GitHub as a machine-checked proof of Kuramoto stability. Local inspection shows files devoted to complex Ott--Antonsen dynamics and continuum rigidity. That project and this one are complementary. The former addresses continuum/Ott--Antonsen stability structure; this library addresses finite-$N$ algebraic identities, weighted finite networks, and Hebbian phase-plus-weight descent.

The broader Kuramoto literature includes the original synchronisation model, order-parameter analysis, Ott--Antonsen reductions, stability theory, and adaptive-coupling variants. This paper does not attempt to survey that literature exhaustively. Its focus is the Lean artifact and the proof-engineering methodology needed to formalise a finite subset of that theory.

## 6. Limitations and Future Work

The algebraic core proves identities rather than trajectory-level theorems, but the frontier module now bridges that gap for the all-to-all system: ODE existence and uniqueness, Lyapunov stability along trajectories, phase-diameter non-expansion, and full convergence to synchrony from open-semicircle initial data are all proved. Four directions that earlier versions of this library listed as open are therefore now closed.

First, ODE existence and uniqueness for the finite Kuramoto vector field are formalised directly from Mathlib's Picard--Lindelof infrastructure (`kuramoto_ode_exists`, `kuramoto_ode_unique`), connecting the algebraic vector-field definitions to actual solution curves.

Second, Lyapunov stability along trajectories is proved (`lyapunov_nonincreasing_along_trajectory`), reusing the descent identities as designed.

Third, full synchronisation convergence is proved for the all-to-all system from open-semicircle initial data (`allToAll_convergence_to_synchrony`), via the Lyapunov--Barbalat, uniform-confinement, diameter-squeeze, and analysis-core architecture of Section 2.8. It remains open for general coupling topologies and for initial data outside an open semicircle.

Fourth, phase-diameter non-expansion is proved (`semicircle_preserved`) through a finite-family maximum-barrier principle (`finite_max_stays_below`) rather than a Dini-derivative lemma, sidestepping the nonsmooth-analysis infrastructure that was unavailable in the local Mathlib context.

Genuinely open directions remain. The companion Hebbian Max-Cut model includes projection onto a constrained coupling set. Formalising projected constrained dynamics would require tangent-cone, normal-cone, variational-inequality, and KKT machinery beyond the current file set.

Separately, the Hebbian phase-plus-weight descent connects naturally to associative-memory dynamics. Reading the adaptive weights $W$ as a learned coupling makes a synchronised phase configuration an attractor selected by the weight field — the same mechanism that underlies Hopfield associative memory and its statistical-mechanics storage-capacity analysis (Amit, Gutfreund & Sompolinsky, 1985). The modern continuous-state Hopfield network, and its established equivalence to transformer attention (Ramsauer et al., 2021), suggests a route from the present finite-$N$ descent identities toward formal retrieval- and capacity-level guarantees for attention-like dynamics. Formalising the storage-capacity and retrieval-stability side of this picture is a natural, if substantial, extension and is not attempted here.

Finally, the development suggests possible Mathlib contributions: reusable lemmas for coordinate derivatives through `Function.update`, finite-dimensional gradient notation over `Fin N`, and templates for differentiating nested finite sums of trigonometric expressions.

## 7. Conclusion

`kuramoto-lean` is a Lean 4 foundation for finite-$N$ Kuramoto and Hebbian phase-plus-weight dynamics. It formalises order-parameter boundedness, uniform and weighted gradient identities, contraction sign facts, Lyapunov descent identities, Hebbian weight and phase gradient identities, and a small witness-geometry force-asymmetry result. On top of this algebraic core, a frontier layer proves ODE existence and uniqueness, Lyapunov stability along trajectories, phase-diameter non-expansion, and a full all-to-all convergence-to-synchrony theorem: from any open-semicircle initial condition the order-parameter norm tends to one. The entire library of 27 theorems is machine-checked sorry-free with axiom footprint `{propext, Classical.choice, Quot.sound}`. The companion `flywheel-universe` project supplies the experimental and modelling context; this library supplies the proof spine. More broadly, the project demonstrates that AI-assisted Lean development can produce clean, reproducible artifacts rapidly when paired with strict API verification, scoped theorem targets, and honest boundaries around what has and has not been proved.

## References and Links

- `kuramoto-lean` repository: <https://github.com/velvetmonkey/kuramoto-lean>
- Paper DOI: <https://doi.org/10.5281/zenodo.20468619>
- Paper record: <https://zenodo.org/records/20468619>
- Companion `flywheel-universe` repository: <https://github.com/velvetmonkey/flywheel-universe>
- Companion Max-Cut paper record: <https://zenodo.org/records/20303914>
- Live Hebbian Kuramoto demo: <https://velvetmonkey.github.io/flywheel-universe/>
- Lean theorem prover: <https://lean-lang.org/>
- Mathlib: <https://github.com/leanprover-community/mathlib4>
- ATLAS Lean repository: <https://github.com/facebookresearch/atlas-lean>
- `taejun-song/kuramoto-lean`: <https://github.com/taejun-song/kuramoto-lean>

### Cited works

- Amit, D. J., Gutfreund, H., & Sompolinsky, H. (1985). Spin-glass models of neural networks. *Physical Review A*, 32(2), 1007–1018. <https://doi.org/10.1103/PhysRevA.32.1007>
- Ramsauer, H., Schäfl, B., Lehner, J., Seidl, P., Widrich, M., Gruber, L., Holzleitner, M., Adler, T., Kreil, D., Kopp, M., Klambauer, G., Brandstetter, J., & Hochreiter, S. (2021). Hopfield Networks is All You Need. *International Conference on Learning Representations (ICLR)*. <https://arxiv.org/abs/2008.02217>
