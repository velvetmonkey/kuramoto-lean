# kuramoto-lean: A Lean 4 Library for Finite-N Kuramoto Synchronisation Dynamics

Ben Cassie  
Independent Researcher  
bencassie@outlook.com  
ORCID: 0009-0004-1899-7627

Published on Zenodo. DOI: 10.5281/zenodo.20468619.

## Abstract

We present `kuramoto-lean`, a Lean 4 / Mathlib library for finite-$N$ Kuramoto oscillator dynamics. The library takes a finite-dimensional geometric approach on phase configurations, distinct from the Ott--Antonsen manifold and continuum-limit formalism used in complementary Kuramoto formalisation work. It contains 39 public theorem declarations, all machine-checked sorry-free, admit-free, and with no project-defined axioms; committed `#print axioms` transcript guards for the headline frontier and discrete results record the footprint `{propext, Classical.choice, Quot.sound}`. Nine public theorems form the algebraic core (order-parameter boundedness, gradient and Lyapunov-descent identities, contraction sign facts, Hebbian phase-plus-weight descent); fourteen frontier theorems add ODE existence and uniqueness via Picard--Lindelof, Lyapunov stability along trajectories, and convergence to synchrony for all-to-all and uniformly positive floor coupling; and sixteen discrete theorems establish fixed-step skew confinement, a stochastic-matrix reformulation, geometric contraction, and convergence of the skew to zero. The continuous convergence theorems are precisely scoped by their hypotheses, and the discrete convergence theorem additionally requires at least three oscillators and a positive step size; none is a general Kuramoto synchronisation result. We describe the library contents, the continuous and discrete convergence proof architectures, and the `#check`-before-cite development discipline used to avoid hallucinated API names during AI-assisted Lean development.

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

The library also serves as the formal proof spine for the companion `flywheel-universe` project, which studies budgeted Hebbian Kuramoto dynamics for Max-Cut under coupling-resource constraints. The companion project supplies the experimental model, browser demo, and benchmark context; this library supplies a machine-checked formalisation of the unprojected algebraic descent core, together with a frontier layer that proves all-to-all convergence to synchrony for the unconstrained system. The companion paper is available at the Zenodo record <https://doi.org/10.5281/zenodo.20469680>. The present library does not formalise the full projected constrained dynamics, projected KKT stationarity, or trajectory-level convergence claims from that project.

The remainder of the paper is organised as follows. Section 2 describes the library module by module. Section 3 records the verified artifact and reproducibility information. Section 4 describes the development methodology, especially the `#check`-before-cite discipline. Section 5 situates the library relative to the companion project, witness-theory framing, ATLAS, and related Kuramoto formalisation work. Section 6 states the limitations and future work. Section 7 concludes.

## 2. The Library

The repository consists of a root import file, `Kuramoto.lean`, and ten modules under `Kuramoto/`, nine of which contain public theorem declarations. Throughout this paper, a “public theorem declaration” means a source line beginning exactly `theorem ` in a tracked Lean file on `master`, counted reproducibly with `git ls-files '*.lean' | xargs grep -hE '^theorem ' | wc -l`; declarations beginning `private theorem` and all `lemma` declarations are excluded. Under that convention, the algebraic modules contribute 9 public theorems, `Frontier.lean` contributes 14, and the two discrete modules contribute 16, for 39 in total. Six public lemmas are useful supporting results but do not enter this count. The following catalogue summarises the algebraic results without relying on a wide table, so that the rendered PDF remains readable.

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

The frontier module moves from algebraic identities to trajectory-level dynamics. It contains fourteen public theorem declarations: smoothness of the Kuramoto vector field, ODE existence and uniqueness via Mathlib's Picard--Lindelof infrastructure, Lyapunov derivative identities and monotonicity along trajectories, semicircle extremal contraction, phase-diameter non-expansion, a synchrony characterisation of the order parameter, a Lyapunov lower bound, the capstone all-to-all convergence to synchrony, and its generalisation to symmetric coupling with a uniform positive off-diagonal floor (together with a corollary rederiving the all-to-all theorem from the floor theorem). An earlier edition reported fifteen by also counting the public supporting lemma `sin_nonneg_of_phase_between`; no frontier theorem was removed or made private.

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

#### Floor-coupling generalisation

The convergence theorem extends beyond all-to-all coupling. The floor-coupling theorem replaces the hypothesis $W_{ij}=1$ (for $i \ne j$) with a uniform positive off-diagonal floor: a symmetric matrix $W$ and a constant $w_{\min}>0$ with $w_{\min} \le W_{ij}$ for all $i \ne j$.

```lean
theorem floor_coupling_convergence_to_synchrony
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWsym : ∀ i j, W i j = W j i)
    (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi) :
    Filter.Tendsto (fun t => ‖kuramotoR N (θ t)‖) Filter.atTop (nhds 1)
```

The proof reuses the same Lyapunov--Barbalat, uniform-confinement, diameter-squeeze, and analysis-core architecture; the abstract analysis lemmas (the barrier principle, the Barbalat lemma, the diameter analysis core, and the order-parameter step) are shared unchanged with the all-to-all proof. Three ingredients change. The strict extremal contraction is re-proved from the floor, and is in fact simpler than the all-to-all version: a direct term-sign argument shows $F_{\max} \le -K\,w_{\min}\sin(D) < 0 < K\,w_{\min}\sin(D) \le F_{\min}$ whenever the diameter $D$ lies in $(0,\pi)$, with no sine-pairing over the non-extremal indices. The diameter-squeeze bound becomes $K\,w_{\min}\sin(D(t)) \le F_{\mathrm{argmin}}$, so the contraction rate is governed by $w_{\min}$. And the $\le 1$ weight ceiling used by the all-to-all Lipschitz and bounded-below estimates is replaced by a bound derived inside the proof: since the matrix is finite, $B := 1 + \sum_i\sum_j |W_{ij}|$ bounds every entry, so no ceiling hypothesis is required.

Two hypotheses one might expect are absent, deliberately. No nonnegativity assumption is needed, because off-diagonal nonnegativity already follows from the positive floor; and no zero-diagonal assumption is needed, because diagonal entries only ever multiply $\sin(\theta_i-\theta_i)=\sin 0=0$ in the vector field and are inert. A corollary (`allToAll_convergence_to_synchrony'`) rederives the all-to-all theorem from the floor theorem by instantiating $w_{\min}=1$; the original all-to-all theorem is also kept as an independent statement.

Both convergence theorems depend only on the axioms `{propext, Classical.choice, Quot.sound}`; they use no `sorry`, no `admit`, no `native_decide`, and no new axioms. For the floor-coupling theorem this footprint is additionally pinned in the source by a `#guard_msgs`-checked `#print axioms` command at the end of `Frontier.lean`, so the build itself fails if the footprint ever drifts.

### 2.9 `Discrete.lean`

The first discrete module replaces the continuous trajectory by a fixed-step Euler update of the weighted field,

$$
\theta_i^{k+1}=\theta_i^k+hK\sum_j W_{ij}\sin(\theta_j^k-\theta_i^k),
$$

and defines the phase diameter as the current maximum phase minus the current minimum phase. Its four public theorems establish confinement and a concrete two-node witness.

- **One-step diameter confinement** (`discreteStep_diam_le`): for a nonempty finite population, $K>0$, $h\ge 0$, a positive constant $w_{\min}$ below every off-diagonal weight, current diameter below $\pi$, and the per-row step condition $hK\,\mathrm{rowSum}_i\le 1$, one Euler step cannot increase the diameter. The statement does not require symmetry of $W$; the positive floor and step bound are the load-bearing hypotheses.
- **All-time bounded skew** (`discreteFlow_bounded_skew`): under the same hypotheses at the initial state, every iterate has diameter at most the initial diameter, and therefore remains below $\pi$. This is confinement, not convergence to a common phase.
- **Two-node row sum** (`rowSum_ones_two`): for the constant unit matrix on `Fin 2`, the off-diagonal row sum is exactly one for either row.
- **Concrete two-node witness** (`fleet_clock_two_nodes_bounded_skew`): with $N=2$, $K=h=1$, $W_{ij}=1$, and initial phases $(0,1)$, every iterate has diameter at most its initial diameter. This narrow witness sits at equality in the step bound and does not claim strict contraction.

The discrete confinement proof is not a direct reuse of the continuous semicircle argument: an Euler step can overshoot unless the explicit step bound is imposed. Committed transcript guards record the standard axiom footprint for `discreteStep_diam_le`, `discreteFlow_bounded_skew`, and `fleet_clock_two_nodes_bounded_skew`.

### 2.10 `DiscreteConvergence.lean`

The second discrete module strengthens confinement to geometric convergence through a state-dependent stochastic matrix. Writing $\sin x=\operatorname{sinc}(x)x$, it represents one update as $\theta^{k+1}=P(\theta^k)\theta^k$ and uses a Dobrushin pairwise estimate. Its twelve public theorems are as follows.

- **Diameter nonnegativity** (`diameter_nonneg`): every phase diameter is nonnegative when `Fin N` is nonempty.
- **Sinc chord bound** (`sinc_lower`): if $0<D<\pi$ and $0\le y\le D$, then $\operatorname{sinc}(D)\le\operatorname{sinc}(y)$.
- **Signed-gap sinc bound** (`sinc_ge_of_gap`): if $0<D_0<\pi$ and $|x|\le D_0$, then $\operatorname{sinc}(D_0)\le\operatorname{sinc}(x)$; evenness of sinc handles either sign of the phase gap.
- **Dobrushin pair estimate** (`dobrushin_pair`): for $N\ge3$, a row-stochastic nonnegative matrix whose off-diagonal entries are at least $\alpha$ maps any two distinct rows to averages differing by at most $(1-(N-2)\alpha)(M-m)$ when every input lies in $[m,M]$. The theorem itself does not assume that this factor lies in $(0,1)$; that fact is supplied later from the Kuramoto hypotheses.
- **Sinc reconstruction** (`sinc_mul_self`): for every real $x$, $\operatorname{sinc}(x)x=\sin x$, including $x=0$.
- **Diagonal matrix entry** (`Pmat_diag`): the diagonal of the state-dependent matrix is exactly one minus the sum of the off-diagonal sinc-weighted step coefficients.
- **Off-diagonal matrix entry** (`Pmat_offdiag`): for $i\ne j$, $P_{ij}=hKW_{ij}\operatorname{sinc}(\theta_j-\theta_i)$.
- **Row stochasticity** (`Pmat_row_sum`): every row of $P$ sums exactly to one; nonnegativity is not part of this theorem and is established under the later step and floor hypotheses.
- **Faithful reformulation** (`discreteStep_eq_Pmat`): the Euler update at each coordinate equals the corresponding $P$-weighted average of the current phases.
- **Strict contraction factor** (`contract_factor`): if $N\ge3$, $K>0$, $h>0$, $w_{\min}>0$, all off-diagonal weights exceed the floor, $0<D_0<\pi$, and $hK\,\mathrm{rowSum}_i\le1$, then $1-(N-2)hKw_{\min}\operatorname{sinc}(D_0)$ lies strictly between zero and one.
- **One-step geometric contraction** (`discreteStep_diam_contract`): under those hypotheses and the additional current bound $\operatorname{diameter}(\theta)\le D_0$, the next diameter is at most that strict factor times the current diameter.
- **Convergence of the discrete flow** (`discreteFlow_tendsto_zero`): if the initial diameter is below $\pi$ under the same $N\ge3$, positive-step, positive-floor, and per-row step hypotheses, the diameter tends to zero along the natural-number iterates.

The last theorem concerns diameter convergence, not a rate-free claim for two nodes or zero step size: at $N=2$ the displayed Dobrushin factor loses its strict term, and at $h=0$ the update is the identity. It also does not cover missing or sign-indefinite off-diagonal couplings, an initial diameter at least $\pi$, or a step size beyond the per-row bound. Committed transcript guards record the standard axiom footprint for the one-step contraction and convergence theorems.

## 3. Verified Artifacts

The repository is available at:

<https://github.com/velvetmonkey/kuramoto-lean>

The artifact reviewed for this paper had commit:

```text
c5f4238de912da6fdf0c410742d1cfc26ec0326b
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
import Kuramoto.Discrete
import Kuramoto.DiscreteConvergence
```

The verification commands are:

```bash
lake exe cache get
lake build
rg "sorry|admit|axiom" Kuramoto/
rg '^[[:space:]]*(sorry|admit)\b|^[[:space:]]*axiom\b' Kuramoto/ --glob '*.lean'
git ls-files '*.lean' | xargs grep -hE '^theorem ' | wc -l
```

The update described here was reviewed at the commit above without rerunning a Lean build: this documentation lane was explicitly limited to reading source and metadata. A structural search for declarations beginning `sorry`, `admit`, or `axiom` returns no matches. The broader `rg "sorry|admit|axiom" Kuramoto/` search has fifteen textual matches, all in explanatory comments, expected-output docstrings, or the six `#print axioms` transcript guards; none is proof code or an axiom declaration. The ten module files contain 2,598 lines in `Kuramoto/*.lean` and expose 39 public theorem declarations (9 algebraic, 14 frontier, and 16 discrete), with public and private lemmas excluded from that count. The frontier guard for `floor_coupling_convergence_to_synchrony` and five discrete guards report `{propext, Classical.choice, Quot.sound}`. The earlier manual `#print axioms` result for `allToAll_convergence_to_synchrony` reports the same set; its theorem statement and proof are unchanged at the reviewed commit, while only the floor-coupling result is protected by a committed frontier guard.

## 4. Development Methodology

The library was developed with an explicit `#check`-before-cite discipline. Before a Mathlib lemma name was used in a proof, the name was checked against the pinned Mathlib version. Names that failed to elaborate were not used. This rule is simple, but it addresses a common failure mode in AI-assisted Lean development: plausible API names that do not exist in the local version of Mathlib.

The importance of this rule became visible during development. Several expected names were absent or unsuitable under the pinned toolchain, and some informal theorem statements required correction after Lean exposed a sign or normalisation issue. For example, the general pairwise contraction expression must use a subtraction to represent the contribution to relative velocity; using a plus sign would cancel to zero under symmetry. Similarly, the zero-regularisation connection between `hebbianL` and `weightedKuramotoV` is equality, not equality up to a factor of two, because both definitions use full double sums.

A second methodological constraint was scoped target selection. Each proof attempt was framed around a concrete theorem statement and a proof strategy before proof search began. This reduced the search space and kept the development focused on finite algebraic identities rather than broader ODE claims. The result is a library of narrow but reliable facts: derivative identities, sign inequalities, and finite-sum descent statements.

Version pinning is also essential. Lean and Mathlib APIs evolve quickly, especially around analysis, derivatives, finite sums, and coercions. The pinned `lean-toolchain` and Mathlib revision make the artifact reproducible. A theorem that compiles against this commit has a precise dependency context; a theorem that merely appears plausible in prose does not.

Finally, zero-sorry verification should be interpreted correctly. The absence of `sorry`, `admit`, and new axioms means that the stated Lean theorems are fully checked from the imported foundations. It does not mean that the theorems imply more than they state. The algebraic core proves gradient and Lyapunov-descent identities; the frontier module proves ODE existence and uniqueness, Lyapunov stability along trajectories, and convergence to synchrony from open-semicircle initial data for all-to-all coupling and, more generally, for symmetric coupling with a uniform positive off-diagonal floor. What remains outside the library is broader still: convergence from arbitrary (non-semicircle) initial conditions, synchronisation under fully general coupling (sign-indefinite weights, or nonnegative weights without a uniform positive floor), and the constrained projected dynamics of the companion Max-Cut model. The convergence theorems are precisely scoped by their hypotheses and should be read as exactly those statements, not as a general Kuramoto synchronisation result.

## 5. Connections

### 5.1 Companion `flywheel-universe` project

The companion project `flywheel-universe` studies budgeted Hebbian Kuramoto dynamics for Max-Cut under coupling-resource constraints. It includes an experimental benchmark suite and a live browser demo:

- Project: <https://github.com/velvetmonkey/flywheel-universe>
- Live demo: <https://velvetmonkey.github.io/flywheel-universe/>
- Companion paper record: <https://doi.org/10.5281/zenodo.20469680>

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

Third, full synchronisation convergence is proved from open-semicircle initial data, first for the all-to-all system (`allToAll_convergence_to_synchrony`) and then for any symmetric coupling with a uniform positive off-diagonal floor (`floor_coupling_convergence_to_synchrony`), via the Lyapunov--Barbalat, uniform-confinement, diameter-squeeze, and analysis-core architecture of Section 2.8. The earlier open item "synchronisation under general (non-all-to-all) coupling" is therefore partially closed: the floor-coupling case is proved. What remains genuinely open is convergence under fully general coupling — sign-indefinite weights, or nonnegative weights whose off-diagonal entries lack a uniform positive floor (for example, coupling graphs with missing edges) — and convergence from initial data outside an open semicircle.

Fourth, phase-diameter non-expansion is proved (`semicircle_preserved`) through a finite-family maximum-barrier principle (`finite_max_stays_below`) rather than a Dini-derivative lemma, sidestepping the nonsmooth-analysis infrastructure that was unavailable in the local Mathlib context.

Genuinely open directions remain: the fully general (non-floor or sign-indefinite) coupling and non-semicircle initial data just described, and the projected dynamics of the companion model. The companion Hebbian Max-Cut model includes projection onto a constrained coupling set. Formalising projected constrained dynamics would require tangent-cone, normal-cone, variational-inequality, and KKT machinery beyond the current file set.

Separately, the Hebbian phase-plus-weight descent connects naturally to associative-memory dynamics. Reading the adaptive weights $W$ as a learned coupling makes a synchronised phase configuration an attractor selected by the weight field — the same mechanism that underlies Hopfield associative memory and its statistical-mechanics storage-capacity analysis (Amit, Gutfreund & Sompolinsky, 1985). The modern continuous-state Hopfield network, and its established equivalence to transformer attention (Ramsauer et al., 2021), suggests a route from the present finite-$N$ descent identities toward formal retrieval- and capacity-level guarantees for attention-like dynamics. Formalising the storage-capacity and retrieval-stability side of this picture is a natural, if substantial, extension and is not attempted here.

Finally, the development suggests possible Mathlib contributions: reusable lemmas for coordinate derivatives through `Function.update`, finite-dimensional gradient notation over `Fin N`, and templates for differentiating nested finite sums of trigonometric expressions.

## 7. Conclusion

`kuramoto-lean` is a Lean 4 foundation for finite-$N$ Kuramoto and Hebbian phase-plus-weight dynamics. It formalises order-parameter boundedness, uniform and weighted gradient identities, contraction sign facts, Lyapunov descent identities, Hebbian weight and phase gradient identities, and a small witness-geometry force-asymmetry result. On top of this algebraic core, a frontier layer proves ODE existence and uniqueness, Lyapunov stability along trajectories, phase-diameter non-expansion, and convergence-to-synchrony theorems: from any open-semicircle initial condition the order-parameter norm tends to one, for all-to-all coupling and, via the floor-coupling generalisation, for any symmetric coupling matrix with a uniform positive off-diagonal floor. The discrete layer adds fixed-step confinement and, for at least three oscillators under its positive-floor and step-size hypotheses, geometric convergence of the phase diameter to zero. The entire library has 39 public theorem declarations under the source convention stated in Section 2; it is machine-checked sorry-free, with no project-defined axioms and committed headline transcripts reporting footprint `{propext, Classical.choice, Quot.sound}`. The companion `flywheel-universe` project supplies the experimental and modelling context; this library supplies the proof spine. More broadly, the project demonstrates that AI-assisted Lean development can produce clean, reproducible artifacts rapidly when paired with strict API verification, scoped theorem targets, and honest boundaries around what has and has not been proved.

## References and Links

- `kuramoto-lean` repository: <https://github.com/velvetmonkey/kuramoto-lean>
- Paper DOI: <https://doi.org/10.5281/zenodo.20468619>
- Paper record: <https://zenodo.org/records/20468619>
- Companion `flywheel-universe` repository: <https://github.com/velvetmonkey/flywheel-universe>
- Companion Max-Cut paper record: <https://doi.org/10.5281/zenodo.20469680>
- Live Hebbian Kuramoto demo: <https://velvetmonkey.github.io/flywheel-universe/>
- Lean theorem prover: <https://lean-lang.org/>
- Mathlib: <https://github.com/leanprover-community/mathlib4>
- ATLAS Lean repository: <https://github.com/facebookresearch/atlas-lean>
- `taejun-song/kuramoto-lean`: <https://github.com/taejun-song/kuramoto-lean>

### Cited works

- Amit, D. J., Gutfreund, H., & Sompolinsky, H. (1985). Spin-glass models of neural networks. *Physical Review A*, 32(2), 1007–1018. <https://doi.org/10.1103/PhysRevA.32.1007>
- Ramsauer, H., Schäfl, B., Lehner, J., Seidl, P., Widrich, M., Adler, T., Gruber, L., Holzleitner, M., Pavlović, M., Sandve, G. K., Greiff, V., Kreil, D., Kopp, M., Klambauer, G., Brandstetter, J., & Hochreiter, S. (2021). Hopfield Networks is All You Need. *International Conference on Learning Representations (ICLR)*. <https://arxiv.org/abs/2008.02217>
