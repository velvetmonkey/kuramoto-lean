import Mathlib
import Kuramoto.Weighted
import Kuramoto.Contraction
import Kuramoto.OrderParameter
import Kuramoto.GradientFlow

/-!
# Kuramoto Frontier: ODE Solutions, Lyapunov Stability, and Synchronisation

This file extends the Kuramoto oscillator library with results on:
1. ODE existence and uniqueness (the vector field is smooth, hence locally Lipschitz)
2. Lyapunov stability along trajectories
3. Local synchronisation under the semicircle condition
4. Phase diameter non-expansion
5. Convergence to synchrony

We build on the algebraic identities proved in `Weighted.lean`, `Contraction.lean`,
and `GradientFlow.lean`.
-/

open Real Finset

noncomputable section

/-! ## Target 1: Smoothness of the Kuramoto vector field and ODE existence -/

/-- The Kuramoto vector field as a function `(Fin N → ℝ) → (Fin N → ℝ)`. -/
def kuramotoVectorField (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  fun θ i => weightedKuramotoF K N W i θ

/-
The Kuramoto vector field is smooth (infinitely differentiable).
-/
theorem kuramotoVectorField_contDiff (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    ContDiff ℝ ⊤ (kuramotoVectorField K N W) := by
      apply_rules [ ContDiff.mul, ContDiff.sum, contDiff_const, contDiff_apply ];
      fun_prop

/-
The Kuramoto vector field is locally Lipschitz at every point.
-/
theorem kuramotoVectorField_locallyLipschitz (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) :
    ∀ θ₀ : Fin N → ℝ, ∃ (ε : ℝ) (_ : 0 < ε) (L : NNReal),
      LipschitzOnWith L (kuramotoVectorField K N W) (Metric.ball θ₀ ε) := by
  -- � Apply� the fact that a C^1 function on a finite-dimensional space is locally Lipschitz.
  have h_lipschitz : ∀ θ₀ : (Fin N) → ℝ, ∃ ε > 0, ∃ L, LipschitzOnWith L (kuramotoVectorField K N W) (Metric.ball θ₀ ε) := by
    intro θ₀
    have h_cont_diff : ContDiff ℝ 1 (kuramotoVectorField K N W) := by
      exact ContDiff.of_le ( kuramotoVectorField_contDiff K N W ) ( by norm_num )
    have h_lipschitz : ∃ ε > 0, ∃ L, ∀ x ∈ Metric.ball θ₀ ε, ∀ y ∈ Metric.ball θ₀ ε, ‖kuramotoVectorField K N W x - kuramotoVectorField K N W y‖ ≤ L * ‖x - y‖ := by
      have h_lipschitz : ∃ ε > 0, ∃ L, ∀ x ∈ Metric.ball θ₀ ε, ‖fderiv ℝ (kuramotoVectorField K N W) x‖ ≤ L := by
        have := h_cont_diff.continuous_fderiv;
        exact ⟨ 1, zero_lt_one, _, fun x hx => le_csSup ( IsCompact.bddAbove <| isCompact_closedBall θ₀ 1 |> IsCompact.image <| continuous_norm.comp <| this one_ne_zero ) <| Set.mem_image_of_mem _ <| Metric.mem_closedBall.mpr <| le_of_lt hx ⟩;
      obtain ⟨ ε, ε_pos, L, hL ⟩ := h_lipschitz;
      use ε, ε_pos, L;
      intro x hx y hy;
      have := @Convex.norm_image_sub_le_of_norm_fderiv_le;
      simpa only [ norm_sub_rev ] using this ( fun z hz => h_cont_diff.contDiffAt.differentiableAt ( by norm_num ) ) hL ( convex_ball θ₀ ε ) hx hy;
    obtain ⟨ ε, hε, L, hL ⟩ := h_lipschitz;
    exact ⟨ ε, hε, ⟨ L.toNNReal, by simpa [ lipschitzOnWith_iff_norm_sub_le ] using fun x hx y hy => le_trans ( hL x hx y hy ) ( mul_le_mul_of_nonneg_right ( le_max_left _ _ ) ( norm_nonneg _ ) ) ⟩ ⟩;
  grind +qlia

/-
ODE existence for the Kuramoto system: for any initial condition θ₀,
    there exist ε > 0 and a local solution θ : ℝ → (Fin N → ℝ) defined on (-ε, ε)
    satisfying dθ/dt = F(θ) and θ(0) = θ₀.
    Follows from Picard–Lindelöf since the vector field is C¹.
-/
theorem kuramoto_ode_exists (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ₀ : Fin N → ℝ) :
    ∃ (θ : ℝ → Fin N → ℝ),
      θ 0 = θ₀ ∧
      ∃ (ε : ℝ) (_ : 0 < ε),
        ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t := by
          have h_cont_diff : ContDiff ℝ 1 (kuramotoVectorField K N W) := by
            exact ContDiff.of_le ( kuramotoVectorField_contDiff K N W ) ( by norm_num );
          have := @ContDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀;
          simpa using this ( h_cont_diff.contDiffAt ) 0

/-
ODE forward uniqueness: any two solutions to the Kuramoto ODE with the same initial
    condition agree on a forward interval [0, T]. Uses `ODE_solution_unique` (Gronwall).
-/
theorem kuramoto_ode_unique (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ)
    (θ θ' : ℝ → Fin N → ℝ) {T : ℝ} (_hT : 0 ≤ T)
    (hinit : θ 0 = θ' 0)
    (hf : ContinuousOn θ (Set.Icc 0 T))
    (hf' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt θ
      (kuramotoVectorField K N W (θ t)) (Set.Ici t) t)
    (hg : ContinuousOn θ' (Set.Icc 0 T))
    (hg' : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt θ'
      (kuramotoVectorField K N W (θ' t)) (Set.Ici t) t)
    (hLip : ∃ (M : NNReal), LipschitzWith M (kuramotoVectorField K N W)) :
    Set.EqOn θ θ' (Set.Icc 0 T) := by
      -- Apply the Picard-Lindel �ö�f theorem to conclude that the solutions are equal.
      have picard_lindelof : ∀ {f g : ℝ → (Fin N → ℝ)}, ContinuousOn f (Set.Icc 0 T) → ContinuousOn g (Set.Icc 0 T) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt f (kuramotoVectorField K N W (f t)) (Set.Ici t) t) → (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt g (kuramotoVectorField K N W (g t)) (Set.Ici t) t) → f 0 = g 0 → Set.EqOn f g (Set.Icc 0 T) := by
        intros f g hf hg hf' hg' hinit
        have := @ODE_solution_unique;
        exact this ( fun t => hLip.choose_spec ) hf hf' hg hg' hinit;
      exact picard_lindelof hf hg hf' hg' hinit

/-! ## Target 2: Lyapunov stability along trajectories -/

/-
The derivative of V along the Kuramoto ODE is the sum of F_i * (∂V/∂θ_i),
    which equals -∑ F_i² ≤ 0 by the gradient identity.
-/
theorem lyapunov_derivative_eq
    (K : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i, weightedKuramotoF K N W i θ *
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) =
    -(∑ i, weightedKuramotoF K N W i θ ^ 2) := by
      rw [ ← Finset.sum_neg_distrib ];
      exact Finset.sum_congr rfl fun i _ => by rw [ weighted_gradient_identity K N W hW θ i ] ; ring;

/-
The Lyapunov derivative is non-positive: d/dt V(θ) ≤ 0 along the gradient flow.
-/
theorem lyapunov_derivative_nonpos
    (K : ℝ) (hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (θ : Fin N → ℝ) :
    ∑ i, weightedKuramotoF K N W i θ *
      deriv (fun x => weightedKuramotoV K N W (Function.update θ i x)) (θ i) ≤ 0 := by
        apply weighted_lyapunov_descent K hK N W hW θ

/-
The Lyapunov function V(θ(t)) has non-positive time derivative along ODE solutions
    when W is symmetric and K > 0.
    The chain rule gives d/dt V(θ(t)) = ∑ᵢ Fᵢ(θ) · (∂V/∂θᵢ)(θ),
    which is ≤ 0 by `weighted_lyapunov_descent`.
-/
theorem lyapunov_nonincreasing_along_trajectory
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t) :
    ∀ t, HasDerivAt (fun s => weightedKuramotoV K N W (θ s))
      (∑ i, weightedKuramotoF K N W i (θ t) *
        deriv (fun x => weightedKuramotoV K N W (Function.update (θ t) i x)) ((θ t) i)) t := by
  intros t
  have h_diff : DifferentiableAt ℝ (fun s => weightedKuramotoV K N W s) (θ t) := by
    apply_rules [ DifferentiableAt.neg, DifferentiableAt.const_mul, DifferentiableAt.sum, DifferentiableAt.cos, differentiableAt_id, differentiableAt_const ];
    fun_prop;
  convert HasFDerivAt.comp_hasDerivAt t ( h_diff.hasFDerivAt ) ( hsol t ) using 1;
  have h_fderiv : ∀ i, deriv (fun x => weightedKuramotoV K N W (Function.update (θ t) i x)) (θ t i) = (fderiv ℝ (fun s => weightedKuramotoV K N W s) (θ t)) (fun j => if j = i then 1 else 0) := by
    intro i; rw [ deriv ] ;
    rw [ show ( fun x => weightedKuramotoV K N W ( Function.update ( θ t ) i x ) ) = ( fun s => weightedKuramotoV K N W s ) ∘ ( fun x => Function.update ( θ t ) i x ) by ext; rfl, fderiv_comp ] <;> norm_num [ h_diff ];
    · rw [ deriv_pi ] <;> norm_num [ Function.update_apply ];
      · exact congr_arg _ ( funext fun j => by aesop );
      · exact fun j => by split_ifs <;> norm_num;
    · intro j; by_cases hj : j = i <;> simp +decide [ hj, Function.update_apply ] ;
  rw [ show kuramotoVectorField K N W ( θ t ) = ∑ i, ( weightedKuramotoF K N W i ( θ t ) ) • ( fun j => if j = i then 1 else 0 : Fin N → ℝ ) from ?_ ];
  · rw [ map_sum, Finset.sum_congr rfl ] ; intros ; aesop;
  · ext i; simp +decide [ kuramotoVectorField ] ;

/-! ## Target 3: Local synchronisation under the semicircle condition -/

/-
Key algebraic step: for any pair (i,j) with uniform coupling (W i k = W j k)
    and non-negative symmetric weights, the relative velocity F_i - F_j can be expressed
    as a negative prefactor times a weighted cosine sum. When all phases lie within
    an open semicircle, the pair achieving the phase DIAMETER (max minus min) has
    all cosine contributions non-negative.
-/
theorem semicircle_extremal_contraction
    (K : ℝ) (_hK : 0 < K) (N : ℕ) (_hN : 0 < N)
    (W : Fin N → Fin N → ℝ) (_hW : ∀ i j, W i j = W j i)
    (hWnn : ∀ i j, 0 ≤ W i j)
    (θ : Fin N → ℝ) (i j : Fin N) (_hij : i ≠ j)
    (_hWij : 0 < W i j)
    (hWeq : ∀ k, W i k = W j k)
    (hmax : ∀ k, θ k ≤ θ i)   -- i achieves the maximum phase
    (hmin : ∀ k, θ j ≤ θ k)   -- j achieves the minimum phase
    (hgap : θ i - θ j < Real.pi) :
    weightedKuramotoF K N W i θ - weightedKuramotoF K N W j θ ≤ 0 := by
      unfold weightedKuramotoF; simp +decide [ *, Finset.mul_sum _ _ _ ] ; ring_nf;
      refine Finset.sum_le_sum fun k _ => ?_ ; simp +decide [ *, mul_assoc ] ; ring_nf ; (
      exact mul_nonpos_of_nonneg_of_nonpos ( hWnn _ _ ) ( Real.sin_nonpos_of_nonpos_of_neg_pi_le ( by linarith [ hmax k, hmin k ] ) ( by linarith [ hmax k, hmin k ] ) ) |> le_trans <| mul_nonneg ( hWnn _ _ ) ( Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith [ hmax k, hmin k ] ) ( by linarith [ hmax k, hmin k ] ) ));

/-
Helper: sin is non-negative on [0, π]. Under the extremal condition,
    each sin(θ_k - θ_j) ≥ 0 and sin(θ_i - θ_k) ≥ 0.
-/
lemma sin_nonneg_of_phase_between
    (θ : Fin N → ℝ) (i j k : Fin N)
    (hmax : θ k ≤ θ i) (hmin : θ j ≤ θ k)
    (hgap : θ i - θ j < Real.pi) :
    0 ≤ Real.sin (θ k - θ j) ∧ 0 ≤ Real.sin (θ i - θ k) := by
      constructor <;> exact Real.sin_nonneg_of_nonneg_of_le_pi ( by linarith ) ( by linarith )

/-! ## Target 4: Phase diameter non-expansion -/

/-
The time derivative of the extremal phase gap (max minus min) is non-positive
    at any time when the semicircle condition holds.
    This is the infinitesimal version of phase diameter non-expansion.
    Combined with the semicircle preservation (which would require a comparison
    argument not available in Mathlib), this would give the full non-expansion result.

    Note: Mathlib lacks Dini-type lemmas for differentiating the max of a finite set
    of smooth functions, so we prove the weaker pointwise result using the
    extremal contraction theorem.
-/
theorem extremal_gap_derivative_nonpos
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 0 < N)
    (W : Fin N → Fin N → ℝ) (hW : ∀ i j, W i j = W j i)
    (hWnn : ∀ i j, 0 ≤ W i j)
    (hWeq : ∀ i j k, W i k = W j k)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (t : ℝ) (i j : Fin N) (hij : i ≠ j)
    (hWij : 0 < W i j)
    (hmax : ∀ k, θ t k ≤ θ t i)   -- i has max phase at time t
    (hmin : ∀ k, θ t j ≤ θ t k)   -- j has min phase at time t
    (hgap : θ t i - θ t j < Real.pi) :
    HasDerivAt (fun s => θ s i - θ s j)
      (weightedKuramotoF K N W i (θ t) - weightedKuramotoF K N W j (θ t)) t ∧
    weightedKuramotoF K N W i (θ t) - weightedKuramotoF K N W j (θ t) ≤ 0 := by
      constructor;
      · convert HasDerivAt.sub ( hasDerivAt_pi.1 ( hsol t ) i ) ( hasDerivAt_pi.1 ( hsol t ) j ) using 1;
      · apply_rules [ semicircle_extremal_contraction ]

/-! ## Target 5: Convergence to synchrony -/

/-
At full synchrony (θ i = θ j for all i, j), the order parameter norm equals 1.
-/
theorem kuramotoR_norm_eq_one_at_synchrony
    (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ)
    (hsync : ∀ i j : Fin N, θ i = θ j) :
    ‖kuramotoR N θ‖ = 1 := by
      unfold kuramotoR; norm_num [ ← hsync ⟨ 0, hN ⟩ ] ;
      linarith

/-
The Lyapunov function V(θ) is bounded below by -(K/2) * N²
    when 0 ≤ W_{ij} ≤ 1.
-/
theorem weightedKuramotoV_bounded_below
    (K : ℝ) (hK : 0 < K) (N : ℕ)
    (W : Fin N → Fin N → ℝ) (hWnn : ∀ i j, 0 ≤ W i j) (hWle : ∀ i j, W i j ≤ 1)
    (θ : Fin N → ℝ) :
    -(K / 2) * (N : ℝ) ^ 2 ≤ weightedKuramotoV K N W θ := by
      exact mul_le_mul_of_nonpos_left ( le_trans ( Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => show W i j * Real.cos ( θ j - θ i ) ≤ 1 by nlinarith [ hWnn i j, hWle i j, Real.cos_le_one ( θ j - θ i ) ] ) ( by norm_num; nlinarith ) ) ( by linarith )

/-- Full convergence to synchrony under all-to-all coupling, K > 0, and
    initial phases in an open semicircle.

    NOTE: The full proof requires LaSalle’s invariance principle or Barbalat’s lemma,
    neither of which is currently available in Mathlib (as of v4.28.0).
    The proof strategy would be:
    1. V(θ(t)) is non-increasing and bounded below → V converges.
    2. By Barbalat’s lemma, d/dt V → 0 as t → ∞.
    3. Since d/dt V = -∑ F_i², this gives F_i → 0 for all i.
    4. F_i = 0 for all i together with the semicircle condition implies synchrony.

    What IS proved above:
    • `lyapunov_derivative_eq`: d/dt V = -∑ F_i²
    • `lyapunov_nonincreasing_along_trajectory`: V has non-positive derivative along solutions
    • `extremal_gap_derivative_nonpos`: the extremal gap contracts
    • `kuramotoR_norm_eq_one_at_synchrony`: at synchrony, ‖R‖ = 1
-/
theorem allToAll_convergence_to_synchrony
    (K : ℝ) (hK : 0 < K) (N : ℕ) (hN : 2 ≤ N)
    (W : Fin N → Fin N → ℝ) (hWdiag : ∀ i, W i i = 0)
    (hWoff : ∀ i j, i ≠ j → W i j = 1)
    (θ : ℝ → Fin N → ℝ)
    (hsol : ∀ t, HasDerivAt θ (kuramotoVectorField K N W (θ t)) t)
    (hsemi : ∀ a b : Fin N, |θ 0 a - θ 0 b| < Real.pi) :
    Filter.Tendsto (fun t => ‖kuramotoR N (θ t)‖) Filter.atTop (nhds 1) := by
  sorry

end