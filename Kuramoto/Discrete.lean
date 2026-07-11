/- SPDX-License-Identifier: MIT -/

import Kuramoto.Weighted

/-!
# Discrete fleet-clock: bounded phase skew under a step-size condition

The "when" half of a coordination-free fleet clock. A fleet of nodes holds local phases,
gossips neighbour phases, and nudges via a **discrete (fixed-step / Euler)** Kuramoto update
of the *same* weighted vector field proved to synchronise in continuous time
(`Kuramoto.weightedKuramotoF`, `floor_coupling_convergence_to_synchrony`). We prove that,
started inside an open half-circle and stepped below an explicit step bound, the fleet keeps
its phase skew **bounded below `π` for all time, with no coordinator**.

## Continuous → discrete: what transfers and what is new

The continuous floor-coupling proof rests on two continuous-time engines — semicircle
invariance (`finite_max_stays_below`, a first-crossing `deriv < 0` argument) and Barbalat's
lemma (an interval-integral / MVT argument). **Neither ports mechanically**: a single Euler
step can overshoot the confinement, so both need an explicit small-step hypothesis. The
*algebraic* content — the sign of the coupling at the extremal nodes — does transfer, and is
what this module rebuilds discretely.

The result here is **not** a mechanical port: the continuous theorem proves exact synchrony
but gives *no rate*, so the step bound `h·K·rowSum ≤ 1` is genuinely new content, not a reused
constant. It is load-bearing — it is exactly what rules out per-step overshoot (see the
`hstep` use in `discreteStep_diam_le`); drop it and the max phase can jump past its neighbours.

## Honest scope

Proved: the phase skew (diameter = max phase − min phase) is **non-increasing** each step, hence
bounded below `π` forever — the CLAIM's "bounded skew, no coordinator", which is exactly what a
trustless TTL/epoch clock needs (clocks within a bounded window, not perfectly identical).

**Named residual (NOT proved here):** strict contraction `diameter (k+1) ≤ (1−δ)·diameter k`,
hence exact synchrony `diameter → 0`. That needs the floor to force strict decrease of the
*new* extremal pair after a step (the argmax can change) plus a discrete-Barbalat summability —
a genuinely harder rung, deliberately left as future work.

## Composition with the CRDT "what" half (documentation)

crdt-lean's Strong Eventual Consistency (`Crdt/Convergence.lean`, already proved) makes replicas
agree on *state* — the "what". This brick's bounded-skew result makes replicas agree on
*phase/epoch within a bounded window* — the "when". Together they document a coordination-free,
machine-verified fleet clock for the seal mesh under partition. This composition is narrative;
we intentionally add **no** cross-repo dependency the proof does not use.
-/

namespace Kuramoto

open Finset Real

variable {N : ℕ}

/-- One fixed-step (Euler) update of the weighted Kuramoto vector field. -/
noncomputable def discreteStep (K h : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ) :
    Fin N → ℝ :=
  fun i => θ i + h * weightedKuramotoF K N W i θ

/-- The fleet trajectory: `k` discrete steps from an initial phase assignment. -/
noncomputable def discreteFlow (K h : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (θ₀ : Fin N → ℝ) :
    ℕ → (Fin N → ℝ) :=
  fun k => (discreteStep K h N W)^[k] θ₀

/-- Off-diagonal coupling row sum `S_i = ∑_{j ≠ i} W i j` — the per-node coupling budget the
step bound constrains. -/
def rowSum (N : ℕ) (W : Fin N → Fin N → ℝ) (i : Fin N) : ℝ :=
  ∑ j ∈ univ.erase i, W i j

/-- Maximum phase across the fleet. -/
noncomputable def phaseMax [NeZero N] (θ : Fin N → ℝ) : ℝ := univ.sup' univ_nonempty θ

/-- Minimum phase across the fleet. -/
noncomputable def phaseMin [NeZero N] (θ : Fin N → ℝ) : ℝ := univ.inf' univ_nonempty θ

/-- Phase **skew**: the spread between the leading and trailing clocks. -/
noncomputable def diameter [NeZero N] (θ : Fin N → ℝ) : ℝ := phaseMax θ - phaseMin θ

/-- **The per-step invariance lemma.** Under the step bound `h·K·rowSum ≤ 1` and a
half-circle skew (`diameter θ < π`), one discrete step does not increase the skew. The step
bound is load-bearing: it is precisely what keeps every node — including a non-extremal one
that is rising — from overshooting the current maximum. -/
theorem discreteStep_diam_le [NeZero N] (K h : ℝ) (hK : 0 < K) (hh : 0 ≤ h)
    (W : Fin N → Fin N → ℝ) (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (θ : Fin N → ℝ) (hdiam : diameter θ < π)
    (hstep : ∀ i, h * K * rowSum N W i ≤ 1) :
    diameter (discreteStep K h N W θ) ≤ diameter θ := by
  -- nonnegativity of the coupling row sum
  have hrow_nn : ∀ i, 0 ≤ rowSum N W i := by
    intro i; apply Finset.sum_nonneg; intro j hj
    exact le_trans (le_of_lt hw) (hWfloor i j (Finset.ne_of_mem_erase hj).symm)
  -- the coupling sum is bounded by the room to the top / floor to the bottom
  have hinner_up : ∀ i, ∑ j, W i j * sin (θ j - θ i) ≤ rowSum N W i * (phaseMax θ - θ i) := by
    intro i
    have hi0 : W i i * sin (θ i - θ i) = 0 := by simp
    rw [← Finset.sum_erase univ (f := fun j => W i j * sin (θ j - θ i)) (a := i) hi0,
      rowSum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hWij : (0 : ℝ) ≤ W i j := le_trans (le_of_lt hw) (hWfloor i j hji)
    have hsin : sin (θ j - θ i) ≤ phaseMax θ - θ i := by
      rcases le_total 0 (θ j - θ i) with hpos | hnp
      · have h1 : sin (θ j - θ i) ≤ θ j - θ i := by
          rcases eq_or_lt_of_le hpos with he | hlt
          · rw [← he]; simp
          · exact le_of_lt (Real.sin_lt hlt)
        have h2 : θ j ≤ phaseMax θ := Finset.le_sup' θ (mem_univ j)
        linarith
      · have hbound : -π < θ j - θ i := by
          have hle : θ i - θ j ≤ diameter θ := by
            have hi_le : θ i ≤ phaseMax θ := Finset.le_sup' θ (mem_univ i)
            have lo_le : phaseMin θ ≤ θ j := Finset.inf'_le θ (mem_univ j)
            unfold diameter; linarith
          linarith
        have hs0 : sin (θ j - θ i) ≤ 0 :=
          Real.sin_nonpos_of_nonpos_of_neg_pi_le hnp (le_of_lt hbound)
        have h2 : θ i ≤ phaseMax θ := Finset.le_sup' θ (mem_univ i)
        linarith
    exact mul_le_mul_of_nonneg_left hsin hWij
  have hinner_lo : ∀ i, rowSum N W i * (phaseMin θ - θ i) ≤ ∑ j, W i j * sin (θ j - θ i) := by
    intro i
    have hi0 : W i i * sin (θ i - θ i) = 0 := by simp
    rw [← Finset.sum_erase univ (f := fun j => W i j * sin (θ j - θ i)) (a := i) hi0,
      rowSum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hji : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hWij : (0 : ℝ) ≤ W i j := le_trans (le_of_lt hw) (hWfloor i j hji)
    have hsin : phaseMin θ - θ i ≤ sin (θ j - θ i) := by
      rcases le_total (θ j - θ i) 0 with hnp | hp
      · have h1 : θ j - θ i ≤ sin (θ j - θ i) := by
          rcases eq_or_lt_of_le hnp with he | hlt
          · rw [he]; simp
          · have hy : 0 < -(θ j - θ i) := by linarith
            have := Real.sin_lt hy
            rw [Real.sin_neg] at this; linarith
        have h2 : phaseMin θ ≤ θ j := Finset.inf'_le θ (mem_univ j)
        linarith
      · have hbound : θ j - θ i ≤ π := by
          have hle : θ j - θ i ≤ diameter θ := by
            have hj_le : θ j ≤ phaseMax θ := Finset.le_sup' θ (mem_univ j)
            have lo_le : phaseMin θ ≤ θ i := Finset.inf'_le θ (mem_univ i)
            unfold diameter; linarith
          linarith
        have hs0 : 0 ≤ sin (θ j - θ i) :=
          Real.sin_nonneg_of_nonneg_of_le_pi hp hbound
        have h2 : phaseMin θ ≤ θ i := Finset.inf'_le θ (mem_univ i)
        linarith
    exact mul_le_mul_of_nonneg_left hsin hWij
  -- no node overshoots the max / undershoots the min
  have hU : ∀ i, discreteStep K h N W θ i ≤ phaseMax θ := by
    intro i
    have hi_le : θ i ≤ phaseMax θ := Finset.le_sup' θ (mem_univ i)
    have hdnn : 0 ≤ phaseMax θ - θ i := by linarith
    have hbig : h * (K * ∑ j, W i j * sin (θ j - θ i)) ≤ phaseMax θ - θ i := by
      calc h * (K * ∑ j, W i j * sin (θ j - θ i))
          ≤ h * (K * (rowSum N W i * (phaseMax θ - θ i))) := by
            apply mul_le_mul_of_nonneg_left _ hh
            exact mul_le_mul_of_nonneg_left (hinner_up i) (le_of_lt hK)
        _ = h * K * rowSum N W i * (phaseMax θ - θ i) := by ring
        _ ≤ 1 * (phaseMax θ - θ i) := mul_le_mul_of_nonneg_right (hstep i) hdnn
        _ = phaseMax θ - θ i := one_mul _
    simp only [discreteStep, weightedKuramotoF]
    linarith
  have hL : ∀ i, phaseMin θ ≤ discreteStep K h N W θ i := by
    intro i
    have lo_le : phaseMin θ ≤ θ i := Finset.inf'_le θ (mem_univ i)
    have hdnp : phaseMin θ - θ i ≤ 0 := by linarith
    have hbig : phaseMin θ - θ i ≤ h * (K * ∑ j, W i j * sin (θ j - θ i)) := by
      calc phaseMin θ - θ i
          = 1 * (phaseMin θ - θ i) := (one_mul _).symm
        _ ≤ h * K * rowSum N W i * (phaseMin θ - θ i) :=
            mul_le_mul_of_nonpos_right (hstep i) hdnp
        _ = h * (K * (rowSum N W i * (phaseMin θ - θ i))) := by ring
        _ ≤ h * (K * ∑ j, W i j * sin (θ j - θ i)) := by
            apply mul_le_mul_of_nonneg_left _ hh
            exact mul_le_mul_of_nonneg_left (hinner_lo i) (le_of_lt hK)
    simp only [discreteStep, weightedKuramotoF]
    linarith
  -- assemble: max drops (weakly), min rises (weakly), so the skew does not grow
  have hmax' : phaseMax (discreteStep K h N W θ) ≤ phaseMax θ :=
    Finset.sup'_le _ _ (fun i _ => hU i)
  have hmin' : phaseMin θ ≤ phaseMin (discreteStep K h N W θ) :=
    Finset.le_inf' _ _ (fun i _ => hL i)
  unfold diameter
  linarith

/-- **Headline — coordinator-free bounded skew.** Started inside an open half-circle and
stepped below the step bound, the fleet's phase skew never grows: it stays below `π` for all
discrete time, with no coordinator. This is the "when" half of the fleet clock. -/
theorem discreteFlow_bounded_skew [NeZero N] (K h : ℝ) (hK : 0 < K) (hh : 0 ≤ h)
    (W : Fin N → Fin N → ℝ) (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (θ₀ : Fin N → ℝ) (hdiam0 : diameter θ₀ < π)
    (hstep : ∀ i, h * K * rowSum N W i ≤ 1) :
    ∀ k, diameter (discreteFlow K h N W θ₀ k) ≤ diameter θ₀ := by
  intro k
  induction k with
  | zero => simp [discreteFlow]
  | succ n ih =>
    have hdn : diameter (discreteFlow K h N W θ₀ n) < π := lt_of_le_of_lt ih hdiam0
    have hstepeq : discreteFlow K h N W θ₀ (n + 1)
        = discreteStep K h N W (discreteFlow K h N W θ₀ n) := by
      simp only [discreteFlow, Function.iterate_succ', Function.comp_apply]
    rw [hstepeq]
    exact le_trans
      (discreteStep_diam_le K h hK hh W w_min hw hWfloor _ hdn hstep) ih

/-! ### Concrete witness — two nodes, all-to-all, step at the boundary

A minimal runnable instance: `N = 2`, unit all-to-all coupling (`W ≡ 1`, floor `w_min = 1`),
`K = h = 1` so the step bound `h·K·rowSum = 1 ≤ 1` holds at equality, initial skew `1 < π`.
The fleet's skew stays bounded for all time. -/

/-- `rowSum` of the unit all-to-all matrix on `Fin 2` is `1`. -/
theorem rowSum_ones_two (i : Fin 2) : rowSum 2 (fun _ _ => 1) i = 1 := by
  simp [rowSum, Finset.sum_const, Finset.card_erase_of_mem]

theorem fleet_clock_two_nodes_bounded_skew :
    ∀ k, diameter (discreteFlow 1 1 2 (fun _ _ => 1) ![0, 1] k)
      ≤ diameter (![0, 1] : Fin 2 → ℝ) := by
  have hdiam0 : diameter (![0, 1] : Fin 2 → ℝ) < π := by
    have hmax : phaseMax (![0, 1] : Fin 2 → ℝ) ≤ 1 :=
      Finset.sup'_le _ _ (fun i _ => by fin_cases i <;> norm_num)
    have hmin : (0 : ℝ) ≤ phaseMin (![0, 1] : Fin 2 → ℝ) :=
      Finset.le_inf' _ _ (fun i _ => by fin_cases i <;> norm_num)
    have hpi : (1 : ℝ) < π := by have := Real.pi_gt_three; linarith
    unfold diameter; linarith
  exact discreteFlow_bounded_skew 1 1 (by norm_num) (by norm_num) (fun _ _ => 1) 1 (by norm_num)
    (fun i j _ => le_refl 1) ![0, 1] hdiam0
    (fun i => by rw [rowSum_ones_two]; norm_num)

/-! ### Axiom-footprint gate

The discrete fleet-clock results sit on the standard foundational axioms only —
no `sorryAx`, no `Lean.ofReduceBool` (`native_decide`). Drift fails the build. -/

/--
info: 'Kuramoto.discreteStep_diam_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms discreteStep_diam_le

/--
info: 'Kuramoto.discreteFlow_bounded_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms discreteFlow_bounded_skew

/--
info: 'Kuramoto.fleet_clock_two_nodes_bounded_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fleet_clock_two_nodes_bounded_skew

end Kuramoto
