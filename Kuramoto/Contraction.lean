import Mathlib
import Kuramoto.GradientFlow

open Real Finset

lemma kuramoto_relative_velocity
    (K : ℝ) (θ : Fin 2 → ℝ) :
    kuramotoF K 2 0 θ - kuramotoF K 2 1 θ = -K * Real.sin (θ 0 - θ 1) := by
  unfold kuramotoF
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [sub_self, Real.sin_zero, zero_add, add_zero]
  have hsin : Real.sin (θ 1 - θ 0) = -Real.sin (θ 0 - θ 1) := by
    have harg : θ 1 - θ 0 = -(θ 0 - θ 1) := by ring
    rw [harg, Real.sin_neg]
  rw [hsin]
  ring

theorem kuramoto_pairwise_contraction
    (K : ℝ) (hK : 0 < K) (θ : Fin 2 → ℝ)
    (hgap : 0 < θ 0 - θ 1) (hpi : θ 0 - θ 1 < Real.pi) :
    kuramotoF K 2 0 θ < kuramotoF K 2 1 θ := by
  have hrel := kuramoto_relative_velocity K θ
  have hsin : 0 < Real.sin (θ 0 - θ 1) :=
    Real.sin_pos_of_pos_of_lt_pi hgap hpi
  have hneg : -K * Real.sin (θ 0 - θ 1) < 0 := by
    nlinarith [mul_pos hK hsin]
  have hsub : kuramotoF K 2 0 θ - kuramotoF K 2 1 θ < 0 := by
    rw [hrel]
    exact hneg
  linarith
