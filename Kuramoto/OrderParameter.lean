import Mathlib

open Complex Finset

-- The Kuramoto order parameter for N oscillators with phases θ : Fin N → ℝ
-- Each oscillator contributes a unit phasor exp(iθ_k)
-- Target: ‖R‖ ≤ 1 where R = (∑_k exp(iθ_k)) / N
noncomputable def kuramotoR (N : ℕ) (θ : Fin N → ℝ) : ℂ :=
  (∑ k, Complex.exp (θ k * Complex.I)) / N

theorem kuramotoR_norm_le_one (N : ℕ) (hN : 0 < N) (θ : Fin N → ℝ) :
    ‖kuramotoR N θ‖ ≤ 1 := by
  have hnorm (k : Fin N) : ‖Complex.exp (θ k * Complex.I)‖ = 1 := by
    rw [← Circle.coe_exp]
    exact Circle.norm_coe (Circle.exp (θ k))
  have hsum :
      ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖ ≤ (N : ℝ) := by
    calc
      ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖
          ≤ ∑ k : Fin N, ‖Complex.exp (θ k * Complex.I)‖ := by
            simpa using norm_sum_le (Finset.univ : Finset (Fin N))
              (fun k : Fin N => Complex.exp (θ k * Complex.I))
      _ = (N : ℝ) := by
            simp [hnorm]
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  calc
    ‖kuramotoR N θ‖
        = ‖∑ k : Fin N, Complex.exp (θ k * Complex.I)‖ / (N : ℝ) := by
          simp [kuramotoR]
    _ ≤ (N : ℝ) / (N : ℝ) := by
          exact div_le_div_of_nonneg_right hsum hNreal.le
    _ = 1 := div_self hNreal.ne'
