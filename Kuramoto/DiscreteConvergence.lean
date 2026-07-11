/- SPDX-License-Identifier: MIT -/

import Kuramoto.Discrete

/-!
# Discrete Kuramoto convergence: geometric contraction of the skew to zero

The named residual of the fleet-clock brick (`Kuramoto/Discrete.lean`, which proved the skew is
non-increasing and stays `< π`). Here `discreteFlow` does not merely confine the skew — it
**contracts it to zero geometrically**: `diameter(k+1) ≤ (1−δ)·diameter k` with `δ` a positive
constant, hence `diameter → 0`.

## The idea (state-dependent averaging + Dobrushin)

Writing `sin x = sinc x · x`, one discrete step is a **stochastic averaging** `θ(k+1) = P(θ)·θ`
(`Pmat`): rows sum to `1`; off-diagonal `≥ 0` (`sinc > 0` on `(−π,π)`); diagonal `≥ 0` **exactly
by the step bound** `h·K·rowSum ≤ 1` (since `sinc ≤ 1`). The floor makes every off-diagonal
`P_ij ≥ α := h·K·w_min·sinc(D₀) > 0`, a **constant** (because `diameter` never grows, so
`sinc(θ_j−θ_i) ≥ sinc(D₀)`). The **Dobrushin ergodicity coefficient** then contracts the
diameter: `diameter(k+1) ≤ (1 − (N−2)α)·diameter k`. This dissolves both barriers the continuous
proof left open — the changing argmax (Dobrushin bounds all pairs at once) and any Barbalat-style
summability (`δ` is a constant, so convergence is geometric).

## Honest scope

Requires `N ≥ 3` and `0 < h`. At `N = 2` the same non-strict step bound admits a boundary
**swap** `(m,M) → (m+sin D, M−sin D)`, diameter `≈ D` — no contraction; `N ≥ 3`'s extra nodes
break the oscillation. `h = 0` is the trivial no-op. Both are genuine, named edges: the factor
`δ = (N−2)·h·K·w_min·sinc(D₀)` is `0` in exactly those cases.
-/

namespace Kuramoto

open Finset Real

variable {N : ℕ}

theorem diameter_nonneg [NeZero N] (θ : Fin N → ℝ) : 0 ≤ diameter θ := by
  unfold diameter
  have h1 : phaseMin θ ≤ θ (Classical.arbitrary (Fin N)) := Finset.inf'_le θ (mem_univ _)
  have h2 : θ (Classical.arbitrary (Fin N)) ≤ phaseMax θ := Finset.le_sup' θ (mem_univ _)
  linarith

/-! ### The two engine lemmas (see module doc) -/

/-- Sinc is bounded below by its value at the diameter: chord bound from concavity of `sin`. -/
theorem sinc_lower {D y : ℝ} (hD : 0 < D) (hDpi : D < π) (hy0 : 0 ≤ y) (hyD : y ≤ D) :
    Real.sinc D ≤ Real.sinc y := by
  rcases eq_or_lt_of_le hy0 with hy | hy
  · rw [← hy, Real.sinc_zero]; exact Real.sinc_le_one D
  · have hDne : D ≠ 0 := ne_of_gt hD
    have hyne : y ≠ 0 := ne_of_gt hy
    have hconc := strictConcaveOn_sin_Icc.concaveOn
    have h0 : (0:ℝ) ∈ Set.Icc 0 π := ⟨le_rfl, Real.pi_pos.le⟩
    have hDmem : D ∈ Set.Icc (0:ℝ) π := ⟨hD.le, hDpi.le⟩
    have hb : (0:ℝ) ≤ y / D := div_nonneg hy0 hD.le
    have ha : (0:ℝ) ≤ 1 - y / D := by
      have : y / D ≤ 1 := (div_le_one hD).mpr hyD; linarith
    have hch := hconc.2 h0 hDmem ha hb (by ring)
    simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add, mul_zero] at hch
    have hxeq : y / D * D = y := by field_simp
    rw [hxeq] at hch
    -- hch : y / D * sin D ≤ sin y
    have cross : Real.sin D * y ≤ Real.sin y * D := by
      have hm := mul_le_mul_of_nonneg_right hch hD.le
      have hyD : y / D * Real.sin D * D = Real.sin D * y := by field_simp
      rw [hyD] at hm; linarith
    rw [Real.sinc_of_ne_zero (ne_of_gt hD), Real.sinc_of_ne_zero (ne_of_gt hy),
      div_le_iff₀ hD, div_mul_eq_mul_div, le_div_iff₀ hy]
    exact cross

/-- `sinc(x) ≥ sinc(D₀)` whenever `|x| ≤ D₀` (either sign, via `sinc` evenness). -/
theorem sinc_ge_of_gap {D₀ x : ℝ} (hD0 : 0 < D₀) (hpi : D₀ < π) (hx : |x| ≤ D₀) :
    Real.sinc D₀ ≤ Real.sinc x := by
  have hev : Real.sinc x = Real.sinc |x| := by
    rcases abs_choice x with h | h
    · rw [h]
    · rw [h, Real.sinc_neg]
  rw [hev]; exact sinc_lower hD0 hpi (abs_nonneg x) hx

/-- Dobrushin pairwise contraction: for a stochastic matrix whose off-diagonal entries are all
`≥ α`, every pair of averaged coordinates differs by at most `(1 − (N−2)α)` times the spread. -/
theorem dobrushin_pair (hN : 3 ≤ N) (θ : Fin N → ℝ) (P : Fin N → Fin N → ℝ)
    (hrow : ∀ i, ∑ j, P i j = 1) (hnn : ∀ i j, 0 ≤ P i j)
    (hoff : ∀ i j, i ≠ j → α ≤ P i j)
    (i l : Fin N) (hil : i ≠ l)
    (m M : ℝ) (hm : ∀ j, m ≤ θ j) (hMx : ∀ j, θ j ≤ M) :
    (∑ j, P i j * θ j) - (∑ j, P l j * θ j) ≤ (1 - ((N:ℝ) - 2) * α) * (M - m) := by
  have hD : 0 ≤ M - m := by have := hm i; have := hMx i; linarith
  have hzero : ∑ j, (P i j - P l j) = 0 := by
    rw [Finset.sum_sub_distrib, hrow, hrow]; ring
  have key : (∑ j, P i j * θ j) - (∑ j, P l j * θ j) = ∑ j, (P i j - P l j) * (θ j - m) := by
    have e1 : ∑ j, (P i j - P l j) * (θ j - m)
        = ∑ j, ((P i j - P l j) * θ j - (P i j - P l j) * m) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [e1, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [key]
  have step1 : ∑ j, (P i j - P l j) * (θ j - m)
      ≤ ∑ j, max (P i j - P l j) 0 * (M - m) := by
    apply Finset.sum_le_sum; intro j _
    have hu0 : 0 ≤ θ j - m := by have := hm j; linarith
    have huD : θ j - m ≤ M - m := by have := hMx j; linarith
    exact le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hu0)
      (mul_le_mul_of_nonneg_left huD (le_max_right _ _))
  refine le_trans step1 ?_
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hD
  have hmaxmin : ∀ j, max (P i j - P l j) 0 = P i j - min (P i j) (P l j) := by
    intro j; rcases le_total (P l j) (P i j) with h | h
    · rw [max_eq_left (by linarith), min_eq_right h]
    · rw [max_eq_right (by linarith), min_eq_left h]; ring
  rw [Finset.sum_congr rfl (fun j _ => hmaxmin j), Finset.sum_sub_distrib, hrow]
  have h2card : ({i, l} : Finset (Fin N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hil),
      Finset.card_singleton]
  have hc : (univ \ {i,l} : Finset (Fin N)).card = N - 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, h2card]
  have hcard : ((univ \ {i,l} : Finset (Fin N)).card : ℝ) = (N:ℝ) - 2 := by
    rw [hc, Nat.cast_sub (by omega)]; norm_num
  have hmin_ge : ((N:ℝ) - 2) * α ≤ ∑ j, min (P i j) (P l j) := by
    calc ((N:ℝ) - 2) * α
        = ((univ \ {i,l} : Finset (Fin N)).card : ℝ) * α := by rw [hcard]
      _ = ∑ _j ∈ univ \ {i,l}, α := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ univ \ {i,l}, min (P i j) (P l j) := by
          apply Finset.sum_le_sum; intro j hj
          rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hj
          simp only [not_or] at hj
          exact le_min (hoff i j (Ne.symm hj.2.1)) (hoff l j (Ne.symm hj.2.2))
      _ ≤ ∑ j, min (P i j) (P l j) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          intro j _ _; exact le_min (hnn i j) (hnn l j)
  linarith

/-! ### The stochastic-matrix reformulation of one discrete step -/

/-- One discrete step as a state-dependent stochastic matrix: `θ(k+1) = P(θ)·θ`. -/
noncomputable def Pmat (K h : ℝ) (N : ℕ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ)
    (i j : Fin N) : ℝ :=
  if i = j then 1 - ∑ l ∈ univ.erase i, h * K * W i l * Real.sinc (θ l - θ i)
  else h * K * W i j * Real.sinc (θ j - θ i)

theorem sinc_mul_self (x : ℝ) : Real.sinc x * x = Real.sin x := by
  rcases eq_or_ne x 0 with h | h
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]; field_simp

theorem Pmat_diag (K h : ℝ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    Pmat K h N W θ i i = 1 - ∑ l ∈ univ.erase i, h * K * W i l * Real.sinc (θ l - θ i) := by
  unfold Pmat; rw [if_pos rfl]

theorem Pmat_offdiag (K h : ℝ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ) {i j : Fin N}
    (hij : i ≠ j) : Pmat K h N W θ i j = h * K * W i j * Real.sinc (θ j - θ i) := by
  unfold Pmat; rw [if_neg hij]

theorem Pmat_row_sum (K h : ℝ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    ∑ j, Pmat K h N W θ i j = 1 := by
  have herase : ∀ j ∈ univ.erase i,
      Pmat K h N W θ i j = h * K * W i j * Real.sinc (θ j - θ i) := by
    intro j hj; exact Pmat_offdiag K h W θ (Finset.ne_of_mem_erase hj).symm
  rw [← Finset.add_sum_erase univ _ (mem_univ i), Pmat_diag, Finset.sum_congr rfl herase]
  ring

/-- The reformulation is faithful: `discreteStep` equals `Pmat` applied to `θ`. -/
theorem discreteStep_eq_Pmat (K h : ℝ) (W : Fin N → Fin N → ℝ) (θ : Fin N → ℝ) (i : Fin N) :
    discreteStep K h N W θ i = ∑ j, Pmat K h N W θ i j * θ j := by
  -- (A) discreteStep in per-term form
  have hA : discreteStep K h N W θ i
      = θ i + ∑ j, h * K * W i j * Real.sin (θ j - θ i) := by
    simp only [discreteStep, weightedKuramotoF, Finset.mul_sum]
    congr 1; apply Finset.sum_congr rfl; intro j _; ring
  -- (B) the P-average in the same per-term form
  have hB : ∑ j, Pmat K h N W θ i j * θ j
      = θ i + ∑ j, h * K * W i j * Real.sin (θ j - θ i) := by
    rw [← Finset.add_sum_erase univ (fun j => Pmat K h N W θ i j * θ j) (mem_univ i),
      ← Finset.add_sum_erase univ (fun j => h * K * W i j * Real.sin (θ j - θ i)) (mem_univ i)]
    have h0 : h * K * W i i * Real.sin (θ i - θ i) = 0 := by simp
    have hd := Pmat_diag K h W θ i
    rw [hd, h0, zero_add]
    have herase : ∀ j ∈ univ.erase i, Pmat K h N W θ i j * θ j
        = h * K * W i j * Real.sin (θ j - θ i)
          + h * K * W i j * Real.sinc (θ j - θ i) * θ i := by
      intro j hj
      have hq := Pmat_offdiag K h W θ (Finset.ne_of_mem_erase hj).symm
      rw [hq]
      linear_combination (h * K * W i j) * sinc_mul_self (θ j - θ i)
    rw [Finset.sum_congr rfl herase, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  rw [hA, hB]

/-! ### The contraction factor is in `(0,1)` — the load-bearing `δ < 1` bound -/

theorem contract_factor (hN : 3 ≤ N) (K h : ℝ) (hK : 0 < K) (hh : 0 < h)
    (W : Fin N → Fin N → ℝ) (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (D₀ : ℝ) (hD0 : 0 < D₀) (hD0pi : D₀ < π)
    (hstep : ∀ i, h * K * rowSum N W i ≤ 1) :
    0 < 1 - ((N:ℝ) - 2) * (h * K * w_min * Real.sinc D₀)
      ∧ 1 - ((N:ℝ) - 2) * (h * K * w_min * Real.sinc D₀) < 1 := by
  have hi0 : Fin N := ⟨0, by omega⟩
  have hhK : (0:ℝ) ≤ h * K := by positivity
  have hsincD0_pos : 0 < Real.sinc D₀ := by
    rw [Real.sinc_of_ne_zero (ne_of_gt hD0)]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hD0 hD0pi) hD0
  have hsincD0_le : Real.sinc D₀ ≤ 1 := Real.sinc_le_one _
  have hNR : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- rowSum ≥ (N-1) w_min
  have hrs_ge : ((N:ℝ) - 1) * w_min ≤ rowSum N W hi0 := by
    rw [rowSum]
    have hcard : (univ.erase hi0).card = N - 1 := by
      rw [Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, Fintype.card_fin]
    calc ((N:ℝ) - 1) * w_min
        = ((univ.erase hi0).card : ℝ) * w_min := by rw [hcard, Nat.cast_sub (by omega)]; norm_num
      _ = ∑ _l ∈ univ.erase hi0, w_min := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ l ∈ univ.erase hi0, W hi0 l := by
          apply Finset.sum_le_sum; intro l hl
          exact hWfloor hi0 l (Finset.ne_of_mem_erase hl).symm
  -- (N-1)(hK w_min) ≤ 1
  have hNw : ((N:ℝ) - 1) * (h * K * w_min) ≤ 1 := by
    have hmul : h * K * (((N:ℝ) - 1) * w_min) ≤ h * K * rowSum N W hi0 :=
      mul_le_mul_of_nonneg_left hrs_ge hhK
    have hid2 : h * K * (((N:ℝ) - 1) * w_min) = ((N:ℝ) - 1) * (h * K * w_min) := by ring
    have := hstep hi0; linarith [hmul, hid2]
  have hαpos : 0 < h * K * w_min * Real.sinc D₀ := by positivity
  have hpos2 : (0:ℝ) < h * K * w_min := by positivity
  have hαle : h * K * w_min * Real.sinc D₀ ≤ h * K * w_min := by
    have : h * K * w_min * Real.sinc D₀ ≤ h * K * w_min * 1 :=
      mul_le_mul_of_nonneg_left hsincD0_le (by positivity)
    simpa using this
  constructor
  · -- 0 < κ : κ ≥ h K w_min > 0
    have hstep2 : ((N:ℝ) - 2) * (h * K * w_min * Real.sinc D₀)
        ≤ ((N:ℝ) - 2) * (h * K * w_min) :=
      mul_le_mul_of_nonneg_left hαle (by linarith)
    have hid : ((N:ℝ) - 1) * (h * K * w_min)
        = ((N:ℝ) - 2) * (h * K * w_min) + h * K * w_min := by ring
    linarith [hstep2, hNw, hpos2, hid]
  · -- κ < 1 : (N-2)α > 0
    have : 0 < ((N:ℝ) - 2) * (h * K * w_min * Real.sinc D₀) :=
      mul_pos (by linarith) hαpos
    linarith

/-! ### Per-step geometric contraction -/

/-- **Per-step contraction.** With `N ≥ 3`, `0 < h`, the step bound, and the current skew within
`D₀ < π`, one discrete step shrinks the skew by the constant factor `(1 − (N−2)α)`. -/
theorem discreteStep_diam_contract [NeZero N] (hN : 3 ≤ N) (K h : ℝ) (hK : 0 < K) (hh : 0 < h)
    (W : Fin N → Fin N → ℝ) (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (θ : Fin N → ℝ) (D₀ : ℝ) (hD0 : 0 < D₀) (hD0pi : D₀ < π) (hle : diameter θ ≤ D₀)
    (hstep : ∀ i, h * K * rowSum N W i ≤ 1) :
    diameter (discreteStep K h N W θ)
      ≤ (1 - ((N:ℝ) - 2) * (h * K * w_min * Real.sinc D₀)) * diameter θ := by
  set α := h * K * w_min * Real.sinc D₀ with hαdef
  set P := Pmat K h N W θ with hPdef
  have hhK : (0:ℝ) ≤ h * K := by positivity
  have hsincD0_pos : 0 < Real.sinc D₀ := by
    rw [Real.sinc_of_ne_zero (ne_of_gt hD0)]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi hD0 hD0pi) hD0
  have hα_pos : 0 < α := by rw [hαdef]; positivity
  have hWij_nn : ∀ i j, i ≠ j → 0 ≤ W i j := fun i j h => le_trans hw.le (hWfloor i j h)
  have hgap : ∀ i j, |θ j - θ i| ≤ D₀ := by
    intro i j
    have h1 : θ j ≤ phaseMax θ := Finset.le_sup' θ (mem_univ j)
    have h2 : phaseMin θ ≤ θ j := Finset.inf'_le θ (mem_univ j)
    have h3 : θ i ≤ phaseMax θ := Finset.le_sup' θ (mem_univ i)
    have h4 : phaseMin θ ≤ θ i := Finset.inf'_le θ (mem_univ i)
    rw [abs_le]; unfold diameter at hle; constructor <;> linarith
  have hoff : ∀ i j, i ≠ j → α ≤ P i j := by
    intro i j hij
    rw [hPdef]
    have hq := Pmat_offdiag K h W θ hij
    rw [hq]
    have hs : Real.sinc D₀ ≤ Real.sinc (θ j - θ i) := sinc_ge_of_gap hD0 hD0pi (hgap i j)
    have : h * K * w_min * Real.sinc D₀ ≤ h * K * W i j * Real.sinc (θ j - θ i) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hWfloor i j hij) hhK) hs hsincD0_pos.le
        (mul_nonneg hhK (le_trans hw.le (hWfloor i j hij)))
    simpa [hαdef] using this
  have hnn : ∀ i j, 0 ≤ P i j := by
    intro i j
    rcases eq_or_ne i j with rfl | hij
    · rw [hPdef]
      have hq := Pmat_diag K h W θ i
      rw [hq]
      have hbound : ∑ l ∈ univ.erase i, h * K * W i l * Real.sinc (θ l - θ i)
          ≤ h * K * rowSum N W i := by
        rw [rowSum, Finset.mul_sum]
        apply Finset.sum_le_sum; intro l hl
        have hWnn : 0 ≤ W i l := hWij_nn i l (Finset.ne_of_mem_erase hl).symm
        have : h * K * W i l * Real.sinc (θ l - θ i) ≤ h * K * W i l * 1 :=
          mul_le_mul_of_nonneg_left (Real.sinc_le_one _) (by positivity)
        simpa using this
      linarith [hstep i]
    · exact le_trans hα_pos.le (hoff i j hij)
  have hrow : ∀ i, ∑ j, P i j = 1 := fun i => Pmat_row_sum K h W θ i
  have hm : ∀ j, phaseMin θ ≤ θ j := fun j => Finset.inf'_le θ (mem_univ j)
  have hMx : ∀ j, θ j ≤ phaseMax θ := fun j => Finset.le_sup' θ (mem_univ j)
  have hstepP : ∀ i, discreteStep K h N W θ i = ∑ j, P i j * θ j :=
    fun i => discreteStep_eq_Pmat K h W θ i
  obtain ⟨iM, _, hiM⟩ := Finset.exists_mem_eq_sup' univ_nonempty (discreteStep K h N W θ)
  obtain ⟨im, _, him⟩ := Finset.exists_mem_eq_inf' univ_nonempty (discreteStep K h N W θ)
  have hdiam_eq : diameter (discreteStep K h N W θ)
      = (∑ j, P iM j * θ j) - (∑ j, P im j * θ j) := by
    unfold diameter phaseMax phaseMin
    rw [hiM, him, hstepP iM, hstepP im]
  rw [hdiam_eq]
  rcases eq_or_ne iM im with heq | hne
  · rw [heq, sub_self]
    have hκ := (contract_factor hN K h hK hh W w_min hw hWfloor D₀ hD0 hD0pi hstep).1
    have hd := diameter_nonneg θ
    have : 0 ≤ (1 - ((N:ℝ) - 2) * α) * diameter θ := mul_nonneg hκ.le hd
    linarith
  · have hdob := dobrushin_pair hN θ P hrow hnn hoff iM im hne
      (phaseMin θ) (phaseMax θ) hm hMx
    calc (∑ j, P iM j * θ j) - (∑ j, P im j * θ j)
        ≤ (1 - ((N:ℝ) - 2) * α) * (phaseMax θ - phaseMin θ) := hdob
      _ = (1 - ((N:ℝ) - 2) * α) * diameter θ := by unfold diameter; ring

/-! ### Geometric convergence to zero skew (the CLAIM) -/

/-- **Headline — the fleet clock converges.** With `N ≥ 3`, `0 < h`, the step bound, and a
half-circle start, the phase skew tends to zero: the fleet reaches a common phase, coordinator-
free. -/
theorem discreteFlow_tendsto_zero [NeZero N] (hN : 3 ≤ N) (K h : ℝ) (hK : 0 < K) (hh : 0 < h)
    (W : Fin N → Fin N → ℝ) (w_min : ℝ) (hw : 0 < w_min)
    (hWfloor : ∀ i j, i ≠ j → w_min ≤ W i j)
    (θ₀ : Fin N → ℝ) (hpi : diameter θ₀ < π)
    (hstep : ∀ i, h * K * rowSum N W i ≤ 1) :
    Filter.Tendsto (fun k => diameter (discreteFlow K h N W θ₀ k)) Filter.atTop (nhds 0) := by
  set κ := 1 - ((N:ℝ) - 2) * (h * K * w_min * Real.sinc (diameter θ₀)) with hκdef
  have hbs : ∀ k, diameter (discreteFlow K h N W θ₀ k) ≤ diameter θ₀ :=
    discreteFlow_bounded_skew K h hK hh.le W w_min hw hWfloor θ₀ hpi hstep
  have hnn : ∀ k, 0 ≤ diameter (discreteFlow K h N W θ₀ k) := fun k => diameter_nonneg _
  rcases eq_or_lt_of_le (diameter_nonneg θ₀) with h0 | hpos
  · -- synced start: everything is already zero skew
    have hz : ∀ k, diameter (discreteFlow K h N W θ₀ k) = 0 := by
      intro k; have hb := hbs k; have hn := hnn k; rw [← h0] at hb; linarith
    simpa [hz] using tendsto_const_nhds
  · -- positive skew: geometric contraction
    have hfac := contract_factor hN K h hK hh W w_min hw hWfloor (diameter θ₀) hpos hpi hstep
    have hκnn : 0 ≤ κ := hfac.1.le
    have hκlt : κ < 1 := hfac.2
    have hgeom : ∀ k, diameter (discreteFlow K h N W θ₀ k) ≤ κ ^ k * diameter θ₀ := by
      intro k
      induction k with
      | zero => simp [discreteFlow]
      | succ n ih =>
        have hdn : diameter (discreteFlow K h N W θ₀ n) ≤ diameter θ₀ := hbs n
        have hcontract := discreteStep_diam_contract hN K h hK hh W w_min hw hWfloor
          (discreteFlow K h N W θ₀ n) (diameter θ₀) hpos hpi hdn hstep
        have hstepeq : discreteFlow K h N W θ₀ (n + 1)
            = discreteStep K h N W (discreteFlow K h N W θ₀ n) := by
          simp only [discreteFlow, Function.iterate_succ', Function.comp_apply]
        rw [hstepeq]
        calc diameter (discreteStep K h N W (discreteFlow K h N W θ₀ n))
            ≤ κ * diameter (discreteFlow K h N W θ₀ n) := hcontract
          _ ≤ κ * (κ ^ n * diameter θ₀) := mul_le_mul_of_nonneg_left ih hκnn
          _ = κ ^ (n + 1) * diameter θ₀ := by ring
    have htend : Filter.Tendsto (fun k => κ ^ k * diameter θ₀) Filter.atTop (nhds 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hκnn hκlt).mul_const (diameter θ₀)
      simpa using this
    exact squeeze_zero hnn hgeom htend

/-! ### Axiom-footprint gate -/

/--
info: 'Kuramoto.discreteStep_diam_contract' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms discreteStep_diam_contract

/--
info: 'Kuramoto.discreteFlow_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms discreteFlow_tendsto_zero

end Kuramoto
