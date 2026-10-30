/-
  HVFalse/Proofs/Small.lean - small exact claims of the paper (C02a, C04c, C10c3, C10d, C24, C12d)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Proofs.SaddleSigns
import HVFalse.Defs.Saddle

open Real

namespace P18

/-- C02a, l.186: `|z + w̄|² = 2|zw|(cosh y + cos t)`, `y = log(|z|/|w|)`, `t = arg(zw)`. -/
theorem norm_add_conj_sq_cosh (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖z + (starRingEnd ℂ) w‖ ^ 2 = 2 * ‖z * w‖ * (cosh (log (‖z‖ / ‖w‖)) + cos (Complex.arg (z * w))) := by
  have h1 := norm_add_conj_sq z w
  have h2 := sq_add_sq_cosh ‖z‖ ‖w‖ (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  have h3 := Complex.norm_mul_cos_arg (z * w)
  rw [norm_mul] at h3 ⊢
  rw [h1, h2, ← h3]
  ring

/-- C04c, l.207: `q π/p = π/2`, so `e(±π/p) = 0`. -/
theorem ee_contact_zero {p : ℝ} (hp : 0 < p) : ee p (π / p) = 0 ∧ ee p (-(π / p)) = 0 := by
  have e1 : p / 2 * (π / p) = π / 2 := by field_simp
  have e2 : p / 2 * -(π / p) = -(π / 2) := by field_simp
  unfold ee
  rw [e1, e2, cos_neg, cos_pi_div_two]
  simp

theorem tan_half_pos {p : ℝ} (hp1 : 1 < p) : 0 < tan (π / (2 * p)) := by
  have hpi := pi_pos
  have hpos : 0 < p := by linarith
  apply tan_pos_of_pos_of_lt_pi_div_two (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem Ssec_pos {p : ℝ} (hp1 : 1 < p) : 0 < Ssec p := by
  have hpi := pi_pos
  have hpos : 0 < p := by linarith
  have hc : 0 < cos (π / (2 * p)) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / (2 * p) := by positivity
      linarith
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
  unfold Ssec
  positivity

/-- C10c3, l.340-342: `a₂₁ > 0` and `A(p) < 0` on `(4/3, 2)`. -/
theorem a21_pos_Acoef_neg {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < a21 p ∧ Acoef p < 0 := by
  have hp1' : 1 < p := by linarith
  have ht := tan_half_pos hp1'
  have hS := Ssec_pos hp1'
  have hK := K_pos hp1 hp2
  have hH := H_pos hp1 hp2
  have hu : 0 < uu p := by unfold uu; positivity
  constructor
  · unfold a21
    have : 0 < 2 - p := by linarith
    positivity
  · unfold Acoef
    rw [neg_div, neg_lt_zero]
    have : 0 < p := by linarith
    positivity

/-- C10d (a Lean-only helper): the curve coefficient `a₂₁/(2a₀₂)` is positive (`a₂₁ > 0`, l.340; `a₀₂ > 0`, l.375), so
the curve of Prop. 5 has `t < π/p`. -/
theorem valleyC_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < valleyC p := by
  have ha21 := (a21_pos_Acoef_neg hp1 hp2).1
  have hK := K_pos hp1 hp2
  have ha02 : 0 < a02 p := by
    unfold a02
    have : 0 < p := by linarith
    positivity
  unfold valleyC
  positivity

/-- C24, l.344: `A(3/2) = -3/32` (here `S = 4`, `u = 3`, `H = 1`, `K = 1/2`). -/
theorem Acoef_three_halves : Acoef (3 / 2) = -3 / 32 := by
  have e : π / (2 * (3 / 2 : ℝ)) = π / 3 := by ring
  have hS : Ssec (3 / 2) = 4 := by
    unfold Ssec; rw [e, cos_pi_div_three]; norm_num
  have hu : uu (3 / 2) = 3 := by
    unfold uu; rw [e, tan_pi_div_three, sq_sqrt (by norm_num)]
  unfold Acoef
  rw [hS, hu]
  unfold H K
  norm_num

/-- C12d, l.416, l.510: `t = π/2 ∈ int I` for `p = 3/2`, and `sec²(π/3) - 3.98 = 0.02`. -/
theorem point_location : π / 2 ∈ Set.Ioo (-(π / (3 / 2))) (π / (3 / 2)) ∧ Ssec (3 / 2) - 398 / 100 = 2 / 100 := by
  have hpi := pi_pos
  have e : π / (2 * (3 / 2 : ℝ)) = π / 3 := by ring
  refine ⟨⟨by linarith [div_pos hpi (by norm_num : (0 : ℝ) < 3 / 2)], ?_⟩, ?_⟩
  · rw [div_lt_div_iff₀ (by norm_num) (by norm_num)]; linarith
  · unfold Ssec; rw [e, cos_pi_div_three]; norm_num

end P18
