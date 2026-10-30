/-
  HVFalse/Proofs/PointJag.lean - Jaguzović's point (the paper): Γ - e = -1.3102·10⁻³ at (3/2, 4)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  At p = 3/2, s = 4, y = log 2, t = π/2: cosh y = 5/4, cos t = 0, 1 + cos 2ϑ = 1/2, cosh(sy/2) = cosh(log 4) = 17/8,
  q = 3/4, p/s = 3/8, e(π/2) = √3 cos(3π/8) = √3 √(2-√2)/2. True value -1.31022055·10⁻³ (mpmath, 40 digits).
  Each term is bounded by rationals through integer powers (rpow_le_of_pow_le / le_rpow_of_pow_le).
-/
import HVFalse.Proofs.Bridges

open Real

namespace P18

theorem jag_closed_form :
    Gam (3 / 2) 4 (log 2) (π / 2) - ee (3 / 2) (π / 2) =
      (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) - (17 / 8 : ℝ) ^ ((3 : ℝ) / 8) - √3 * √(2 - √2) / 2 := by
  obtain ⟨hθ, h2θ, hqt, -⟩ := angle_facts
  have h4 : (4 : ℝ) * log 2 / 2 = log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have hc2 : cosh (log 2) = 5 / 4 := by rw [cosh_log (by norm_num)]; norm_num
  have hc4 : cosh (log 4) = 17 / 8 := by rw [cosh_log (by norm_num)]; norm_num
  unfold Gam ee
  rw [hθ, h2θ, hqt, hc2, h4, hc4, cos_pi_div_two, tan_pi_div_three,
    ← div_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4 + 0) (by norm_num : (0 : ℝ) ≤ 1 + -1 / 2)]
  have hq : (3 / 2 : ℝ) / 2 = 3 / 4 := by norm_num
  have hs : (3 / 2 : ℝ) / 4 = 3 / 8 := by norm_num
  have hb : ((5 / 4 + 0 : ℝ) / (1 + -1 / 2)) = 5 / 2 := by norm_num
  rw [hq, hs, hb]
  ring

theorem jag_bounds_A :
    (1988176821 / 10 ^ 9 : ℝ) ≤ (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) ∧ (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 1988176823 / 10 ^ 9 := by
  constructor
  · have h := le_rpow_of_pow_le (x := 5 / 2) (b := 1988176821 / 10 ^ 9) (m := 3) (n := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  · have h := rpow_le_of_pow_le (x := 5 / 2) (b := 1988176823 / 10 ^ 9) (m := 3) (n := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h

theorem jag_bounds_B :
    (1326659894 / 10 ^ 9 : ℝ) ≤ (17 / 8 : ℝ) ^ ((3 : ℝ) / 8) ∧ (17 / 8 : ℝ) ^ ((3 : ℝ) / 8) ≤ 1326659895 / 10 ^ 9 := by
  constructor
  · have h := le_rpow_of_pow_le (x := 17 / 8) (b := 1326659894 / 10 ^ 9) (m := 3) (n := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  · have h := rpow_le_of_pow_le (x := 17 / 8) (b := 1326659895 / 10 ^ 9) (m := 3) (n := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h

theorem jag_bounds_C :
    (17320508075 / 10 ^ 10 : ℝ) * (7653668647 / 10 ^ 10) ≤ √3 * √(2 - √2) ∧
      √3 * √(2 - √2) ≤ (17320508076 / 10 ^ 10 : ℝ) * (7653668648 / 10 ^ 10) := by
  have l3 : (17320508075 / 10 ^ 10 : ℝ) ≤ √3 := by rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
  have u3 : √3 ≤ (17320508076 / 10 ^ 10 : ℝ) := by rw [sqrt_le_left (by norm_num)]; norm_num
  have l2 : √2 ≤ 2 - (7653668647 / 10 ^ 10 : ℝ) ^ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have u2 : 2 - (7653668648 / 10 ^ 10 : ℝ) ^ 2 ≤ √2 := by rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h22 : √2 ≤ 2 := by rw [sqrt_le_left (by norm_num)]; norm_num
  have lc : (7653668647 / 10 ^ 10 : ℝ) ≤ √(2 - √2) := by
    rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have uc : √(2 - √2) ≤ (7653668648 / 10 ^ 10 : ℝ) := by
    rw [sqrt_le_left (by norm_num)]; linarith
  exact ⟨mul_le_mul l3 lc (by norm_num) (sqrt_nonneg 3),
    mul_le_mul u3 uc (sqrt_nonneg _) (by norm_num)⟩

/-- C15a, l.410-411: Jaguzović's point `(log 2, π/2)` at `(p,s) = (3/2, 4)`: `Γ - e = -1.3102·10⁻³` to within `5·10⁻⁸`. -/
theorem jaguzovic_point :
    |Gam (3 / 2) 4 (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-13102 / 10 ^ 7)| ≤ 5 / 10 ^ 8 := by
  rw [jag_closed_form, abs_le]
  obtain ⟨hA1, hA2⟩ := jag_bounds_A
  obtain ⟨hB1, hB2⟩ := jag_bounds_B
  obtain ⟨hC1, hC2⟩ := jag_bounds_C
  constructor <;> norm_num at hA1 hA2 hB1 hB2 hC1 hC2 ⊢ <;> linarith

/-- Corollary used by C15b: Jaguzović's point is a failure point of (eq:two) inside `I`. -/
theorem jaguzovic_point_neg : Gam (3 / 2) 4 (log 2) (π / 2) - ee (3 / 2) (π / 2) < 0 := by
  have h := (abs_le.mp jaguzovic_point).2
  linarith

end P18
