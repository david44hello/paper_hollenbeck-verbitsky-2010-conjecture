/-
  HVFalse/Proofs/UMean.lean - the circle mean of the minorant E (paper Sec. 2, l.182-183)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper (l.182-183): "its mean over |ζ| = r is r^q tanϑ sin(qπ)/(qπ) > 0 = E(0)". In polar form ζ = r e^{it},
  -π < t ≤ π, arg ζ = t, so E = r^q e(t) with e(t) = tanϑ cos(qt), and the mean is
  (2π)⁻¹ ∫_{-π}^{π} r^q tanϑ cos(qt) dt = r^q tanϑ (2π)⁻¹ (2 sin(qπ)/q) = r^q tanϑ sin(qπ)/(qπ).
  It is > 0 since 0 < ϑ < π/2 and 0 < qπ < π (q = p/2 ∈ (1/2, 1)); and E(0) = 0^q e(0) = 0.
-/
import HVFalse.Defs.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Real

namespace P18.UMean

theorem integral_cos_q {q : ℝ} (hq : q ≠ 0) :
    ∫ t in (-π)..π, cos (q * t) = 2 * sin (q * π) / q := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => cos x) hq, integral_cos, mul_neg, sin_neg]
  rw [smul_eq_mul]
  field_simp
  ring

theorem U_mean {p r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hr : 0 < r) :
    (2 * π)⁻¹ * ∫ t in (-π)..π, r ^ (p / 2) * ee p t
        = r ^ (p / 2) * tan (π / (2 * p)) * sin (p / 2 * π) / (p / 2 * π) ∧
      0 < r ^ (p / 2) * tan (π / (2 * p)) * sin (p / 2 * π) / (p / 2 * π) ∧
      ‖(0 : ℂ)‖ ^ (p / 2) * ee p (Complex.arg 0) = 0 := by
  have hq : (p / 2 : ℝ) ≠ 0 := by
    have : (0 : ℝ) < p / 2 := by linarith
    exact this.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [ee]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cos_q hq]
    field_simp
  · have h1 : 0 < r ^ (p / 2) := Real.rpow_pos_of_pos hr _
    have hθ : π / (2 * p) < π / 2 := div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
    have h2 : 0 < tan (π / (2 * p)) :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (by have := Real.pi_pos; positivity) hθ
    have h3 : 0 < sin (p / 2 * π) :=
      Real.sin_pos_of_pos_of_lt_pi (by have := Real.pi_pos; nlinarith) (by nlinarith [Real.pi_pos])
    have h4 : 0 < p / 2 * π := by have := Real.pi_pos; nlinarith
    positivity
  · simp [Real.zero_rpow hq]

end P18.UMean
