/-
  HVFalse/Proofs/Prop8StepE.lean - Prop. 8 (paper l.455), step (e): "2 sin(x/2) ≥ 0.99 x there"
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Used in the paper for 0 < x < x_0 ≤ e^{-1500}; Lean proves it on [0, 1/10], which contains that range.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace P18.Prop8StepE

/-- Proof of Prop. 8, step (e): `2 sin(x/2) ≥ 0.99 x` for `0 ≤ x ≤ 1/10`. From `sin y > y - y³/6` (`y > 0`) at
`y = x/2`: `2 sin(x/2) > x - x³/24 ≥ 0.99 x`, as `x² ≤ 1/100`. -/
theorem two_sin_half_ge : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 10), 99 / 100 * x ≤ 2 * Real.sin (x / 2) := by
  rintro x ⟨hx0, hx1⟩
  rcases hx0.lt_or_eq with hpos | rfl
  · have h := Real.sin_gt_sub_cube (x := x / 2) (by positivity)
    have hx2 : x ^ 2 ≤ 1 / 100 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx2 hpos.le]
  · simp

end P18.Prop8StepE
