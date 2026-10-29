/-
  HVFalse/Defs/Basic.lean - the real-variable definitions of the paper (Gamma, e, H, K, trig convexity)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

open Real

namespace P18

/-- Paper Sec. 2: `Γ(y,t) = (cosh y + cos t)^q / (1 + cos 2ϑ)^q - cosh(s y/2)^(p/s)`, with `q = p/2`, `ϑ = π/(2p)`. -/
noncomputable def Gam (p s y t : ℝ) : ℝ :=
  (cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2) - cosh (s * y / 2) ^ (p / s)

/-- Paper Sec. 2: `e(t) = tan ϑ · cos(q t)` for `|t| ≤ π`. This is the FORMULA; the paper extends it `2π`-periodically, so
statements about `ee` are the paper's statements on `|t| ≤ π` (where (2) is stated). -/
noncomputable def ee (p t : ℝ) : ℝ := tan (π / (2 * p)) * cos (p / 2 * t)

/-- `H(p,u)` of Prop. saddle. -/
def H (p u : ℝ) : ℝ := -2*(p-1)*u^2 + (3*(2-p)^2 + 2*p)*u + 3*(2-p)^2 - 2

/-- `K(p,u)` of Prop. saddle. -/
def K (p u : ℝ) : ℝ := (p-1)*u - 1

/-- q-trigonometric convexity: [HKV2003, (3.1)] for `t ↦ φ(t/q)`, multiplied out (`sin(q(y-x)) > 0` when `0 < q(y-x) < π`). -/
def TrigConvex (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  ∀ x t y : ℝ, x < t → t < y → q * (y - x) < π →
    φ t * sin (q * (y - x)) ≤ φ x * sin (q * (y - t)) + φ y * sin (q * (t - x))

end P18
