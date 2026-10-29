/-
  HVFalse/Defs/Saddle.lean - the named coefficients of Prop. saddle (the paper, Prop. 5, l.323-383)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Basic

open Real

namespace P18

/-- Paper l.323: `S := sec²ϑ`, `ϑ = π/(2p)`. -/
noncomputable def Ssec (p : ℝ) : ℝ := 1 / cos (π / (2 * p)) ^ 2

/-- Paper l.323: `u = S - 1`; written as `tan²ϑ` (the paper uses `tan²ϑ = u`, l.364; equal to `S - 1` where `cos ϑ ≠ 0`). -/
noncomputable def uu (p : ℝ) : ℝ := tan (π / (2 * p)) ^ 2

/-- Paper l.323 and l.326: `a₀₂ = pK/8`, with `K = (p-1)u - 1`. -/
noncomputable def a02 (p : ℝ) : ℝ := p * K p (uu p) / 8

/-- Paper l.326: `a₂₁ = p(2-p) tan ϑ · S / 16`. -/
noncomputable def a21 (p : ℝ) : ℝ := p * (2 - p) * tan (π / (2 * p)) * Ssec p / 16

/-- Paper l.325: the valley is `t = π/p - (a₂₁/(2a₀₂)) y²`; this is the coefficient `a₂₁/(2a₀₂)`. -/
noncomputable def valleyC (p : ℝ) : ℝ := a21 p / (2 * a02 p)

/-- Paper l.326: `Q₄(p) = -pSuH/(384K)` (Lean name `Acoef`). -/
noncomputable def Acoef (p : ℝ) : ℝ := -(p * Ssec p * uu p * H p (uu p)) / (384 * K p (uu p))

end P18
