/-
  HVFalse/Defs/CitedDefs.lean - notions used only to STATE the cited axioms (HVFalse/Cited/*.lean)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import HVFalse.Defs.Potential

open Real

namespace P18

/-- HKV2003 (2.1)/(2.4): `∫₀^{2π} u(θ) dθ/2π ≥ 0` for `u` with values in `[-∞, ∞)` that is upper semicontinuous along the
circle (so bounded above; the integral lies in `[-∞, ∞)`). Written through truncations: the integral of `u` is `≥ 0` iff the
integral of every truncation `max(u, -n)` is `≥ 0` (`⇒`: `max(u,-n) ≥ u`; `⇐`: monotone convergence, the truncations decrease
to `u` and are bounded above). The factor `1/2π` is dropped (it does not change the sign). -/
def CircleIntNonneg (u : ℝ → EReal) : Prop :=
  ∀ n : ℕ, 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), trunc n (u θ)

end P18
