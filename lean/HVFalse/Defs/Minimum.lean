/-
  HVFalse/Defs/Minimum.lean - m(t) = inf_y Γ(y,t) and M(ζ) = |ζ|^q m(arg ζ) (the paper, l.185, l.296)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  WARNING (junk value): `⨅ y : ℝ` in ℝ is the true infimum only when the set is bounded below. For `s ≤ sec²ϑ` it is
  (C03c: the infimum is attained). For `s > sec²ϑ` `Γ` may be unbounded below and then Lean's value is 0 (meaningless).
  So use `mfun` ONLY under a hypothesis `s ≤ Ssec p`. Statements.lean never uses it: claims say `∀ y, φ t ≤ Gam p s y t`.
-/
import Mathlib
import HVFalse.Defs.Basic

open Real

namespace P18

/-- Paper l.185: `m(t) = inf_{y ∈ ℝ} Γ(y,t)` (meaningful for `s ≤ sec²ϑ` only; see the warning above). -/
noncomputable def mfun (p s t : ℝ) : ℝ := ⨅ y : ℝ, Gam p s y t

/-- Paper l.296: `M(ζ) = |ζ|^q m(arg ζ)` (at `ζ = 0`: `0^q m(0) = 0`). -/
noncomputable def Mfun (p s : ℝ) (ζ : ℂ) : ℝ := ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ)

end P18
