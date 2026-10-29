/-
  HVFalse/Defs/PotentialC.lean - upper regularization and "locally uniformly bounded above" on ℂ
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Used by the paper's own proof (l.289-304) that the largest subharmonic minorant V of a q-homogeneous M is
  q-homogeneous, which replaces HKV2003's p.244 Remark. Values in EReal (a complete lattice: no junk values here).
-/
import Mathlib

namespace P18

/-- Demailly §4.C.3, p. 38, on ℂ: the upper semicontinuous regularization `u⋆(z) = lim_{ε→0} sup_{B(z,ε)} u`. -/
noncomputable def uscRegC (u : ℂ → EReal) (z : ℂ) : EReal :=
  ⨅ ε : {ε : ℝ // 0 < ε}, ⨆ y ∈ Metric.ball z (ε : ℝ), u y

/-- "Locally uniformly bounded above" (Demailly §4.C.3) on ℂ: every point has a ball and a real bound valid for every member
of the family. -/
def LocUnifBddAboveC {ι : Type} (u : ι → ℂ → EReal) : Prop :=
  ∀ z : ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ (i : ι) (y : ℂ), y ∈ Metric.ball z ε → u i y ≤ (M : EReal)

end P18
