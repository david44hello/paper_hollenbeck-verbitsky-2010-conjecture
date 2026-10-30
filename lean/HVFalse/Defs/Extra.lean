/-
  HVFalse/Defs/Extra.lean - Blaschke products and feasibility in Prop. 14
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import HVFalse.Defs.Basic
import HVFalse.Defs.HV
import HVFalse.Defs.Potential

open Real

namespace P18

/-- A finite Blaschke product with zeros `zs` (each `0 < |a| < 1` is assumed where used):
`B(ζ) = ∏_a (ζ - a) / (1 - ā ζ)`. Paper l.273-274 (Lemma 3: "the Blaschke product of the zeros of g"). -/
noncomputable def blaschke (zs : List ℂ) (ζ : ℂ) : ℂ :=
  (zs.map fun a => (ζ - a) / (1 - (starRingEnd ℂ) a * ζ)).prod

/-- Paper l.620-622 (Prop. 14): `λ` is FEASIBLE if a q-subtrigonometric `φ ≤ m_λ` exists, `q = p/2`
(`φ ≤ m_λ` written pointwise: `φ(t) ≤ Γ_λ(y,t)` for all `y, t`). -/
def LamFeasible (p s lam : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, QSubtrig (p / 2) φ ∧ ∀ y t : ℝ, φ t ≤ GamLam p s lam y t

end P18
