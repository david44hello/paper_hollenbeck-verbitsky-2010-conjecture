/-
  HVFalse/Defs/Explicit.lean - the explicit counterexample of Prop. explicit (the paper, Prop. 8, l.441-487); Hardy-space bound
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib

open Real

namespace P18.Explicit

/-- l.442: `t₂ = 179/100`. -/
noncomputable def tS : ℝ := 179 / 100
/-- l.442: `t₃ = 2π/3 + 136/10000`. -/
noncomputable def bA : ℝ := 2 * π / 3 + 136 / 10000
/-- l.442: `y₂ = 4865/10000`. -/
noncomputable def y2 : ℝ := 4865 / 10000
/-- l.443: `α₋ = t₂/π + 2/3`. -/
noncomputable def aA : ℝ := tS / π + 2 / 3
/-- l.443: `α₊ = (t₃ - t₂)/π`. -/
noncomputable def aB : ℝ := (bA - tS) / π
/-- l.443: `α_π = 2 - α₋ - α₊`. -/
noncomputable def aC : ℝ := 2 - aA - aB
/-- l.444: `γ = t₃ - (π/2)(α₋ + α₊) - (δ/4)(α₊ - α₋)`. -/
noncomputable def gam (δ : ℝ) : ℝ := bA - π / 2 * (aA + aB) - δ / 4 * (aB - aA)

/-- `e^{iδ/2}`. -/
noncomputable def ePlus (δ : ℝ) : ℂ := Complex.exp (Complex.I * ((δ / 2 : ℝ) : ℂ))
/-- `e^{-iδ/2}`. -/
noncomputable def eMinus (δ : ℝ) : ℂ := Complex.exp (-(Complex.I * ((δ / 2 : ℝ) : ℂ)))

/-- l.446: `Π(ξ) = (1+ξ)^{-α_π/2} / ((1 - ξ e^{iδ/2})^{α₋/2} (1 - ξ e^{-iδ/2})^{α₊/2})`, principal branches. -/
noncomputable def Pi (δ : ℝ) (ζ : ℂ) : ℂ :=
  (1 + ζ) ^ (-((aC : ℝ) : ℂ) / 2) / ((1 - ζ * ePlus δ) ^ (((aA : ℝ) : ℂ) / 2) * (1 - ζ * eMinus δ) ^ (((aB : ℝ) : ℂ) / 2))

/-- l.447: `Y(ξ) = y₂ [δ/(2π) + (1/(πi)) log((1 - ξ e^{-iδ/2})/(1 - ξ e^{iδ/2}))]`, principal log. -/
noncomputable def Yf (δ : ℝ) (ζ : ℂ) : ℂ :=
  ((y2 : ℝ) : ℂ) * (((δ / (2 * π) : ℝ) : ℂ) + 1 / ((π : ℂ) * Complex.I) * Complex.log ((1 - ζ * eMinus δ) / (1 - ζ * ePlus δ)))

/-- l.449: `z = e^{iγ/2} Π e^{Y/2}`. -/
noncomputable def zf (δ : ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((gam δ / 2 : ℝ) : ℂ)) * Pi δ ζ * Complex.exp (Yf δ ζ / 2)

/-- l.449: `w = ξ e^{iγ/2} Π e^{-Y/2}`. -/
noncomputable def wf (δ : ℝ) (ζ : ℂ) : ℂ :=
  ζ * Complex.exp (Complex.I * ((gam δ / 2 : ℝ) : ℂ)) * Pi δ ζ * Complex.exp (-(Yf δ ζ) / 2)

/-- Membership in the Hardy space `H^p` of the disc: holomorphic in the open disc with `sup_{r<1} ∫₀^{2π} |f(re^{iθ})|^p dθ < ∞`. -/
def InHardy (p : ℝ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧
    ∃ M : ℝ, ∀ r ∈ Set.Ioo (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * π), ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p ≤ M

end P18.Explicit
