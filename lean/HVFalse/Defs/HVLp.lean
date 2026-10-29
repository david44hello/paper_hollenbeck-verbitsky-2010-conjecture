/-
  HVFalse/Defs/HVLp.lean - the Hollenbeck-Verbitsky inequality (eq:HV) on ALL of L^p(T)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper (l.65-67) states (eq:HV) for f ∈ L^p(T): ‖(|P₊f|^s + |P₋f|^s)^{1/s}‖_p ≤ C ‖f‖_p, with
  P₊f = Σ_{n ≥ 0} f̂(n) e^{inθ} and P₋f = Σ_{n < 0} f̂(n) e^{inθ}. Here P₊f and P₋f are named by their Fourier coefficients:
  `HVIneqLp` quantifies over all f, g, h ∈ L^p(T) such that ĝ(n) = f̂(n) for n ≥ 0 and 0 for n < 0, and ĥ(n) = f̂(n) for n < 0
  and 0 for n ≥ 0. (That such g, h exist is M. Riesz's theorem; a function in L^p ⊂ L^1 is fixed by its Fourier
  coefficients, so g, h are P₊f, P₋f.) The definition uses no axiom. `T = ℝ/2πℤ` carries Lebesgue measure; the
  normalization dθ/2π cancels.
-/
import Mathlib
import HVFalse.Defs.HV

open Real MeasureTheory

namespace P18

/-- `0 < 2π`, so that `AddCircle (2 * π)` has its Haar measure and Fourier theory. -/
instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨by positivity⟩

/-- The circle `T = ℝ/2πℤ` (Lebesgue measure, total mass `2π`; `fourier n` is `θ ↦ e^{inθ}`). -/
abbrev Circ : Type := AddCircle (2 * π)

/-- `L^p(T)`, complex valued. -/
abbrev LpT (p : ℝ) : Type := Lp ℂ (ENNReal.ofReal p) (volume : Measure Circ)

/-- Paper (eq:HV), l.65-67, on all of `L^p(T)` with constant `C`: for `f ∈ L^p` and `g = P₊f`, `h = P₋f` (named by their
Fourier coefficients), `‖(|g|^s + |h|^s)^{1/s}‖_p ≤ C ‖f‖_p`. -/
def HVIneqLp (p s C : ℝ) : Prop :=
  ∀ f g h : LpT p,
    (∀ n : ℤ, fourierCoeff (⇑g) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0) →
    (∀ n : ℤ, fourierCoeff (⇑h) n = if n < 0 then fourierCoeff (⇑f) n else 0) →
    eLpNorm (fun x => (‖g x‖ ^ s + ‖h x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume

end P18
