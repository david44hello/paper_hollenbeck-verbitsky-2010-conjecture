/-
  HVFalse/Defs/PotentialOn.lean - subharmonic on an open set, polar sectors, usc regularization (for Thm B and Sec. 7)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
  Textbook: J.-P. Demailly, Complex Analytic and Differential Geometry (version June 21, 2012, open online book).
-/
import Mathlib
import HVFalse.Defs.Potential

open Real

namespace P18

/-- Demailly (4.12) b), p. 33, on an open `Ω ⊂ ℂ`: `u : Ω → [-∞, ∞)` upper semicontinuous with `u(a) ≤ μ_S(u; a, r)` for every
closed disc `B̄(a, r) ⊂ Ω` (truncated form, as in `IsSubharmonic`). With `Ω = univ` this is `IsSubharmonic`. -/
def IsSubharmonicOn (Ω : Set ℂ) (u : ℂ → EReal) : Prop :=
  (∀ z ∈ Ω, u z ≠ ⊤) ∧ UpperSemicontinuousOn u Ω ∧
    ∀ (n : ℕ) (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
      trunc n (u c) ≤ circleAverage (fun z => trunc n (u z)) c r

/-- The polar sector `{r e^{iθ} : r > 0, a < θ < b}` (used with `b - a < 2π`, so `θ` is unique). -/
def sectorPolar (a b : ℝ) : Set ℂ :=
  {z | ∃ r : ℝ, 0 < r ∧ ∃ θ ∈ Set.Ioo a b, z = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)}

/-- Demailly §4.C.3, p. 38: the upper semicontinuous regularization `u⋆(z) = lim_{ε→0} sup_{B(z,ε)} u` (on ℂ²). -/
noncomputable def uscReg (u : ℂ × ℂ → EReal) (x : ℂ × ℂ) : EReal :=
  ⨅ ε : {ε : ℝ // 0 < ε}, ⨆ y ∈ Metric.ball x (ε : ℝ), u y

/-- "Locally uniformly bounded above" (Demailly §4.C.3; Levenberg p. 3: "uniformly bounded above on any compact subset"):
every point has a ball and a real bound valid for every member of the family. -/
def LocUnifBddAbove {ι : Type} (u : ι → ℂ × ℂ → EReal) : Prop :=
  ∀ x : ℂ × ℂ, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ (i : ι) (y : ℂ × ℂ), y ∈ Metric.ball x ε → u i y ≤ (M : EReal)

end P18
