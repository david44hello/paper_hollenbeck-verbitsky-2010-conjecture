/-
  HVFalse/Defs/Potential.lean - subharmonic, plurisubharmonic, q-subtrigonometric (the paper, Secs. 3 and 6)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  TRUST SURFACE. Every line here must be the TEXTBOOK notion (Demailly, Complex Analytic and Differential Geometry,
  online book, version of June 21, 2012, Ch. I: (4.12) b), p. 33, and (5.1), p. 39). Notes for the reviewer:
  (1) `IsSubharmonic` uses the sub-mean-value inequality on EVERY circle: this is Demailly, Complex Analytic and Differential
      Geometry (2012), Theorem and definition (4.12) b), p. 33, with Ω = ℂ ("u(a) ≤ μ_S(u; a, r), ∀ B̄(a,r) ⊂ Ω"); (4.12)
      also shows it equivalent to the local form e) (small circles). Demailly allows u ≡ -∞ ((4.17), p. 35), as we do.
  (2) It states the inequality for the truncations max(u, -n), n ∈ ℕ, so that every integral is of a bounded measurable
      function (no junk value). For usc u this is equivalent to `u(c) ≤ (1/2π) ∫ u(c + r e^{iθ}) dθ ∈ [-∞, ∞)`:
      (⇐) max(u,-n) is subharmonic when u is; (⇒) monotone convergence as n → ∞ (the integrands decrease to u and are
      bounded above on the circle).
  (3) u ≡ -∞ IS subharmonic here, as in Demailly (4.12) (which does not exclude it); (5.1) b) asks the same of the
      restriction to every complex line.
-/
import Mathlib

open Real

namespace P18

/-- The truncation `max(u, -n)` as a real number (finite because `u ≠ ⊤` is part of every definition below). -/
noncomputable def trunc (n : ℕ) (x : EReal) : ℝ := (max x (-(n : EReal))).toReal

/-- Subharmonic on ℂ (values in `[-∞, ∞)`): never `⊤`, upper semicontinuous, and the sub-mean-value inequality on every
circle, for every truncation `max(u, -n)`. -/
def IsSubharmonic (u : ℂ → EReal) : Prop :=
  (∀ z, u z ≠ ⊤) ∧ UpperSemicontinuous u ∧
    ∀ (n : ℕ) (c : ℂ) (r : ℝ), 0 < r → trunc n (u c) ≤ circleAverage (fun z => trunc n (u z)) c r

/-- Plurisubharmonic on ℂ² (Demailly (5.1), p. 39, with Ω = ℂ²): never `⊤`, upper semicontinuous, and subharmonic (or ≡ -∞) on
every complex line `λ ↦ a + λ b`. -/
def IsPSH (u : ℂ × ℂ → EReal) : Prop :=
  (∀ x, u x ≠ ⊤) ∧ UpperSemicontinuous u ∧ ∀ a b : ℂ × ℂ, IsSubharmonic (fun l : ℂ => u (a + l • b))

/-- Paper l.235-236: a `2π`-periodic finite `φ` is q-subtrigonometric if `|ζ|^q φ(arg ζ)` is subharmonic on ℂ
(at `ζ = 0` the function is `0^q φ(0) = 0`, `q > 0`). -/
def QSubtrig (q : ℝ) (φ : ℝ → ℝ) : Prop :=
  Function.Periodic φ (2 * π) ∧ IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ q * φ (Complex.arg ζ) : ℝ) : EReal))

end P18
