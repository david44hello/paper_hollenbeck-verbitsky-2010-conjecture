/-
  HVFalse/Defs/HV.lean - the Hollenbeck-Verbitsky inequality (eq:HV) and the functions G, E, Γ_λ of the paper
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  SCOPE NOTE (for every reader and reviewer). The paper states (eq:HV) for f ∈ L^p(T). Here `HVIneq` quantifies over
  trigonometric polynomials f = Σ_n c_n e^{inθ} (finitely many c_n ≠ 0), where P₊ and P₋ are exact finite sums.
  * A FAILURE (`¬ HVIneq`) exhibits a trigonometric polynomial violating (eq:HV): at least as strong as the paper's failure.
  * A VALIDITY (`HVIneq`) is the paper's statement on the dense class of trigonometric polynomials; the step to all of L^p
    is M. Riesz's theorem + density (the paper's own words "by density", l.171). That step IS proved: the L^p form
    is `HVIneqLp` (Defs/HVLp.lean), and Paper row C01b proves HVIneqLp ↔ HVIneq (density + [HV2000]).
  Both sides of (eq:HV) are raised to the power p and the normalization dθ/2π is dropped (it cancels).
-/
import Mathlib
import HVFalse.Defs.Basic

open Real

namespace P18

/-- The term `c_n e^{inθ}`. -/
noncomputable def mode (n : ℤ) (a : ℂ) (θ : ℝ) : ℂ := a * Complex.exp ((((n : ℝ) * θ : ℝ) : ℂ) * Complex.I)

/-- A trigonometric polynomial `f(θ) = Σ_n c_n e^{inθ}`, `c` with finite support. -/
noncomputable def trig (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ := c.sum fun n a => mode n a θ

/-- Paper l.62: the analytic projection `P₊f = Σ_{n ≥ 0} f̂(n) e^{inθ}`. -/
noncomputable def Pplus (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ := c.sum fun n a => if 0 ≤ n then mode n a θ else 0

/-- Paper l.62: the co-analytic projection `P₋f = f - P₊f`. -/
noncomputable def Pminus (c : ℤ →₀ ℂ) (θ : ℝ) : ℂ := trig c θ - Pplus c θ

/-- Paper (eq:HV), l.65-67, with constant `C`, on trigonometric polynomials, both sides to the power `p`:
`∫₀^{2π} ((|P₊f|^s + |P₋f|^s)^{1/s})^p dθ ≤ C^p ∫₀^{2π} |f|^p dθ`. -/
def HVIneq (p s C : ℝ) : Prop :=
  ∀ c : ℤ →₀ ℂ,
    ∫ θ in (0 : ℝ)..(2 * π), ((‖Pplus c θ‖ ^ s + ‖Pminus c θ‖ ^ s) ^ (1 / s)) ^ p
      ≤ C ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖trig c θ‖ ^ p

/-- Paper l.69: the conjectured constant `2^{1/s} / (2 cos(π/2p))` (for `1 < p < 2`). -/
noncomputable def hvConst (p s : ℝ) : ℝ := 2 ^ (1 / s) / (2 * cos (π / (2 * p)))

/-- Paper l.79: `G(z,w) = A^p |z + w̄|^p - ((|z|^s + |w|^s)/2)^{p/s}`, `A = 1/(2 cos ϑ)`, `ϑ = π/(2p)`. -/
noncomputable def G (p s : ℝ) (z w : ℂ) : ℝ :=
  (1 / (2 * cos (π / (2 * p)))) ^ p * ‖z + (starRingEnd ℂ) w‖ ^ p - ((‖z‖ ^ s + ‖w‖ ^ s) / 2) ^ (p / s)

/-- Paper (eq:discs), right side, l.172-174: `∫_T G∘h ≥ 0` for every polynomial disc `h = (z, w)` with `w(0) = 0`. -/
def DiscIneq (p s : ℝ) : Prop :=
  ∀ z w : Polynomial ℂ, w.coeff 0 = 0 →
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π),
      G p s (z.eval (Complex.exp ((θ : ℂ) * Complex.I))) (w.eval (Complex.exp ((θ : ℂ) * Complex.I)))

/-- Paper (eq:two), l.187-189: `Γ(y,t) ≥ e(t)` for all `y ∈ ℝ`, `t ∈ [-π, π]`. -/
def TwoVar (p s : ℝ) : Prop := ∀ y t : ℝ, t ∈ Set.Icc (-π) π → ee p t ≤ Gam p s y t

/-- Paper l.180-184: the minorant `E(z,w) = |zw|^q e(arg zw)` (`arg ∈ (-π, π]`, where `e` is the paper's formula). -/
noncomputable def Efun (p : ℝ) (z w : ℂ) : ℝ := ‖z * w‖ ^ (p / 2) * ee p (Complex.arg (z * w))

/-- Paper Sec. 7, l.618: `Γ_λ` (the constant `A` replaced by `λ^{1/p} A`, so the first term of `Γ` is multiplied by `λ`). -/
noncomputable def GamLam (p s lam y t : ℝ) : ℝ :=
  lam * ((cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2)) - cosh (s * y / 2) ^ (p / s)

end P18
