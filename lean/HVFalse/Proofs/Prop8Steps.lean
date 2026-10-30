/-
  HVFalse/Proofs/Prop8Steps.lean - Prop. 8 (paper l.477-478): two hand steps behind the integral of `G` over the circle
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  For the explicit pair: (c) on each of the three open arcs, `G(z, w) = |zw|^q Γ(y_j, t_j)` with `q = p/2 = 3/4`;
  (d) `|zw|^q = Π_k |2 sin((θ - θ_k)/2)|^(-q α_k)` with `θ_k = -δ/2, δ/2, π` and `α_k = α₋, α₊, α_π`.
-/
import HVFalse.Proofs.Arcs
import HVFalse.Proofs.Bridges

open Real Set

namespace P18

namespace Prop8Steps

open ArcsAux

/-! ### (c) the integrand on the three arcs -/

/-- Where `arg(zw) = t ≠ 0` and `log|z/w| = y`: `G(z, w) = |zw|^{3/4} Γ(y, t)` (`p = 3/2`, `s = 398/100`); `arg(zw) ≠ 0`
gives `zw ≠ 0`, so `lift_pointwise` applies. -/
theorem G_eq_of_arc {z w : ℂ} {y t : ℝ} (ht : t ≠ 0) (harg : Complex.arg (z * w) = t)
    (hlog : Real.log (‖z‖ / ‖w‖) = y) :
    G (3 / 2) (398 / 100) z w = ‖z * w‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) y t := by
  have hzw : z * w ≠ 0 := by
    intro h
    rw [h, Complex.arg_zero] at harg
    exact ht harg.symm
  obtain ⟨hz, hw⟩ := mul_ne_zero_iff.1 hzw
  unfold G
  rw [lift_pointwise (3 / 2) (398 / 100) (by norm_num) (by norm_num) (by norm_num) z w hz hw, hlog, harg,
    show ((3 : ℝ) / 2) / 2 = 3 / 4 by norm_num]

/-- (c) "the integral is `Σ_j Γ(y_j, t_j) ∫_{arc_j} |zw|^q`", pointwise: on each open arc `G = |zw|^{3/4} Γ(y_j, t_j)`. -/
theorem arc_integrand :
    let δ := Real.exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    (∀ θ ∈ Set.Ioo (-π) (-(δ / 2)), G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3))) ∧
    (∀ θ ∈ Set.Ioo (-(δ / 2)) (δ / 2), G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS) ∧
    (∀ θ ∈ Set.Ioo (δ / 2) π, G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 Explicit.bA) := by
  intro δ Z W
  obtain ⟨h1, h2, h3⟩ := explicit_arcs
  have hpi := Real.pi_pos
  refine ⟨fun θ hθ => G_eq_of_arc ?_ (h1 θ hθ).1 (h1 θ hθ).2, fun θ hθ => G_eq_of_arc ?_ (h2 θ hθ).1 (h2 θ hθ).2,
    fun θ hθ => G_eq_of_arc ?_ (h3 θ hθ).1 (h3 θ hθ).2⟩
  · exact (by linarith : -(2 * π / 3) < 0).ne
  · norm_num [Explicit.tS]
  · unfold Explicit.bA
    positivity

/-! ### (d) the modulus `|zw|^q` -/

/-- `((C^{-c/2} / (A^{a/2} B^{b/2}))^2)^{3/4} = A^{-(3/4)a} B^{-(3/4)b} C^{-(3/4)c}` for `A, B, C ≥ 0`. -/
theorem rpow_combine {A B C a b c : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ((C ^ (-c / 2) / (A ^ (a / 2) * B ^ (b / 2))) ^ 2) ^ (3 / 4 : ℝ) =
      A ^ (-(3 / 4) * a) * B ^ (-(3 / 4) * b) * C ^ (-(3 / 4) * c) := by
  have hCe : 0 ≤ C ^ (-c / 2) := Real.rpow_nonneg hC _
  have hAe : 0 ≤ A ^ (a / 2) := Real.rpow_nonneg hA _
  have hBe : 0 ≤ B ^ (b / 2) := Real.rpow_nonneg hB _
  have hq : 0 ≤ C ^ (-c / 2) / (A ^ (a / 2) * B ^ (b / 2)) := div_nonneg hCe (mul_nonneg hAe hBe)
  have ec : -c / 2 * (((2 : ℕ) : ℝ) * (3 / 4)) = -(3 / 4) * c := by push_cast; ring
  have ea : a / 2 * (((2 : ℕ) : ℝ) * (3 / 4)) = 3 / 4 * a := by push_cast; ring
  have eb : b / 2 * (((2 : ℕ) : ℝ) * (3 / 4)) = 3 / 4 * b := by push_cast; ring
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq, Real.div_rpow hCe (mul_nonneg hAe hBe), Real.mul_rpow hAe hBe,
    ← Real.rpow_mul hC, ← Real.rpow_mul hA, ← Real.rpow_mul hB, ec, ea, eb,
    show -(3 / 4 : ℝ) * a = -(3 / 4 * a) by ring, show -(3 / 4 : ℝ) * b = -(3 / 4 * b) by ring,
    Real.rpow_neg hA, Real.rpow_neg hB]
  ring

/-- `|1 + e^{iθ}| = |2 sin((θ - π)/2)|`. -/
theorem norm_one_add_exp (θ : ℝ) :
    ‖1 + Complex.exp ((θ : ℂ) * Complex.I)‖ = |2 * Real.sin ((θ - π) / 2)| := by
  rw [one_add_exp_polar, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    show (θ - π) / 2 = θ / 2 - π / 2 by ring, Real.sin_sub_pi_div_two, mul_neg, abs_neg]

/-- `|1 - e^{iφ}| = |2 sin(φ/2)|`. -/
theorem norm_one_sub_exp (φ : ℝ) :
    ‖1 - Complex.exp ((φ : ℂ) * Complex.I)‖ = |2 * Real.sin (φ / 2)| := by
  rw [one_sub_exp_polar, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `|Π| = |1 + ζ|^{-α_π/2} / (|1 - ζ e^{iδ/2}|^{α₋/2} |1 - ζ e^{-iδ/2}|^{α₊/2})` (real exponents). -/
theorem norm_Pi (δ : ℝ) (ζ : ℂ) :
    ‖Explicit.Pi δ ζ‖ = ‖1 + ζ‖ ^ (-Explicit.aC / 2) /
      (‖1 - ζ * Explicit.ePlus δ‖ ^ (Explicit.aA / 2) * ‖1 - ζ * Explicit.eMinus δ‖ ^ (Explicit.aB / 2)) := by
  have e1 : -((Explicit.aC : ℝ) : ℂ) / 2 = ((-Explicit.aC / 2 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((Explicit.aA : ℝ) : ℂ) / 2 = ((Explicit.aA / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((Explicit.aB : ℝ) : ℂ) / 2 = ((Explicit.aB / 2 : ℝ) : ℂ) := by push_cast; ring
  unfold Explicit.Pi
  rw [norm_div, norm_mul, e1, e2, e3, Complex.norm_cpow_real, Complex.norm_cpow_real, Complex.norm_cpow_real]

/-- (d) "`|zw|^q = Π_k |2 sin((θ - θ_k)/2)|^{-q α_k}`" on the circle (`θ_k = -δ/2, δ/2, π`; `q = 3/4`). The identity
holds for every real `θ`; the hypotheses of the paper's statement are kept. -/
theorem arc_modulus :
    let δ := Real.exp (-2500)
    ∀ θ ∈ Set.Ioo (-π) π, θ ≠ -(δ / 2) → θ ≠ δ / 2 →
      ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 4 : ℝ)
        = |2 * Real.sin ((θ + δ / 2) / 2)| ^ (-(3 / 4) * Explicit.aA) *
          |2 * Real.sin ((θ - δ / 2) / 2)| ^ (-(3 / 4) * Explicit.aB) *
          |2 * Real.sin ((θ - π) / 2)| ^ (-(3 / 4) * Explicit.aC) := by
  intro δ θ _ _ _
  have hg : ‖Complex.exp (Complex.I * ((Explicit.gam δ : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  obtain ⟨hzA, hzB⟩ := zeta_mul_e δ θ
  rw [explicit_product, norm_mul, norm_mul, hg, Complex.norm_exp_ofReal_mul_I, one_mul, one_mul, norm_pow, norm_Pi,
    hzA, hzB, norm_one_add_exp, norm_one_sub_exp, norm_one_sub_exp]
  exact rpow_combine (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)

end Prop8Steps

end P18
