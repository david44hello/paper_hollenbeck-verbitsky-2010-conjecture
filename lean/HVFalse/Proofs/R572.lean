/-
  HVFalse/Proofs/R572.lean - the identity Γ - e = exp(q|y|)Φ (Sec. 2), the end-point remark via [MM, Sec. 2] (Sec. 2),
  and two numbers of Prop. 8 and its remark; rows C04j, C04k, C04l, C04m, C13f2, C13g2 (C04m in Statements.lean)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Basic
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV
import HVFalse.Defs.HVLp
import HVFalse.Defs.Explicit
import HVFalse.Cited.MM2022

open Real

namespace P18.R572

/-- `cos(π/(2p)) > 0` for `p > 1`. -/
theorem cos_half_pos {p : ℝ} (hp1 : 1 < p) : 0 < cos (π / (2 * p)) := by
  apply Real.cos_pos_of_mem_Ioo
  have hpi := Real.pi_pos
  have hp0 : 0 < p := by linarith
  constructor
  · have : 0 < π / (2 * p) := by positivity
    linarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- `2 + 2 cos(π/p) = (2 cos(π/(2p)))²`. -/
theorem two_add_two_cos {p : ℝ} (hp1 : 1 < p) : 2 + 2 * cos (π / p) = (2 * cos (π / (2 * p))) ^ 2 := by
  have hp0 : p ≠ 0 := (by linarith : (0 : ℝ) < p).ne'
  have h : π / p = 2 * (π / (2 * p)) := by field_simp
  rw [h, Real.cos_two_mul]
  ring

/-- `cos(π/p) > -1` for `p > 1`. -/
theorem cos_pi_div_gt {p : ℝ} (hp1 : 1 < p) : -1 < cos (π / p) := by
  have h := two_add_two_cos hp1
  have hc := cos_half_pos hp1
  have : 0 < (2 * cos (π / (2 * p))) ^ 2 := by positivity
  linarith

/-- [MM2022, Sec. 2] at `t = 1` (the instance the paper uses at l.66 and l.633): every valid constant `C` is
`≥ C_HV = hvConst p s`. Proved from the axiom `Cited.mm2022_lower_bound`. -/
theorem mm2022_lower_bound_one (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (C : ℝ) (hC : 0 < C)
    (hHV : HVIneqLp p s C) : hvConst p s ≤ C := by
  have h := Cited.mm2022_lower_bound p s hp1 hp2 hs 1 zero_le_one le_rfl C hC hHV
  have hc := cos_half_pos hp1
  have hrad : (1 : ℝ) + 1 ^ 2 + 2 * 1 * cos (π / p) = (2 * cos (π / (2 * p))) ^ 2 := by
    rw [← two_add_two_cos hp1]; ring
  rw [hrad, Real.sqrt_sq (by linarith), Real.one_rpow, show (1 : ℝ) + 1 = 2 by norm_num] at h
  unfold hvConst
  exact h

/-- The function `Φ(r,t)` of Sec. 2 (l.200): `((1 + r² + 2r cos t)/(2(1 + cos 2ϑ)))^q - ((1 + r^s)/2)^{p/s} - r^q e(t)`. -/
noncomputable def Phi (p s r t : ℝ) : ℝ :=
  ((1 + r ^ 2 + 2 * r * cos t) / (2 * (1 + cos (2 * (π / (2 * p)))))) ^ (p / 2)
    - ((1 + r ^ s) / 2) ^ (p / s) - r ^ (p / 2) * ee p t

/-- Sec. 2 (l.198-202): with `r = exp(-|y|)`, `Γ(y,t) - e(t) = exp(q|y|) Φ(r,t)` (row C04j). -/
theorem gam_sub_ee_eq_phi {p s : ℝ} (hp1 : 1 < p) (hs : 0 < s) (y t : ℝ) :
    Gam p s y t - ee p t = exp (p / 2 * |y|) * Phi p s (exp (-|y|)) t := by
  have hE : 0 < exp |y| := exp_pos _
  have hr : 0 < exp (-|y|) := exp_pos _
  have hEr : exp |y| * exp (-|y|) = 1 := by rw [← exp_add]; simp
  have hEr2 : exp |y| * exp (-|y|) ^ 2 = exp (-|y|) := by rw [sq, ← mul_assoc, hEr, one_mul]
  have hD : 0 < 1 + cos (2 * (π / (2 * p))) := by
    rw [Real.cos_two_mul]; nlinarith [cos_half_pos hp1]
  have hN : 0 ≤ 1 + exp (-|y|) ^ 2 + 2 * exp (-|y|) * cos t := by
    nlinarith [mul_nonneg hr.le (by linarith [neg_one_le_cos t] : (0 : ℝ) ≤ cos t + 1), sq_nonneg (1 - exp (-|y|))]
  -- the first term of Γ
  have h1 : cosh y + cos t = exp |y| * (1 + exp (-|y|) ^ 2 + 2 * exp (-|y|) * cos t) / 2 := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    linear_combination (-1 / 2 : ℝ) * hEr2 + (-cos t) * hEr
  have hT1 : (cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2)
      = exp (p / 2 * |y|) *
        ((1 + exp (-|y|) ^ 2 + 2 * exp (-|y|) * cos t) / (2 * (1 + cos (2 * (π / (2 * p)))))) ^ (p / 2) := by
    have h0 : 0 ≤ cosh y + cos t := by linarith [Real.one_le_cosh y, neg_one_le_cos t]
    rw [← Real.div_rpow h0 hD.le, h1]
    rw [show exp |y| * (1 + exp (-|y|) ^ 2 + 2 * exp (-|y|) * cos t) / 2 / (1 + cos (2 * (π / (2 * p))))
        = exp |y| * ((1 + exp (-|y|) ^ 2 + 2 * exp (-|y|) * cos t) / (2 * (1 + cos (2 * (π / (2 * p)))))) by
      field_simp]
    rw [Real.mul_rpow hE.le (div_nonneg hN (by linarith)), ← Real.exp_mul, mul_comm |y|]
  -- the second term of Γ
  have h2 : cosh (s * y / 2) = exp (s * |y| / 2) * ((1 + exp (-|y|) ^ s) / 2) := by
    have habs : |s * y / 2| = s * |y| / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hs, abs_two]
    rw [← Real.cosh_abs, habs, Real.cosh_eq, ← Real.exp_mul]
    have e1 : exp (s * |y| / 2) * exp (-|y| * s) = exp (-(s * |y| / 2)) := by rw [← exp_add]; ring_nf
    linear_combination (-1 / 2 : ℝ) * e1
  have hT2 : cosh (s * y / 2) ^ (p / s) = exp (p / 2 * |y|) * ((1 + exp (-|y|) ^ s) / 2) ^ (p / s) := by
    rw [h2, Real.mul_rpow (exp_pos _).le (by positivity), ← Real.exp_mul]
    congr 2
    field_simp
  have hT3 : exp (p / 2 * |y|) * exp (-|y|) ^ (p / 2) = 1 := by
    rw [← Real.exp_mul, ← exp_add]; simp; ring
  unfold Gam Phi
  rw [hT1, hT2]
  linear_combination (ee p t) * hT3

/-- The right-hand side of the bound of [MM, Sec. 2] in the paper's variables (l.213):
`2^{1/s} cosh(sy/2)^{1/s} (2cosh y + 2cos(π/p))^{-1/2}`. -/
noncomputable def mmRhs (p s y : ℝ) : ℝ :=
  2 ^ (1 / s) * cosh (s * y / 2) ^ (1 / s) * (2 * cosh y + 2 * cos (π / p)) ^ (-(1 / 2) : ℝ)

/-- l.213-214: the right-hand side "equals `C^HV` at `y = 0`". -/
theorem mmRhs_zero {p s : ℝ} (hp1 : 1 < p) : mmRhs p s 0 = hvConst p s := by
  have hc := cos_half_pos hp1
  unfold mmRhs hvConst
  simp only [mul_zero, zero_div, Real.cosh_zero, Real.one_rpow, mul_one]
  rw [two_add_two_cos hp1, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (by linarith)]
  ring

/-- l.214: the right-hand side "exceeds it exactly when `Γ(y,π/p) < 0`" (raise both sides to the power `p`). -/
theorem hv_lt_mmRhs_iff {p s : ℝ} (hp1 : 1 < p) (y : ℝ) :
    hvConst p s < mmRhs p s y ↔ Gam p s y (π / p) < 0 := by
  have hp0 : 0 < p := by linarith
  have hc := cos_half_pos hp1
  have hD : 0 < 2 * cosh y + 2 * cos (π / p) := by nlinarith [Real.one_le_cosh y, cos_pi_div_gt hp1]
  have hK : 0 < cosh (s * y / 2) := Real.cosh_pos _
  have h2 : (0 : ℝ) < 2 ^ (1 / s) := by positivity
  have hsq : 0 < Real.sqrt (2 * cosh y + 2 * cos (π / p)) := Real.sqrt_pos.mpr hD
  have hKs : 0 < cosh (s * y / 2) ^ (1 / s) := by positivity
  -- the ratio `(cosh y + cos(π/p))/(1 + cos 2ϑ)` is `D / c²`
  have hratio : (cosh y + cos (π / p)) / (1 + cos (2 * (π / (2 * p))))
      = (2 * cosh y + 2 * cos (π / p)) / (2 * cos (π / (2 * p))) ^ 2 := by
    have h1 : 1 + cos (2 * (π / (2 * p))) = 2 * cos (π / (2 * p)) ^ 2 := by rw [Real.cos_two_mul]; ring
    rw [h1]
    field_simp
  have hG : Gam p s y (π / p)
      = ((2 * cosh y + 2 * cos (π / p)) / (2 * cos (π / (2 * p))) ^ 2) ^ (p / 2) - cosh (s * y / 2) ^ (p / s) := by
    unfold Gam
    rw [← Real.div_rpow (by linarith [Real.one_le_cosh y, cos_pi_div_gt hp1])
      (by rw [Real.cos_two_mul]; nlinarith [sq_nonneg (cos (π / (2 * p)))]), hratio]
  have hsplit : Real.sqrt (2 * cosh y + 2 * cos (π / p)) / (2 * cos (π / (2 * p)))
      = ((2 * cosh y + 2 * cos (π / p)) / (2 * cos (π / (2 * p))) ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by linarith)]
  have hR : mmRhs p s y = 2 ^ (1 / s) * (cosh (s * y / 2) ^ (1 / s) / Real.sqrt (2 * cosh y + 2 * cos (π / p))) := by
    unfold mmRhs
    rw [Real.rpow_neg hD.le, ← Real.sqrt_eq_rpow]
    ring
  have hV : hvConst p s = 2 ^ (1 / s) * (1 / (2 * cos (π / (2 * p)))) := by unfold hvConst; ring
  have hDc : 0 ≤ (2 * cosh y + 2 * cos (π / p)) / (2 * cos (π / (2 * p))) ^ 2 := div_nonneg hD.le (sq_nonneg _)
  have hmul : ∀ a b : ℝ, (2 ^ (1 / s) * a < 2 ^ (1 / s) * b ↔ a < b) :=
    fun a b => ⟨fun h => lt_of_mul_lt_mul_left h h2.le, fun h => mul_lt_mul_of_pos_left h h2⟩
  rw [hR, hV, hmul, hG, sub_neg, lt_div_iff₀ hsq, one_div_mul_eq_div, hsplit,
    ← Real.rpow_lt_rpow_iff (Real.rpow_nonneg hDc _) hKs.le hp0, ← Real.rpow_mul hDc, ← Real.rpow_mul hK.le]
  constructor <;> intro h <;> convert h using 2 <;> ring

/-- MM's expression at `t = exp(-y)` is the paper's right-hand side `mmRhs p s y`. -/
theorem mm_value_at_exp {p s : ℝ} (hp1 : 1 < p) (hs : 0 < s) (y : ℝ) :
    (1 + exp (-y) ^ s) ^ (1 / s) / Real.sqrt (1 + exp (-y) ^ 2 + 2 * exp (-y) * cos (π / p)) = mmRhs p s y := by
  have hD : 0 < 2 * cosh y + 2 * cos (π / p) := by nlinarith [Real.one_le_cosh y, cos_pi_div_gt hp1]
  have hnum : 1 + exp (-y) ^ s = exp (-(s * y / 2)) * (2 * cosh (s * y / 2)) := by
    rw [← Real.exp_mul, Real.cosh_eq]
    have e1 : exp (-(s * y / 2)) * exp (s * y / 2) = 1 := by rw [← exp_add]; simp
    have e2 : exp (-(s * y / 2)) * exp (-(s * y / 2)) = exp (-y * s) := by rw [← exp_add]; ring_nf
    linear_combination (-1 : ℝ) * e1 + (-1 : ℝ) * e2
  have hden : 1 + exp (-y) ^ 2 + 2 * exp (-y) * cos (π / p) = exp (-y) * (2 * cosh y + 2 * cos (π / p)) := by
    rw [Real.cosh_eq]
    have e1 : exp (-y) * exp y = 1 := by rw [← exp_add]; simp
    linear_combination (-1 : ℝ) * e1
  have hsqe : Real.sqrt (exp (-y)) = exp (-(y / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  have hpow : exp (-(s * y / 2)) ^ (1 / s) = exp (-(y / 2)) := by
    rw [← Real.exp_mul]; congr 1; field_simp
  rw [hnum, hden, Real.mul_rpow (exp_pos _).le (by positivity), Real.mul_rpow (by norm_num) (Real.cosh_pos _).le,
    hpow, Real.sqrt_mul (exp_pos _).le, hsqe]
  unfold mmRhs
  rw [Real.rpow_neg hD.le, ← Real.sqrt_eq_rpow]
  field_simp

/-- l.212-213: "By [MM, Sec. 2], `C* ≥ 2^{1/s} cosh(sy/2)^{1/s} (2cosh y + 2cos(π/p))^{-1/2}` for every `y ≥ 0`"
(row C04k; the axiom `Cited.mm2022_lower_bound` at `t = exp(-y)`). -/
theorem mm_bound_y {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {y : ℝ} (hy : 0 ≤ y) {C : ℝ} (hC : 0 < C)
    (hHV : HVIneqLp p s C) : mmRhs p s y ≤ C := by
  have h := Cited.mm2022_lower_bound p s hp1 hp2 hs (exp (-y)) (exp_pos _).le (by rw [Real.exp_le_one_iff]; linarith) C hC hHV
  rwa [mm_value_at_exp hp1 hs y] at h

/-- Prop. 8 proof (l.472): "`qα₋ ≈ 0.927`, `qα₊ ≈ 0.076` and `qα_π ≈ 0.497`" (row C13f2), each within `5·10⁻⁴`. -/
theorem explicit_exponents_approx :
    |3 / 4 * Explicit.aA - 927 / 1000| < 5 / 10 ^ 4 ∧ |3 / 4 * Explicit.aB - 76 / 1000| < 5 / 10 ^ 4 ∧
      |3 / 4 * Explicit.aC - 497 / 1000| < 5 / 10 ^ 4 := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have hA : Explicit.aA = 179 / 100 * (1 / π) + 2 / 3 := by unfold Explicit.aA Explicit.tS; ring
  have hB : Explicit.aB = 2 / 3 + (136 / 10000 - 179 / 100) * (1 / π) := by
    unfold Explicit.aB Explicit.bA Explicit.tS; field_simp; ring
  have hC : Explicit.aC = 2 / 3 - 136 / 10000 * (1 / π) := by unfold Explicit.aC; rw [hA, hB]; ring
  have hlo : 1 / (3.141593 : ℝ) < 1 / π := one_div_lt_one_div_of_lt Real.pi_pos Real.pi_lt_d6
  have hhi : 1 / π < 1 / (3.141592 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) Real.pi_gt_d6
  norm_num at hlo hhi
  rw [hA, hB, hC]
  simp only [one_div]
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_lt] <;> constructor <;> nlinarith

/-- The remark after Prop. 8 (l.498): `η = a₋ + a₊ - 1 = q(t₃ - π/p)/π` at `p = 3/2` (row C13g2). -/
theorem explicit_eta_middle :
    3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 = 3 / 4 * (Explicit.bA - π / (3 / 2)) / π := by
  have hpi : π ≠ 0 := Real.pi_ne_zero
  unfold Explicit.aA Explicit.aB
  field_simp
  ring

end P18.R572
