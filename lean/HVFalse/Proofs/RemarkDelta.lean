/-
  HVFalse/Proofs/RemarkDelta.lean - the exact claims of the remark "the size of δ" (paper l.496-507, after Prop. 8)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Explicit
import HVFalse.Defs.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

open Real

namespace P18.RemarkDelta

/-! ## The exponents and the two arc endpoints (`p = 3/2`, `q = 3/4`, `ϑ = π/3`) -/

/-- `η = α₋ + α₊ - 1 = 0.0102/π` (with `α_± = (3/4) α_{A,B}`). -/
theorem eta_eq : 3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 = 102 / 10000 / π := by
  have hπ : π ≠ 0 := pi_ne_zero
  unfold Explicit.aA Explicit.aB Explicit.tS Explicit.bA
  field_simp
  ring

/-- `q t₂ = π α₋ - π/2`. -/
theorem tS_eq : 3 / 4 * Explicit.tS = π * (3 / 4 * Explicit.aA) - π / 2 := by
  have hπ : π ≠ 0 := pi_ne_zero
  unfold Explicit.aA
  field_simp
  ring

/-- `q t₃ = π/2 + π η`. -/
theorem bA_eq : 3 / 4 * Explicit.bA = π / 2 + π * (3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1) := by
  have hπ : π ≠ 0 := pi_ne_zero
  unfold Explicit.aA Explicit.aB
  field_simp
  ring

/-- `e(t₂) = tan ϑ · sin(π α₋)`. -/
theorem ee_tS : ee (3 / 2) Explicit.tS = tan (π / 3) * sin (π * (3 / 4 * Explicit.aA)) := by
  unfold ee
  rw [show π / (2 * (3 / 2 : ℝ)) = π / 3 by ring,
    show (3 / 2 : ℝ) / 2 * Explicit.tS = π * (3 / 4 * Explicit.aA) - π / 2 by linear_combination tS_eq,
    cos_sub_pi_div_two]

/-- `e(t₃) = -tan ϑ · sin(π η)`. -/
theorem ee_bA :
    ee (3 / 2) Explicit.bA = -(tan (π / 3) * sin (π * (3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1))) := by
  unfold ee
  rw [show π / (2 * (3 / 2 : ℝ)) = π / 3 by ring,
    show (3 / 2 : ℝ) / 2 * Explicit.bA = π * (3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1) + π / 2 by
      linear_combination bA_eq,
    cos_add_pi_div_two, mul_neg]

/-! ## The `e`-terms of `W₁` cancel (Beta = Gamma quotient, then reflection) -/

/-- For `0 < a < 1`, `b < 1`, `0 < a + b - 1`: `sin(πa) B(1-a, 1-b) = sin(π(a+b-1)) B(1-b, a+b-1)`. Both sides times
`Γ(a) Γ(2-a-b)` equal `π Γ(1-b)`, by `Γ(u)Γ(v) = Γ(u+v) B(u,v)` and `Γ(z)Γ(1-z) sin(πz) = π`. -/
theorem beta_cancel (am ap : ℝ) (ham0 : 0 < am) (ham1 : am < 1) (hap : ap < 1) (hη0 : 0 < am + ap - 1) :
    sin (π * am) * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re =
      sin (π * (am + ap - 1)) * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((am + ap - 1 : ℝ) : ℂ)).re := by
  have hs1 : sin (π * am) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])).ne'
  have hs2 : sin (π * (am + ap - 1)) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hη0) (by nlinarith [pi_pos])).ne'
  have hS1 : Complex.sin ((π : ℂ) * (am : ℂ)) ≠ 0 := by exact_mod_cast hs1
  have hS2 : Complex.sin ((π : ℂ) * ((am : ℂ) + (ap : ℂ) - 1)) ≠ 0 := by exact_mod_cast hs2
  have hB1 : Complex.Gamma (1 - (am : ℂ)) * Complex.Gamma (1 - (ap : ℂ)) =
      Complex.Gamma (1 - ((am : ℂ) + (ap : ℂ) - 1)) * Complex.betaIntegral (1 - (am : ℂ)) (1 - (ap : ℂ)) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 - (am : ℂ)) (t := 1 - (ap : ℂ))
      (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith)
      (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith)
    rwa [show 1 - (am : ℂ) + (1 - (ap : ℂ)) = 1 - ((am : ℂ) + (ap : ℂ) - 1) by ring] at h
  have hB2 : Complex.Gamma (1 - (ap : ℂ)) * Complex.Gamma ((am : ℂ) + (ap : ℂ) - 1) =
      Complex.Gamma (am : ℂ) * Complex.betaIntegral (1 - (ap : ℂ)) ((am : ℂ) + (ap : ℂ) - 1) := by
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := 1 - (ap : ℂ)) (t := (am : ℂ) + (ap : ℂ) - 1)
      (by simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]; linarith)
      (by simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith)
    rwa [show 1 - (ap : ℂ) + ((am : ℂ) + (ap : ℂ) - 1) = (am : ℂ) by ring] at h
  have hR1 : Complex.Gamma (am : ℂ) * Complex.Gamma (1 - (am : ℂ)) * Complex.sin ((π : ℂ) * (am : ℂ)) = π := by
    rw [Complex.Gamma_mul_Gamma_one_sub]
    field_simp
  have hR2 : Complex.Gamma ((am : ℂ) + (ap : ℂ) - 1) * Complex.Gamma (1 - ((am : ℂ) + (ap : ℂ) - 1)) *
      Complex.sin ((π : ℂ) * ((am : ℂ) + (ap : ℂ) - 1)) = π := by
    rw [Complex.Gamma_mul_Gamma_one_sub]
    field_simp
  have hG : Complex.Gamma (am : ℂ) * Complex.Gamma (1 - ((am : ℂ) + (ap : ℂ) - 1)) ≠ 0 :=
    mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simpa using ham0))
      (Complex.Gamma_ne_zero_of_re_pos
        (by simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re]; linarith))
  have hC : ((sin (π * am) : ℝ) : ℂ) * Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ) =
      ((sin (π * (am + ap - 1)) : ℝ) : ℂ) * Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((am + ap - 1 : ℝ) : ℂ) := by
    push_cast
    apply mul_left_cancel₀ hG
    linear_combination (-(Complex.Gamma (am : ℂ)) * Complex.sin ((π : ℂ) * (am : ℂ))) * hB1 +
      Complex.Gamma (1 - (ap : ℂ)) * hR1 +
      (Complex.Gamma (1 - ((am : ℂ) + (ap : ℂ) - 1)) * Complex.sin ((π : ℂ) * ((am : ℂ) + (ap : ℂ) - 1))) * hB2 -
      Complex.Gamma (1 - (ap : ℂ)) * hR2
  simpa only [Complex.re_ofReal_mul] using congrArg Complex.re hC

/-! ## The third arc: `Γ(0, t₁) = e(t₁) = 0` at `t₁ = -2π/3` -/

/-- `Γ(0, -2π/3) = 0` at `(p, s) = (3/2, 3.98)`. -/
theorem gam_arc_zero : Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 := by
  have hpos : (0 : ℝ) < 1 + cos (2 * π / 3) := by
    rw [show 2 * π / 3 = π - π / 3 by ring, cos_pi_sub, cos_pi_div_three]
    norm_num
  unfold Gam
  rw [cos_neg, cosh_zero, show 2 * (π / (2 * (3 / 2 : ℝ))) = 2 * π / 3 by ring,
    div_self (rpow_pos_of_pos hpos ((3 / 2 : ℝ) / 2)).ne', show (398 / 100 : ℝ) * 0 / 2 = 0 by ring, cosh_zero,
    one_rpow, sub_self]

/-- `e(-2π/3) = 0` at `p = 3/2`. -/
theorem ee_arc_zero : ee (3 / 2) (-(2 * π / 3)) = 0 := by
  unfold ee
  rw [show (3 / 2 : ℝ) / 2 * -(2 * π / 3) = -(π / 2) by ring, cos_neg, cos_pi_div_two, mul_zero]

/-! ## The remark -/

/-- The remark "the size of `δ`" (l.496-507), its exact claims: `η = 0.0102/π`, `q t₂ = π α₋ - π/2`, `q t₃ = π/2 + π η`,
`e(t₂) = tan ϑ sin(π α₋)`, `e(t₃) = -tan ϑ sin(π η)`, the `e`-terms of `W₁` cancel (so `W₁ = Σ (Γ - e) B` literally), and
`Γ(0, t₁) = e(t₁) = 0` at the contact point `(0, -π/p)` (l.434-435). -/
theorem remark_delta_exact :
    let am : ℝ := 3 / 4 * Explicit.aA
    let ap : ℝ := 3 / 4 * Explicit.aB
    let η : ℝ := am + ap - 1
    η = 102 / 10000 / π ∧ 3 / 4 * Explicit.tS = π * am - π / 2 ∧ 3 / 4 * Explicit.bA = π / 2 + π * η ∧
    ee (3 / 2) Explicit.tS = Real.tan (π / 3) * Real.sin (π * am) ∧
    ee (3 / 2) Explicit.bA = -(Real.tan (π / 3) * Real.sin (π * η)) ∧
    ee (3 / 2) Explicit.tS * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re +
      ee (3 / 2) Explicit.bA * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re = 0
    ∧ (Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re
        + Gam (3 / 2) (398 / 100) 0 Explicit.bA * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re
      = (Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS) * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re
        + (Gam (3 / 2) (398 / 100) 0 Explicit.bA - ee (3 / 2) Explicit.bA) * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re)
    ∧ (Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 ∧ ee (3 / 2) (-(2 * π / 3)) = 0) := by
  dsimp only
  have ham1 : 3 / 4 * Explicit.aA < 1 := by
    have h : 179 / 100 / π < 2 / 3 := by
      rw [div_lt_iff₀ pi_pos]
      linarith [pi_gt_three]
    unfold Explicit.aA Explicit.tS
    linarith
  have ham0 : 0 < 3 / 4 * Explicit.aA := by
    unfold Explicit.aA Explicit.tS
    positivity
  have hap : 3 / 4 * Explicit.aB < 1 := by
    have h : (Explicit.bA - Explicit.tS) / π < 1 := by
      rw [div_lt_iff₀ pi_pos]
      unfold Explicit.bA Explicit.tS
      linarith [pi_pos]
    unfold Explicit.aB
    linarith
  have hη0 : 0 < 3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 := by
    rw [eta_eq]
    positivity
  have hsum : ee (3 / 2) Explicit.tS * (Complex.betaIntegral ((1 - 3 / 4 * Explicit.aA : ℝ) : ℂ)
        ((1 - 3 / 4 * Explicit.aB : ℝ) : ℂ)).re +
      ee (3 / 2) Explicit.bA * (Complex.betaIntegral ((1 - 3 / 4 * Explicit.aB : ℝ) : ℂ)
        ((3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 : ℝ) : ℂ)).re = 0 := by
    rw [ee_tS, ee_bA]
    linear_combination tan (π / 3) * beta_cancel _ _ ham0 ham1 hap hη0
  refine ⟨eta_eq, tS_eq, bA_eq, ee_tS, ee_bA, hsum, ?_, gam_arc_zero, ee_arc_zero⟩
  linear_combination hsum

end P18.RemarkDelta
