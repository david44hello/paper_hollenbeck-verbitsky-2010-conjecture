/-
  HVFalse/Proofs/Arcs.lean - C13e: (log|z/w|, arg zw) on the three arcs of T (the paper, proof of Prop. 8)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route. On |ζ| = 1 every base of Π is a polar number with an explicit argument:
    1 + e^{iθ} = 2cos(θ/2) e^{iθ/2},   1 - e^{iφ} = 2sin(φ/2) e^{i(φ-π)/2} = (-2sin(φ/2)) e^{i(φ+π)/2}.
  So each principal log is explicit (Complex.log_exp), Π = exp P, zw = e^{iγ} ζ Π² = exp E (explicit_product), and
  z/w = e^Y/ζ. Hence arg zw = Im E and log|z/w| = Re Y; both are constant on each arc since α_A + α_B + α_C = 2.
-/
import HVFalse.Defs.Explicit
import HVFalse.Proofs.SmallB

open Real Set

namespace P18

namespace ArcsAux

open Explicit

/-! ## Polar numbers and their principal logarithms -/

/-- `r e^{ic} = exp (log r + c i)` for `r > 0`. -/
theorem polar_eq_exp {r : ℝ} (hr : 0 < r) (c : ℝ) :
    (r : ℂ) * Complex.exp ((c : ℂ) * Complex.I) = Complex.exp ((Real.log r : ℂ) + (c : ℂ) * Complex.I) := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

/-- `log (exp (r + c i)) = r + c i` for `c ∈ (-π, π]`. -/
theorem log_exp_polar (r : ℝ) {c : ℝ} (hc : c ∈ Ioc (-π) π) :
    Complex.log (Complex.exp ((r : ℂ) + (c : ℂ) * Complex.I)) = (r : ℂ) + (c : ℂ) * Complex.I :=
  Complex.log_exp (by simpa using hc.1) (by simpa using hc.2)

/-- `arg (exp (r + c i)) = c` for `c ∈ (-π, π]`. -/
theorem arg_exp_polar (r : ℝ) {c : ℝ} (hc : c ∈ Ioc (-π) π) :
    Complex.arg (Complex.exp ((r : ℂ) + (c : ℂ) * Complex.I)) = c := by
  rw [← Complex.log_im, log_exp_polar r hc]; simp

/-- `Re (a + b i) = a`. -/
theorem re_polar (a b : ℝ) : ((a : ℂ) + (b : ℂ) * Complex.I).re = a := by simp

/-- `w = e^{iφ/2}` satisfies `w · w⁻¹ = 1`, `e^{iφ} = w²`. -/
theorem exp_half_sq (φ : ℝ) :
    Complex.exp ((φ : ℂ) * Complex.I) = Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

/-- `2 cos(φ/2) = w + w⁻¹` with `w = e^{iφ/2}`. -/
theorem two_cos_half (φ : ℝ) :
    ((2 * Real.cos (φ / 2) : ℝ) : ℂ) =
      Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) + (Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))⁻¹ := by
  rw [← Complex.exp_neg]; push_cast; rw [Complex.two_cos, neg_mul]

/-- `2 sin(φ/2) = (w⁻¹ - w) i` with `w = e^{iφ/2}`. -/
theorem two_sin_half (φ : ℝ) :
    ((2 * Real.sin (φ / 2) : ℝ) : ℂ) =
      ((Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I))⁻¹ - Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I)) * Complex.I := by
  rw [← Complex.exp_neg]; push_cast; rw [Complex.two_sin, neg_mul]

/-- `e^{i(φ ∓ π)/2} = ∓ i w` with `w = e^{iφ/2}`. -/
theorem exp_shift_half (φ : ℝ) :
    Complex.exp ((((φ - π) / 2 : ℝ) : ℂ) * Complex.I) = Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * -Complex.I ∧
      Complex.exp ((((φ + π) / 2 : ℝ) : ℂ) * Complex.I) = Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * Complex.I := by
  have hm : Complex.exp ((((φ - π) / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp (-π / 2 * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hp : Complex.exp ((((φ + π) / 2 : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) * Complex.exp (π / 2 * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hm, hp, Complex.exp_neg_pi_div_two_mul_I, Complex.exp_pi_div_two_mul_I]
  exact ⟨rfl, rfl⟩

/-- `1 + e^{iθ} = 2 cos(θ/2) e^{iθ/2}`. -/
theorem one_add_exp_polar (θ : ℝ) :
    1 + Complex.exp ((θ : ℂ) * Complex.I) =
      ((2 * Real.cos (θ / 2) : ℝ) : ℂ) * Complex.exp (((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hinv := mul_inv_cancel₀ (Complex.exp_ne_zero (((θ / 2 : ℝ) : ℂ) * Complex.I))
  rw [exp_half_sq θ, two_cos_half θ]
  linear_combination (-1 : ℂ) * hinv

/-- `1 - e^{iφ} = 2 sin(φ/2) e^{i(φ-π)/2}`. -/
theorem one_sub_exp_polar (φ : ℝ) :
    1 - Complex.exp ((φ : ℂ) * Complex.I) =
      ((2 * Real.sin (φ / 2) : ℝ) : ℂ) * Complex.exp ((((φ - π) / 2 : ℝ) : ℂ) * Complex.I) := by
  set w := Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) with hw
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ (Complex.exp_ne_zero _)
  rw [exp_half_sq φ, two_sin_half φ, (exp_shift_half φ).1]
  linear_combination (w⁻¹ * w - w * w) * Complex.I_sq + (-1 : ℂ) * hinv

/-- `1 - e^{iφ} = (-2 sin(φ/2)) e^{i(φ+π)/2}`. -/
theorem one_sub_exp_polar' (φ : ℝ) :
    1 - Complex.exp ((φ : ℂ) * Complex.I) =
      ((-(2 * Real.sin (φ / 2)) : ℝ) : ℂ) * Complex.exp ((((φ + π) / 2 : ℝ) : ℂ) * Complex.I) := by
  set w := Complex.exp (((φ / 2 : ℝ) : ℂ) * Complex.I) with hw
  have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ (Complex.exp_ne_zero _)
  rw [exp_half_sq φ, Complex.ofReal_neg, two_sin_half φ, (exp_shift_half φ).2]
  linear_combination (w⁻¹ * w - w * w) * Complex.I_sq + (-1 : ℂ) * hinv

/-- For `θ ∈ (-π, π)`: `1 + e^{iθ} = exp (log(2cos(θ/2)) + (θ/2) i)`. -/
theorem one_add_exp_eq {θ : ℝ} (h0 : -π < θ) (h1 : θ < π) :
    1 + Complex.exp ((θ : ℂ) * Complex.I) =
      Complex.exp ((Real.log (2 * Real.cos (θ / 2)) : ℂ) + ((θ / 2 : ℝ) : ℂ) * Complex.I) := by
  have hc : 0 < Real.cos (θ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  rw [one_add_exp_polar, polar_eq_exp (by linarith)]

/-- For `φ ∈ (0, 2π)`: `1 - e^{iφ} = exp (log(2sin(φ/2)) + ((φ-π)/2) i)`. -/
theorem one_sub_exp_eq_pos {φ : ℝ} (h0 : 0 < φ) (h1 : φ < 2 * π) :
    1 - Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((Real.log (2 * Real.sin (φ / 2)) : ℂ) + (((φ - π) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hs : 0 < Real.sin (φ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  rw [one_sub_exp_polar, polar_eq_exp (by linarith)]

/-- For `φ ∈ (-2π, 0)`: `1 - e^{iφ} = exp (log(-2sin(φ/2)) + ((φ+π)/2) i)`. -/
theorem one_sub_exp_eq_neg {φ : ℝ} (h0 : -(2 * π) < φ) (h1 : φ < 0) :
    1 - Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((Real.log (-(2 * Real.sin (φ / 2))) : ℂ) + (((φ + π) / 2 : ℝ) : ℂ) * Complex.I) := by
  have hs : Real.sin (φ / 2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  rw [one_sub_exp_polar', polar_eq_exp (by linarith)]

/-- `ζ e^{±iδ/2} = e^{i(θ ± δ/2)}` for `ζ = e^{iθ}`. -/
theorem zeta_mul_e (δ θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) * ePlus δ = Complex.exp (((θ + δ / 2 : ℝ) : ℂ) * Complex.I) ∧
      Complex.exp ((θ : ℂ) * Complex.I) * eMinus δ = Complex.exp (((θ - δ / 2 : ℝ) : ℂ) * Complex.I) := by
  unfold ePlus eMinus
  rw [← Complex.exp_add, ← Complex.exp_add]
  constructor <;> (congr 1; push_cast; ring)

/-! ## `Π`, `zw` and `log|z/w|` from the polar forms of the three bases -/

/-- The three bases of `Π` in exponential form, with arguments in `(-π, π]`. -/
structure Bases (δ : ℝ) (ζ : ℂ) (r1 c1 rA cA rB cB : ℝ) : Prop where
  h1 : 1 + ζ = Complex.exp ((r1 : ℂ) + (c1 : ℂ) * Complex.I)
  hA : 1 - ζ * ePlus δ = Complex.exp ((rA : ℂ) + (cA : ℂ) * Complex.I)
  hB : 1 - ζ * eMinus δ = Complex.exp ((rB : ℂ) + (cB : ℂ) * Complex.I)
  hc1 : c1 ∈ Ioc (-π) π
  hcA : cA ∈ Ioc (-π) π
  hcB : cB ∈ Ioc (-π) π

/-- `Π = exp P` with `P = -(α_C/2) L₁ - (α_A/2) L_A - (α_B/2) L_B`. -/
theorem Pi_eq {δ : ℝ} {ζ : ℂ} {r1 c1 rA cA rB cB : ℝ} (hb : Bases δ ζ r1 c1 rA cA rB cB) :
    Pi δ ζ = Complex.exp (((r1 : ℂ) + (c1 : ℂ) * Complex.I) * (-((aC : ℝ) : ℂ) / 2) -
      (((rA : ℂ) + (cA : ℂ) * Complex.I) * (((aA : ℝ) : ℂ) / 2) +
        ((rB : ℂ) + (cB : ℂ) * Complex.I) * (((aB : ℝ) : ℂ) / 2))) := by
  unfold Pi
  rw [hb.h1, hb.hA, hb.hB, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _), Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    log_exp_polar _ hb.hc1, log_exp_polar _ hb.hcA, log_exp_polar _ hb.hcB, ← Complex.exp_add, ← Complex.exp_sub]

/-- `zw = exp (R + c i)` with `c = γ + θ - α_C c₁ - α_A c_A - α_B c_B`. -/
theorem zw_eq {δ θ r1 c1 rA cA rB cB : ℝ} (hb : Bases δ (Complex.exp ((θ : ℂ) * Complex.I)) r1 c1 rA cA rB cB) :
    zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * wf δ (Complex.exp ((θ : ℂ) * Complex.I)) =
      Complex.exp (((-(aC * r1 + aA * rA + aB * rB) : ℝ) : ℂ) +
        ((gam δ + θ - aC * c1 - aA * cA - aB * cB : ℝ) : ℂ) * Complex.I) := by
  rw [explicit_product, Pi_eq hb, sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- `arg zw = γ + θ - α_C c₁ - α_A c_A - α_B c_B` when this lies in `(-π, π]`. -/
theorem arg_zw {δ θ r1 c1 rA cA rB cB : ℝ} (hb : Bases δ (Complex.exp ((θ : ℂ) * Complex.I)) r1 c1 rA cA rB cB)
    (hc : gam δ + θ - aC * c1 - aA * cA - aB * cB ∈ Ioc (-π) π) :
    Complex.arg (zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * wf δ (Complex.exp ((θ : ℂ) * Complex.I))) =
      gam δ + θ - aC * c1 - aA * cA - aB * cB := by
  rw [zw_eq hb, arg_exp_polar _ hc]

/-- `Y = y₂ (δ/(2π) + (c_B - c_A)/π) + (…) i` when `c_B - c_A ∈ (-π, π]`. -/
theorem Yf_eq {δ : ℝ} {ζ : ℂ} {r1 c1 rA cA rB cB : ℝ} (hb : Bases δ ζ r1 c1 rA cA rB cB)
    (hBA : cB - cA ∈ Ioc (-π) π) :
    Yf δ ζ = ((y2 * (δ / (2 * π) + (cB - cA) / π) : ℝ) : ℂ) + ((-(y2 * (rB - rA) / π)) : ℝ) * Complex.I := by
  have e : ((rB : ℂ) + (cB : ℂ) * Complex.I) - ((rA : ℂ) + (cA : ℂ) * Complex.I) =
      ((rB - rA : ℝ) : ℂ) + ((cB - cA : ℝ) : ℂ) * Complex.I := by push_cast; ring
  unfold Yf
  rw [hb.hA, hb.hB, ← Complex.exp_sub, e, log_exp_polar _ hBA, one_div, mul_inv, Complex.inv_I]
  push_cast
  linear_combination (-(y2 : ℂ) * (π : ℂ)⁻¹ * ((cB : ℂ) - cA)) * Complex.I_sq

/-- `log(‖z‖/‖w‖) = Re Y = y₂ (δ/(2π) + (c_B - c_A)/π)` on `|ζ| = 1`. -/
theorem logratio_eq {δ : ℝ} {ζ : ℂ} {r1 c1 rA cA rB cB : ℝ} (hb : Bases δ ζ r1 c1 rA cA rB cB)
    (hBA : cB - cA ∈ Ioc (-π) π) (hζ : ‖ζ‖ = 1) :
    Real.log (‖zf δ ζ‖ / ‖wf δ ζ‖) = y2 * (δ / (2 * π) + (cB - cA) / π) := by
  have hP0 : ‖Pi δ ζ‖ ≠ 0 := by rw [Pi_eq hb]; exact norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)
  have hI (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  have hZ : ‖zf δ ζ‖ = ‖Pi δ ζ‖ * Real.exp ((Yf δ ζ).re / 2) := by
    unfold zf; rw [norm_mul, norm_mul, hI, Complex.norm_exp]; simp
  have hW : ‖wf δ ζ‖ = ‖Pi δ ζ‖ * Real.exp (-(Yf δ ζ).re / 2) := by
    unfold wf; rw [norm_mul, norm_mul, norm_mul, hI, hζ, Complex.norm_exp]; simp [neg_div]
  rw [hZ, hW, mul_div_mul_left _ _ hP0, ← Real.exp_sub, Real.log_exp, Yf_eq hb hBA, re_polar]
  ring

/-! ## The three arcs (any `0 < δ < 2`) -/

theorem bA_mem : bA ∈ Ioc (-π) π := by
  unfold bA; constructor <;> linarith [pi_gt_three]

theorem tS_mem : tS ∈ Ioc (-π) π := by
  unfold tS; constructor <;> linarith [pi_gt_three]

/-- `π α_A = t* + 2π/3` and `π α_B = b - t*`. -/
theorem pi_mul_exps : π * aA = tS + 2 * π / 3 ∧ π * aB = bA - tS := by
  have hpi : π ≠ 0 := pi_ne_zero
  constructor
  · unfold aA; field_simp
  · unfold aB; field_simp

/-- Arc 1, `θ ∈ (-π, -δ/2)`: `arg zw = -2π/3`, `log|z/w| = 0`. -/
theorem arc1 {δ θ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2) (h0 : -π < θ) (h1 : θ < -(δ / 2)) :
    Complex.arg (zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * wf δ (Complex.exp ((θ : ℂ) * Complex.I))) = -(2 * π / 3) ∧
      Real.log (‖zf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ / ‖wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖) = 0 := by
  have hpi := pi_gt_three
  obtain ⟨hzA, hzB⟩ := zeta_mul_e δ θ
  have hb : Bases δ (Complex.exp ((θ : ℂ) * Complex.I)) (Real.log (2 * Real.cos (θ / 2))) (θ / 2)
      (Real.log (-(2 * Real.sin ((θ + δ / 2) / 2)))) (((θ + δ / 2) + π) / 2)
      (Real.log (-(2 * Real.sin ((θ - δ / 2) / 2)))) (((θ - δ / 2) + π) / 2) :=
    { h1 := one_add_exp_eq h0 (by linarith)
      hA := by rw [hzA]; exact one_sub_exp_eq_neg (by linarith) (by linarith)
      hB := by rw [hzB]; exact one_sub_exp_eq_neg (by linarith) (by linarith)
      hc1 := ⟨by linarith, by linarith⟩
      hcA := ⟨by linarith, by linarith⟩
      hcB := ⟨by linarith, by linarith⟩ }
  have hc : gam δ + θ - aC * (θ / 2) - aA * (((θ + δ / 2) + π) / 2) - aB * (((θ - δ / 2) + π) / 2) =
      -(2 * π / 3) := by
    unfold gam aC; linear_combination (-1 : ℝ) * pi_mul_exps.1 + (-1 : ℝ) * pi_mul_exps.2
  refine ⟨?_, ?_⟩
  · rw [arg_zw hb (by rw [hc]; constructor <;> linarith), hc]
  · rw [logratio_eq hb ⟨by linarith, by linarith⟩ (Complex.norm_exp_ofReal_mul_I θ)]
    ring

/-- Arc 2, `θ ∈ (-δ/2, δ/2)`: `arg zw = t*`, `log|z/w| = y₂`. -/
theorem arc2 {δ θ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2) (h0 : -(δ / 2) < θ) (h1 : θ < δ / 2) :
    Complex.arg (zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * wf δ (Complex.exp ((θ : ℂ) * Complex.I))) = tS ∧
      Real.log (‖zf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ / ‖wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖) = y2 := by
  have hpi := pi_gt_three
  obtain ⟨hzA, hzB⟩ := zeta_mul_e δ θ
  have hb : Bases δ (Complex.exp ((θ : ℂ) * Complex.I)) (Real.log (2 * Real.cos (θ / 2))) (θ / 2)
      (Real.log (2 * Real.sin ((θ + δ / 2) / 2))) (((θ + δ / 2) - π) / 2)
      (Real.log (-(2 * Real.sin ((θ - δ / 2) / 2)))) (((θ - δ / 2) + π) / 2) :=
    { h1 := one_add_exp_eq (by linarith) (by linarith)
      hA := by rw [hzA]; exact one_sub_exp_eq_pos (by linarith) (by linarith)
      hB := by rw [hzB]; exact one_sub_exp_eq_neg (by linarith) (by linarith)
      hc1 := ⟨by linarith, by linarith⟩
      hcA := ⟨by linarith, by linarith⟩
      hcB := ⟨by linarith, by linarith⟩ }
  have hc : gam δ + θ - aC * (θ / 2) - aA * (((θ + δ / 2) - π) / 2) - aB * (((θ - δ / 2) + π) / 2) = tS := by
    unfold gam aC; linear_combination (-1 : ℝ) * pi_mul_exps.2
  refine ⟨?_, ?_⟩
  · rw [arg_zw hb (by rw [hc]; exact tS_mem), hc]
  · rw [logratio_eq hb ⟨by linarith, by linarith⟩ (Complex.norm_exp_ofReal_mul_I θ)]
    have hpi0 : π ≠ 0 := pi_ne_zero
    field_simp; ring

/-- Arc 3, `θ ∈ (δ/2, π)`: `arg zw = b`, `log|z/w| = 0`. -/
theorem arc3 {δ θ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2) (h0 : δ / 2 < θ) (h1 : θ < π) :
    Complex.arg (zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * wf δ (Complex.exp ((θ : ℂ) * Complex.I))) = bA ∧
      Real.log (‖zf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ / ‖wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖) = 0 := by
  have hpi := pi_gt_three
  obtain ⟨hzA, hzB⟩ := zeta_mul_e δ θ
  have hb : Bases δ (Complex.exp ((θ : ℂ) * Complex.I)) (Real.log (2 * Real.cos (θ / 2))) (θ / 2)
      (Real.log (2 * Real.sin ((θ + δ / 2) / 2))) (((θ + δ / 2) - π) / 2)
      (Real.log (2 * Real.sin ((θ - δ / 2) / 2))) (((θ - δ / 2) - π) / 2) :=
    { h1 := one_add_exp_eq (by linarith) h1
      hA := by rw [hzA]; exact one_sub_exp_eq_pos (by linarith) (by linarith)
      hB := by rw [hzB]; exact one_sub_exp_eq_pos (by linarith) (by linarith)
      hc1 := ⟨by linarith, by linarith⟩
      hcA := ⟨by linarith, by linarith⟩
      hcB := ⟨by linarith, by linarith⟩ }
  have hc : gam δ + θ - aC * (θ / 2) - aA * (((θ + δ / 2) - π) / 2) - aB * (((θ - δ / 2) - π) / 2) = bA := by
    unfold gam aC; ring
  refine ⟨?_, ?_⟩
  · rw [arg_zw hb (by rw [hc]; exact bA_mem), hc]
  · rw [logratio_eq hb ⟨by linarith, by linarith⟩ (Complex.norm_exp_ofReal_mul_I θ)]
    ring

end ArcsAux

open ArcsAux in
/-- C13e, Prop. 8 proof: with `δ = e^{-2500}`, on the arcs `(-π, -δ/2)`, `(-δ/2, δ/2)`, `(δ/2, π)` one has
`(arg zw, log|z/w|) = (-2π/3, 0)`, `(t*, y₂)`, `(b, 0)`. Type identical to `P18.Paper.C13e_explicit_arcs`. -/
theorem explicit_arcs :
    let δ := exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    (∀ θ ∈ Ioo (-π) (-(δ / 2)), Complex.arg (Z θ * W θ) = -(2 * π / 3) ∧ log (‖Z θ‖ / ‖W θ‖) = 0) ∧
    (∀ θ ∈ Ioo (-(δ / 2)) (δ / 2), Complex.arg (Z θ * W θ) = Explicit.tS ∧ log (‖Z θ‖ / ‖W θ‖) = Explicit.y2) ∧
    (∀ θ ∈ Ioo (δ / 2) π, Complex.arg (Z θ * W θ) = Explicit.bA ∧ log (‖Z θ‖ / ‖W θ‖) = 0) := by
  intro δ Z W
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ2 : δ < 2 := by
    have : δ < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  exact ⟨fun θ hθ => arc1 hδ0 hδ2 hθ.1 hθ.2, fun θ hθ => arc2 hδ0 hδ2 hθ.1 hθ.2,
    fun θ hθ => arc3 hδ0 hδ2 hθ.1 hθ.2⟩

end P18
