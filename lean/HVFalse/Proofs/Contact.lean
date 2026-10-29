/-
  HVFalse/Proofs/Contact.lean - Lemma contact, quadratic part (the paper): Γ(0,t) ≤ e(t) + C (t ∓ π/p)^2
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route: for 0 ≤ q ≤ 1 and x ≥ 0, Bernoulli gives x^q ≤ 1 + q(x - 1). With x = (1 + cos t)/(1 + cos(π/p)) this bounds
  Γ(0,t) = x^q - 1 by q (cos t - cos(π/p))/(1 + cos(π/p)), so Γ(0,t) - e(t) ≤ χ(t), a trig polynomial in t and qt.
  The paper's sentence "m ≤ e + C(t ∓ π/p)^2 near ±π/p" then follows from m(t) ≤ Γ(0,t).
-/
import HVFalse.Proofs.Bridges
import Mathlib.Analysis.Calculus.MeanValue

open Real

namespace P18

/-- Two mean-value steps: if `f a = 0`, `f' a = 0` and `|f''| ≤ M` everywhere, then `|f t| ≤ M (t - a)^2`. -/
theorem abs_le_of_second_deriv_bound {f f' f'' : ℝ → ℝ} {M a : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hM : ∀ x, |f'' x| ≤ M)
    (h0 : f a = 0) (h1 : f' a = 0) (t : ℝ) : |f t| ≤ M * (t - a) ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a)
  have step1 : ∀ x, |f' x| ≤ M * |x - a| := by
    intro x
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f') (f' := f'') (s := Set.univ)
      (fun z _ => (hf' z).hasDerivWithinAt) (fun z _ => by rw [Real.norm_eq_abs]; exact hM z) convex_univ
      (Set.mem_univ a) (Set.mem_univ x)
    rw [h1, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f') (s := Set.uIcc a t)
    (C := M * |t - a|) (fun z _ => (hf z).hasDerivWithinAt)
    (fun z hz => by
      rw [Real.norm_eq_abs]
      exact le_trans (step1 z) (mul_le_mul_of_nonneg_left (Set.abs_sub_left_of_mem_uIcc hz) hM0))
    (convex_uIcc a t) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |f t| ≤ M * |t - a| * |t - a| := h
    _ = M * (t - a) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

/-- `χ(t) = q (cos t - cos(π/p))/(1 + cos(π/p)) - e(t)`: the Bernoulli upper bound of `Γ(0,t) - e(t)`. -/
noncomputable def chi (p t : ℝ) : ℝ :=
  p / 2 * (cos t - cos (π / p)) / (1 + cos (π / p)) - tan (π / (2 * p)) * cos (p / 2 * t)

/-- `χ'`. -/
noncomputable def chi1 (p t : ℝ) : ℝ :=
  p / 2 * -sin t / (1 + cos (π / p)) + tan (π / (2 * p)) * (p / 2) * sin (p / 2 * t)

/-- `χ''`. -/
noncomputable def chi2 (p t : ℝ) : ℝ :=
  p / 2 * -cos t / (1 + cos (π / p)) + tan (π / (2 * p)) * (p / 2) ^ 2 * cos (p / 2 * t)

theorem chi_hasDerivAt (p t : ℝ) : HasDerivAt (chi p) (chi1 p t) t := by
  have h1 := (((hasDerivAt_cos t).sub_const (cos (π / p))).const_mul (p / 2)).div_const (1 + cos (π / p))
  have h2 := (((hasDerivAt_id' t).const_mul (p / 2)).cos).const_mul (tan (π / (2 * p)))
  have h3 := h1.sub h2
  unfold chi chi1
  convert h3 using 1
  ring

theorem chi1_hasDerivAt (p t : ℝ) : HasDerivAt (chi1 p) (chi2 p t) t := by
  have h1 := ((hasDerivAt_sin t).neg.const_mul (p / 2)).div_const (1 + cos (π / p))
  have h2 := (((hasDerivAt_id' t).const_mul (p / 2)).sin).const_mul (tan (π / (2 * p)) * (p / 2))
  have h3 := h1.add h2
  unfold chi1 chi2
  convert h3 using 1
  ring

/-- `|χ''| ≤ M` with `M = (p/2)/(1 + cos(π/p)) + |tan ϑ| (p/2)^2`. -/
theorem chi2_bound (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (t : ℝ) :
    |chi2 p t| ≤ p / 2 / (1 + cos (π / p)) + |tan (π / (2 * p))| * (p / 2) ^ 2 := by
  have hd := denom_pos p hp1 hp2
  have hA : 0 < p / 2 / (1 + cos (π / p)) := div_pos (by linarith) hd
  have e1 : p / 2 * -cos t / (1 + cos (π / p)) = -(p / 2 / (1 + cos (π / p))) * cos t := by
    field_simp
  have hk : |tan (π / (2 * p)) * cos (p / 2 * t)| ≤ |tan (π / (2 * p))| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have hkab := abs_le.mp hk
  have hc1 := neg_one_le_cos t
  have hc2 := cos_le_one t
  have hq2 : 0 ≤ (p / 2) ^ 2 := sq_nonneg _
  unfold chi2
  rw [e1]
  have e2 : tan (π / (2 * p)) * (p / 2) ^ 2 * cos (p / 2 * t) =
      (p / 2) ^ 2 * (tan (π / (2 * p)) * cos (p / 2 * t)) := by ring
  rw [e2, abs_le]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hkab.1 hq2, mul_le_mul_of_nonneg_left hkab.2 hq2]

theorem chi_contact (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : chi p (π / p) = 0 := by
  have hpos : 0 < p := by linarith
  have e : p / 2 * (π / p) = π / 2 := by field_simp
  unfold chi
  rw [e, cos_pi_div_two]
  ring

theorem chi_contact_neg (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : chi p (-(π / p)) = 0 := by
  have hpos : 0 < p := by linarith
  have e : p / 2 * -(π / p) = -(π / 2) := by field_simp
  unfold chi
  rw [e, cos_neg, cos_neg, cos_pi_div_two]
  ring

theorem chi1_contact (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : chi1 p (π / p) = 0 := by
  have hpos : 0 < p := by linarith
  have hd := denom_pos p hp1 hp2
  have ha := half_angle p hp1 hp2
  have e : p / 2 * (π / p) = π / 2 := by field_simp
  unfold chi1
  rw [e, sin_pi_div_two, ← ha]
  field_simp
  ring

theorem chi1_contact_neg (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : chi1 p (-(π / p)) = 0 := by
  have hpos : 0 < p := by linarith
  have hd := denom_pos p hp1 hp2
  have ha := half_angle p hp1 hp2
  have e : p / 2 * -(π / p) = -(π / 2) := by field_simp
  unfold chi1
  rw [e, sin_neg, sin_neg, sin_pi_div_two, ← ha]
  field_simp
  ring

/-- Bernoulli step: `Γ(0,t) - e(t) ≤ χ(t)` for every `t` and every `s`. -/
theorem gam_zero_sub_ee_le_chi (p s t : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Gam p s 0 t - ee p t ≤ chi p t := by
  have hd := denom_pos p hp1 hp2
  have hsv : (cosh 0 + cos t) / (1 + cos (π / p)) = 1 + (cos t - cos (π / p)) / (1 + cos (π / p)) := by
    rw [cosh_zero]; field_simp; ring
  have hge : -1 ≤ (cos t - cos (π / p)) / (1 + cos (π / p)) := by
    have h0 : 0 ≤ (cosh 0 + cos t) / (1 + cos (π / p)) := by
      rw [cosh_zero]; exact div_nonneg (by linarith [neg_one_le_cos t]) hd.le
    linarith [hsv ▸ h0]
  have hb := rpow_one_add_le_one_add_mul_self hge (p := p / 2) (by linarith) (by linarith)
  rw [gam_eq_div p s 0 t hp1 hp2, hsv, mul_zero, zero_div, cosh_zero, one_rpow]
  unfold chi ee
  rw [mul_div_assoc]
  linarith

/-- C05 (global form): one constant `C` works for every `t`, at both contact points `±π/p`, for every `s`. -/
theorem contact_quadratic_global (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, ∀ t : ℝ, Gam p s 0 t ≤ ee p t + C * (t - π / p) ^ 2 ∧
      Gam p s 0 t ≤ ee p t + C * (t + π / p) ^ 2 := by
  refine ⟨p / 2 / (1 + cos (π / p)) + |tan (π / (2 * p))| * (p / 2) ^ 2, fun t => ⟨?_, ?_⟩⟩
  · have h := abs_le_of_second_deriv_bound (chi_hasDerivAt p) (chi1_hasDerivAt p) (chi2_bound p hp1 hp2)
      (chi_contact p hp1 hp2) (chi1_contact p hp1 hp2) t
    linarith [gam_zero_sub_ee_le_chi p s t hp1 hp2, le_abs_self (chi p t)]
  · have h := abs_le_of_second_deriv_bound (chi_hasDerivAt p) (chi1_hasDerivAt p) (chi2_bound p hp1 hp2)
      (chi_contact_neg p hp1 hp2) (chi1_contact_neg p hp1 hp2) t
    rw [sub_neg_eq_add] at h
    linarith [gam_zero_sub_ee_le_chi p s t hp1 hp2, le_abs_self (chi p t)]

/-- C05, the statement shape at `+π/p` (paper: "m ≤ e + C(t - π/p)^2 near π/p", with `m(t) ≤ Γ(0,t)`). -/
theorem contact_quadratic {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t, |t - π / p| < δ → Gam p s 0 t ≤ ee p t + C * (t - π / p) ^ 2 := by
  obtain ⟨C, hC⟩ := contact_quadratic_global p s hp1 hp2
  exact ⟨C, 1, one_pos, fun t _ => (hC t).1⟩

/-- C05 at `-π/p`. -/
theorem contact_quadratic_neg {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t, |t + π / p| < δ → Gam p s 0 t ≤ ee p t + C * (t + π / p) ^ 2 := by
  obtain ⟨C, hC⟩ := contact_quadratic_global p s hp1 hp2
  exact ⟨C, 1, one_pos, fun t _ => (hC t).2⟩

end P18
