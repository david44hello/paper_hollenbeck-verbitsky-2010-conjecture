/-
  HVFalse/Proofs/Bridges.lean - 34 elementary bridge theorems (T1-T5), moved VERBATIM
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Basic

open Real

namespace P18

/-! ## T1: the algebra of Prop. saddle -/

/-- Paper: "with S = u + 1, 2K(S-2) - 3(2-p)^2 S = -H". -/
theorem saddle_identity (p u : ℝ) :
    2 * K p u * ((u+1) - 2) - 3*(2-p)^2*(u+1) = - H p u := by
  unfold K H; ring

/-- Paper: "H(4/3,u) = -(2/3)(u^2 - 6u + 1)". -/
theorem H_four_thirds (u : ℝ) : H (4/3) u = -(2/3)*(u^2 - 6*u + 1) := by
  unfold H; ring

/-- Paper: the y^4 coefficient a40 at s = S. -/
theorem a40_identity (p S : ℝ) :
    p*S^3/192 - p^2*S^2/128 + p*S/96 + p*(p-2)*S^2/128 = p*S*(S-1)*(S-2)/192 := by
  ring

/-- Paper: A = a40 - a21^2/(4 a02) = -pSuH/(384K), with S = u+1, a21^2 = p^2(2-p)^2 u S^2/256, a02 = pK/8. -/
theorem A_identity (p u : ℝ) (hp : p ≠ 0) (hK : K p u ≠ 0) :
    p*(u+1)*u*((u+1)-2)/192 - (p^2*(2-p)^2*u*(u+1)^2/256) / (4*(p*K p u/8))
      = -(p*(u+1)*u*H p u)/(384*K p u) := by
  field_simp
  unfold K H
  ring

/-- Paper (i): u(4/3) = 3 + 2 sqrt 2 is a root of u^2 - 6u + 1. -/
theorem u43_root : (3 + 2*Real.sqrt 2)^2 - 6*(3 + 2*Real.sqrt 2) + 1 = 0 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  linear_combination (4:ℝ) * h

/-- Paper (i): tan^2(3 pi/8) = 3 + 2 sqrt 2. -/
theorem tan_three_pi_div_eight_sq : Real.tan (3*Real.pi/8)^2 = 3 + 2*Real.sqrt 2 := by
  have h1 : 3*Real.pi/8 = Real.pi/2 - Real.pi/8 := by ring
  have h2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2' : (0:ℝ) ≤ 2 - Real.sqrt 2 := by linarith
  have hs2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.sq_sqrt (show (0:ℝ) ≤ 2 + Real.sqrt 2 by positivity)
  have hm := Real.sq_sqrt h2'
  have hm0 : 0 < Real.sqrt (2 - Real.sqrt 2) := Real.sqrt_pos.mpr (by linarith)
  rw [Real.tan_eq_sin_div_cos, h1, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub,
    Real.cos_pi_div_eight, Real.sin_pi_div_eight, div_pow, div_pow, div_pow, hp, hm]
  have hden : (2 - Real.sqrt 2) ≠ 0 := by linarith
  field_simp
  linear_combination (2:ℝ) * hs2

/-- Paper (iii): K(4/3) = 2 sqrt 2/3, with u(4/3) = 3 + 2 sqrt 2. -/
theorem K_four_thirds : K (4/3) (3 + 2*Real.sqrt 2) = 2*Real.sqrt 2/3 := by
  unfold K; ring

/-- Paper (ii): H(2,1) = 0 and both partial derivatives of H vanish at (2,1). -/
theorem H_two_one : H 2 1 = 0 ∧ (-2*(1:ℝ)^2 + (6*2-10)*1 - 6*(2-2)) = 0 ∧ (-4*((2:ℝ)-1)*1 + 3*(2-2)^2 + 2*2) = 0 := by
  unfold H; norm_num

/-- Paper (ii): d^2H/dp^2 at p = 2 equals 12 + 2 pi - pi^2 > 0. -/
theorem H_second_deriv_pos : 0 < 12 + 2*Real.pi - Real.pi^2 := by
  nlinarith [Real.pi_lt_d2, Real.pi_gt_three]

/-! ## T2: Lemma contact and the pointwise part of Lemma lift -/

/-- `1 + cos(pi/p) = 2 cos^2(pi/(2p)) > 0` for 1 < p < 2. -/
theorem denom_pos (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : 0 < 1 + cos (π / p) := by
  have hpos : 0 < p := by linarith
  have hth : π / p = 2 * (π / (2 * p)) := by field_simp
  have hc : 0 < cos (π / (2 * p)) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / (2 * p) := by positivity
      linarith [pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pi_pos]
  rw [hth, cos_two_mul]
  nlinarith [sq_nonneg (cos (π / (2 * p)))]

/-- Bridge to the working form: Gam p s y t = ((cosh y + cos t)/(1 + cos(pi/p)))^(p/2) - cosh(s y/2)^(p/s). -/
theorem gam_eq_div (p s y t : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    Gam p s y t = ((cosh y + cos t) / (1 + cos (π / p))) ^ (p / 2) - cosh (s * y / 2) ^ (p / s) := by
  have hpos : 0 < p := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hC : 0 ≤ cosh y + cos t := by nlinarith [one_le_cosh y, neg_one_le_cos t]
  unfold Gam
  rw [h2, div_rpow hC (denom_pos p hp1 hp2).le]

/-- Paper, Lemma contact: Gamma(0, pi/p) = 0 (for every s). -/
theorem gam_contact (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : Gam p s 0 (π / p) = 0 := by
  have hd := denom_pos p hp1 hp2
  rw [gam_eq_div p s 0 (π / p) hp1 hp2]
  simp [cosh_zero, div_self hd.ne']

/-- Paper, Lemma contact: Gamma(0, -pi/p) = 0 (for every s). -/
theorem gam_contact_neg (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) : Gam p s 0 (-(π / p)) = 0 := by
  have hd := denom_pos p hp1 hp2
  rw [gam_eq_div p s 0 (-(π / p)) hp1 hp2]
  simp [cosh_zero, cos_neg, div_self hd.ne']

/-- sin(pi/p) / (1 + cos(pi/p)) = tan(pi/(2p)) (half-angle), for 1 < p < 2. -/
theorem half_angle (p : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    sin (π / p) / (1 + cos (π / p)) = tan (π / (2 * p)) := by
  have hpos : 0 < p := by linarith
  have hth : π / p = 2 * (π / (2 * p)) := by field_simp
  have hd := denom_pos p hp1 hp2
  have hc : cos (π / (2 * p)) ≠ 0 := by
    intro h0
    rw [hth, cos_two_mul, h0] at hd
    norm_num at hd
  rw [hth] at hd ⊢
  rw [sin_two_mul, cos_two_mul, tan_eq_sin_div_cos]
  have hd' : 1 + (2 * cos (π / (2 * p)) ^ 2 - 1) ≠ 0 := by
    rw [cos_two_mul] at hd; exact hd.ne'
  field_simp
  ring

/-- Paper, Lemma contact: psi = Gamma(0, .) - e has psi'(pi/p) = 0 (for every s). -/
theorem psi_deriv_contact (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (fun t => Gam p s 0 t - ee p t) 0 (π / p) := by
  have hpos : 0 < p := by linarith
  have hd := denom_pos p hp1 hp2
  set D := 1 + cos (π / p) with hD
  have hbase : (1 + cos (π / p)) / D = 1 := div_self hd.ne'
  have hf : HasDerivAt (fun t => (1 + cos t) / D) (-sin (π / p) / D) (π / p) :=
    ((hasDerivAt_cos (π / p)).const_add 1).div_const D
  have h1 := hf.rpow_const (p := p / 2) (Or.inl (by rw [hbase]; norm_num))
  have hg : HasDerivAt (fun t => cos (p / 2 * t)) (-sin (p / 2 * (π / p)) * (p / 2)) (π / p) := by
    have := ((hasDerivAt_id (π / p)).const_mul (p / 2)).cos
    simpa using this
  have h2 := hg.const_mul (tan (π / (2 * p)))
  have hfun : (fun t => Gam p s 0 t - ee p t)
      = (fun t => ((1 + cos t) / D) ^ (p / 2) - 1 - tan (π / (2 * p)) * cos (p / 2 * t)) := by
    funext t; rw [gam_eq_div p s 0 t hp1 hp2]; unfold ee; simp [cosh_zero, hD]
  rw [hfun]
  have hq : p / 2 * (π / p) = π / 2 := by field_simp
  have key := (h1.sub_const 1).sub h2
  convert key using 1
  rw [hbase, Real.one_rpow, hq, sin_pi_div_two, ← half_angle p hp1 hp2]
  ring

/-- Paper, Lemma contact: psi'(-pi/p) = 0 (for every s). -/
theorem psi_deriv_contact_neg (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (fun t => Gam p s 0 t - ee p t) 0 (-(π / p)) := by
  have hpos : 0 < p := by linarith
  have hd := denom_pos p hp1 hp2
  set D := 1 + cos (π / p) with hD
  have hbase : (1 + cos (-(π / p))) / D = 1 := by rw [cos_neg]; exact div_self hd.ne'
  have hf : HasDerivAt (fun t => (1 + cos t) / D) (-sin (-(π / p)) / D) (-(π / p)) :=
    ((hasDerivAt_cos (-(π / p))).const_add 1).div_const D
  have h1 := hf.rpow_const (p := p / 2) (Or.inl (by rw [hbase]; norm_num))
  have hg : HasDerivAt (fun t => cos (p / 2 * t)) (-sin (p / 2 * -(π / p)) * (p / 2)) (-(π / p)) := by
    have := ((hasDerivAt_id (-(π / p))).const_mul (p / 2)).cos
    simpa using this
  have h2 := hg.const_mul (tan (π / (2 * p)))
  have hfun : (fun t => Gam p s 0 t - ee p t)
      = (fun t => ((1 + cos t) / D) ^ (p / 2) - 1 - tan (π / (2 * p)) * cos (p / 2 * t)) := by
    funext t; rw [gam_eq_div p s 0 t hp1 hp2]; unfold ee; simp [cosh_zero, hD]
  rw [hfun]
  have hq : p / 2 * -(π / p) = -(π / 2) := by field_simp
  have key := (h1.sub_const 1).sub h2
  convert key using 1
  rw [hbase, Real.one_rpow, hq, sin_neg, sin_neg, sin_pi_div_two, ← half_angle p hp1 hp2]
  ring

open ComplexConjugate in
/-- |z + conj w|^2 = |z|^2 + |w|^2 + 2 Re(z w). -/
theorem norm_add_conj_sq (z w : ℂ) : ‖z + conj w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * w).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.normSq_conj,
    Complex.conj_conj]

/-- For a, b > 0: a^2 + b^2 = 2 a b cosh(log(a/b)). -/
theorem sq_add_sq_cosh (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 + b ^ 2 = 2 * (a * b) * cosh (log (a / b)) := by
  rw [cosh_eq, exp_neg, exp_log (div_pos ha hb)]
  field_simp

/-- For a, b > 0, s real: a^s + b^s = 2 (a b)^(s/2) cosh(s log(a/b)/2). -/
theorem rpow_add_rpow_cosh (a b s : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a ^ s + b ^ s = 2 * (a * b) ^ (s / 2) * cosh (s * log (a / b) / 2) := by
  rw [rpow_def_of_pos ha, rpow_def_of_pos hb, rpow_def_of_pos (mul_pos ha hb), cosh_eq,
    log_mul ha.ne' hb.ne', log_div ha.ne' hb.ne']
  rw [show 2 * exp ((log a + log b) * (s / 2)) * ((exp (s * (log a - log b) / 2) + exp (-(s * (log a - log b) / 2))) / 2)
      = exp ((log a + log b) * (s / 2)) * exp (s * (log a - log b) / 2)
        + exp ((log a + log b) * (s / 2)) * exp (-(s * (log a - log b) / 2)) by ring]
  rw [← exp_add, ← exp_add]
  congr 1 <;> congr 1 <;> ring

/-- x^p = (x^2)^(p/2) for x >= 0. -/
theorem rpow_eq_sq_rpow (x p : ℝ) (hx : 0 ≤ x) : x ^ p = (x ^ 2) ^ (p / 2) := by
  rw [← rpow_natCast, ← rpow_mul hx]
  congr 1
  push_cast
  ring

open ComplexConjugate in
/-- Paper, Lemma lift (pointwise part): for z, w != 0, with A = 1/(2 cos(pi/2p)),
    A^p |z + conj w|^p - ((|z|^s + |w|^s)/2)^(p/s) = |zw|^(p/2) Gamma(log|z/w|, arg(zw)). -/
theorem lift_pointwise (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    (1 / (2 * cos (π / (2 * p)))) ^ p * ‖z + conj w‖ ^ p - ((‖z‖ ^ s + ‖w‖ ^ s) / 2) ^ (p / s)
      = ‖z * w‖ ^ (p / 2) * Gam p s (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) := by
  have hpos : 0 < p := by linarith
  have ha : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set a := ‖z‖ with ha_def
  set b := ‖w‖ with hb_def
  set y := log (a / b) with hy
  set t := Complex.arg (z * w) with ht
  have hd := denom_pos p hp1 hp2
  have hth : π / p = 2 * (π / (2 * p)) := by field_simp
  have hc : 0 < cos (π / (2 * p)) := by
    apply cos_pos_of_mem_Ioo
    constructor
    · have : 0 < π / (2 * p) := by positivity
      linarith [pi_pos]
    · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [pi_pos]
  have hD : 1 + cos (π / p) = 2 * cos (π / (2 * p)) ^ 2 := by rw [hth, cos_two_mul]; ring
  have hre : (z * w).re = a * b * cos t := by
    rw [← Complex.norm_mul_cos_arg, norm_mul]
  have hC : 0 ≤ cosh y + cos t := by nlinarith [one_le_cosh y, neg_one_le_cos t]
  -- first term: A^p |z + conj w|^p = (a b)^(p/2) ((cosh y + cos t)/(1 + cos(pi/p)))^(p/2)
  have hsq : ‖z + conj w‖ ^ 2 = 2 * (a * b) * (cosh y + cos t) := by
    rw [norm_add_conj_sq, hre, sq_add_sq_cosh a b ha hb]; ring
  have hA : 0 < 1 / (2 * cos (π / (2 * p))) := by positivity
  have hfirst : (1 / (2 * cos (π / (2 * p)))) ^ p * ‖z + conj w‖ ^ p
      = (a * b) ^ (p / 2) * ((cosh y + cos t) / (1 + cos (π / p))) ^ (p / 2) := by
    rw [rpow_eq_sq_rpow _ p hA.le, rpow_eq_sq_rpow _ p (norm_nonneg _), hsq,
      ← mul_rpow (by positivity) (by positivity), ← mul_rpow (by positivity) (by positivity)]
    congr 1
    rw [hD]
    field_simp
  -- second term: ((a^s + b^s)/2)^(p/s) = (a b)^(p/2) cosh(s y/2)^(p/s)
  have hsecond : ((a ^ s + b ^ s) / 2) ^ (p / s) = (a * b) ^ (p / 2) * cosh (s * y / 2) ^ (p / s) := by
    rw [rpow_add_rpow_cosh a b s ha hb,
      show 2 * (a * b) ^ (s / 2) * cosh (s * log (a / b) / 2) / 2 = (a * b) ^ (s / 2) * cosh (s * y / 2) by rw [hy]; ring,
      mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity)]
    congr 2
    field_simp
  rw [hfirst, hsecond, norm_mul, gam_eq_div p s y t hp1 hp2]
  ring

/-! ## T3: Prop. point -/

/-- Bridge: an upper bound of `x^(m/n)` from the integer-power comparison `x^m ≤ b^n`. -/
lemma rpow_le_of_pow_le {x b : ℝ} {m n : ℕ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hn : n ≠ 0)
    (h : x ^ m ≤ b ^ n) : x ^ ((m : ℝ) / n) ≤ b := by
  rw [div_eq_mul_inv, rpow_mul hx, rpow_natCast]
  calc (x ^ m) ^ ((n : ℝ)⁻¹) ≤ (b ^ n) ^ ((n : ℝ)⁻¹) :=
        rpow_le_rpow (pow_nonneg hx m) h (by positivity)
    _ = b := pow_rpow_inv_natCast hb hn

/-- Bridge: a lower bound of `x^(m/n)` from the integer-power comparison `b^n ≤ x^m`. -/
lemma le_rpow_of_pow_le {x b : ℝ} {m n : ℕ} (hx : 0 ≤ x) (hb : 0 ≤ b) (hn : n ≠ 0)
    (h : b ^ n ≤ x ^ m) : b ≤ x ^ ((m : ℝ) / n) := by
  rw [div_eq_mul_inv, rpow_mul hx, rpow_natCast]
  calc b = (b ^ n) ^ ((n : ℝ)⁻¹) := (pow_rpow_inv_natCast hb hn).symm
    _ ≤ (x ^ m) ^ ((n : ℝ)⁻¹) := rpow_le_rpow (pow_nonneg hb n) h (by positivity)

/-- The angles and the hyperbolic cosine at the point. -/
lemma angle_facts :
    π / (2 * (3 / 2 : ℝ)) = π / 3 ∧ cos (2 * (π / 3)) = -1 / 2 ∧
    cos ((3 / 2 : ℝ) / 2 * (π / 2)) = √(2 - √2) / 2 ∧ cosh (log (9 / 5)) = 53 / 45 := by
  refine ⟨by ring, ?_, ?_, ?_⟩
  · have h : 2 * (π / 3) = π - π / 3 := by ring
    rw [h, cos_pi_sub, cos_pi_div_three]; norm_num
  · have h : (3 / 2 : ℝ) / 2 * (π / 2) = π / 2 - π / 8 := by ring
    rw [h, cos_pi_div_two_sub, sin_pi_div_eight]
  · rw [cosh_log (by norm_num)]; norm_num

/-- `cosh(s y/2) = X`, with `X = ((9/5)^(199/100) + (5/9)^(199/100))/2` as in the paper. -/
lemma cosh_X :
    cosh ((398 / 100 : ℝ) * log (9 / 5) / 2) =
      ((9 / 5 : ℝ) ^ ((199 : ℝ) / 100) + (5 / 9 : ℝ) ^ ((199 : ℝ) / 100)) / 2 := by
  have hx : (398 / 100 : ℝ) * log (9 / 5) / 2 = log (9 / 5) * ((199 : ℝ) / 100) := by ring
  have h59 : (5 / 9 : ℝ) = (9 / 5 : ℝ)⁻¹ := by norm_num
  have hpos : (0 : ℝ) < 9 / 5 := by norm_num
  rw [hx, cosh_eq, ← mul_neg, ← rpow_def_of_pos hpos, ← rpow_def_of_pos hpos,
    rpow_neg hpos.le, h59, inv_rpow hpos.le]

/-- An earlier draft's Prop. point, closed form: `Γ(y,t) - e(t) = (106/45)^(3/4) - X^(75/199) - √3 √(2-√2)/2`. -/
theorem point_closed_form :
    Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) =
      (106 / 45 : ℝ) ^ ((3 : ℝ) / 4)
        - (((9 / 5 : ℝ) ^ ((199 : ℝ) / 100) + (5 / 9 : ℝ) ^ ((199 : ℝ) / 100)) / 2) ^ ((75 : ℝ) / 199)
        - √3 * √(2 - √2) / 2 := by
  obtain ⟨hθ, h2θ, hqt, hch⟩ := angle_facts
  unfold Gam ee
  rw [hθ, h2θ, hqt, hch, cos_pi_div_two, tan_pi_div_three, cosh_X,
    ← div_rpow (by norm_num : (0 : ℝ) ≤ 53 / 45 + 0) (by norm_num : (0 : ℝ) ≤ 1 + -1 / 2)]
  have hq : (3 / 2 : ℝ) / 2 = 3 / 4 := by norm_num
  have hs : (3 / 2 : ℝ) / (398 / 100) = 75 / 199 := by norm_num
  have hb : ((53 / 45 + 0 : ℝ) / (1 + -1 / 2)) = 106 / 45 := by norm_num
  rw [hq, hs, hb]
  ring

/-- An earlier draft's Prop. point, sign: `Γ(log(9/5), π/2) - e(π/2) < -4.1e-4 < 0` at `(p, s) = (3/2, 398/100)`. -/
theorem point_fails : Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) < -41 / 100000 := by
  rw [point_closed_form]
  -- first term: (106/45)^(3/4) ≤ U1
  have hT1 : (106 / 45 : ℝ) ^ ((3 : ℝ) / 4) ≤ 380277 / 200000 := by
    have h := rpow_le_of_pow_le (x := 106 / 45) (b := 380277 / 200000) (m := 3) (n := 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  -- (9/5)^(199/100) in [a, b], hence X ≥ X0 = (a + 1/b)/2
  have hu_lo : (3221011 / 1000000 : ℝ) ≤ (9 / 5 : ℝ) ^ ((199 : ℝ) / 100) := by
    have h := le_rpow_of_pow_le (x := 9 / 5) (b := 3221011 / 1000000) (m := 199) (n := 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  have hu_hi : (9 / 5 : ℝ) ^ ((199 : ℝ) / 100) ≤ 805253 / 250000 := by
    have h := rpow_le_of_pow_le (x := 9 / 5) (b := 805253 / 250000) (m := 199) (n := 100)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  have hinv : (805253 / 250000 : ℝ)⁻¹ ≤ (5 / 9 : ℝ) ^ ((199 : ℝ) / 100) := by
    rw [show (5 / 9 : ℝ) = (9 / 5 : ℝ)⁻¹ by norm_num, inv_rpow (by norm_num)]
    exact inv_anti₀ (by positivity) hu_hi
  have hX : (3221011 / 1000000 + (805253 / 250000 : ℝ)⁻¹) / 2 ≤
      ((9 / 5 : ℝ) ^ ((199 : ℝ) / 100) + (5 / 9 : ℝ) ^ ((199 : ℝ) / 100)) / 2 := by linarith
  -- second term: X^(75/199) ≥ X0^(75/199) ≥ L2
  have hT2 : (619487 / 500000 : ℝ) ≤
      (((9 / 5 : ℝ) ^ ((199 : ℝ) / 100) + (5 / 9 : ℝ) ^ ((199 : ℝ) / 100)) / 2) ^ ((75 : ℝ) / 199) := by
    have h := le_rpow_of_pow_le (x := (3221011 / 1000000 + (805253 / 250000 : ℝ)⁻¹) / 2)
      (b := 619487 / 500000) (m := 75) (n := 199) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h' : (619487 / 500000 : ℝ) ≤ ((3221011 / 1000000 + (805253 / 250000 : ℝ)⁻¹) / 2) ^ ((75 : ℝ) / 199) := by
      simpa using h
    exact h'.trans (rpow_le_rpow (by norm_num) hX (by norm_num))
  -- third term: √3 √(2 - √2)/2 ≥ s3 c / 2
  have hs3 : (34641 / 20000 : ℝ) ≤ √3 := by
    rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hs2 : √2 ≤ 2 - (382683 / 500000 : ℝ) ^ 2 := by
    rw [sqrt_le_left (by norm_num)]; norm_num
  have hc : (382683 / 500000 : ℝ) ≤ √(2 - √2) := by
    rw [le_sqrt (by norm_num) (by nlinarith [hs2])]; linarith
  have hR : (34641 / 20000 : ℝ) * (382683 / 500000) ≤ √3 * √(2 - √2) :=
    mul_le_mul hs3 hc (by norm_num) (sqrt_nonneg 3)
  linarith

/-! ## T4: the finite part of the relaxation lemma of Sec. 7 -/


/-- Relaxation, part 1: a q-trigonometrically convex function satisfies the discrete inequality of Sec. 7 at every step `h`
    with `2qh < π`, i.e. `φ(t+h) + φ(t-h) - 2 cos(qh) φ(t) ≥ 0`. -/
theorem discrete_of_trigConvex {q h : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hh : 0 < h) (h2 : 2 * q * h < π)
    (hφ : TrigConvex q φ) (t : ℝ) : 2 * cos (q * h) * φ t ≤ φ (t + h) + φ (t - h) := by
  have hqh : 0 < q * h := mul_pos hq hh
  have hlen : q * (t + h - (t - h)) < π := by
    have e : q * (t + h - (t - h)) = 2 * q * h := by ring
    rw [e]; exact h2
  have key := hφ (t - h) t (t + h) (by linarith) (by linarith) hlen
  have e1 : q * (t + h - (t - h)) = 2 * (q * h) := by ring
  have e2 : q * (t + h - t) = q * h := by ring
  have e3 : q * (t - (t - h)) = q * h := by ring
  rw [e1, e2, e3, sin_two_mul] at key
  have hs : 0 < sin (q * h) := sin_pos_of_pos_of_lt_pi hqh (by linarith)
  have l3 : sin (q * h) * (2 * cos (q * h) * φ t) = φ t * (2 * sin (q * h) * cos (q * h)) := by ring
  have l4 : sin (q * h) * (φ (t + h) + φ (t - h)) = φ (t - h) * sin (q * h) + φ (t + h) * sin (q * h) := by ring
  have hmul : sin (q * h) * (2 * cos (q * h) * φ t) ≤ sin (q * h) * (φ (t + h) + φ (t - h)) := by
    rw [l3, l4]; exact key
  exact le_of_mul_le_mul_left hmul hs

/-- The q-sinusoid on the cell `[t0, t0 + h]` with values `a` at `t0` and `b` at `t0 + h` (a solution of `φ'' + q^2 φ = 0`). -/
noncomputable def qsin (q h t0 a b : ℝ) (t : ℝ) : ℝ :=
  (a * sin (q * (t0 + h - t)) + b * sin (q * (t - t0))) / sin (q * h)

theorem qsin_left {q h t0 a b : ℝ} (hs : sin (q * h) ≠ 0) : qsin q h t0 a b t0 = a := by
  unfold qsin
  have e1 : q * (t0 + h - t0) = q * h := by ring
  have e2 : q * (t0 - t0) = 0 := by ring
  rw [e1, e2, sin_zero, mul_zero, add_zero, mul_div_assoc, div_self hs, mul_one]

theorem qsin_right {q h t0 a b : ℝ} (hs : sin (q * h) ≠ 0) : qsin q h t0 a b (t0 + h) = b := by
  unfold qsin
  have e1 : q * (t0 + h - (t0 + h)) = 0 := by ring
  have e2 : q * (t0 + h - t0) = q * h := by ring
  rw [e1, e2, sin_zero, mul_zero, zero_add, mul_div_assoc, div_self hs, mul_one]

theorem qsin_hasDerivAt (q h t0 a b t : ℝ) :
    HasDerivAt (qsin q h t0 a b)
      ((-a * q * cos (q * (t0 + h - t)) + b * q * cos (q * (t - t0))) / sin (q * h)) t := by
  have h1 : HasDerivAt (fun x => q * (t0 + h - x)) (q * (-1)) t :=
    ((hasDerivAt_id' t).const_sub (t0 + h)).const_mul q
  have h2 : HasDerivAt (fun x => q * (x - t0)) (q * 1) t :=
    ((hasDerivAt_id' t).sub_const t0).const_mul q
  have h4 := ((h1.sin.const_mul a).add (h2.sin.const_mul b)).div_const (sin (q * h))
  unfold qsin
  convert h4 using 1
  ring

/-- Relaxation, part 2 (the jump formula of Sec. 7): with node values `a, b, c` at `t0, t0 + h, t0 + 2h`, the right derivative
    minus the left derivative of the interpolant at the middle node is `q (a + c - 2 cos(qh) b) / sin(qh)`. -/
theorem interpolant_jump (q h t0 a b c : ℝ) :
    deriv (qsin q h (t0 + h) b c) (t0 + h) - deriv (qsin q h t0 a b) (t0 + h) =
      q * (a + c - 2 * cos (q * h) * b) / sin (q * h) := by
  rw [(qsin_hasDerivAt q h (t0 + h) b c (t0 + h)).deriv, (qsin_hasDerivAt q h t0 a b (t0 + h)).deriv]
  have e0 : q * (t0 + h - (t0 + h)) = 0 := by ring
  have e1 : q * (t0 + h + h - (t0 + h)) = q * h := by ring
  have e2 : q * (t0 + h - t0) = q * h := by ring
  rw [e0, e1, e2, cos_zero]
  ring

/-- Relaxation, part 3: for `q > 0` and `sin(qh) > 0`, the jump is nonnegative iff the discrete inequality holds at that node. -/
theorem jump_nonneg_iff {q h a b c : ℝ} (hq : 0 < q) (hs : 0 < sin (q * h)) :
    0 ≤ q * (a + c - 2 * cos (q * h) * b) / sin (q * h) ↔ 2 * cos (q * h) * b ≤ a + c := by
  constructor
  · intro hJ
    have hX : 0 ≤ q * (a + c - 2 * cos (q * h) * b) := by
      have hm := mul_nonneg hJ hs.le
      rwa [div_mul_cancel₀ _ hs.ne'] at hm
    nlinarith
  · intro hd
    apply div_nonneg _ hs.le
    apply mul_nonneg hq.le
    linarith

/-! ## T5: monotonicity of Gamma in s, its symmetries, and exactness of e -/

/-! ### (a) Gamma decreases in s -/

/-- Power means of `e^(±y/2)`, orders `r ≤ s`: `cosh(r y/2)^(s/r) ≤ cosh(s y/2)` (Jensen for `x ↦ x^(s/r)`, `s/r ≥ 1`). -/
theorem cosh_rpow_mono (r s y : ℝ) (hr : 0 < r) (hrs : r ≤ s) :
    cosh (r * y / 2) ^ (s / r) ≤ cosh (s * y / 2) := by
  have hexp : 1 ≤ s / r := by rw [le_div_iff₀ hr]; linarith
  have hA : (0 : ℝ) ≤ exp (r * y / 2) := (exp_pos _).le
  have hB : (0 : ℝ) ≤ exp (-(r * y / 2)) := (exp_pos _).le
  have key := (convexOn_rpow hexp).2 (Set.mem_Ici.mpr hA) (Set.mem_Ici.mpr hB)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at key
  have e1 : exp (r * y / 2) ^ (s / r) = exp (s * y / 2) := by
    rw [← exp_mul]; congr 1; field_simp
  have e2 : exp (-(r * y / 2)) ^ (s / r) = exp (-(s * y / 2)) := by
    rw [← exp_mul]; congr 1; field_simp
  rw [e1, e2] at key
  have hmid : (exp (r * y / 2) + exp (-(r * y / 2))) / 2 = 1 / 2 * exp (r * y / 2) + 1 / 2 * exp (-(r * y / 2)) := by ring
  rw [cosh_eq, cosh_eq, hmid]
  linarith [key]

/-- Paper Sec. 2: "Since `cosh(sy/2)^(1/s)` is a power mean of `e^(±y/2)`, `Γ` decreases in `s`" (this makes `s0(p)` well
defined; it is also the "monotonicity in `s`" of Sec. 6). -/
theorem gam_antitone_s (p r s y t : ℝ) (hp : 0 < p) (hr : 0 < r) (hrs : r ≤ s) :
    Gam p s y t ≤ Gam p r y t := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hc : 0 ≤ cosh (r * y / 2) := (cosh_pos _).le
  have h1 : cosh (r * y / 2) ^ (p / r) = (cosh (r * y / 2) ^ (s / r)) ^ (p / s) := by
    rw [← rpow_mul hc]; congr 1; field_simp
  have h2 : (cosh (r * y / 2) ^ (s / r)) ^ (p / s) ≤ cosh (s * y / 2) ^ (p / s) :=
    rpow_le_rpow (rpow_nonneg hc _) (cosh_rpow_mono r s y hr hrs) (by positivity)
  unfold Gam
  linarith [h1, h2]

/-! ### (b) Symmetries -/

/-- `Γ` is even in `y`. -/
theorem gam_even_y (p s y t : ℝ) : Gam p s (-y) t = Gam p s y t := by
  have hneg : s * -y / 2 = -(s * y / 2) := by ring
  unfold Gam
  rw [cosh_neg, hneg, cosh_neg]

/-- `Γ` is even in `t`. -/
theorem gam_even_t (p s y t : ℝ) : Gam p s y (-t) = Gam p s y t := by
  unfold Gam
  rw [cos_neg]

/-- `Γ` is `2π`-periodic in `t` (it lives on the cylinder). -/
theorem gam_periodic_t (p s y t : ℝ) : Gam p s y (t + 2 * π) = Gam p s y t := by
  unfold Gam
  rw [cos_add_two_pi]

/-- `e` is even in `t` (as a formula; the paper's `e` on `|t| ≤ π`). -/
theorem ee_even (p t : ℝ) : ee p (-t) = ee p t := by
  unfold ee
  rw [mul_neg, cos_neg]

/-- Paper Sec. 6: "By evenness it suffices to take `y ≥ 0`, `t ∈ [0, π]`": `Ψ(y,t) = Ψ(|y|,|t|)`.
(`ee` is the formula `tan ϑ cos(qt)`; it is the paper's `e` on `|t| ≤ π`, where (2) is stated.) -/
theorem psi_abs (p s y t : ℝ) : Gam p s y t - ee p t = Gam p s |y| |t| - ee p |t| := by
  rcases le_total 0 y with hy | hy
  · rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg hy, abs_of_nonneg ht]
    · rw [abs_of_nonneg hy, abs_of_nonpos ht, gam_even_t, ee_even]
  · rcases le_total 0 t with ht | ht
    · rw [abs_of_nonpos hy, abs_of_nonneg ht, gam_even_y]
    · rw [abs_of_nonpos hy, abs_of_nonpos ht, gam_even_y, gam_even_t, ee_even]

/-- Paper Sec. 4 (proof of Prop. saddle): "`∂_y Ψ = 0` by evenness", at `y = 0`, for every `t`. Where `y ↦ Ψ(y,t)` is not
differentiable at `0` (only `t = π` mod `2π`) this holds through the convention `deriv = 0`; the genuine statement is
`psi_hasDerivAt_y_zero`. -/
theorem psi_deriv_y_zero (p s t : ℝ) : deriv (fun y => Gam p s y t - ee p t) 0 = 0 := by
  set f : ℝ → ℝ := fun y => Gam p s y t - ee p t with hf
  have hsymm : (fun y => f (-y)) = f := by
    funext y
    simp only [hf, gam_even_y]
  have h := deriv_comp_neg (f := f) (x := 0)
  rw [hsymm, neg_zero] at h
  linarith

/-- The genuine derivative: if `1 + cos t ≠ 0` (so near the contact point `(0, π/p)`, where `1 + cos(π/p) > 0`), then
`y ↦ Ψ(y,t)` is differentiable at `0` with derivative `0`. -/
theorem psi_hasDerivAt_y_zero (p s t : ℝ) (ht : 1 + cos t ≠ 0) :
    HasDerivAt (fun y => Gam p s y t - ee p t) 0 0 := by
  have hd1 : DifferentiableAt ℝ (fun y : ℝ => (cosh y + cos t) ^ (p / 2)) 0 := by
    apply DifferentiableAt.rpow_const
    · exact (differentiableAt_id.cosh).add_const _
    · left
      simpa [cosh_zero] using ht
  have hd2 : DifferentiableAt ℝ (fun y : ℝ => cosh (s * y / 2) ^ (p / s)) 0 := by
    apply DifferentiableAt.rpow_const
    · exact ((differentiableAt_id.const_mul s).div_const 2).cosh
    · left
      simp
  have hd : DifferentiableAt ℝ (fun y => Gam p s y t - ee p t) 0 := by
    unfold Gam
    exact ((hd1.div_const _).sub hd2).sub_const _
  have h := hd.hasDerivAt
  rwa [psi_deriv_y_zero] at h

/-! ### (c) e is exact for the discrete inequality and solves e'' + q^2 e = 0 -/

/-- Paper Sec. 7: "The inequality is exact for `cos(qt)`": `e(t+h) + e(t-h) - 2 cos(qh) e(t) = 0` (for the formula `ee`, so for
the paper's `e` whenever `t ± h` and `t` lie in `[-π, π]`). -/
theorem ee_discrete_exact (p t h : ℝ) : ee p (t + h) + ee p (t - h) - 2 * cos (p / 2 * h) * ee p t = 0 := by
  have h1 : p / 2 * (t + h) = p / 2 * t + p / 2 * h := by ring
  have h2 : p / 2 * (t - h) = p / 2 * t - p / 2 * h := by ring
  unfold ee
  rw [h1, h2, cos_add, cos_sub]
  ring

/-- First derivative of `e`. -/
theorem ee_hasDerivAt (p t : ℝ) :
    HasDerivAt (ee p) (-(tan (π / (2 * p)) * (p / 2)) * sin (p / 2 * t)) t := by
  have h := (((hasDerivAt_id' t).const_mul (p / 2)).cos).const_mul (tan (π / (2 * p)))
  exact h.congr_deriv (by ring)

/-- `e'' = -q^2 e`, i.e. `e` solves `φ'' + q^2 φ = 0` (the q-trigonometric functions of Sec. 3 and Sec. 7). -/
theorem ee_ode (p t : ℝ) : HasDerivAt (deriv (ee p)) (-(p / 2) ^ 2 * ee p t) t := by
  have hd : deriv (ee p) = fun x => -(tan (π / (2 * p)) * (p / 2)) * sin (p / 2 * x) := by
    funext x
    exact (ee_hasDerivAt p x).deriv
  rw [hd]
  have h := (((hasDerivAt_id' t).const_mul (p / 2)).sin).const_mul (-(tan (π / (2 * p)) * (p / 2)))
  convert h using 1
  unfold ee
  ring

end P18
