/-
  HVFalse/Proofs/Coercive.lean - Γ(·,t) is coercive for s ≤ sec²ϑ, uniformly in t (the paper)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route. (a) with x = 2cos ϑ: the coefficient is positive iff s log x < log 2. If x ≤ 1 this is clear; if x > 1 then
  s ≤ 4/x² and, with u = x² < 2, the tangent line log u ≤ log 2 + u/2 - 1 at u = 2 and log 2 < 1 give 4 log x < x² log 2
  (the paper's "x² - 4 log₂ x decreases on [1, √2] to 0").
  (b) Γ(y,t) ≥ ((cosh y - 1)/D)^q - cosh(sy/2)^(p/s) = e^{qy} B(e^{-y}) with B continuous at 0 and B(0) = the coefficient
  of (a); evenness in y handles y < 0. (c) extreme value theorem. (d) Γ(0,t) ≤ (2/D)^q - 1 for every t.
-/
import HVFalse.Proofs.Bridges
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact

open Real Filter Topology

namespace P18

theorem cos_half_pos {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 < cos (π / (2 * p)) := by
  have hpos : 0 < p := by linarith
  have hpi := pi_pos
  apply cos_pos_of_mem_Ioo
  constructor
  · have : 0 < π / (2 * p) := by positivity
    linarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

theorem cos_half_sq_lt {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : cos (π / (2 * p)) ^ 2 < 1 / 2 := by
  have hpos : 0 < p := by linarith
  have hpi := pi_pos
  have hc0 := cos_half_pos hp1 hp2
  have hlt : π / 4 < π / (2 * p) := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have hle : π / (2 * p) ≤ π / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hc := cos_lt_cos_of_nonneg_of_le_pi_div_two (by positivity) hle hlt
  rw [cos_pi_div_four] at hc
  have h2 : √2 / 2 * (√2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  nlinarith

/-- `1 + cos(π/p) = 2 cos²(π/(2p))`. -/
theorem denom_eq_two_cos_sq (p : ℝ) (hp : p ≠ 0) : 1 + cos (π / p) = 2 * cos (π / (2 * p)) ^ 2 := by
  have h : π / p = 2 * (π / (2 * p)) := by field_simp
  rw [h, cos_two_mul]
  ring

/-- The heart of (a): `s log(2 cos ϑ) < log 2`. -/
theorem coeff_key {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) :
    s * log (2 * cos (π / (2 * p))) < log 2 := by
  have hc0 := cos_half_pos hp1 hp2
  have hc2 := cos_half_sq_lt hp1 hp2
  set c := cos (π / (2 * p)) with hc
  have hlog2 := log_pos (one_lt_two : (1 : ℝ) < 2)
  by_cases hl : log (2 * c) ≤ 0
  · nlinarith [mul_le_mul_of_nonneg_left hl hs.le]
  push_neg at hl
  have hu : log ((2 * c) ^ 2) = 2 * log (2 * c) := by rw [Real.log_pow]; norm_num
  have htan := log_le_sub_one_of_pos (show 0 < (2 * c) ^ 2 / 2 by positivity)
  rw [Real.log_div (by positivity) (by norm_num), hu] at htan
  have hl2 := Real.log_two_lt_d9
  have hprod := mul_pos (show 0 < 1 - 2 * c ^ 2 by linarith) (show 0 < 1 - log 2 by norm_num at hl2; linarith)
  have h2 : log (2 * c) < c ^ 2 * log 2 := by nlinarith
  have h1 : s * log (2 * c) ≤ 1 / c ^ 2 * log (2 * c) := mul_le_mul_of_nonneg_right hsS hl.le
  calc s * log (2 * c) ≤ 1 / c ^ 2 * log (2 * c) := h1
    _ < log 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
      linarith

/-- C03 (a), paper l.216-219: the coefficient `(2 cos ϑ)^(-p) - 2^(-p/s)` of `e^{q|y|}` is positive for `0 < s ≤ sec²ϑ`. -/
theorem coeff_pos {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) :
    0 < (2 * cos (π / (2 * p))) ^ (-p) - 2 ^ (-p / s) := by
  have key := coeff_key hp1 hp2 hs hsS
  have hx : 0 < 2 * cos (π / (2 * p)) := by linarith [cos_half_pos hp1 hp2]
  rw [sub_pos, rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), rpow_def_of_pos hx, exp_lt_exp,
    show log 2 * (-p / s) = -(p * log 2) / s by ring, div_lt_iff₀ hs]
  nlinarith [mul_lt_mul_of_pos_left key (show 0 < p by linarith)]

/-- `B(z) = ((1-z)²/(2D))^q - ((1+z^s)/2)^(p/s)`, so that the lower bound of `Γ(y,·)` is `e^{qy} B(e^{-y})`. -/
noncomputable def coerB (p s z : ℝ) : ℝ :=
  ((1 - z) ^ 2 / (2 * (1 + cos (π / p)))) ^ (p / 2) - ((1 + z ^ s) / 2) ^ (p / s)

theorem cosh_sub_one_eq (y : ℝ) : cosh y - 1 = exp y * ((1 - exp (-y)) ^ 2 / 2) := by
  have he : exp y * exp (-y) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  rw [cosh_eq]
  linear_combination (1 - exp (-y) / 2) * he

theorem cosh_half_eq (s y : ℝ) : cosh (s * y / 2) = exp (s * y / 2) * ((1 + exp (-y) ^ s) / 2) := by
  have he : exp (s * y / 2) * exp (-y) ^ s = exp (-(s * y / 2)) := by
    rw [← exp_mul, ← exp_add]; ring_nf
  rw [cosh_eq]
  linear_combination (-1 / 2 : ℝ) * he

/-- `Γ(y,t) ≥ e^{qy} B(e^{-y})` for every `y, t`. -/
theorem gam_ge_factor {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (y t : ℝ) :
    exp (p / 2 * y) * coerB p s (exp (-y)) ≤ Gam p s y t := by
  have hd := denom_pos p hp1 hp2
  have hq : 0 ≤ p / 2 := by linarith
  have hA : 0 ≤ (1 - exp (-y)) ^ 2 / (2 * (1 + cos (π / p))) := by positivity
  have hbase : (cosh y - 1) / (1 + cos (π / p)) = exp y * ((1 - exp (-y)) ^ 2 / (2 * (1 + cos (π / p)))) := by
    rw [cosh_sub_one_eq]; field_simp
  have hmono : ((cosh y - 1) / (1 + cos (π / p))) ^ (p / 2) ≤ ((cosh y + cos t) / (1 + cos (π / p))) ^ (p / 2) :=
    rpow_le_rpow (div_nonneg (by linarith [one_le_cosh y]) hd.le)
      (div_le_div_of_nonneg_right (by linarith [neg_one_le_cos t]) hd.le) hq
  rw [hbase, mul_rpow (exp_pos y).le hA, ← exp_mul] at hmono
  have hC : cosh (s * y / 2) ^ (p / s) = exp (p / 2 * y) * ((1 + exp (-y) ^ s) / 2) ^ (p / s) := by
    rw [cosh_half_eq, mul_rpow (exp_pos _).le (by positivity), ← exp_mul]
    congr 2
    field_simp
  rw [gam_eq_div p s y t hp1 hp2, hC]
  unfold coerB
  rw [show y * (p / 2) = p / 2 * y by ring] at hmono
  rw [mul_sub]
  linarith

theorem coerB_continuousAt {p s : ℝ} (hp1 : 1 < p) (hs : 0 < s) : ContinuousAt (coerB p s) 0 := by
  unfold coerB
  apply ContinuousAt.sub
  · exact ((((continuousAt_const.sub continuousAt_id).pow 2).div_const _)).rpow_const (Or.inr (by linarith))
  · exact ((continuousAt_const.add (continuousAt_id.rpow_const (Or.inr hs.le))).div_const 2).rpow_const
      (Or.inr (div_nonneg (by linarith) hs.le))

/-- `B(0)` is the coefficient of (a). -/
theorem coerB_zero {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    coerB p s 0 = (2 * cos (π / (2 * p))) ^ (-p) - 2 ^ (-p / s) := by
  have hpos : 0 < p := by linarith
  have hc0 := cos_half_pos hp1 hp2
  have hx : 0 < 2 * cos (π / (2 * p)) := by linarith
  unfold coerB
  rw [zero_rpow hs.ne', sub_zero, add_zero, one_pow, denom_eq_two_cos_sq p hpos.ne']
  rw [rpow_def_of_pos (by positivity), rpow_def_of_pos (by norm_num), rpow_def_of_pos hx,
    rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have e1 : 1 / (2 * (2 * cos (π / (2 * p)) ^ 2)) = ((2 * cos (π / (2 * p))) ^ 2)⁻¹ := by ring
  rw [e1, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
  congr 2 <;> push_cast <;> ring

theorem gam_lower_tendsto {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) :
    Tendsto (fun y => exp (p / 2 * y) * coerB p s (exp (-y))) atTop atTop := by
  have hB : Tendsto (fun y => coerB p s (exp (-y))) atTop (𝓝 (coerB p s 0)) :=
    (coerB_continuousAt hp1 hs).tendsto.comp tendsto_exp_neg_atTop_nhds_zero
  have hk : 0 < coerB p s 0 := by rw [coerB_zero hp1 hp2 hs]; exact coeff_pos hp1 hp2 hs hsS
  exact (tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith : (0 : ℝ) < p / 2))).atTop_mul_pos hk hB

/-- C03 (b): `Γ(y,t) → +∞` as `|y| → ∞`, uniformly in `t`, for `0 < s ≤ sec²ϑ`. -/
theorem gam_tendsto {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ y t : ℝ, R ≤ |y| → M ≤ Gam p s y t := by
  intro M
  obtain ⟨R, hR⟩ := (tendsto_atTop_atTop.mp (gam_lower_tendsto hp1 hp2 hs hsS)) M
  refine ⟨R, fun y t hy => le_trans (hR |y| hy) ?_⟩
  rcases abs_choice y with h | h
  · rw [h]; exact gam_ge_factor hp1 hp2 hs y t
  · rw [h, ← gam_even_y p s y t]; exact gam_ge_factor hp1 hp2 hs (-y) t

theorem gam_continuous_y {p s : ℝ} (hp1 : 1 < p) (hs : 0 < s) (t : ℝ) : Continuous (fun y => Gam p s y t) := by
  unfold Gam
  apply Continuous.sub
  · exact ((continuous_cosh.add continuous_const).rpow_const (fun _ => Or.inr (by linarith))).div_const _
  · exact (continuous_cosh.comp ((continuous_const.mul continuous_id).div_const 2)).rpow_const
      (fun _ => Or.inr (div_nonneg (by linarith) hs.le))

/-- C03 (c): for `0 < s ≤ sec²ϑ` the infimum `m(t)` of `Γ(·,t)` is attained. -/
theorem gam_min_attained {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) : ∀ t, ∃ y0, ∀ y, Gam p s y0 t ≤ Gam p s y t := by
  intro t
  apply (gam_continuous_y hp1 hs t).exists_forall_le
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · rw [tendsto_atBot_atTop]
    intro M
    obtain ⟨R, hR⟩ := gam_tendsto hp1 hp2 hs hsS M
    exact ⟨-|R|, fun y hy => hR y t (le_trans (le_abs_self R) (by linarith [neg_le_abs y]))⟩
  · rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨R, hR⟩ := gam_tendsto hp1 hp2 hs hsS M
    exact ⟨|R|, fun y hy => hR y t (le_trans (le_abs_self R) (hy.trans (le_abs_self y)))⟩

/-- `Γ(0,t) ≤ (2/D)^q - 1` for every `t`. -/
theorem gam_zero_le {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (t : ℝ) :
    Gam p s 0 t ≤ (2 / (1 + cos (π / p))) ^ (p / 2) - 1 := by
  have hd := denom_pos p hp1 hp2
  rw [gam_eq_div p s 0 t hp1 hp2, cosh_zero, mul_zero, zero_div, cosh_zero, one_rpow]
  have h := rpow_le_rpow (div_nonneg (by linarith [neg_one_le_cos t]) hd.le)
    (div_le_div_of_nonneg_right (by linarith [cos_le_one t] : 1 + cos t ≤ 2) hd.le) (by linarith : (0 : ℝ) ≤ p / 2)
  linarith

/-- C03 (d): all minimizers of `Γ(·,t)` lie in one bounded set, for all `t`. -/
theorem gam_minimizers_bounded {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ 1 / cos (π / (2 * p)) ^ 2) :
    ∃ R, ∀ t y0, (∀ y, Gam p s y0 t ≤ Gam p s y t) → |y0| ≤ R := by
  obtain ⟨R, hR⟩ := gam_tendsto hp1 hp2 hs hsS ((2 / (1 + cos (π / p))) ^ (p / 2) - 1 + 1)
  refine ⟨R, fun t y0 hmin => ?_⟩
  by_contra h
  push_neg at h
  have h1 := hR y0 t h.le
  have h2 := hmin 0
  have h3 := gam_zero_le (s := s) hp1 hp2 t
  linarith

end P18
