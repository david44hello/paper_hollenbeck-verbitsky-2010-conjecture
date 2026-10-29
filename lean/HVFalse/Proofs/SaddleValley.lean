/-
  HVFalse/Proofs/SaddleValley.lean - Prop. saddle: Γ - e = A(p) y⁴ + O(y⁶) along the valley, and a failure point
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Method (the paper's: Taylor expansion at (0, π/p)). All remainders are `=O[𝓝 0]` statements:
    exp w = 1 + w + w²/2 + O(w³),  log(1+z) = z - z²/2 + O(z³),  so (1+z)^r = 1 + rz + r(r-1)/2 z² + O(z³);
    cosh(ky) = 1 + k²y²/2 + k⁴y⁴/24 + O(y⁶);  cos τ = 1 - τ²/2 + O(τ⁴);  sin τ = τ + O(τ³).
  `rpow_expand`: if ξ = αy² + βy⁴ + O(y⁶) then (1+ξ)^r = 1 + rαy² + (rβ + r(r-1)/2 α²) y⁴ + O(y⁶).
-/
import HVFalse.Defs.Saddle
import HVFalse.Proofs.SaddleSigns
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real Asymptotics Filter Topology

namespace P18

namespace SaddleValley

/-- `yⁿ = O(yᵐ)` at `0` for `m ≤ n`. -/
theorem pow_isBigO_pow {m n : ℕ} (h : m ≤ n) : (fun y : ℝ => y ^ n) =O[𝓝 0] (fun y => y ^ m) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with y hy
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, one_mul]
  exact pow_le_pow_of_le_one (abs_nonneg y) hy.le h

/-- `c·y^k → 0` at `0` for `k ≥ 1`. -/
theorem tendsto_mul_pow {k : ℕ} (hk : k ≠ 0) (c : ℝ) : Tendsto (fun y : ℝ => c * y ^ k) (𝓝 0) (𝓝 0) := by
  have : Continuous (fun y : ℝ => c * y ^ k) := by fun_prop
  simpa [zero_pow hk] using this.tendsto 0

/-- `exp w = 1 + w + w²/2 + O(w³)`. -/
theorem exp3 : (fun w : ℝ => exp w - (1 + w + w ^ 2 / 2)) =O[𝓝 0] (fun w => w ^ 3) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with w hw
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hw
  have hb := Real.exp_bound (x := w) (n := 3) hw.le (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
  norm_num at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have e : exp w - (1 + w + w ^ 2 / 2) = exp w - (1 + w + w ^ 2 / 2) := rfl
  calc |exp w - (1 + w + w ^ 2 / 2)| = |exp w - (1 + w + w ^ 2 * (1 / 2))| := by ring_nf
    _ ≤ |w| ^ 3 * (2 / 9) := by convert hb using 2; ring
    _ ≤ |w| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg w) 3]

/-- `log(1+z) = z - z²/2 + O(z³)`. -/
theorem log3 : (fun z : ℝ => log (1 + z) - (z - z ^ 2 / 2)) =O[𝓝 0] (fun z => z ^ 3) := by
  apply IsBigO.of_bound 2
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) (by norm_num : (0:ℝ) < 1/2)] with z hz
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hz
  have hz1 : |-z| < 1 := by rw [abs_neg]; linarith
  have hb := Real.abs_log_sub_add_sum_range_le (n := 2) hz1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at hb
  norm_num at hb
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
  have hden : 1 / 2 ≤ 1 - |z| := by linarith
  have hq : |z| ^ 3 / (1 - |z|) ≤ 2 * |z| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg (abs_nonneg z) 3]
  calc |log (1 + z) - (z - z ^ 2 / 2)| = |-z + z ^ 2 / 2 + log (1 + z)| := by ring_nf
    _ ≤ |z| ^ 3 / (1 - |z|) := by convert hb using 2
    _ ≤ 2 * |z| ^ 3 := hq

/-- `(1+z)^r = 1 + r z + r(r-1)/2 z² + O(z³)`. -/
theorem rpow3 (r : ℝ) :
    (fun z : ℝ => (1 + z) ^ r - (1 + r * z + r * (r - 1) / 2 * z ^ 2)) =O[𝓝 0] (fun z => z ^ 3) := by
  set w : ℝ → ℝ := fun z => log (1 + z) * r with hw_def
  have hlog := log3
  have hz3z : (fun z : ℝ => z ^ 3) =O[𝓝 0] (fun z => z) := by
    simpa using pow_isBigO_pow (m := 1) (n := 3) (by norm_num)
  have hz2z : (fun z : ℝ => z ^ 2) =O[𝓝 0] (fun z => z) := by
    simpa using pow_isBigO_pow (m := 1) (n := 2) (by norm_num)
  have hz3z2 : (fun z : ℝ => z ^ 3) =O[𝓝 0] (fun z => z ^ 2) := pow_isBigO_pow (by norm_num)
  -- w - r(z - z²/2) = O(z³)
  have hw1 : (fun z => w z - r * (z - z ^ 2 / 2)) =O[𝓝 0] (fun z : ℝ => z ^ 3) := by
    have := hlog.const_mul_left r
    refine this.congr_left (fun z => ?_)
    simp only [hw_def]; ring
  -- w = O(z)
  have hwO : w =O[𝓝 0] (fun z : ℝ => z) := by
    have hlin : (fun z : ℝ => r * (z - z ^ 2 / 2)) =O[𝓝 0] (fun z => z) := by
      have h1 : (fun z : ℝ => z - z ^ 2 / 2) =O[𝓝 0] (fun z => z) :=
        (isBigO_refl (fun z : ℝ => z) _).sub (hz2z.const_mul_left (1/2) |>.congr_left (fun z => by ring))
      exact h1.const_mul_left r
    refine ((hw1.trans hz3z).add hlin).congr_left (fun z => ?_)
    ring
  have hw0 : Tendsto w (𝓝 0) (𝓝 0) := hwO.trans_tendsto tendsto_id
  have hE : (fun z => exp (w z) - (1 + w z + w z ^ 2 / 2)) =O[𝓝 0] (fun z => w z ^ 3) :=
    exp3.comp_tendsto hw0
  have hw3 : (fun z => w z ^ 3) =O[𝓝 0] (fun z : ℝ => z ^ 3) := hwO.pow 3
  -- (w - rz)(w + rz) = O(z³)
  have hwmr : (fun z => w z - r * z) =O[𝓝 0] (fun z : ℝ => z ^ 2) := by
    have h2 : (fun z : ℝ => -(r / 2) * z ^ 2) =O[𝓝 0] (fun z => z ^ 2) := (isBigO_refl _ _).const_mul_left _
    refine ((hw1.trans hz3z2).add h2).congr_left (fun z => ?_)
    ring
  have hwpr : (fun z => w z + r * z) =O[𝓝 0] (fun z : ℝ => z) :=
    hwO.add ((isBigO_refl (fun z : ℝ => z) _).const_mul_left r)
  have hprod : (fun z => (w z - r * z) * (w z + r * z) / 2) =O[𝓝 0] (fun z : ℝ => z ^ 3) := by
    have := (hwmr.mul hwpr).const_mul_left (1/2)
    refine (this.congr_right (fun z => ?_)).congr_left (fun z => ?_)
    · ring
    · ring
  have hsum := ((hE.trans hw3).add hw1).add hprod
  have hev : ∀ᶠ z in 𝓝 (0:ℝ), (exp (w z) - (1 + w z + w z ^ 2 / 2)) + (w z - r * (z - z ^ 2 / 2))
      + (w z - r * z) * (w z + r * z) / 2 = (1 + z) ^ r - (1 + r * z + r * (r - 1) / 2 * z ^ 2) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with z hz
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hz
    have hpos : 0 < 1 + z := by have := neg_abs_le z; linarith
    rw [rpow_def_of_pos hpos]
    simp only [hw_def]
    ring
  exact hsum.congr' hev (EventuallyEq.refl _ _)

/-- If `ξ = αy² + βy⁴ + O(y⁶)` then `(1+ξ)^r = 1 + rαy² + (rβ + r(r-1)/2·α²) y⁴ + O(y⁶)`. -/
theorem rpow_expand {ξ : ℝ → ℝ} {α β : ℝ} (r : ℝ)
    (hξ : (fun y => ξ y - (α * y ^ 2 + β * y ^ 4)) =O[𝓝 0] (fun y => y ^ 6)) :
    (fun y => (1 + ξ y) ^ r - (1 + r * α * y ^ 2 + (r * β + r * (r - 1) / 2 * α ^ 2) * y ^ 4))
      =O[𝓝 0] (fun y => y ^ 6) := by
  have h62 : (fun y : ℝ => y ^ 6) =O[𝓝 0] (fun y => y ^ 2) := pow_isBigO_pow (by norm_num)
  have h64 : (fun y : ℝ => y ^ 6) =O[𝓝 0] (fun y => y ^ 4) := pow_isBigO_pow (by norm_num)
  have h42 : (fun y : ℝ => y ^ 4) =O[𝓝 0] (fun y => y ^ 2) := pow_isBigO_pow (by norm_num)
  have hP2 : (fun y : ℝ => α * y ^ 2 + β * y ^ 4) =O[𝓝 0] (fun y => y ^ 2) :=
    ((isBigO_refl (fun y : ℝ => y ^ 2) _).const_mul_left α).add ((h42).const_mul_left β)
  have hξ2 : ξ =O[𝓝 0] (fun y : ℝ => y ^ 2) :=
    ((hξ.trans h62).add hP2).congr_left (fun y => by ring)
  have hξ0 : Tendsto ξ (𝓝 0) (𝓝 0) := by
    refine hξ2.trans_tendsto ?_
    simpa using tendsto_mul_pow (k := 2) (by norm_num) 1
  have hR : (fun y => (1 + ξ y) ^ r - (1 + r * ξ y + r * (r - 1) / 2 * ξ y ^ 2)) =O[𝓝 0] (fun y => ξ y ^ 3) :=
    (rpow3 r).comp_tendsto hξ0
  have hξ3 : (fun y => ξ y ^ 3) =O[𝓝 0] (fun y : ℝ => y ^ 6) :=
    (hξ2.pow 3).congr_right (fun y => by ring)
  have hm : (fun y => ξ y - α * y ^ 2) =O[𝓝 0] (fun y : ℝ => y ^ 4) :=
    ((hξ.trans h64).add ((isBigO_refl (fun y : ℝ => y ^ 4) _).const_mul_left β)).congr_left (fun y => by ring)
  have hp : (fun y => ξ y + α * y ^ 2) =O[𝓝 0] (fun y : ℝ => y ^ 2) :=
    hξ2.add ((isBigO_refl (fun y : ℝ => y ^ 2) _).const_mul_left α)
  have hsq : (fun y => r * (r - 1) / 2 * ((ξ y - α * y ^ 2) * (ξ y + α * y ^ 2))) =O[𝓝 0] (fun y : ℝ => y ^ 6) :=
    ((hm.mul hp).congr_right (fun y => by ring)).const_mul_left _
  have hlin : (fun y => r * (ξ y - (α * y ^ 2 + β * y ^ 4))) =O[𝓝 0] (fun y : ℝ => y ^ 6) := hξ.const_mul_left r
  refine (((hR.trans hξ3).add hlin).add hsq).congr_left (fun y => ?_)
  ring

/-- `cosh(k y) - 1 = (k²/2) y² + (k⁴/24) y⁴ + O(y⁶)`. -/
theorem cosh6 (k : ℝ) :
    (fun y : ℝ => (cosh (k * y) - 1) - (k ^ 2 / 2 * y ^ 2 + k ^ 4 / 24 * y ^ 4)) =O[𝓝 0] (fun y => y ^ 6) := by
  apply IsBigO.of_bound (k ^ 6)
  have hδ : (0:ℝ) < 1 / (|k| + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) hδ] with y hy
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hy
  have hky : |k * y| ≤ 1 := by
    rw [abs_mul]
    have h1 : |y| * (|k| + 1) < 1 := by rwa [lt_div_iff₀ (by positivity)] at hy
    nlinarith [abs_nonneg k, abs_nonneg y]
  have hky' : |-(k * y)| ≤ 1 := by rwa [abs_neg]
  have hb1 := Real.exp_bound (x := k * y) (n := 6) hky (by norm_num)
  have hb2 := Real.exp_bound (x := -(k * y)) (n := 6) hky' (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_neg] at hb1 hb2
  norm_num at hb1 hb2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, Real.cosh_eq]
  set E1 := rexp (k * y) - (1 + k * y + (k * y) ^ 2 / 2 + (k * y) ^ 3 / 6 + (k * y) ^ 4 / 24 + (k * y) ^ 5 / 120)
    with hE1
  set E2 := rexp (-(k * y)) - (1 + -(k * y) + (k * y) ^ 2 / 2 + (-(k * y)) ^ 3 / 6 + (-(k * y)) ^ 4 / 24
    + (-(k * y)) ^ 5 / 120) with hE2
  have hsplit : (rexp (k * y) + rexp (-(k * y))) / 2 - 1 - (k ^ 2 / 2 * y ^ 2 + k ^ 4 / 24 * y ^ 4) = (E1 + E2) / 2 := by
    rw [hE1, hE2]; ring
  have hk6 : (|k| * |y|) ^ 6 = k ^ 6 * |y| ^ 6 := by
    rw [mul_pow, ← abs_pow k 6, abs_of_nonneg (by positivity)]
  have hy6 : 0 ≤ |y| ^ 6 := by positivity
  have hkk : 0 ≤ k ^ 6 := by positivity
  rw [hsplit, abs_div, abs_two, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have htri := abs_add_le E1 E2
  rw [hk6] at hb1 hb2
  nlinarith [htri, hb1, hb2]

/-- `cos τ = 1 - τ²/2 + O(τ⁴)`. -/
theorem cos4 : (fun τ : ℝ => cos τ - (1 - τ ^ 2 / 2)) =O[𝓝 0] (fun τ => τ ^ 4) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with τ hτ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hτ
  have hb := Real.cos_bound hτ.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  nlinarith [pow_nonneg (abs_nonneg τ) 4]

/-- `sin τ = τ + O(τ³)`. -/
theorem sin3 : (fun τ : ℝ => sin τ - τ) =O[𝓝 0] (fun τ => τ ^ 3) := by
  apply IsBigO.of_bound 1
  filter_upwards [Metric.ball_mem_nhds (0:ℝ) one_pos] with τ hτ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hτ
  have hb := Real.sin_bound hτ.le
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, one_mul]
  have ha : 0 ≤ |τ| := abs_nonneg τ
  have h5 : |τ| ^ 5 ≤ |τ| ^ 3 := pow_le_pow_of_le_one ha hτ.le (by norm_num)
  have htri : |sin τ - τ| ≤ |sin τ - (τ - τ ^ 3 / 6)| + |τ ^ 3 / 6| := by
    have := abs_add_le (sin τ - (τ - τ ^ 3 / 6)) (-(τ ^ 3 / 6))
    rw [abs_neg] at this
    convert this using 2; ring
  rw [abs_div, abs_pow] at htri
  norm_num at htri
  nlinarith [pow_nonneg ha 3]


section Specific

variable {p : ℝ}

/-- `ϑ = π/(2p) ∈ (0, π/2)` for `p > 1`, so `cos ϑ > 0`. -/
theorem cos_th_pos (hp1 : 1 < p) : 0 < cos (π / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  apply cos_pos_of_mem_Ioo
  constructor
  · have : 0 < π / (2 * p) := by positivity
    linarith [pi_pos]
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]

/-- The trigonometric values of Prop. saddle in terms of `T = tan ϑ`, `ϑ = π/(2p)`. -/
theorem trig_T (hp1 : 1 < p) :
    Ssec p = 1 + tan (π / (2 * p)) ^ 2 ∧
    1 + cos (2 * (π / (2 * p))) = 2 / (1 + tan (π / (2 * p)) ^ 2) ∧
    cos (π / p) = (1 - tan (π / (2 * p)) ^ 2) / (1 + tan (π / (2 * p)) ^ 2) ∧
    sin (π / p) = 2 * tan (π / (2 * p)) / (1 + tan (π / (2 * p)) ^ 2) := by
  have ha := cos_th_pos hp1
  have hp0 : p ≠ 0 := by linarith
  have h2 : π / p = 2 * (π / (2 * p)) := by field_simp
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = π / (2 * p) := ⟨_, rfl⟩
  rw [← hθ] at ha h2 ⊢
  have hs := sin_sq_add_cos_sq θ
  have hT : tan θ = sin θ / cos θ := tan_eq_sin_div_cos θ
  have hS : 1 + tan θ ^ 2 = 1 / cos θ ^ 2 := by
    rw [hT, div_pow]; field_simp; linarith [hs]
  have hT2 : tan θ ^ 2 = 1 / cos θ ^ 2 - 1 := by linarith [hS]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Ssec, ← hθ]; rw [hS]
  · rw [cos_two_mul, hS]; field_simp; ring
  · rw [h2, cos_two_mul, hS, hT2]; field_simp; ring
  · rw [h2, sin_two_mul, hS, hT]; field_simp

/-- `e` along the valley: `e(π/p - c y²) = T·sin((p/2) c y²) = T (p/2) c y² + O(y⁶)`. -/
theorem ee_valley (hp0 : p ≠ 0) (c : ℝ) :
    (fun y : ℝ => ee p (π / p - c * y ^ 2) - tan (π / (2 * p)) * (p / 2 * c) * y ^ 2)
      =O[𝓝 0] (fun y => y ^ 6) := by
  set m := p / 2 * c with hm
  have hs : (fun y : ℝ => sin (m * y ^ 2) - m * y ^ 2) =O[𝓝 0] (fun y => (m * y ^ 2) ^ 3) :=
    sin3.comp_tendsto (tendsto_mul_pow (by norm_num) m)
  have h3 : (fun y : ℝ => (m * y ^ 2) ^ 3) =O[𝓝 0] (fun y => y ^ 6) :=
    ((isBigO_refl (fun y : ℝ => y ^ 6) _).const_mul_left (m ^ 3)).congr_left (fun y => by ring)
  refine ((hs.trans h3).const_mul_left (tan (π / (2 * p)))).congr_left (fun y => ?_)
  have harg : p / 2 * (π / p - c * y ^ 2) = π / 2 - m * y ^ 2 := by rw [hm]; field_simp
  simp only [ee, harg, cos_pi_div_two_sub]
  ring

/-- `ξ₁ = u/D - 1 = α₁y² + β₁y⁴ + O(y⁶)`, `u = cosh y + cos(π/p - c y²)`, `D = 1 + cos 2ϑ`. -/
theorem xi1_expand (hp1 : 1 < p) (hp2 : p < 2) (c : ℝ) :
    (fun y : ℝ => ((cosh y + cos (π / p - c * y ^ 2)) / (1 + cos (2 * (π / (2 * p)))) - 1)
        - ((1/2 + sin (π / p) * c) / (1 + cos (2 * (π / (2 * p)))) * y ^ 2
          + (1/24 - cos (π / p) * c ^ 2 / 2) / (1 + cos (2 * (π / (2 * p)))) * y ^ 4))
      =O[𝓝 0] (fun y => y ^ 6) := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD : 0 < 1 + cos (π / p) := denom_pos p hp1 hp2
  rw [h2]
  set D := 1 + cos (π / p) with hD_def
  set cP := cos (π / p)
  set sP := sin (π / p)
  have hc6 : (fun y : ℝ => (cosh y - 1) - (1 / 2 * y ^ 2 + 1 / 24 * y ^ 4)) =O[𝓝 0] (fun y => y ^ 6) := by
    have := cosh6 1
    simpa using this
  have hcos : (fun y : ℝ => cos (c * y ^ 2) - (1 - (c * y ^ 2) ^ 2 / 2)) =O[𝓝 0] (fun y => y ^ 6) := by
    have h4 := cos4.comp_tendsto (tendsto_mul_pow (k := 2) (by norm_num) c)
    have h86 : (fun y : ℝ => (c * y ^ 2) ^ 4) =O[𝓝 0] (fun y => y ^ 6) :=
      (((pow_isBigO_pow (m := 6) (n := 8) (by norm_num)).const_mul_left (c ^ 4))).congr_left (fun y => by ring)
    exact h4.trans h86
  have hsin : (fun y : ℝ => sin (c * y ^ 2) - c * y ^ 2) =O[𝓝 0] (fun y => y ^ 6) := by
    have h3 := sin3.comp_tendsto (tendsto_mul_pow (k := 2) (by norm_num) c)
    have h66 : (fun y : ℝ => (c * y ^ 2) ^ 3) =O[𝓝 0] (fun y => y ^ 6) :=
      ((isBigO_refl (fun y : ℝ => y ^ 6) _).const_mul_left (c ^ 3)).congr_left (fun y => by ring)
    exact h3.trans h66
  have hsum := ((hc6.add (hcos.const_mul_left cP)).add (hsin.const_mul_left sP)).const_mul_left (1 / D)
  refine hsum.congr_left (fun y => ?_)
  rw [cos_sub]
  field_simp
  ring

/-- Term 1 of `Γ`: `(cosh y + cos t)^q / D^q = 1 + qα₁y² + (qβ₁ + q(q-1)/2·α₁²) y⁴ + O(y⁶)` along `t = π/p - c y²`. -/
theorem term1_expand (hp1 : 1 < p) (hp2 : p < 2) (c : ℝ) :
    (fun y : ℝ => (cosh y + cos (π / p - c * y ^ 2)) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2)
      - (1 + p / 2 * ((1/2 + sin (π / p) * c) / (1 + cos (2 * (π / (2 * p))))) * y ^ 2
        + (p / 2 * ((1/24 - cos (π / p) * c ^ 2 / 2) / (1 + cos (2 * (π / (2 * p)))))
          + p / 2 * (p / 2 - 1) / 2 * ((1/2 + sin (π / p) * c) / (1 + cos (2 * (π / (2 * p))))) ^ 2) * y ^ 4))
      =O[𝓝 0] (fun y => y ^ 6) := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD : 0 < 1 + cos (2 * (π / (2 * p))) := by rw [h2]; exact denom_pos p hp1 hp2
  refine (rpow_expand (p / 2) (xi1_expand hp1 hp2 c)).congr_left (fun y => ?_)
  have hu : 0 ≤ cosh y + cos (π / p - c * y ^ 2) := by
    have := one_le_cosh y; have := neg_one_le_cos (π / p - c * y ^ 2); linarith
  rw [add_sub_cancel, div_rpow hu hD.le]

/-- Term 2 of `Γ`: `cosh(S y/2)^r = 1 + r(S/2)²/2·y² + (r(S/2)⁴/24 + r(r-1)/2·((S/2)²/2)²) y⁴ + O(y⁶)`. -/
theorem term2_expand (S r : ℝ) :
    (fun y : ℝ => cosh (S * y / 2) ^ r
      - (1 + r * ((S / 2) ^ 2 / 2) * y ^ 2 + (r * ((S / 2) ^ 4 / 24) + r * (r - 1) / 2 * ((S / 2) ^ 2 / 2) ^ 2) * y ^ 4))
      =O[𝓝 0] (fun y => y ^ 6) := by
  refine (rpow_expand r (cosh6 (S / 2))).congr_left (fun y => ?_)
  have e : S / 2 * y = S * y / 2 := by ring
  rw [add_sub_cancel, e]

/-- The valley in `O`-form: `Γ - e - A y⁴ = O(y⁶)` along `t = π/p - c_v y²` at `s = S`. -/
theorem valley_isBigO (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    (fun y : ℝ => Gam p (Ssec p) y (π / p - valleyC p * y ^ 2) - ee p (π / p - valleyC p * y ^ 2) - Acoef p * y ^ 4)
      =O[𝓝 0] (fun y => y ^ 6) := by
  have hp1' : 1 < p := by linarith
  have hp0 : p ≠ 0 := by linarith
  have hK : K p (uu p) ≠ 0 := (K_pos hp1 hp2).ne'
  have h1 := term1_expand hp1' hp2 (valleyC p)
  have h2 := term2_expand (Ssec p) (p / Ssec p)
  have h3 := ee_valley hp0 (valleyC p)
  refine ((h1.sub h2).sub h3).congr_left (fun y => ?_)
  obtain ⟨hS, hD, hcP, hsP⟩ := trig_T hp1'
  simp only [Gam]
  have hcoef : (1 + p / 2 * ((1/2 + sin (π / p) * valleyC p) / (1 + cos (2 * (π / (2 * p))))) * y ^ 2
        + (p / 2 * ((1/24 - cos (π / p) * valleyC p ^ 2 / 2) / (1 + cos (2 * (π / (2 * p)))))
          + p / 2 * (p / 2 - 1) / 2 * ((1/2 + sin (π / p) * valleyC p) / (1 + cos (2 * (π / (2 * p))))) ^ 2) * y ^ 4)
      - (1 + p / Ssec p * ((Ssec p / 2) ^ 2 / 2) * y ^ 2 + (p / Ssec p * ((Ssec p / 2) ^ 4 / 24)
          + p / Ssec p * (p / Ssec p - 1) / 2 * ((Ssec p / 2) ^ 2 / 2) ^ 2) * y ^ 4)
      - tan (π / (2 * p)) * (p / 2 * valleyC p) * y ^ 2 = Acoef p * y ^ 4 := by
    have hK' := hK
    simp only [valleyC, a21, a02, Acoef, uu] at hK' ⊢
    rw [hS, hD, hcP, hsP]
    rw [uu] at hK
    set T := tan (π / (2 * p))
    have hT1 : 0 < 1 + T ^ 2 := by positivity
    field_simp
    simp only [K, H]
    ring
  linarith [hcoef]

end Specific

/-- **Prop. saddle, the valley** (tex l.325-327, l.354-361): at `s = S = sec²ϑ`, along `t = π/p - (a₂₁/(2a₀₂)) y²`,
    `Γ - e = A(p) y⁴ + O(y⁶)`. -/
theorem saddle_valley_proved {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      |Gam p (Ssec p) y (π / p - valleyC p * y ^ 2) - ee p (π / p - valleyC p * y ^ 2) - Acoef p * y ^ 4| ≤ C * y ^ 6 := by
  obtain ⟨C, hC⟩ := (valley_isBigO hp1 hp2).bound
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, δ, hδ, fun y hy => ?_⟩
  have h := hball (by rwa [Real.dist_eq, sub_zero])
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ y ^ 6)] at h

/-- `A(p) < 0` for `4/3 < p < 2` (tex l.326): from `H > 0`, `K > 0`. -/
theorem Acoef_neg {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : Acoef p < 0 := by
  have hp0 : 0 < p := by linarith
  have hH := H_pos hp1 hp2
  have hK := K_pos hp1 hp2
  have hS : 0 < Ssec p := by unfold Ssec; have := cos_th_pos (p := p) (by linarith); positivity
  have hu : 0 < uu p := by
    unfold uu
    have hc := cos_th_pos (p := p) (by linarith)
    have hs : 0 < sin (π / (2 * p)) := by
      apply sin_pos_of_pos_of_lt_pi (by positivity)
      rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
    rw [tan_eq_sin_div_cos]; positivity
  unfold Acoef
  have : 0 < p * Ssec p * uu p * H p (uu p) / (384 * K p (uu p)) := by positivity
  linarith [neg_div (384 * K p (uu p)) (p * Ssec p * uu p * H p (uu p))]

/-- The valley coefficient `c_v = a₂₁/(2a₀₂) > 0` (tex l.361: "the valley has t < π/p"). -/
theorem valleyC_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < valleyC p := by
  have hp0 : 0 < p := by linarith
  have hK := K_pos hp1 hp2
  have hc := cos_th_pos (p := p) (by linarith)
  have hs : 0 < sin (π / (2 * p)) := by
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hT : 0 < tan (π / (2 * p)) := by rw [tan_eq_sin_div_cos]; positivity
  have hS : 0 < Ssec p := by unfold Ssec; positivity
  have h2p : 0 < 2 - p := by linarith
  unfold valleyC a21 a02
  positivity

/-- **Theorem A's input** (tex l.391): at `s = sec²ϑ` there is a point with `0 < t < π/p` and `Γ < e`. -/
theorem saddle_point_proved {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ y t : ℝ, 0 < t ∧ t < π / p ∧ Gam p (Ssec p) y t < ee p t := by
  obtain ⟨C, δ, hδ, hb⟩ := saddle_valley_proved hp1 hp2
  have hA := Acoef_neg hp1 hp2
  have hc := valleyC_pos hp1 hp2
  have hp0 : 0 < p := by linarith
  have hπp : 0 < π / p := by positivity
  set M := max C 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hCM : C ≤ M := le_max_left _ _
  set y := min (δ / 2) (min 1 (min (-Acoef p / (2 * M)) (π / p / (2 * valleyC p)))) with hy
  have hy0 : 0 < y := by
    simp only [hy, lt_min_iff]
    refine ⟨by linarith, by norm_num, by apply div_pos (by linarith) (by linarith), by positivity⟩
  have hyδ : y < δ := by have := min_le_left (δ / 2) (min 1 (min (-Acoef p / (2 * M)) (π / p / (2 * valleyC p)))); linarith
  have hy1 : y ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hyA : y ≤ -Acoef p / (2 * M) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hyc : y ≤ π / p / (2 * valleyC p) := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hy2 : y ^ 2 ≤ y := by nlinarith
  have hy2pos : 0 < y ^ 2 := by positivity
  refine ⟨y, π / p - valleyC p * y ^ 2, ?_, ?_, ?_⟩
  · have h1 : valleyC p * y ^ 2 ≤ valleyC p * (π / p / (2 * valleyC p)) := by
      apply mul_le_mul_of_nonneg_left (le_trans hy2 hyc) hc.le
    have h2 : valleyC p * (π / p / (2 * valleyC p)) = π / p / 2 := by field_simp
    linarith
  · have : 0 < valleyC p * y ^ 2 := by positivity
    linarith
  · have hbound := hb y (by rw [abs_of_pos hy0]; exact hyδ)
    have hup := (abs_le.mp hbound).2
    have hMy : M * y ^ 2 ≤ -Acoef p / 2 := by
      have := mul_le_mul_of_nonneg_left (le_trans hy2 hyA) (by linarith : (0:ℝ) ≤ M)
      have e : M * (-Acoef p / (2 * M)) = -Acoef p / 2 := by field_simp
      linarith
    have hy4 : 0 < y ^ 4 := by positivity
    have hC6 : C * y ^ 6 ≤ M * y ^ 2 * y ^ 4 := by
      have : C * y ^ 6 ≤ M * y ^ 6 := mul_le_mul_of_nonneg_right hCM (by positivity)
      nlinarith
    have : M * y ^ 2 * y ^ 4 ≤ -Acoef p / 2 * y ^ 4 := mul_le_mul_of_nonneg_right hMy hy4.le
    nlinarith

end SaddleValley

end P18
