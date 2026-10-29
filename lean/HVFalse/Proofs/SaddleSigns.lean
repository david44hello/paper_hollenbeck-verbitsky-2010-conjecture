/-
  HVFalse/Proofs/SaddleSigns.lean - Prop. saddle: K > 0 and H > 0 for 4/3 < p < 2, by hand, no interval arithmetic
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route (the paper, l.373-378, certifies the signs with interval arithmetic, Arb and mpmath). Put c = cos(π/p) and x = π/p - π/2, so
  x ∈ (0, π/4) and sin x = -c. Then
    uu p = (1 - c)/(1 + c),   K = (p - 2 - p c)/(1 + c),   H = 4 F/(1 + c)²,   F = (3/2)(2-p)²(1+c) - (2-p)c - p c².
  K > 0 is Jordan's inequality 2x/π < sin x. Since p (2x + π) = 2π, F (2x + π)² = 2 Φ(x, sin x), where
    Φ(x, σ) = 12x² - 8x²σ + 2πxσ - 2πxσ² - π²σ²   (a quadratic in σ with negative leading coefficient),
  and Φ(x, sin x) > 0 on (0, π/4): for x ≤ 1/2 from x - x³/6 < sin x < x; for x > 1/2 from Taylor bounds of cos and sin
  at h = π/4 - x and the concavity of Φ in σ.
-/
import HVFalse.Defs.Saddle
import HVFalse.Proofs.Bridges
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

namespace P18

namespace SaddleSigns

/-- The polynomial `Φ(x, σ)`: `H > 0` reduces to `Φ(x, sin x) > 0` on `(0, π/4)`. -/
noncomputable def Phi (x σ : ℝ) : ℝ := 12*x^2 - 8*x^2*σ + 2*π*x*σ - 2*π*x*σ^2 - π^2*σ^2

/-- `F(p, c)`: `H p (uu p) = 4 F / (1 + c)²` with `c = cos(π/p)`. -/
noncomputable def F (p c : ℝ) : ℝ := 3/2*(2-p)^2*(1+c) - (2-p)*c - p*c^2

/-- The three-point identity of a quadratic in `σ` with leading coefficient `-(2πx + π²)`. -/
theorem Phi_three_point (x σ σ1 σ2 : ℝ) :
    (σ2 - σ1) * Phi x σ = (σ2 - σ) * Phi x σ1 + (σ - σ1) * Phi x σ2
      + (2*π*x + π^2) * ((σ2 - σ1) * (σ - σ1) * (σ2 - σ)) := by
  unfold Phi; ring

/-- Concavity in `σ`: `Φ(x, ·) > 0` at both ends of an interval gives `Φ(x, ·) > 0` inside it. -/
theorem Phi_pos_of_ends {x σ σ1 σ2 : ℝ} (hx : 0 < x) (h1 : σ1 ≤ σ) (h2 : σ ≤ σ2) (h12 : σ1 < σ2)
    (hP1 : 0 < Phi x σ1) (hP2 : 0 < Phi x σ2) : 0 < Phi x σ := by
  have hA : 0 < 2*π*x + π^2 := by positivity
  have t3 : 0 ≤ (2*π*x + π^2) * ((σ2 - σ1) * (σ - σ1) * (σ2 - σ)) :=
    mul_nonneg hA.le (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have t12 : 0 < (σ2 - σ) * Phi x σ1 + (σ - σ1) * Phi x σ2 := by
    rcases eq_or_lt_of_le h2 with h | h
    · have a : 0 ≤ (σ2 - σ) * Phi x σ1 := mul_nonneg (by linarith) hP1.le
      have b : 0 < (σ - σ1) * Phi x σ2 := mul_pos (by linarith) hP2
      linarith
    · have a : 0 < (σ2 - σ) * Phi x σ1 := mul_pos (by linarith) hP1
      have b : 0 ≤ (σ - σ1) * Phi x σ2 := mul_nonneg (by linarith) hP2.le
      linarith
  have key := Phi_three_point x σ σ1 σ2
  have hprod : 0 < (σ2 - σ1) * Phi x σ := by linarith
  by_contra hneg
  push Not at hneg
  nlinarith

/-- Region 1: `Φ(x, sin x) > 0` for `0 < x ≤ 1/2`, from `x - x³/6 < sin x < x`. -/
theorem Phi_pos_small {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1/2) : 0 < Phi x (sin x) := by
  have hs1 : sin x < x := sin_lt hx0
  have hs2 : x - x^3/6 < sin x := sin_gt_sub_cube hx0
  have hx2 : x^2 ≤ 1/4 := by nlinarith
  have hlo : 23/24 * x ≤ sin x := by nlinarith
  have hσ0 : 0 ≤ sin x := by linarith
  have hπ1 := pi_gt_d2
  have hπ2 := pi_lt_d2
  have hπ0 : 0 < π := pi_pos
  have hsq : sin x ^ 2 ≤ x ^ 2 := by nlinarith
  have e1 : 8*x^2*sin x ≤ 8*x^3 := by nlinarith
  have e2 : 2*π*(23/24)*x^2 ≤ 2*π*x*sin x := by
    have h' := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ 2*π*x)
    linarith
  have e3 : 2*π*x*sin x^2 ≤ 2*π*x^3 := by nlinarith
  have e4 : π^2*sin x^2 ≤ π^2*x^2 := by nlinarith
  have hπsq : π^2 < 9.93 := by nlinarith
  have hxπ : x*π ≤ 1/2*π := by nlinarith
  have hq : 0 < (12 + 23/12*π - π^2) - x*(8 + 2*π) := by nlinarith
  have hfin : 0 < x^2 * ((12 + 23/12*π - π^2) - x*(8 + 2*π)) := mul_pos (by positivity) hq
  unfold Phi
  nlinarith

/-- Region 2, the lower end `σ₁ = r(1 - h - h²/2)` (`r = √2/2`, `h = π/4 - x`): `Φ = h·P₁(h)` with `P₁ > 0`. -/
theorem Phi_pos_end1 {h r : ℝ} (hh0 : 0 < h) (hh1 : h < 2854/10000) (hr2 : r^2 = 1/2)
    (hrlo : 0.7071 < r) (hrhi : r < 0.70711) : 0 < Phi (π/4 - h) (r*(1 - h - h^2/2)) := by
  have expand : Phi (π/4 - h) (r*(1 - h - h^2/2)) = h * ((3*π^2/2 + 2*π*r - 5*π) + (-2*π*r - 2*π - 8*r + 12)*h
      + (-3*π^2/4 - π*r + 8*r)*h^2 + (-3*π^2/16 + π + 4*r)*h^3 + π/4*h^4) := by
    unfold Phi
    linear_combination (π*(4*h - 3*π)*(h^2 + 2*h - 2)^2/8) * hr2
  rw [expand]
  apply mul_pos hh0
  have hπ1 := pi_gt_d6
  have hπ2 := pi_lt_d6
  have hπsq1 : 9.8696 < π^2 := by nlinarith
  have hπsq2 : π^2 < 9.86961 := by nlinarith
  have hπr1 : 3.141592 * 0.7071 < π*r := by nlinarith
  have hπr2 : π*r < 3.141593 * 0.70711 := by nlinarith
  have k1 : 3.5 < 3*π^2/2 + 2*π*r - 5*π := by linarith
  have k2 : -4.39 < -2*π*r - 2*π - 8*r + 12 := by linarith
  have k3 : -3.97 < -3*π^2/4 - π*r + 8*r := by linarith
  have k4 : 0 < -3*π^2/16 + π + 4*r := by linarith
  have k5 : 0 < π/4 := by positivity
  have hh2 : h^2 < 0.0815 := by nlinarith
  have m2 : 0 ≤ ((-2*π*r - 2*π - 8*r + 12) + 4.39)*h := mul_nonneg (by linarith) hh0.le
  have m3 : 0 ≤ ((-3*π^2/4 - π*r + 8*r) + 3.97)*h^2 := mul_nonneg (by linarith) (by positivity)
  have m4 : 0 ≤ (-3*π^2/16 + π + 4*r)*h^3 := mul_nonneg k4.le (by positivity)
  have m5 : 0 ≤ π/4*h^4 := mul_nonneg k5.le (by positivity)
  nlinarith

/-- Region 2, the upper end `σ₂ = r(1 - h + h³/6)`: `Φ = h·P₂(h)` with `P₂ > 0`. -/
theorem Phi_pos_end2 {h r : ℝ} (hh0 : 0 < h) (hh1 : h < 2854/10000) (hr2 : r^2 = 1/2)
    (hrlo : 0.7071 < r) (hrhi : r < 0.70711) : 0 < Phi (π/4 - h) (r*(1 - h + h^3/6)) := by
  have expand : Phi (π/4 - h) (r*(1 - h + h^3/6)) = h * ((3*π^2/2 + 2*π*r - 5*π)
      + (-3*π^2/4 - 2*π*r - 2*π - 8*r + 12)*h + (-π^2/4 + π + 8*r)*h^2 + (π^2/4 + π*r/3 + π/3)*h^3
      + (-π/3 - 4*r/3)*h^4 + (-π^2/48)*h^5 + π/36*h^6) := by
    unfold Phi
    linear_combination (π*(4*h - 3*π)*(h^3 - 6*h + 6)^2/72) * hr2
  rw [expand]
  apply mul_pos hh0
  have hπ1 := pi_gt_d6
  have hπ2 := pi_lt_d6
  have hπsq1 : 9.8696 < π^2 := by nlinarith
  have hπsq2 : π^2 < 9.86961 := by nlinarith
  have hπr1 : 3.141592 * 0.7071 < π*r := by nlinarith
  have hπr2 : π*r < 3.141593 * 0.70711 := by nlinarith
  have k1 : 3.539 < 3*π^2/2 + 2*π*r - 5*π := by linarith
  have k2 : -11.79 < -3*π^2/4 - 2*π*r - 2*π - 8*r + 12 := by linarith
  have k3 : 0 < -π^2/4 + π + 8*r := by linarith
  have k4 : 0 < π^2/4 + π*r/3 + π/3 := by linarith
  have k5 : -1.991 < -π/3 - 4*r/3 := by linarith
  have k6 : -0.2057 < -π^2/48 := by linarith
  have k7 : 0 < π/36 := by positivity
  have hh2 : h^2 < 0.0815 := by nlinarith
  have hh4 : h^4 < 0.00664 := by nlinarith
  have hh5 : h^5 < 0.0019 := by nlinarith
  have m2 : 0 ≤ ((-3*π^2/4 - 2*π*r - 2*π - 8*r + 12) + 11.79)*h := mul_nonneg (by linarith) hh0.le
  have m3 : 0 ≤ (-π^2/4 + π + 8*r)*h^2 := mul_nonneg k3.le (by positivity)
  have m4 : 0 ≤ (π^2/4 + π*r/3 + π/3)*h^3 := mul_nonneg k4.le (by positivity)
  have m5 : 0 ≤ ((-π/3 - 4*r/3) + 1.991)*h^4 := mul_nonneg (by linarith) (by positivity)
  have m6 : 0 ≤ ((-π^2/48) + 0.2057)*h^5 := mul_nonneg (by linarith) (by positivity)
  have m7 : 0 ≤ π/36*h^6 := mul_nonneg k7.le (by positivity)
  nlinarith

/-- Region 2: `Φ(x, sin x) > 0` for `1/2 < x < π/4`. -/
theorem Phi_pos_large {x : ℝ} (hx0 : 1/2 < x) (hx1 : x < π/4) : 0 < Phi x (sin x) := by
  have hπ2 := pi_lt_d6
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = π/4 - x := ⟨_, rfl⟩
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = √2/2 := ⟨_, rfl⟩
  have hh0 : 0 < h := by linarith
  have hh1 : h < 2854/10000 := by linarith
  have hx : x = π/4 - h := by linarith
  have hr2 : r^2 = 1/2 := by
    rw [hr_def, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num
  have hr0 : 0 < r := by rw [hr_def]; positivity
  have hrlo : 0.7071 < r := by nlinarith
  have hrhi : r < 0.70711 := by nlinarith
  have hsin : sin x = r * (cos h - sin h) := by
    rw [hx, sin_sub, sin_pi_div_four, cos_pi_div_four, hr_def]; ring
  have hc1 : 1 - h^2/2 ≤ cos h := one_sub_sq_div_two_le_cos
  have hc2 : cos h ≤ 1 := cos_le_one h
  have hs1 : sin h < h := sin_lt hh0
  have hs2 : h - h^3/6 < sin h := sin_gt_sub_cube hh0
  have hlo : r*(1 - h - h^2/2) ≤ sin x := by
    rw [hsin]; exact mul_le_mul_of_nonneg_left (by linarith) hr0.le
  have hhi : sin x ≤ r*(1 - h + h^3/6) := by
    rw [hsin]; exact mul_le_mul_of_nonneg_left (by linarith) hr0.le
  have h12 : r*(1 - h - h^2/2) < r*(1 - h + h^3/6) := by
    apply mul_lt_mul_of_pos_left _ hr0
    nlinarith
  have hx0' : 0 < x := by linarith
  apply Phi_pos_of_ends hx0' hlo hhi h12
  · rw [hx]; exact Phi_pos_end1 hh0 hh1 hr2 hrlo hrhi
  · rw [hx]; exact Phi_pos_end2 hh0 hh1 hr2 hrlo hrhi

/-- `Φ(x, sin x) > 0` on `(0, π/4)`. -/
theorem Phi_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < π/4) : 0 < Phi x (sin x) := by
  rcases le_or_gt x (1/2) with h | h
  · exact Phi_pos_small hx0 h
  · exact Phi_pos_large h hx1

/-- `uu p = (1 - c)/(1 + c)` with `c = cos(π/p)`. -/
theorem uu_eq {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    uu p = (1 - cos (π / p)) / (1 + cos (π / p)) := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : π / p = 2 * (π / (2 * p)) := by field_simp
  have hc : cos (π / p) = 2 * cos (π / (2 * p)) ^ 2 - 1 := by rw [h2, cos_two_mul]
  have hpos : 0 < 1 + cos (π / p) := denom_pos p hp1 hp2
  have hcos2 : cos (π / (2 * p)) ^ 2 ≠ 0 := by
    intro h0; rw [h0] at hc; linarith
  have hcos : cos (π / (2 * p)) ≠ 0 := fun h0 => hcos2 (by rw [h0]; ring)
  unfold uu
  rw [tan_eq_sin_div_cos, div_pow, sin_sq, hc]
  field_simp
  ring

/-- `K(p, (1-c)/(1+c)) = (p - 2 - p c)/(1 + c)`. -/
theorem K_eq {p c : ℝ} (hc : 1 + c ≠ 0) : K p ((1 - c) / (1 + c)) = (p - 2 - p * c) / (1 + c) := by
  unfold K; field_simp; ring

/-- `H(p, (1-c)/(1+c)) = 4 F(p,c)/(1 + c)²`. -/
theorem H_eq {p c : ℝ} (hc : 1 + c ≠ 0) : H p ((1 - c) / (1 + c)) = 4 * F p c / (1 + c) ^ 2 := by
  unfold H F; field_simp; ring

/-- Jordan's inequality at `x = π/p - π/2`: `2/p - 1 < -cos(π/p)` for `1 < p < 2`. -/
theorem jordan_c {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 2 / p - 1 < -cos (π / p) := by
  have hp0 : 0 < p := by linarith
  have hπ : 0 < π := pi_pos
  have hlt1 : π / 2 < π / p := div_lt_div_of_pos_left hπ hp0 hp2
  have hlt2 : π / p < π := by rw [div_lt_iff₀ hp0]; nlinarith
  have hj := mul_lt_sin (x := π / p - π / 2) (by linarith) (by linarith)
  rw [sin_sub_pi_div_two] at hj
  have e : 2 / π * (π / p - π / 2) = 2 / p - 1 := by field_simp
  linarith

/-- `F(p, cos(π/p)) > 0` for `4/3 < p < 2`. -/
theorem F_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < F p (cos (π / p)) := by
  have hp0 : 0 < p := by linarith
  have hπ : 0 < π := pi_pos
  obtain ⟨x, hx_def⟩ : ∃ x : ℝ, x = π / p - π / 2 := ⟨_, rfl⟩
  have hlt1 : π / 2 < π / p := div_lt_div_of_pos_left hπ hp0 hp2
  have hlt2 : π / p < 3 * π / 4 := by rw [div_lt_div_iff₀ hp0 (by norm_num)]; nlinarith
  have hx0 : 0 < x := by linarith
  have hx1 : x < π / 4 := by linarith
  have hrel : p * (2 * x + π) = 2 * π := by rw [hx_def]; field_simp; ring
  have hc : cos (π / p) = -sin x := by rw [hx_def, sin_sub_pi_div_two]; ring
  have key : F p (-sin x) * (2 * x + π) ^ 2 = 2 * Phi x (sin x) := by
    unfold F Phi
    linear_combination (-(3*p*π*sin x - 3*p*π + 6*p*sin x*x - 6*p*x + 2*π*sin x^2 - 4*π*sin x + 6*π
      + 4*sin x^2*x - 20*sin x*x + 24*x)/2) * hrel
  have hΦ := Phi_pos hx0 hx1
  have hw : 0 < (2 * x + π) ^ 2 := by positivity
  rw [hc]
  by_contra hneg
  push Not at hneg
  nlinarith

end SaddleSigns

open SaddleSigns in
/-- **Prop. saddle, sign of `K`** (tex l.324, l.370, l.372): `K = (p-1)u - 1 > 0` for `4/3 < p < 2`, `u = tan²(π/(2p))`.
    Route difference: Jordan's inequality instead of the paper's 16 Arb intervals. -/
theorem K_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < K p (uu p) := by
  have hp1' : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hd := denom_pos p hp1' hp2
  rw [uu_eq hp1' hp2, K_eq hd.ne']
  apply div_pos _ hd
  have hj := mul_lt_mul_of_pos_left (jordan_c hp1' hp2) hp0
  have e : p * (2 / p - 1) = 2 - p := by field_simp
  linarith

open SaddleSigns in
/-- **Prop. saddle, sign of `H`** (tex l.324, l.363-378): `H(p, u) > 0` for `4/3 < p < 2`, `u = tan²(π/(2p))`.
    Route difference: an exact identity `H = 4F/(1+c)²` and `F (2x+π)² = 2Φ(x, sin x)` with elementary bounds, instead of the
    paper's 367 Arb intervals and the Taylor argument at `p = 2`. -/
theorem H_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < H p (uu p) := by
  have hp1' : 1 < p := by linarith
  have hd := denom_pos p hp1' hp2
  rw [uu_eq hp1' hp2, H_eq hd.ne']
  exact div_pos (mul_pos (by norm_num) (F_pos hp1 hp2)) (pow_pos hd 2)

end P18
