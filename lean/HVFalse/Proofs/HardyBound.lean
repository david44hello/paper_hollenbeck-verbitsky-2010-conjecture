/-
  HVFalse/Proofs/HardyBound.lean - C13b: the explicit pair `z, w` of Prop. 8 is in `H^{3/2}` for every `δ ∈ (0, 2π)`
  (the paper, proof of Prop. 8, l.471-473), from C13u (`0 ≤ Re Y ≤ y₂` in the disc) and one domination bound
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route: for `|c| = 1` and `0 ≤ r ≤ 1`, `|1 - c| ≤ 2|1 - rc|`. All `α_k > 0` and `Σ α_k = 2`, so
  `|Π(re^{iθ})| ≤ 2|Π(e^{iθ})|` off the three singular angles; with C13u, `|z(re^{iθ})|, |w(re^{iθ})| ≤ 2e^{y₂/2}|Π(e^{iθ})|`.
  On the circle `|Π|^{3/2} = Π_k |2 sin((θ - θ_k)/2)|^{-(3/4)α_k}` (`R2e.P`), which is integrable (`(3/4)α_k < 1`).
-/
import HVFalse.Proofs.R2e
import HVFalse.Proofs.R2c
import HVFalse.Paper.ComputerChecked

open Real MeasureTheory Set
open scoped Interval

namespace P18.HardyBound

/-! ### The domination bound -/

/-- `|1 - c| ≤ 2|1 - rc|` for `|c| = 1` and `0 ≤ r ≤ 1`. -/
theorem norm_one_sub_le {c : ℂ} (hc : ‖c‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖1 - c‖ ≤ 2 * ‖1 - (r : ℂ) * c‖ := by
  have h1 : ‖1 - c‖ ≤ ‖1 - (r : ℂ) * c‖ + ‖(r : ℂ) * c - c‖ := norm_sub_le_norm_sub_add_norm_sub 1 _ c
  have h2 : ‖(r : ℂ) * c - c‖ = 1 - r := by
    rw [show (r : ℂ) * c - c = ((r - 1 : ℝ) : ℂ) * c by push_cast; ring, norm_mul, hc, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have h3 : 1 - r ≤ ‖1 - (r : ℂ) * c‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * c)
    rwa [norm_one, norm_mul, hc, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
  linarith

/-- `Y^(-a) ≤ 2^a X^(-a)` when `0 < X ≤ 2Y` and `a ≥ 0`. -/
theorem rpow_neg_le_of_le_two_mul {X Y a : ℝ} (ha : 0 ≤ a) (hX : 0 < X) (hXY : X ≤ 2 * Y) :
    Y ^ (-a) ≤ 2 ^ a * X ^ (-a) := by
  have hX2 : 0 < X / 2 := by positivity
  calc Y ^ (-a) ≤ (X / 2) ^ (-a) := Real.rpow_le_rpow_of_nonpos hX2 (by linarith) (by linarith)
    _ = 2 ^ a * X ^ (-a) := by
      rw [Real.div_rpow hX.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]

/-- `|Π| = |1 + ζ|^{-α_π/2} |1 - ζe^{iδ/2}|^{-α₋/2} |1 - ζe^{-iδ/2}|^{-α₊/2}`. -/
theorem norm_Pi_eq_mul (δ : ℝ) (ζ : ℂ) :
    ‖Explicit.Pi δ ζ‖ = ‖1 + ζ‖ ^ (-(Explicit.aC / 2)) * ‖1 - ζ * Explicit.ePlus δ‖ ^ (-(Explicit.aA / 2)) *
      ‖1 - ζ * Explicit.eMinus δ‖ ^ (-(Explicit.aB / 2)) := by
  rw [Prop8Steps.norm_Pi, neg_div, Real.rpow_neg (norm_nonneg (1 - ζ * Explicit.ePlus δ)),
    Real.rpow_neg (norm_nonneg (1 - ζ * Explicit.eMinus δ))]
  ring

/-- `α_π/2 + α₋/2 + α₊/2 = 1`. -/
theorem half_exps_sum : Explicit.aC / 2 + Explicit.aA / 2 + Explicit.aB / 2 = 1 := by
  unfold Explicit.aC; ring

/-- The domination bound: `|Π(rζ₀)| ≤ 2|Π(ζ₀)|` for `|ζ₀| = 1`, `0 ≤ r ≤ 1`, `ζ₀` not a singular point. -/
theorem norm_Pi_radial_le (δ : ℝ) {ζ₀ : ℂ} (h0 : ‖ζ₀‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA : 0 < ‖1 + ζ₀‖) (hB : 0 < ‖1 - ζ₀ * Explicit.ePlus δ‖) (hC : 0 < ‖1 - ζ₀ * Explicit.eMinus δ‖) :
    ‖Explicit.Pi δ ((r : ℂ) * ζ₀)‖ ≤ 2 * ‖Explicit.Pi δ ζ₀‖ := by
  have hp : ‖ζ₀ * Explicit.ePlus δ‖ = 1 := by rw [norm_mul, h0, R2c.norm_ePlus, mul_one]
  have hm : ‖ζ₀ * Explicit.eMinus δ‖ = 1 := by rw [norm_mul, h0, R2c.norm_eMinus, mul_one]
  have hn : ‖-ζ₀‖ = 1 := by rw [norm_neg, h0]
  have e1 : (1 : ℂ) + (r : ℂ) * ζ₀ = 1 - (r : ℂ) * (-ζ₀) := by ring
  have e2 : (1 : ℂ) - (r : ℂ) * ζ₀ * Explicit.ePlus δ = 1 - (r : ℂ) * (ζ₀ * Explicit.ePlus δ) := by ring
  have e3 : (1 : ℂ) - (r : ℂ) * ζ₀ * Explicit.eMinus δ = 1 - (r : ℂ) * (ζ₀ * Explicit.eMinus δ) := by ring
  have b1 := norm_one_sub_le hn hr0 hr1
  rw [sub_neg_eq_add] at b1
  have b2 := norm_one_sub_le hp hr0 hr1
  have b3 := norm_one_sub_le hm hr0 hr1
  have hAa := R2b.aA_pos
  have hBb := R2b.aB_pos
  have hCc := R2b.aC_pos
  have f1 := rpow_neg_le_of_le_two_mul (a := Explicit.aC / 2) (by linarith) hA b1
  have f2 := rpow_neg_le_of_le_two_mul (a := Explicit.aA / 2) (by linarith) hB b2
  have f3 := rpow_neg_le_of_le_two_mul (a := Explicit.aB / 2) (by linarith) hC b3
  rw [norm_Pi_eq_mul, norm_Pi_eq_mul, e1, e2, e3]
  have n1 := Real.rpow_nonneg (norm_nonneg (1 - (r : ℂ) * (-ζ₀))) (-(Explicit.aC / 2))
  have n2 := Real.rpow_nonneg (norm_nonneg (1 - (r : ℂ) * (ζ₀ * Explicit.ePlus δ))) (-(Explicit.aA / 2))
  have n3 := Real.rpow_nonneg (norm_nonneg (1 - (r : ℂ) * (ζ₀ * Explicit.eMinus δ))) (-(Explicit.aB / 2))
  have m1 := Real.rpow_nonneg (norm_nonneg (1 + ζ₀)) (-(Explicit.aC / 2))
  have m2 := Real.rpow_nonneg (norm_nonneg (1 - ζ₀ * Explicit.ePlus δ)) (-(Explicit.aA / 2))
  have k1 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Explicit.aC / 2)
  have k2 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Explicit.aA / 2)
  calc _ ≤ (2 ^ (Explicit.aC / 2) * ‖1 + ζ₀‖ ^ (-(Explicit.aC / 2))) *
        (2 ^ (Explicit.aA / 2) * ‖1 - ζ₀ * Explicit.ePlus δ‖ ^ (-(Explicit.aA / 2))) *
        (2 ^ (Explicit.aB / 2) * ‖1 - ζ₀ * Explicit.eMinus δ‖ ^ (-(Explicit.aB / 2))) :=
        mul_le_mul (mul_le_mul f1 f2 n2 (mul_nonneg k1 m1)) f3 n3 (mul_nonneg (mul_nonneg k1 m1) (mul_nonneg k2 m2))
    _ = 2 ^ (Explicit.aC / 2 + Explicit.aA / 2 + Explicit.aB / 2) * (‖1 + ζ₀‖ ^ (-(Explicit.aC / 2)) *
        ‖1 - ζ₀ * Explicit.ePlus δ‖ ^ (-(Explicit.aA / 2)) * ‖1 - ζ₀ * Explicit.eMinus δ‖ ^ (-(Explicit.aB / 2))) := by
      rw [Real.rpow_add two_pos, Real.rpow_add two_pos]
      ring
    _ = _ := by rw [half_exps_sum, Real.rpow_one]

/-! ### `|z|` and `|w|` in terms of `|Π|` and `Re Y` -/

theorem norm_exp_I_mul (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I x

theorem norm_zf (δ : ℝ) (ζ : ℂ) :
    ‖Explicit.zf δ ζ‖ = ‖Explicit.Pi δ ζ‖ * Real.exp ((Explicit.Yf δ ζ).re / 2) := by
  unfold Explicit.zf
  rw [norm_mul, norm_mul, norm_exp_I_mul, one_mul, Complex.norm_exp]
  congr 2
  simp

theorem norm_wf (δ : ℝ) (ζ : ℂ) :
    ‖Explicit.wf δ ζ‖ = ‖ζ‖ * ‖Explicit.Pi δ ζ‖ * Real.exp (-(Explicit.Yf δ ζ).re / 2) := by
  unfold Explicit.wf
  rw [norm_mul, norm_mul, norm_mul, norm_exp_I_mul, mul_one, Complex.norm_exp]
  congr 2
  simp

/-- `K = 2 e^{y₂/2}`, the constant of the domination bound. -/
noncomputable def K : ℝ := 2 * Real.exp (Explicit.y2 / 2)

theorem K_pos : 0 < K := by unfold K; positivity

/-- The three singular angles are avoided: `|1 + ζ₀|, |1 - ζ₀e^{±iδ/2}| > 0`. -/
structure Regular (δ : ℝ) (ζ₀ : ℂ) : Prop where
  hA : 0 < ‖1 + ζ₀‖
  hB : 0 < ‖1 - ζ₀ * Explicit.ePlus δ‖
  hC : 0 < ‖1 - ζ₀ * Explicit.eMinus δ‖

/-- `|z(rζ₀)|, |w(rζ₀)| ≤ K |Π(ζ₀)|` for `|ζ₀| = 1` regular and `0 < r < 1` (C13u: `0 ≤ Re Y ≤ y₂`). -/
theorem norm_zw_radial_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {ζ₀ : ℂ} (h0 : ‖ζ₀‖ = 1)
    (hreg : Regular δ ζ₀) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖Explicit.zf δ ((r : ℂ) * ζ₀)‖ ≤ K * ‖Explicit.Pi δ ζ₀‖ ∧
      ‖Explicit.wf δ ((r : ℂ) * ζ₀)‖ ≤ K * ‖Explicit.Pi δ ζ₀‖ := by
  have hnorm : ‖(r : ℂ) * ζ₀‖ = r := by
    rw [norm_mul, h0, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hball : (r : ℂ) * ζ₀ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hr1
  obtain ⟨hY0, hY1⟩ := R2c.C13u_ReY_bounds hδ0 hδ1 _ hball
  have hP := norm_Pi_radial_le δ h0 hr0.le hr1.le hreg.hA hreg.hB hreg.hC
  have hPn := norm_nonneg (Explicit.Pi δ ((r : ℂ) * ζ₀))
  have hy2 : 0 < Explicit.y2 := by unfold Explicit.y2; norm_num
  have he1 : 1 ≤ Real.exp (Explicit.y2 / 2) := Real.one_le_exp (by linarith)
  have he2 : Real.exp ((Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2) ≤ Real.exp (Explicit.y2 / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have he3 : Real.exp (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he3' := (Real.exp_pos (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2)).le
  have hP0 := norm_nonneg (Explicit.Pi δ ζ₀)
  unfold K
  constructor
  · rw [norm_zf]
    calc ‖Explicit.Pi δ ((r : ℂ) * ζ₀)‖ * Real.exp ((Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2)
        ≤ (2 * ‖Explicit.Pi δ ζ₀‖) * Real.exp (Explicit.y2 / 2) :=
          mul_le_mul hP he2 (Real.exp_pos _).le (by positivity)
      _ = 2 * Real.exp (Explicit.y2 / 2) * ‖Explicit.Pi δ ζ₀‖ := by ring
  · rw [norm_wf, hnorm]
    calc r * ‖Explicit.Pi δ ((r : ℂ) * ζ₀)‖ * Real.exp (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2)
        ≤ 1 * (2 * ‖Explicit.Pi δ ζ₀‖) * 1 :=
          mul_le_mul (mul_le_mul hr1.le hP hPn zero_le_one) he3 he3' (by positivity)
      _ ≤ 2 * Real.exp (Explicit.y2 / 2) * ‖Explicit.Pi δ ζ₀‖ := by nlinarith

/-! ### `|Π|^{3/2}` on the circle is `R2e.P` -/

/-- On the circle, `|Π(e^{iθ})|^{3/2} = Π_k |2 sin((θ - θ_k)/2)|^{-(3/4)α_k}` (`θ_k = -δ/2, δ/2, π`). -/
theorem norm_Pi_circle_rpow (δ θ : ℝ) :
    ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 2 : ℝ) =
      R2e.P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC) θ := by
  obtain ⟨hzA, hzB⟩ := ArcsAux.zeta_mul_e δ θ
  have h32 : ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 2 : ℝ) =
      (‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ 2) ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [h32, Prop8Steps.norm_Pi, hzA, hzB, Prop8Steps.norm_one_add_exp, Prop8Steps.norm_one_sub_exp,
    Prop8Steps.norm_one_sub_exp, Prop8Steps.rpow_combine (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)]
  simp only [R2e.P, R2e.fac, sub_neg_eq_add, neg_mul]


/-! ### `R2e.P` is integrable over a period, for every `δ ∈ (0, 2π)` -/

/-- `R2e.P` is integrable on `[-π, π]` for `0 < δ < 2π` and exponents in `[0, 1)`: as in `R2e.P_arcs`, but the outer
arcs are split at their midpoints `∓(π/2 + δ/4)`, so that each piece has one singular factor, at an end. -/
theorem P_period {δ x y z : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y)
    (hy1 : y < 1) (hz0 : 0 ≤ z) (hz1 : z < 1) : IntervalIntegrable (R2e.P δ x y z) volume (-π) π := by
  have hpi := pi_gt_three
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = π / 2 + δ / 4 := ⟨_, rfl⟩
  have eA : R2e.P δ x y z = fun θ => R2e.fac (-(δ / 2)) x θ * (R2e.fac (δ / 2) y θ * R2e.fac π z θ) :=
    funext fun θ => by unfold R2e.P; ring
  have eB : R2e.P δ x y z = fun θ => R2e.fac (δ / 2) y θ * (R2e.fac (-(δ / 2)) x θ * R2e.fac π z θ) :=
    funext fun θ => by unfold R2e.P; ring
  have p1 : IntervalIntegrable (R2e.P δ x y z) volume (-π) (-m) := by
    have hs := R2e.fac_right (c := -π) hz0 hz1 (by linarith : (0 : ℝ) < π / 2 - δ / 4)
      (by linarith : π / 2 - δ / 4 ≤ π)
    rw [show -π + (π / 2 - δ / 4) = -m by rw [hm]; ring, ← R2e.fac_pi] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (-(δ / 2)) x θ * R2e.fac (δ / 2) y θ) [[-π, -m]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => R2e.sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => R2e.sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    exact hs.continuousOn_mul hc
  have p2 : IntervalIntegrable (R2e.P δ x y z) volume (-m) (-(δ / 2)) := by
    have hs := R2e.fac_left (c := -(δ / 2)) hx0 hx1 (by linarith : (0 : ℝ) < π / 2 - δ / 4)
      (by linarith : π / 2 - δ / 4 ≤ π)
    rw [show -(δ / 2) - (π / 2 - δ / 4) = -m by rw [hm]; ring] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (δ / 2) y θ * R2e.fac π z θ) [[-m, -(δ / 2)]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => R2e.sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := π) (a := z) fun θ hθ => R2e.sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eA]
    exact hs.mul_continuousOn hc
  have p3 : IntervalIntegrable (R2e.P δ x y z) volume (-(δ / 2)) 0 := by
    have hs := R2e.fac_right (c := -(δ / 2)) hx0 hx1 (by linarith : (0 : ℝ) < δ / 2) (by linarith : δ / 2 ≤ π)
    rw [show -(δ / 2) + δ / 2 = 0 by ring] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (δ / 2) y θ * R2e.fac π z θ) [[-(δ / 2), 0]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => R2e.sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := π) (a := z) fun θ hθ => R2e.sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eA]
    exact hs.mul_continuousOn hc
  have p4 : IntervalIntegrable (R2e.P δ x y z) volume 0 (δ / 2) := by
    have hs := R2e.fac_left (c := δ / 2) hy0 hy1 (by linarith : (0 : ℝ) < δ / 2) (by linarith : δ / 2 ≤ π)
    rw [show δ / 2 - δ / 2 = 0 by ring] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (-(δ / 2)) x θ * R2e.fac π z θ) [[0, δ / 2]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => R2e.sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := π) (a := z) fun θ hθ => R2e.sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eB]
    exact hs.mul_continuousOn hc
  have p5 : IntervalIntegrable (R2e.P δ x y z) volume (δ / 2) m := by
    have hs := R2e.fac_right (c := δ / 2) hy0 hy1 (by linarith : (0 : ℝ) < π / 2 - δ / 4)
      (by linarith : π / 2 - δ / 4 ≤ π)
    rw [show δ / 2 + (π / 2 - δ / 4) = m by rw [hm]; ring] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (-(δ / 2)) x θ * R2e.fac π z θ) [[δ / 2, m]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => R2e.sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := π) (a := z) fun θ hθ => R2e.sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eB]
    exact hs.mul_continuousOn hc
  have p6 : IntervalIntegrable (R2e.P δ x y z) volume m π := by
    have hs := R2e.fac_left (c := π) hz0 hz1 (by linarith : (0 : ℝ) < π / 2 - δ / 4) (by linarith : π / 2 - δ / 4 ≤ π)
    rw [show π - (π / 2 - δ / 4) = m by rw [hm]; ring] at hs
    have hc : ContinuousOn (fun θ => R2e.fac (-(δ / 2)) x θ * R2e.fac (δ / 2) y θ) [[m, π]] := by
      rw [uIcc_of_le (by linarith)]
      exact (R2e.fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => R2e.sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (R2e.fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => R2e.sin_ne_of_pos
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    exact hs.continuousOn_mul hc
  exact ((((p1.trans p2).trans p3).trans p4).trans p5).trans p6

theorem fac_periodic (c a : ℝ) : Function.Periodic (R2e.fac c a) (2 * π) := fun θ => by
  unfold R2e.fac
  rw [show (θ + 2 * π - c) / 2 = (θ - c) / 2 + π by ring, Real.sin_add_pi, mul_neg, abs_neg]

theorem P_periodic (δ x y z : ℝ) : Function.Periodic (R2e.P δ x y z) (2 * π) := fun θ => by
  unfold R2e.P
  rw [fac_periodic (-(δ / 2)) x θ, fac_periodic (δ / 2) y θ, fac_periodic π z θ]

/-- `|Π(e^{iθ})|^{3/2}` (as `R2e.P`) is integrable on `[0, 2π]` for every `δ ∈ (0, 2π)`. -/
theorem P_integrable {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    IntervalIntegrable (R2e.P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC)) volume 0 (2 * π) := by
  obtain ⟨hA, hB, hC⟩ := explicit_exponents
  have h := P_period hδ0 hδ1 (by linarith [R2b.aA_pos]) hA (by linarith [R2b.aB_pos]) hB (by linarith [R2b.aC_pos]) hC
  exact (P_periodic _ _ _ _).intervalIntegrable (t := -π) (by positivity)
    (by rw [show -π + 2 * π = π by ring]; exact h) 0 (2 * π)

/-! ### The three singular angles form a null set -/

theorem sin_zero_countable (c : ℝ) : {θ : ℝ | Real.sin ((θ - c) / 2) = 0}.Countable := by
  refine (Set.countable_range (fun n : ℤ => 2 * ((n : ℝ) * π) + c)).mono fun θ hθ => ?_
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hθ
  exact ⟨n, by show 2 * ((n : ℝ) * π) + c = θ; linarith⟩

/-- Almost every point `e^{iθ}` of the circle is regular. -/
theorem ae_regular (δ : ℝ) : ∀ᵐ θ : ℝ ∂volume, Regular δ (Complex.exp ((θ : ℂ) * Complex.I)) := by
  have hS := ((sin_zero_countable π).union (sin_zero_countable (-(δ / 2)))).union (sin_zero_countable (δ / 2))
  refine (hS.ae_notMem volume).mono fun θ hθ => ?_
  simp only [Set.mem_union, not_or] at hθ
  obtain ⟨⟨h1, h2⟩, h3⟩ := hθ
  have h1' : Real.sin ((θ - π) / 2) ≠ 0 := h1
  have h2' : Real.sin ((θ + δ / 2) / 2) ≠ 0 := by rw [← sub_neg_eq_add]; exact h2
  have h3' : Real.sin ((θ - δ / 2) / 2) ≠ 0 := h3
  obtain ⟨hzA, hzB⟩ := ArcsAux.zeta_mul_e δ θ
  refine ⟨?_, ?_, ?_⟩
  · rw [Prop8Steps.norm_one_add_exp]; exact abs_pos.2 (mul_ne_zero two_ne_zero h1')
  · rw [hzA, Prop8Steps.norm_one_sub_exp]; exact abs_pos.2 (mul_ne_zero two_ne_zero h2')
  · rw [hzB, Prop8Steps.norm_one_sub_exp]; exact abs_pos.2 (mul_ne_zero two_ne_zero h3')

/-! ### The `H^{3/2}` bound -/

/-- A holomorphic `F` on the disc with `|F(re^{iθ})| ≤ K|Π(e^{iθ})|` at regular `θ` is in `H^{3/2}`, with
`M = ∫₀^{2π} K^{3/2} |Π(e^{iθ})|^{3/2} dθ`. -/
theorem inHardy_of_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {F : ℂ → ℂ}
    (hd : DifferentiableOn ℂ F (Metric.ball 0 1))
    (hb : ∀ θ r : ℝ, Regular δ (Complex.exp ((θ : ℂ) * Complex.I)) → 0 < r → r < 1 →
      ‖F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖) :
    Explicit.InHardy (3 / 2) F := by
  have hP := P_integrable hδ0 hδ1
  refine ⟨hd, ∫ θ in (0 : ℝ)..(2 * π), K ^ (3 / 2 : ℝ) *
    R2e.P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC) θ, fun r hr => ?_⟩
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegral.integral_of_le h2pi, intervalIntegral.integral_of_le h2pi]
  refine integral_mono_of_nonneg (ae_of_all _ fun θ => ?_) (hP.const_mul (K ^ (3 / 2 : ℝ))).1
    (ae_restrict_of_ae ((ae_regular δ).mono fun θ hθ => ?_))
  · simp only [Pi.zero_apply]; positivity
  · have h := hb θ r hθ hr.1 hr.2
    show ‖F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 2 : ℝ) ≤
      K ^ (3 / 2 : ℝ) * R2e.P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC) θ
    rw [← norm_Pi_circle_rpow, ← Real.mul_rpow K_pos.le (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) h (by norm_num)

/-! ### `z` and `w` are holomorphic in the disc -/

theorem re_one_add_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < (1 + ζ).re := by
  have hr := Complex.re_le_norm (-ζ)
  rw [Complex.neg_re, norm_neg] at hr
  rw [Complex.add_re, Complex.one_re]
  linarith

theorem ne_zero_of_re_pos {u : ℂ} (hu : 0 < u.re) : u ≠ 0 := fun h => by
  rw [h, Complex.zero_re] at hu
  exact lt_irrefl 0 hu

/-- The quotient of two numbers with positive real part lies in the slit plane. -/
theorem div_mem_slitPlane {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) : u / v ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  have hn : 0 < Complex.normSq v := Complex.normSq_pos.2 (ne_zero_of_re_pos hv)
  by_cases h : (u / v).im = 0
  · left
    rw [Complex.div_im, sub_eq_zero, div_left_inj' hn.ne'] at h
    rw [Complex.div_re, ← add_div]
    apply div_pos _ hn
    have key : v.re * (u.re * v.re + u.im * v.im) = u.re * (v.re ^ 2 + v.im ^ 2) := by
      linear_combination v.im * h
    have hpos : 0 < v.re * (u.re * v.re + u.im * v.im) := by
      rw [key]; exact mul_pos hu (add_pos_of_pos_of_nonneg (pow_pos hv 2) (sq_nonneg _))
    exact pos_of_mul_pos_right hpos hv.le
  · exact Or.inr h

theorem re_one_sub_ePlus_pos (δ : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < (1 - ζ * Explicit.ePlus δ).re :=
  R2c.re_one_sub_pos (by rwa [norm_mul, R2c.norm_ePlus, mul_one])

theorem re_one_sub_eMinus_pos (δ : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < (1 - ζ * Explicit.eMinus δ).re :=
  R2c.re_one_sub_pos (by rwa [norm_mul, R2c.norm_eMinus, mul_one])

/-- The three bases of `Π` have positive real part: inside the disc, and at the regular points of the circle. -/
structure Good (δ : ℝ) (ζ : ℂ) : Prop where
  h1 : 0 < (1 + ζ).re
  h2 : 0 < (1 - ζ * Explicit.ePlus δ).re
  h3 : 0 < (1 - ζ * Explicit.eMinus δ).re

theorem good_of_norm_lt (δ : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) : Good δ ζ :=
  ⟨re_one_add_pos hζ, re_one_sub_ePlus_pos δ hζ, re_one_sub_eMinus_pos δ hζ⟩

theorem differentiableAt_Pi {δ : ℝ} {ζ : ℂ} (hg : Good δ ζ) : DifferentiableAt ℂ (Explicit.Pi δ) ζ := by
  have d1 : DifferentiableAt ℂ (fun ξ : ℂ => 1 + ξ) ζ := by fun_prop
  have d2 : DifferentiableAt ℂ (fun ξ : ℂ => 1 - ξ * Explicit.ePlus δ) ζ := by fun_prop
  have d3 : DifferentiableAt ℂ (fun ξ : ℂ => 1 - ξ * Explicit.eMinus δ) ζ := by fun_prop
  have c1 := d1.cpow (differentiableAt_const (-((Explicit.aC : ℝ) : ℂ) / 2))
    (Complex.mem_slitPlane_iff.2 (Or.inl hg.h1))
  have c2 := d2.cpow (differentiableAt_const (((Explicit.aA : ℝ) : ℂ) / 2))
    (Complex.mem_slitPlane_iff.2 (Or.inl hg.h2))
  have c3 := d3.cpow (differentiableAt_const (((Explicit.aB : ℝ) : ℂ) / 2))
    (Complex.mem_slitPlane_iff.2 (Or.inl hg.h3))
  have hne : (1 - ζ * Explicit.ePlus δ) ^ (((Explicit.aA : ℝ) : ℂ) / 2) *
      (1 - ζ * Explicit.eMinus δ) ^ (((Explicit.aB : ℝ) : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (fun h => ne_zero_of_re_pos hg.h2 ((Complex.cpow_eq_zero_iff _ _).1 h).1)
      (fun h => ne_zero_of_re_pos hg.h3 ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  exact c1.div (c2.mul c3) hne

theorem differentiableAt_Yf {δ : ℝ} {ζ : ℂ} (hg : Good δ ζ) : DifferentiableAt ℂ (Explicit.Yf δ) ζ := by
  have d2 : DifferentiableAt ℂ (fun ξ : ℂ => 1 - ξ * Explicit.ePlus δ) ζ := by fun_prop
  have d3 : DifferentiableAt ℂ (fun ξ : ℂ => 1 - ξ * Explicit.eMinus δ) ζ := by fun_prop
  have hq := (d3.div d2 (ne_zero_of_re_pos hg.h2)).clog (div_mem_slitPlane hg.h3 hg.h2)
  exact (differentiableAt_const _).mul ((differentiableAt_const _).add ((differentiableAt_const _).mul hq))

theorem differentiableAt_zf {δ : ℝ} {ζ : ℂ} (hg : Good δ ζ) : DifferentiableAt ℂ (Explicit.zf δ) ζ :=
  ((differentiableAt_const _).mul (differentiableAt_Pi hg)).mul ((differentiableAt_Yf hg).div_const 2).cexp

theorem differentiableAt_wf {δ : ℝ} {ζ : ℂ} (hg : Good δ ζ) : DifferentiableAt ℂ (Explicit.wf δ) ζ :=
  ((differentiableAt_id.mul_const _).mul (differentiableAt_Pi hg)).mul ((differentiableAt_Yf hg).neg.div_const 2).cexp

theorem differentiableOn_zf (δ : ℝ) : DifferentiableOn ℂ (Explicit.zf δ) (Metric.ball 0 1) := fun ζ hζ =>
  (differentiableAt_zf (good_of_norm_lt δ (by simpa using hζ))).differentiableWithinAt

theorem differentiableOn_wf (δ : ℝ) : DifferentiableOn ℂ (Explicit.wf δ) (Metric.ball 0 1) := fun ζ hζ =>
  (differentiableAt_wf (good_of_norm_lt δ (by simpa using hζ))).differentiableWithinAt

/-! ### C13b -/

/-- C13b, Prop. 8 (l.471-473): "we have `z, w ∈ H^p` for every `δ ∈ (0, 2π)`" (`p = 3/2`). -/
theorem C13b_proved : Paper.C13b_explicit_hardy := fun δ hδ0 hδ1 =>
  ⟨inHardy_of_le hδ0 hδ1 (differentiableOn_zf δ) fun θ _ hreg hr0 hr1 =>
      (norm_zw_radial_le hδ0 hδ1 (Complex.norm_exp_ofReal_mul_I θ) hreg hr0 hr1).1,
    inHardy_of_le hδ0 hδ1 (differentiableOn_wf δ) fun θ _ hreg hr0 hr1 =>
      (norm_zw_radial_le hδ0 hδ1 (Complex.norm_exp_ofReal_mul_I θ) hreg hr0 hr1).2⟩

end P18.HardyBound
