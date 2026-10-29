/-
  HVFalse/Proofs/R2e.lean - `|zw|^q` is integrable on each of the three arcs,
  and the integral identity `∫ G = Σ_j Γ_j ∫_{arc_j} |zw|^q` (Prop. 8 proof, l.449-452)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Proofs.Prop8Steps
import HVFalse.Proofs.SmallB
import HVFalse.Proofs.R2b

open Real MeasureTheory Set
open scoped Interval

namespace P18.R2e

/-- One factor `|2 sin((θ - c)/2)|^(-a)` of `|zw|^q` (C13q). -/
noncomputable def fac (c a θ : ℝ) : ℝ := |2 * Real.sin ((θ - c) / 2)| ^ (-a)

/-- The right side of C13q with exponents `x, y, z` at `θ_k = -δ/2, δ/2, π`. -/
noncomputable def P (δ x y z θ : ℝ) : ℝ := fac (-(δ / 2)) x θ * fac (δ / 2) y θ * fac π z θ

theorem fac_measurable (c a : ℝ) : Measurable (fac c a) :=
  (by fun_prop : Continuous fun θ : ℝ => |2 * Real.sin ((θ - c) / 2)|).measurable.pow_const (-a)

theorem fac_continuousOn {c a : ℝ} {s : Set ℝ} (hs : ∀ θ ∈ s, Real.sin ((θ - c) / 2) ≠ 0) :
    ContinuousOn (fac c a) s :=
  (by fun_prop : Continuous fun θ : ℝ => |2 * Real.sin ((θ - c) / 2)|).continuousOn.rpow_const
    fun θ hθ => Or.inl (abs_ne_zero.2 (mul_ne_zero two_ne_zero (hs θ hθ)))

theorem sin_ne_of_neg {u : ℝ} (h1 : -π < u) (h2 : u < 0) : Real.sin u ≠ 0 :=
  (Real.sin_neg_of_neg_of_neg_pi_lt h2 h1).ne

theorem sin_ne_of_pos {u : ℝ} (h1 : 0 < u) (h2 : u < π) : Real.sin u ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi h1 h2).ne'

/-- `|2 sin(u/2)| ≥ (2/π) u` on `[0, π]` (Jordan). -/
theorem jordan {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ π) : 2 / π * u ≤ |2 * Real.sin (u / 2)| := by
  have h := Real.mul_le_sin (x := u / 2) (by linarith) (by linarith)
  calc 2 / π * u = 2 * (2 / π * (u / 2)) := by ring
    _ ≤ 2 * Real.sin (u / 2) := by linarith
    _ ≤ |2 * Real.sin (u / 2)| := le_abs_self _

theorem fac_le {a u : ℝ} (ha0 : 0 ≤ a) (hu0 : 0 < u) (hu : u ≤ π) :
    |2 * Real.sin (u / 2)| ^ (-a) ≤ (2 / π) ^ (-a) * u ^ (-a) := by
  rw [← Real.mul_rpow (by positivity) hu0.le]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) (jordan hu0.le hu) (by linarith)

theorem abs_two_sin_swap (x c : ℝ) : |2 * Real.sin ((x - c) / 2)| = |2 * Real.sin ((c - x) / 2)| := by
  rw [show (x - c) / 2 = -((c - x) / 2) by ring, Real.sin_neg, mul_neg, abs_neg]

theorem fac_pi (z : ℝ) : fac π z = fac (-π) z := funext fun θ => by
  unfold fac
  rw [show (θ - π) / 2 = (θ - -π) / 2 - π by ring, Real.sin_sub_pi, mul_neg, abs_neg]

/-- A singularity at the left end `c`: `fac c a` is integrable on `[c, c + L]`, `L ≤ π`, `0 ≤ a < 1`. -/
theorem fac_right {c a L : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hL0 : 0 < L) (hL : L ≤ π) :
    IntervalIntegrable (fac c a) volume c (c + L) := by
  have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (by linarith : -1 < -a)).comp_sub_right c
  rw [zero_add, add_comm L c] at h1
  refine (h1.const_mul ((2 / π) ^ (-a))).mono_fun (fac_measurable c a).aestronglyMeasurable ?_
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
  have hu : 0 < x - c := by linarith [hx.1]
  show ‖|2 * Real.sin ((x - c) / 2)| ^ (-a)‖ ≤ ‖(2 / π) ^ (-a) * (x - c) ^ (-a)‖
  rw [Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _),
    Real.norm_of_nonneg (mul_nonneg (rpow_nonneg (by positivity) _) (rpow_nonneg hu.le _))]
  exact fac_le ha0 hu (by linarith [hx.2])

/-- A singularity at the right end `c`: `fac c a` is integrable on `[c - L, c]`, `L ≤ π`, `0 ≤ a < 1`. -/
theorem fac_left {c a L : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hL0 : 0 < L) (hL : L ≤ π) :
    IntervalIntegrable (fac c a) volume (c - L) c := by
  have h1 := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := L) (by linarith : -1 < -a)).comp_sub_left c
  rw [sub_zero] at h1
  refine (h1.symm.const_mul ((2 / π) ^ (-a))).mono_fun (fac_measurable c a).aestronglyMeasurable ?_
  rw [uIoc_of_le (by linarith), ← restrict_Ioo_eq_restrict_Ioc]
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun x hx => ?_
  have hu : 0 < c - x := by linarith [hx.2]
  show ‖|2 * Real.sin ((x - c) / 2)| ^ (-a)‖ ≤ ‖(2 / π) ^ (-a) * (c - x) ^ (-a)‖
  rw [abs_two_sin_swap, Real.norm_of_nonneg (rpow_nonneg (abs_nonneg _) _),
    Real.norm_of_nonneg (mul_nonneg (rpow_nonneg (by positivity) _) (rpow_nonneg hu.le _))]
  exact fac_le ha0 hu (by linarith [hx.1])

/-- The product of the three factors is integrable on each arc, for `0 < δ ≤ 1` and exponents in `[0, 1)`: split each
arc at `-1`, `0`, `1`, so that each piece has one singular factor at an end and two continuous factors. -/
theorem P_arcs {δ x y z : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hx0 : 0 ≤ x) (hx1 : x < 1) (hy0 : 0 ≤ y) (hy1 : y < 1)
    (hz0 : 0 ≤ z) (hz1 : z < 1) :
    IntervalIntegrable (P δ x y z) volume (-π) (-(δ / 2)) ∧ IntervalIntegrable (P δ x y z) volume (-(δ / 2)) (δ / 2) ∧
      IntervalIntegrable (P δ x y z) volume (δ / 2) π := by
  have hpi := pi_gt_three
  have eA : P δ x y z = fun θ => fac (-(δ / 2)) x θ * (fac (δ / 2) y θ * fac π z θ) :=
    funext fun θ => by unfold P; ring
  have eB : P δ x y z = fun θ => fac (δ / 2) y θ * (fac (-(δ / 2)) x θ * fac π z θ) :=
    funext fun θ => by unfold P; ring
  have p1 : IntervalIntegrable (P δ x y z) volume (-π) (-1) := by
    have hs := fac_right (c := -π) hz0 hz1 (by linarith : (0 : ℝ) < π - 1) (by linarith : π - 1 ≤ π)
    rw [show -π + (π - 1) = -1 by ring, ← fac_pi] at hs
    have hc : ContinuousOn (fun θ => fac (-(δ / 2)) x θ * fac (δ / 2) y θ) [[-π, -1]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    exact hs.continuousOn_mul hc
  have p2 : IntervalIntegrable (P δ x y z) volume (-1) (-(δ / 2)) := by
    have hs := fac_left (c := -(δ / 2)) hx0 hx1 (by linarith : (0 : ℝ) < 1 - δ / 2) (by linarith : 1 - δ / 2 ≤ π)
    rw [show -(δ / 2) - (1 - δ / 2) = -1 by ring] at hs
    have hc : ContinuousOn (fun θ => fac (δ / 2) y θ * fac π z θ) [[-1, -(δ / 2)]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := π) (a := z) fun θ hθ => sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eA]
    exact hs.mul_continuousOn hc
  have p3 : IntervalIntegrable (P δ x y z) volume (-(δ / 2)) 0 := by
    have hs := fac_right (c := -(δ / 2)) hx0 hx1 (by linarith : (0 : ℝ) < δ / 2) (by linarith : δ / 2 ≤ π)
    rw [show -(δ / 2) + δ / 2 = 0 by ring] at hs
    have hc : ContinuousOn (fun θ => fac (δ / 2) y θ * fac π z θ) [[-(δ / 2), 0]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => sin_ne_of_neg (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := π) (a := z) fun θ hθ => sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eA]
    exact hs.mul_continuousOn hc
  have p4 : IntervalIntegrable (P δ x y z) volume 0 (δ / 2) := by
    have hs := fac_left (c := δ / 2) hy0 hy1 (by linarith : (0 : ℝ) < δ / 2) (by linarith : δ / 2 ≤ π)
    rw [show δ / 2 - δ / 2 = 0 by ring] at hs
    have hc : ContinuousOn (fun θ => fac (-(δ / 2)) x θ * fac π z θ) [[0, δ / 2]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := π) (a := z) fun θ hθ => sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eB]
    exact hs.mul_continuousOn hc
  have p5 : IntervalIntegrable (P δ x y z) volume (δ / 2) 1 := by
    have hs := fac_right (c := δ / 2) hy0 hy1 (by linarith : (0 : ℝ) < 1 - δ / 2) (by linarith : 1 - δ / 2 ≤ π)
    rw [show δ / 2 + (1 - δ / 2) = 1 by ring] at hs
    have hc : ContinuousOn (fun θ => fac (-(δ / 2)) x θ * fac π z θ) [[δ / 2, 1]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := π) (a := z) fun θ hθ => sin_ne_of_neg
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    rw [eB]
    exact hs.mul_continuousOn hc
  have p6 : IntervalIntegrable (P δ x y z) volume 1 π := by
    have hs := fac_left (c := π) hz0 hz1 (by linarith : (0 : ℝ) < π - 1) (by linarith : π - 1 ≤ π)
    rw [show π - (π - 1) = 1 by ring] at hs
    have hc : ContinuousOn (fun θ => fac (-(δ / 2)) x θ * fac (δ / 2) y θ) [[1, π]] := by
      rw [uIcc_of_le (by linarith)]
      exact (fac_continuousOn (c := -(δ / 2)) (a := x) fun θ hθ => sin_ne_of_pos (by linarith [hθ.1])
        (by linarith [hθ.2])).mul (fac_continuousOn (c := δ / 2) (a := y) fun θ hθ => sin_ne_of_pos
          (by linarith [hθ.1]) (by linarith [hθ.2]))
    exact hs.continuousOn_mul hc
  exact ⟨p1.trans p2, p3.trans p4, p5.trans p6⟩

/-- Prop. 8 proof (l.451-452): `|zw|^q` (`q = 3/4`, the explicit pair at `δ = e^{-2500}`) is
interval integrable on each of the three arcs `(-π, -δ/2)`, `(-δ/2, δ/2)`, `(δ/2, π)` ("integrable power singularities"):
by C13q it equals `Π_k |2 sin((θ - θ_k)/2)|^(-qα_k)` off the two points `±δ/2`, with `0 < qα_k < 1` (C13f). -/
theorem C13v_arc_integrable :
    let δ := Real.exp (-2500)
    let F := fun θ : ℝ => ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) *
      Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 4 : ℝ)
    IntervalIntegrable F volume (-π) (-(δ / 2)) ∧ IntervalIntegrable F volume (-(δ / 2)) (δ / 2) ∧
      IntervalIntegrable F volume (δ / 2) π := by
  intro δ F
  have hδ0 : 0 < δ := Real.exp_pos _
  have hδ1 : δ ≤ 1 := by
    have h := Real.exp_le_exp.2 (show (-2500 : ℝ) ≤ 0 by norm_num)
    rwa [Real.exp_zero] at h
  have hpi := pi_gt_three
  obtain ⟨hA, hB, hC⟩ := explicit_exponents
  obtain ⟨a1, a2, a3⟩ := P_arcs hδ0 hδ1 (by linarith [R2b.aA_pos]) hA (by linarith [R2b.aB_pos]) hB
    (by linarith [R2b.aC_pos]) hC
  have hEq : ∀ θ ∈ Ioo (-π) π, θ ≠ -(δ / 2) → θ ≠ δ / 2 →
      P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC) θ = F θ := by
    intro θ hθ h1 h2
    show _ = ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) *
      Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 4 : ℝ)
    rw [Prop8Steps.arc_modulus θ hθ h1 h2]
    simp only [P, fac, sub_neg_eq_add, neg_mul]
    rfl
  refine ⟨a1.congr_uIoo fun θ hθ => ?_, a2.congr_uIoo fun θ hθ => ?_, a3.congr_uIoo fun θ hθ => ?_⟩
  · rw [uIoo_of_le (by linarith)] at hθ
    exact hEq θ ⟨hθ.1, by linarith [hθ.2]⟩ hθ.2.ne (by linarith [hθ.2] : θ < δ / 2).ne
  · rw [uIoo_of_le (by linarith)] at hθ
    exact hEq θ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩ hθ.1.ne' hθ.2.ne
  · rw [uIoo_of_le (by linarith)] at hθ
    exact hEq θ ⟨by linarith [hθ.1], hθ.2⟩ (by linarith [hθ.1] : -(δ / 2) < θ).ne' hθ.1.ne'

/-- The integral identity (l.449-450): "the integral is `Σ_j Γ(y_j,t_j) ∫_{arc_j} |zw|^q`",
over `T` as `(-π, π)` (the common factor `1/2π` is dropped on both sides): C13p on the open arcs, `C13v_arc_integrable`. -/
theorem C13w_arc_integral :
    let δ := Real.exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    ∫ θ in (-π)..π, G (3 / 2) (398 / 100) (Z θ) (W θ) =
      Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) * (∫ θ in (-π)..(-(δ / 2)), ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) +
      Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS * (∫ θ in (-(δ / 2))..(δ / 2), ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) +
      Gam (3 / 2) (398 / 100) 0 Explicit.bA * (∫ θ in (δ / 2)..π, ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) := by
  intro δ Z W
  have hδ0 : 0 < δ := Real.exp_pos _
  have hpi := pi_gt_three
  have hδ1 : δ ≤ 1 := by
    have h := Real.exp_le_exp.2 (show (-2500 : ℝ) ≤ 0 by norm_num)
    rwa [Real.exp_zero] at h
  obtain ⟨i1, i2, i3⟩ : IntervalIntegrable (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) volume (-π) (-(δ / 2)) ∧
      IntervalIntegrable (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) volume (-(δ / 2)) (δ / 2) ∧
      IntervalIntegrable (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) volume (δ / 2) π := C13v_arc_integrable
  obtain ⟨g1, g2, g3⟩ := Prop8Steps.arc_integrand
  have e1 : EqOn (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)))
      (fun θ => G (3 / 2) (398 / 100) (Z θ) (W θ)) (uIoo (-π) (-(δ / 2))) := fun θ hθ => by
    rw [uIoo_of_le (by linarith)] at hθ
    exact (g1 θ hθ).symm
  have e2 : EqOn (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS)
      (fun θ => G (3 / 2) (398 / 100) (Z θ) (W θ)) (uIoo (-(δ / 2)) (δ / 2)) := fun θ hθ => by
    rw [uIoo_of_le (by linarith)] at hθ
    exact (g2 θ hθ).symm
  have e3 : EqOn (fun θ => ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 Explicit.bA)
      (fun θ => G (3 / 2) (398 / 100) (Z θ) (W θ)) (uIoo (δ / 2) π) := fun θ hθ => by
    rw [uIoo_of_le (by linarith)] at hθ
    exact (g3 θ hθ).symm
  have j1 := (i1.mul_const (Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)))).congr_uIoo e1
  have j2 := (i2.mul_const (Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS)).congr_uIoo e2
  have j3 := (i3.mul_const (Gam (3 / 2) (398 / 100) 0 Explicit.bA)).congr_uIoo e3
  rw [← intervalIntegral.integral_add_adjacent_intervals (j1.trans j2) j3,
    ← intervalIntegral.integral_add_adjacent_intervals j1 j2,
    ← intervalIntegral.integral_congr_uIoo e1, ← intervalIntegral.integral_congr_uIoo e2,
    ← intervalIntegral.integral_congr_uIoo e3, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  ring

end P18.R2e
