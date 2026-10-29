/-
  HVFalse/Proofs/R2d.lean - the converse of C06a - a continuous 2π-periodic
  q-trigonometrically convex function is q-subtrigonometric (Levin's description, Sec. 3)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Proofs.VComp
import HVFalse.Proofs.LocGlob

open Real MeasureTheory

namespace P18.R2d

/-- A continuous `2π`-periodic q-trigonometrically convex `φ` has `∫₀^{2π} φ ≥ 0`: integrate
`φ(t) sin(2qh) ≤ (φ(t-h) + φ(t+h)) sin(qh)` over a period. -/
theorem integral_nonneg_of_trigConvex {q : ℝ} (hq0 : 0 < q) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ) : 0 ≤ ∫ x in (0 : ℝ)..(2 * π), φ x := by
  set h : ℝ := π / (4 * q) with hh
  have hh0 : 0 < h := by positivity
  have hqh : q * h = π / 4 := by
    rw [hh]
    field_simp
  have hs1 : 0 < Real.sin (q * h) := by
    rw [hqh]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  have hc1 : Real.cos (q * h) < 1 := by
    nlinarith [Real.cos_sq_add_sin_sq (q * h), Real.cos_le_one (q * h), mul_pos hs1 hs1]
  have hpt : ∀ t, φ t * Real.sin (q * (2 * h)) ≤ (φ (t - h) + φ (t + h)) * Real.sin (q * h) := by
    intro t
    have := htc (t - h) t (t + h) (by linarith) (by linarith)
      (by rw [show t + h - (t - h) = 2 * h by ring, show q * (2 * h) = 2 * (q * h) by ring, hqh]; linarith [pi_pos])
    rw [show t + h - (t - h) = 2 * h by ring, show t + h - t = h by ring, show t - (t - h) = h by ring] at this
    linarith
  have hs2 : Real.sin (q * (2 * h)) = 2 * Real.sin (q * h) * Real.cos (q * h) := by
    rw [show q * (2 * h) = 2 * (q * h) by ring, Real.sin_two_mul]
  have hcm : Continuous fun t => φ (t - h) := hc.comp (continuous_id.sub continuous_const)
  have hcp : Continuous fun t => φ (t + h) := hc.comp (continuous_id.add continuous_const)
  have hmono : ∫ t in (0 : ℝ)..(2 * π), φ t * Real.sin (q * (2 * h))
      ≤ ∫ t in (0 : ℝ)..(2 * π), (φ (t - h) + φ (t + h)) * Real.sin (q * h) :=
    intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * π)
    ((hc.mul continuous_const).intervalIntegrable _ _) (((hcm.add hcp).mul continuous_const).intervalIntegrable _ _)
    (fun t _ => hpt t)
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),
    intervalIntegral.integral_comp_sub_right, intervalIntegral.integral_comp_add_right,
    show (2 * π - h) = (0 - h) + 2 * π by ring, hper.intervalIntegral_add_eq (0 - h) 0,
    show (2 * π + h) = (0 + h) + 2 * π by ring, hper.intervalIntegral_add_eq (0 + h) 0, zero_add] at hmono
  have key : 0 ≤ (∫ x in (0 : ℝ)..(2 * π), φ x) * (2 * Real.sin (q * h) * (1 - Real.cos (q * h))) := by
    rw [hs2] at hmono
    nlinarith [hmono]
  exact (mul_nonneg_iff_of_pos_right (by nlinarith)).1 key

/-- Sec. 3 (l.226-228): "the q-subtrigonometric functions are therefore the 2π-periodic
q-trigonometrically convex functions of Levin's theory" - the converse direction of C06a, for continuous `φ`
(and every `0 < q ≤ 1`). Local sub-mean property of `|ζ|^q φ(arg ζ)`: off `0` from a supporting sinusoid
(`VComp.local_ne_V`); at `0` the circle average is `r^q` times the mean of `φ`, which is `≥ 0`; then the local-to-global
step `LocGlob.locGlob`. -/
theorem C06f_trigConvex_qsubtrig {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ) : QSubtrig q φ := by
  refine ⟨hper, ?_⟩
  have hmean := integral_nonneg_of_trigConvex hq0 hc hper htc
  have hEφ : ∀ x, VComp.Ecirc q φ x = φ x := fun x => by
    simp only [VComp.Ecirc, VComp.Vfun, Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul]
    rw [Complex.arg_exp_mul_I, toIocMod, hper.sub_zsmul_eq]
  apply LocGlob.locGlob (VComp.Vfun q φ) (VComp.Vfun_continuous hq0 hc hper)
  intro a
  by_cases ha : a = 0
  · subst ha
    refine ⟨1, one_pos, fun r hr _ => ?_⟩
    rw [VComp.Vfun_zero hq0, circleAverage_def, smul_eq_mul]
    have hpt : ∀ θ : ℝ, VComp.Vfun q φ (circleMap 0 r θ) = r ^ q * φ θ := fun θ => by
      rw [circleMap_zero, VComp.Vfun_homog r hr, ← hEφ θ]
      rfl
    simp only [hpt]
    rw [intervalIntegral.integral_const_mul]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hmean)
  · exact VComp.local_ne_V hq0 hq1 hc hper htc (h := id) differentiable_id ha

end P18.R2d
