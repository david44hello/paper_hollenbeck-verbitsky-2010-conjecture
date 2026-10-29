/-
  HVFalse/Proofs/NewRows12b.lean - R5: μ = φ'' + q²φ ≥ 0 as a measure (Sec. 3 of the paper)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Sec. 3, "so μ := φ'' + q²φ ≥ 0 as a measure", i.e. ∫ φ (b'' + q²b) ≥ 0 over one period for every 2π-periodic C² test
  function b ≥ 0.
  (1) C23b (Relax.qsubtrig_discrete): φ(t+h) + φ(t-h) - 2cos(qh) φ(t) ≥ 0 for 0 < h, 2qh < π. Times b ≥ 0, integrated:
      J(h) := ∫ φ(t)(b(t+h) + b(t-h) - 2cos(qh) b(t)) dt ≥ 0 (the shifts move from φ to b: φ b is periodic).
  (2) |b(t+h) + b(t-h) - 2b(t) - h² b''(t)| ≤ 2ωh² with ω the oscillation of b'' on [t-h, t+h] (mean value theorem
      twice), and |2 - 2cos(qh) - q²h²| ≤ h⁴ (Real.cos_bound). So |J(h) - h² ∫ φ(b'' + q²b)| ≤ 2π M (2ω + B h²) h².
  (3) If ∫ φ(b'' + q²b) = -η < 0: uniform continuity of b'' on [-π-1, π+1] makes ω and B h² small, a contradiction.
-/
import HVFalse.Proofs.Relax
import HVFalse.Proofs.TrigCont

open Real Set Filter Topology MeasureTheory

namespace P18

namespace NewRows12b

/-- **Second differences**: `|b(t+h) + b(t-h) - 2b(t) - h² b''(t)| ≤ 2ωh²` when `|b''(t+s) - b''(t)| ≤ ω` for `|s| ≤ h`. -/
theorem second_diff_bound {b b1 b2 : ℝ → ℝ} (hb1 : ∀ x, HasDerivAt b (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    {t h ω : ℝ} (hh : 0 ≤ h) (hω : ∀ s ∈ Icc (-h) h, |b2 (t + s) - b2 t| ≤ ω) :
    |b (t + h) + b (t - h) - 2 * b t - h ^ 2 * b2 t| ≤ 2 * ω * h ^ 2 := by
  have hplus : ∀ s, HasDerivAt (fun s => t + s) 1 s := fun s => (hasDerivAt_id s).const_add t
  have hminus : ∀ s, HasDerivAt (fun s => t - s) (-1) s := fun s => (hasDerivAt_id s).const_sub t
  have hω0 : 0 ≤ ω := le_trans (abs_nonneg _) (hω 0 ⟨by linarith, hh⟩)
  -- `g₁(s) = b'(t+s) - b'(t-s) - 2s b''(t)`, with `g₁(0) = 0` and `|g₁'| ≤ 2ω` on `[0, h]`
  have hg1d : ∀ s, HasDerivAt (fun s => b1 (t + s) - b1 (t - s) - 2 * s * b2 t)
      (b2 (t + s) + b2 (t - s) - 2 * b2 t) s := by
    intro s
    have h1 : HasDerivAt (fun s => b1 (t + s)) (b2 (t + s) * 1) s := (hb2 (t + s)).comp s (hplus s)
    have h2 : HasDerivAt (fun s => b1 (t - s)) (b2 (t - s) * -1) s := (hb2 (t - s)).comp s (hminus s)
    have h3 : HasDerivAt (fun s => 2 * s * b2 t) (2 * 1 * b2 t) s :=
      ((hasDerivAt_id s).const_mul 2).mul_const (b2 t)
    exact ((h1.sub h2).sub h3).congr_deriv (by ring)
  have hbound1 : ∀ s ∈ Ico 0 h, ‖b2 (t + s) + b2 (t - s) - 2 * b2 t‖ ≤ 2 * ω := by
    intro s hs
    have e1 := hω s ⟨by linarith [hs.1], hs.2.le⟩
    have e2 := hω (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    rw [← sub_eq_add_neg] at e2
    rw [Real.norm_eq_abs]
    calc |b2 (t + s) + b2 (t - s) - 2 * b2 t| = |(b2 (t + s) - b2 t) + (b2 (t - s) - b2 t)| := by ring_nf
      _ ≤ |b2 (t + s) - b2 t| + |b2 (t - s) - b2 t| := abs_add_le _ _
      _ ≤ 2 * ω := by linarith
  have hg1b : ∀ s ∈ Icc 0 h, |b1 (t + s) - b1 (t - s) - 2 * s * b2 t| ≤ 2 * ω * s := by
    intro s hs
    have hm := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => b1 (t + s) - b1 (t - s) - 2 * s * b2 t) (fun s _ => (hg1d s).hasDerivWithinAt) hbound1 s hs
    beta_reduce at hm
    simpa using hm
  -- `g(s) = b(t+s) + b(t-s) - 2b(t) - s² b''(t)`, with `g(0) = 0` and `g' = g₁`
  have hgd : ∀ s, HasDerivAt (fun s => b (t + s) + b (t - s) - 2 * b t - s ^ 2 * b2 t)
      (b1 (t + s) - b1 (t - s) - 2 * s * b2 t) s := by
    intro s
    have h1 : HasDerivAt (fun s => b (t + s)) (b1 (t + s) * 1) s := (hb1 (t + s)).comp s (hplus s)
    have h2 : HasDerivAt (fun s => b (t - s)) (b1 (t - s) * -1) s := (hb1 (t - s)).comp s (hminus s)
    have h3 : HasDerivAt (fun s => s ^ 2 * b2 t) (2 * s * b2 t) s :=
      ((hasDerivAt_pow 2 s).mul_const (b2 t)).congr_deriv (by norm_num)
    exact (((h1.add h2).sub_const (2 * b t)).sub h3).congr_deriv (by ring)
  have hbound2 : ∀ s ∈ Ico 0 h, ‖b1 (t + s) - b1 (t - s) - 2 * s * b2 t‖ ≤ 2 * ω * h := fun s hs => by
    rw [Real.norm_eq_abs]
    exact (hg1b s ⟨hs.1, hs.2.le⟩).trans (mul_le_mul_of_nonneg_left hs.2.le (by positivity))
  have hm := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => b (t + s) + b (t - s) - 2 * b t - s ^ 2 * b2 t) (fun s _ => (hgd s).hasDerivWithinAt) hbound2 h
    (right_mem_Icc.mpr hh)
  beta_reduce at hm
  rw [show b (t + 0) + b (t - 0) - 2 * b t - (0 : ℝ) ^ 2 * b2 t = 0 by simp <;> ring, sub_zero, sub_zero,
    Real.norm_eq_abs] at hm
  calc |b (t + h) + b (t - h) - 2 * b t - h ^ 2 * b2 t| ≤ 2 * ω * h * h := hm
    _ = 2 * ω * h ^ 2 := by ring

/-- `∫_{-π}^{π} F(t) G(t + d) dt = ∫_{-π}^{π} F(t - d) G(t) dt` for `2π`-periodic continuous `F`, `G`. -/
theorem shift_integral {F G : ℝ → ℝ} (hF : Continuous F) (hG : Continuous G) (hFp : Function.Periodic F (2 * π))
    (hGp : Function.Periodic G (2 * π)) (d : ℝ) :
    ∫ t in (-π)..π, F t * G (t + d) = ∫ t in (-π)..π, F (t - d) * G t := by
  set K : ℝ → ℝ := fun u => F (u - d) * G u with hK
  have hKp : Function.Periodic K (2 * π) := fun u => by
    simp only [hK, show u + 2 * π - d = (u - d) + 2 * π by ring, hFp (u - d), hGp u]
  have h1 : ∫ t in (-π)..π, F t * G (t + d) = ∫ t in (-π)..π, K (t + d) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hK, add_sub_cancel_right]
  rw [h1, intervalIntegral.integral_comp_add_right K d,
    show π + d = (-π + d) + 2 * π by ring, hKp.intervalIntegral_add_eq (-π + d) (-π),
    show -π + 2 * π = π by ring]

/-- **R5**, Sec. 3: `μ := φ'' + q²φ ≥ 0` as a measure, i.e. `∫ φ (b'' + q²b) ≥ 0` over a period for every
`2π`-periodic `C²` test function `b ≥ 0`. -/
theorem mu_nonneg {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (b : ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (hper : Function.Periodic b (2 * π)) (hpos : ∀ t, 0 ≤ b t) :
    0 ≤ ∫ t in (-π)..π, φ t * (deriv (deriv b) t + q ^ 2 * b t) := by
  have hq : 0 < q := by linarith
  have hφc : Continuous φ := TrigCont.qsubtrig_continuous hq0 hq1 hφ
  have hφp := hφ.1
  -- derivatives of `b`
  have hc1 : ContDiff ℝ 1 (deriv b) := ContDiff.deriv' (n := 1) hb
  have hb1 : ∀ x, HasDerivAt b (deriv b x) x := fun x => ((hb.differentiable (by norm_num)) x).hasDerivAt
  have hb2 : ∀ x, HasDerivAt (deriv b) (deriv (deriv b) x) x :=
    fun x => ((hc1.differentiable (by norm_num)) x).hasDerivAt
  have hb2c : Continuous (deriv (deriv b)) := hc1.continuous_deriv le_rfl
  have hbc : Continuous b := hb.continuous
  set b2 := deriv (deriv b) with hb2def
  -- (1) the discrete inequality, integrated, with the shifts moved onto `b`
  have hJ : ∀ h : ℝ, 0 < h → 2 * q * h < π →
      0 ≤ ∫ t in (-π)..π, φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t) := by
    intro h hh h2
    have hc : ∀ d : ℝ, Continuous (fun t => φ t * b (t + d)) := fun d =>
      hφc.mul (hbc.comp (continuous_id.add continuous_const))
    have hs1 := shift_integral hφc hbc hφp hper h
    have hs2 := shift_integral hφc hbc hφp hper (-h)
    simp only [sub_neg_eq_add, ← sub_eq_add_neg] at hs2
    have c1 : Continuous (fun t => φ t * b (t + h)) := hc h
    have c2 : Continuous (fun t => φ t * b (t - h)) := hφc.mul (hbc.comp (continuous_id.sub continuous_const))
    have c12 : Continuous (fun t => φ t * b (t + h) + φ t * b (t - h)) := c1.add c2
    have c3 : Continuous (fun t => 2 * cos (q * h) * (φ t * b t)) := continuous_const.mul (hφc.mul hbc)
    have hsplit : ∫ t in (-π)..π, φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t)
        = (∫ t in (-π)..π, φ t * b (t + h)) + (∫ t in (-π)..π, φ t * b (t - h))
          - 2 * cos (q * h) * ∫ t in (-π)..π, φ t * b t := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (c1.intervalIntegrable _ _)
        (c2.intervalIntegrable _ _), ← intervalIntegral.integral_sub (c12.intervalIntegrable _ _) (c3.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    have hsplit2 : ∫ t in (-π)..π, b t * (φ (t + h) + φ (t - h) - 2 * cos (q * h) * φ t)
        = (∫ t in (-π)..π, φ (t - h) * b t) + (∫ t in (-π)..π, φ (t + h) * b t)
          - 2 * cos (q * h) * ∫ t in (-π)..π, φ t * b t := by
      have ca : Continuous (fun t => φ (t - h) * b t) := (hφc.comp (continuous_id.sub continuous_const)).mul hbc
      have cb : Continuous (fun t => φ (t + h) * b t) := (hφc.comp (continuous_id.add continuous_const)).mul hbc
      have cab : Continuous (fun t => φ (t - h) * b t + φ (t + h) * b t) := ca.add cb
      have cc : Continuous (fun t => 2 * cos (q * h) * (φ t * b t)) := continuous_const.mul (hφc.mul hbc)
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (ca.intervalIntegrable _ _)
        (cb.intervalIntegrable _ _), ← intervalIntegral.integral_sub (cab.intervalIntegrable _ _)
          (cc.intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    have hnn : 0 ≤ ∫ t in (-π)..π, b t * (φ (t + h) + φ (t - h) - 2 * cos (q * h) * φ t) := by
      refine intervalIntegral.integral_nonneg (by linarith [pi_pos]) fun t _ => mul_nonneg (hpos t) ?_
      have := Relax.qsubtrig_discrete hq0 hq1 hh h2 hφ t
      linarith
    rw [hsplit, hs1, hs2]
    rw [hsplit2] at hnn
    linarith
  -- (2)-(3) the ε-argument
  by_contra hneg
  push Not at hneg
  set I := ∫ t in (-π)..π, φ t * (b2 t + q ^ 2 * b t) with hI
  set η := -I with hη
  have hη0 : 0 < η := by linarith
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hφc.continuousOn
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hbc.continuousOn
  set M := max M0 0 with hM
  set B := max B0 0 with hB
  set ε := η / (4 * π * (M + 1)) with hεdef
  have hε : 0 < ε := div_pos hη0 (by positivity)
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := -π - 1) (b := π + 1)).uniformContinuousOn_of_continuous hb2c.continuousOn) (ε / 2)
    (by positivity)
  set h := min (min (δ / 2) 1) (ε / (B + 1)) with hhdef
  have hh0 : 0 < h := lt_min (lt_min (by positivity) one_pos) (div_pos hε (by positivity))
  have hh1 : h ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hhδ : h < δ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hhB : B * h ≤ ε := by
    have : h ≤ ε / (B + 1) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith [le_max_right B0 0]
  have h2 : 2 * q * h < π := by nlinarith [pi_gt_three]
  -- pointwise bound on `[-π, π]`
  have hE : ∀ t ∈ Icc (-π) π, |b (t + h) + b (t - h) - 2 * cos (q * h) * b t - h ^ 2 * (b2 t + q ^ 2 * b t)|
      ≤ 2 * ε * h ^ 2 := by
    intro t ht
    have hosc : ∀ s ∈ Icc (-h) h, |b2 (t + s) - b2 t| ≤ ε / 2 := by
      intro s hs
      have hts : t + s ∈ Icc (-π - 1) (π + 1) := ⟨by linarith [ht.1, hs.1], by linarith [ht.2, hs.2]⟩
      have htK : t ∈ Icc (-π - 1) (π + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hd : dist (t + s) t < δ := by
        rw [Real.dist_eq, add_sub_cancel_left]; exact lt_of_le_of_lt (abs_le.mpr ⟨hs.1, hs.2⟩) hhδ
      have := hunif (t + s) hts t htK hd
      rw [Real.dist_eq] at this
      exact this.le
    have hsd := second_diff_bound hb1 hb2 hh0.le hosc
    have hx : |q * h| ≤ 1 := by rw [abs_of_pos (by positivity)]; nlinarith
    have hcos := Real.cos_bound hx
    have hcos' : |2 - 2 * cos (q * h) - q ^ 2 * h ^ 2| ≤ h ^ 4 := by
      have hq4 : |q * h| ^ 4 ≤ h ^ 4 := by
        rw [abs_of_pos (by positivity)]
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) 4
      calc |2 - 2 * cos (q * h) - q ^ 2 * h ^ 2| = 2 * |cos (q * h) - (1 - (q * h) ^ 2 / 2)| := by
            rw [← abs_two, ← abs_mul, ← abs_neg]; congr 1; ring
        _ ≤ 2 * (|q * h| ^ 4 * (5 / 96)) := by linarith
        _ ≤ h ^ 4 := by nlinarith
    have hbt : |b t| ≤ B := by
      have := hB0 t ht; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    have hsplitE : b (t + h) + b (t - h) - 2 * cos (q * h) * b t - h ^ 2 * (b2 t + q ^ 2 * b t)
        = (b (t + h) + b (t - h) - 2 * b t - h ^ 2 * b2 t) + b t * (2 - 2 * cos (q * h) - q ^ 2 * h ^ 2) := by ring
    rw [hsplitE]
    calc _ ≤ |b (t + h) + b (t - h) - 2 * b t - h ^ 2 * b2 t| + |b t * (2 - 2 * cos (q * h) - q ^ 2 * h ^ 2)| :=
          abs_add_le _ _
      _ ≤ 2 * (ε / 2) * h ^ 2 + B * h ^ 4 := by
          rw [abs_mul]
          exact add_le_add hsd (mul_le_mul hbt hcos' (abs_nonneg _) (le_max_right _ _))
      _ ≤ 2 * ε * h ^ 2 := by
          have hB0' : 0 ≤ B := le_max_right _ _
          have e1 : B * h ^ 4 = (B * h) * (h * h ^ 2) := by ring
          have e2 : (B * h) * (h * h ^ 2) ≤ ε * (1 * h ^ 2) :=
            mul_le_mul hhB (mul_le_mul_of_nonneg_right hh1 (by positivity)) (by positivity) hε.le
          have e3 : ε * (1 * h ^ 2) = ε * h ^ 2 := by ring
          linarith
  -- `J(h) - h² I` is small
  have hdiff : |(∫ t in (-π)..π, φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t)) - h ^ 2 * I|
      ≤ M * (2 * ε * h ^ 2) * |π - -π| := by
    have cJ : Continuous (fun t => φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t)) :=
      hφc.mul (((hbc.comp (continuous_id.add continuous_const)).add (hbc.comp (continuous_id.sub continuous_const))).sub
        (continuous_const.mul hbc))
    have cI : Continuous (fun t => h ^ 2 * (φ t * (b2 t + q ^ 2 * b t))) :=
      continuous_const.mul (hφc.mul (hb2c.add (continuous_const.mul hbc)))
    rw [hI, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (cJ.intervalIntegrable _ _)
      (cI.intervalIntegrable _ _)]
    rw [← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    have htI : t ∈ Icc (-π) π := by
      rw [uIoc_of_le (by linarith [pi_pos])] at ht; exact ⟨ht.1.le, ht.2⟩
    have hφt : |φ t| ≤ M := by
      have := hM0 t htI; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
    have key : |φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t) - h ^ 2 * (φ t * (b2 t + q ^ 2 * b t))|
        ≤ M * (2 * ε * h ^ 2) := by
      rw [show φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t) - h ^ 2 * (φ t * (b2 t + q ^ 2 * b t))
        = φ t * (b (t + h) + b (t - h) - 2 * cos (q * h) * b t - h ^ 2 * (b2 t + q ^ 2 * b t)) by ring, abs_mul]
      exact mul_le_mul hφt (hE t htI) (abs_nonneg _) (le_max_right _ _)
    rw [Real.norm_eq_abs]
    exact key
  have hJh := hJ h hh0 h2
  have h2pi : |π - -π| = 2 * π := by rw [abs_of_pos (by linarith [pi_pos])]; ring
  rw [h2pi] at hdiff
  have hkey : M * (2 * ε * h ^ 2) * (2 * π) < η * h ^ 2 := by
    have hM0' : 0 ≤ M := le_max_right _ _
    have hh2 : 0 < h ^ 2 := by positivity
    have hden : 0 < 4 * π * (M + 1) := by positivity
    have hεη : ε * (4 * π * (M + 1)) = η := by rw [hεdef]; exact div_mul_cancel₀ η hden.ne'
    have hlt : M * (2 * ε) * (2 * π) < η := by nlinarith [mul_pos pi_pos hε, hεη]
    calc M * (2 * ε * h ^ 2) * (2 * π) = (M * (2 * ε) * (2 * π)) * h ^ 2 := by ring
      _ < η * h ^ 2 := mul_lt_mul_of_pos_right hlt hh2
  have hup := (abs_le.mp hdiff).2
  have e : η * h ^ 2 = -(h ^ 2 * I) := by rw [hη]; ring
  linarith

end NewRows12b

end P18
