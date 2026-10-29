/-
  HVFalse/Proofs/Minorant.lean - the minorant E of the paper: E = tan ϑ Re (zw)^q, and E ≤ G
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  C16c route. On {zw ≠ 0}: G = |zw|^q Γ(y, arg zw) (lift_pointwise) and E = |zw|^q e(arg zw), arg ∈ (-π, π], so (eq:two)
  gives E ≤ G. On {zw = 0}: E = 0, and G(z,w) = lim_{ε→0⁺} G(z+ε, w+ε) ≥ lim -|tan ϑ| |(z+ε)(w+ε)|^q = 0.
  (G(z,0) ≥ 0 is not automatic: it is (2cos ϑ)^{-p} ≥ 2^{-p/s}; here it comes from (eq:two) through the limit.)
-/
import HVFalse.Defs.HV
import HVFalse.Proofs.Bridges

open Real Filter Topology

namespace P18

/-- C16b, l.180-181: `E = tan ϑ · Re (zw)^q` (principal power). -/
theorem Efun_eq_re {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    Efun p z w = tan (π / (2 * p)) * ((z * w) ^ ((p / 2 : ℝ) : ℂ)).re := by
  have hq : (p / 2 : ℝ) ≠ 0 := by
    have : 0 < p := by linarith
    positivity
  unfold Efun ee
  by_cases h : z * w = 0
  · rw [h, norm_zero, zero_rpow hq, Complex.zero_cpow (by exact_mod_cast hq), Complex.zero_re]
    ring
  · rw [Complex.cpow_def_of_ne_zero h, Complex.exp_re, Complex.re_mul_ofReal, Complex.im_mul_ofReal,
      Complex.log_re, Complex.log_im, mul_comm (Complex.arg (z * w)), ← rpow_def_of_pos (norm_pos_iff.mpr h)]
    ring

/-- `E ≥ -|tan ϑ| |zw|^q`. -/
theorem Efun_ge_neg (p : ℝ) (z w : ℂ) : -(|tan (π / (2 * p))| * ‖z * w‖ ^ (p / 2)) ≤ Efun p z w := by
  unfold Efun ee
  have h1 : |tan (π / (2 * p)) * cos (p / 2 * Complex.arg (z * w))| ≤ |tan (π / (2 * p))| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)
  have h2 : 0 ≤ ‖z * w‖ ^ (p / 2) := by positivity
  have h3 := mul_le_mul_of_nonneg_left (abs_le.mp h1).1 h2
  linarith

/-- `E ≤ G` on `{z ≠ 0, w ≠ 0}`, from (eq:two). -/
theorem Efun_le_G_of_ne {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (h2 : TwoVar p s)
    {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) : Efun p z w ≤ G p s z w := by
  unfold G
  rw [lift_pointwise p s hp1 hp2 hs z w hz hw]
  unfold Efun
  exact mul_le_mul_of_nonneg_left (h2 _ _ ⟨(Complex.neg_pi_lt_arg _).le, Complex.arg_le_pi _⟩) (by positivity)

theorem continuous_G (p s : ℝ) (hp : 0 < p) (hs : 0 < s) : Continuous fun x : ℂ × ℂ => G p s x.1 x.2 := by
  unfold G
  apply Continuous.sub
  · exact continuous_const.mul
      ((continuous_fst.add (Complex.continuous_conj.comp continuous_snd)).norm.rpow_const fun _ => Or.inr hp.le)
  · exact (((continuous_fst.norm.rpow_const fun _ => Or.inr hs.le).add
      (continuous_snd.norm.rpow_const fun _ => Or.inr hs.le)).div_const 2).rpow_const
      fun _ => Or.inr (div_nonneg hp.le hs.le)

/-- `z + ε ≠ 0` for all small `ε > 0`. -/
theorem exists_add_ofReal_ne_zero (z : ℂ) : ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → z + ε ≠ 0 := by
  by_cases hz : z = 0
  · exact ⟨1, one_pos, fun ε hε _ => by rw [hz, zero_add]; exact_mod_cast hε.ne'⟩
  · refine ⟨‖z‖, norm_pos_iff.mpr hz, fun ε hε hεz h => ?_⟩
    have hzε : z = -(ε : ℂ) := eq_neg_of_add_eq_zero_left h
    rw [hzε, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hεz
    exact lt_irrefl _ hεz

/-- C16c, l.191: (eq:two) gives `E ≤ G` everywhere. -/
theorem Efun_le_G {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (h2 : TwoVar p s) (z w : ℂ) :
    Efun p z w ≤ G p s z w := by
  have hp : 0 < p := by linarith
  by_cases h : z ≠ 0 ∧ w ≠ 0
  · exact Efun_le_G_of_ne hp1 hp2 hs h2 h.1 h.2
  have hzw : z * w = 0 := by
    rw [not_and_or, not_not, not_not] at h
    rcases h with h | h <;> simp [h]
  have hE : Efun p z w = 0 := by
    unfold Efun
    rw [hzw, norm_zero, zero_rpow (by positivity)]
    ring
  rw [hE]
  obtain ⟨δz, hδz, hz⟩ := exists_add_ofReal_ne_zero z
  obtain ⟨δw, hδw, hw⟩ := exists_add_ofReal_ne_zero w
  have hpath : Continuous fun ε : ℝ => ((z + ε, w + ε) : ℂ × ℂ) :=
    (continuous_const.add Complex.continuous_ofReal).prodMk (continuous_const.add Complex.continuous_ofReal)
  have hF : Tendsto (fun ε : ℝ => G p s (z + ε) (w + ε)) (𝓝[>] 0) (𝓝 (G p s z w)) := by
    have := ((continuous_G p s hp hs).comp hpath).tendsto 0
    simp only [Function.comp_def, Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun ε : ℝ => -(|tan (π / (2 * p))| * ‖(z + ε) * (w + ε)‖ ^ (p / 2))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun ε : ℝ => -(|tan (π / (2 * p))| * ‖(z + ε) * (w + ε)‖ ^ (p / 2)) :=
      (continuous_const.mul (((continuous_const.add Complex.continuous_ofReal).mul
        (continuous_const.add Complex.continuous_ofReal)).norm.rpow_const fun _ => Or.inr (by positivity))).neg
    have := hc.tendsto 0
    simp only [Complex.ofReal_zero, add_zero, hzw, norm_zero, zero_rpow (by positivity : (p / 2 : ℝ) ≠ 0),
      mul_zero, neg_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hg hF ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδz hδw)] with ε hε
  exact (Efun_ge_neg p (z + ε) (w + ε)).trans (Efun_le_G_of_ne hp1 hp2 hs h2
    (hz ε hε.1 (hε.2.trans_le (min_le_left _ _))) (hw ε hε.1 (hε.2.trans_le (min_le_right _ _))))

end P18
