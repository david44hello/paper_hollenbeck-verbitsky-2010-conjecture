/-
  HVFalse/Proofs/FailCole.lean - Prop. fail, the "no minorant ⇒ a bad disc" half (the paper, Prop. 4)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route: if every disc integral of M = |ζ|^q m(arg ζ) is ≥ 0, Cole's criterion gives a q-homogeneous subharmonic G ≤ M with
  G(0) ≥ 0; by E1c it is finite on the circle, by E1d its profile φ is trigonometrically convex and 2π-periodic, and φ ≤ m ≤ Γ;
  then forcing gives e ≤ φ ≤ Γ on [-π, π], against a failure point. M is continuous: m = min over |y| ≤ R (C03d) of a jointly
  continuous Γ, and M(ζ) = |ζ|^q m(arccos(Re ζ/|ζ|)) off 0 (m even), so arg's jump on the negative axis is harmless.
-/
import HVFalse.Defs.Minimum
import HVFalse.Defs.Saddle
import HVFalse.Proofs.Sector
import HVFalse.Proofs.Forcing
import HVFalse.Proofs.Coercive

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace FailCole

variable {p s : ℝ}

/-- `Γ` is jointly continuous in `(t, y)`. -/
theorem gam_continuous_ty (hp1 : 1 < p) (hs : 0 < s) : Continuous (fun x : ℝ × ℝ => Gam p s x.2 x.1) := by
  unfold Gam
  have hq : (0:ℝ) ≤ p / 2 := by linarith
  have hr : (0:ℝ) ≤ p / s := div_nonneg (by linarith) hs.le
  refine Continuous.sub (Continuous.div_const ?_ _) ?_
  · exact (Continuous.add (continuous_cosh.comp continuous_snd) (continuous_cos.comp continuous_fst)).rpow_const
      (fun _ => Or.inr hq)
  · exact (continuous_cosh.comp ((continuous_const.mul continuous_snd).div_const 2)).rpow_const (fun _ => Or.inr hr)

/-- The minimum is attained and `mfun` is it. -/
theorem mfun_eq_min (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (t : ℝ) :
    ∃ y0, (∀ y, Gam p s y0 t ≤ Gam p s y t) ∧ mfun p s t = Gam p s y0 t := by
  obtain ⟨y0, hy0⟩ := gam_min_attained hp1 hp2 hs hsS t
  refine ⟨y0, hy0, le_antisymm (ciInf_le ⟨Gam p s y0 t, ?_⟩ y0) (le_ciInf hy0)⟩
  rintro _ ⟨y, rfl⟩; exact hy0 y

/-- `m(t) ≤ Γ(y,t)` for every `y`. -/
theorem mfun_le (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (y t : ℝ) : mfun p s t ≤ Gam p s y t := by
  obtain ⟨y0, hy0, heq⟩ := mfun_eq_min hp1 hp2 hs hsS t
  rw [heq]; exact hy0 y

/-- `m` is continuous. -/
theorem mfun_continuous (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) : Continuous (mfun p s) := by
  obtain ⟨R, hR⟩ := gam_minimizers_bounded hp1 hp2 hs hsS
  have heq : mfun p s = fun t => sInf ((fun y => Gam p s y t) '' Icc (-R) R) := by
    funext t
    obtain ⟨y0, hy0, hm⟩ := mfun_eq_min hp1 hp2 hs hsS t
    have hy0R := hR t y0 hy0
    rw [hm]
    have hl : IsLeast ((fun y => Gam p s y t) '' Icc (-R) R) (Gam p s y0 t) := by
      refine ⟨⟨y0, ⟨by linarith [neg_abs_le y0], le_trans (le_abs_self y0) hy0R⟩, rfl⟩, ?_⟩
      rintro _ ⟨y, -, rfl⟩; exact hy0 y
    exact hl.csInf_eq.symm
  rw [heq]
  exact isCompact_Icc.continuous_sInf (gam_continuous_ty hp1 hs)

/-- `m` is `2π`-periodic. -/
theorem mfun_periodic : Function.Periodic (mfun p s) (2 * π) := by
  intro t; unfold mfun; simp only [gam_periodic_t]

/-- `m` is even. -/
theorem mfun_even (t : ℝ) : mfun p s (-t) = mfun p s t := by
  unfold mfun; simp only [gam_even_t]

/-- `M(ζ) = |ζ|^q m(arccos(Re ζ/|ζ|))` off `0`. -/
theorem Mfun_eq_arccos {ζ : ℂ} (hζ : ζ ≠ 0) :
    Mfun p s ζ = ‖ζ‖ ^ (p / 2) * mfun p s (Real.arccos (ζ.re / ‖ζ‖)) := by
  unfold Mfun
  congr 1
  rw [← Complex.cos_arg hζ, ← cos_abs (Complex.arg ζ),
    Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi ζ)]
  rcases abs_choice (Complex.arg ζ) with h | h <;> rw [h]
  rw [mfun_even]

/-- `M` is continuous on `ℂ`. -/
theorem Mfun_continuous (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) : Continuous (Mfun p s) := by
  have hmc := mfun_continuous hp1 hp2 hs hsS
  have hq : 0 < p / 2 := by linarith
  rw [continuous_iff_continuousAt]
  intro ζ0
  by_cases hζ0 : ζ0 = 0
  · -- at 0: |M ζ| ≤ ‖ζ‖^q · B → 0 = M 0
    subst hζ0
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hmc.continuousOn
    have hM0 : Mfun p s 0 = 0 := by simp [Mfun, zero_rpow hq.ne']
    rw [ContinuousAt, hM0]
    have hbound : ∀ ζ : ℂ, ‖Mfun p s ζ‖ ≤ ‖ζ‖ ^ (p / 2) * B := by
      intro ζ
      unfold Mfun
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (norm_nonneg ζ) _)]
      exact mul_le_mul_of_nonneg_left (hB _ ⟨(Complex.neg_pi_lt_arg ζ).le, Complex.arg_le_pi ζ⟩)
        (rpow_nonneg (norm_nonneg ζ) _)
    have hlim : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * B) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * B) :=
        (continuous_norm.rpow_const (fun _ => Or.inr hq.le)).mul continuous_const
      simpa [zero_rpow hq.ne'] using this.tendsto 0
    exact squeeze_zero_norm hbound hlim
  · -- off 0: the arccos form is continuous
    have hcont : ContinuousAt (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * mfun p s (Real.arccos (ζ.re / ‖ζ‖))) ζ0 := by
      have hn : ‖ζ0‖ ≠ 0 := norm_ne_zero_iff.mpr hζ0
      refine ((continuous_norm.rpow_const (fun _ => Or.inr hq.le)).continuousAt).mul ?_
      exact hmc.continuousAt.comp (Real.continuous_arccos.continuousAt.comp
        (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hn))
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hζ0] with ζ hζ
    exact (Mfun_eq_arccos hζ).symm

/-- `M` is `q`-homogeneous. -/
theorem Mfun_homog (hq : 0 < p / 2) (r : ℝ) (z : ℂ) (hr : 0 < r) : Mfun p s ((r : ℂ) * z) = r ^ (p / 2) * Mfun p s z := by
  by_cases hz : z = 0
  · subst hz; simp [Mfun, zero_rpow hq.ne']
  · unfold Mfun
    rw [Complex.arg_real_mul z hr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      mul_rpow hr.le (norm_nonneg z)]
    ring

/-- `M(e^{it}) = m(t)`. -/
theorem Mfun_exp (t : ℝ) : Mfun p s (Complex.exp ((t : ℂ) * Complex.I)) = mfun p s t := by
  unfold Mfun
  rw [Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I, toIocMod, mfun_periodic.sub_zsmul_eq]

/-- `trunc n x ≥ x` for a real `x`. -/
theorem le_trunc_coe (n : ℕ) (x : ℝ) : x ≤ trunc n (x : EReal) :=
  EReal.coe_le_coe_iff.mp (Sector.le_trunc (EReal.coe_ne_top x) n)

/-- `trunc n x = max x (-n)` for a real `x`. -/
theorem trunc_coe (n : ℕ) (x : ℝ) : trunc n (x : EReal) = max x (-(n : ℝ)) := by
  unfold trunc
  have hn : (-(n : EReal)) = ((-(n : ℝ) : ℝ) : EReal) := by simp
  rcases le_total x (-(n : ℝ)) with h | h
  · have h' : (x : EReal) ≤ -(n : EReal) := by rw [hn]; exact EReal.coe_le_coe_iff.mpr h
    rw [max_eq_right h', max_eq_right h, hn, EReal.toReal_coe]
  · have h' : -(n : EReal) ≤ (x : EReal) := by rw [hn]; exact EReal.coe_le_coe_iff.mpr h
    rw [max_eq_left h', max_eq_left h, EReal.toReal_coe]

end FailCole

end P18
