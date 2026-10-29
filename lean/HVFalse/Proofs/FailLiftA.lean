/-
  HVFalse/Proofs/FailLiftA.lean - L1 part (a): M(ζ) = |ζ|^q m(arg ζ) is continuous; rescaling g(ρζ) avoids zeros on T
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Γ(y,t) depends on t only through cos t (`Gamc`), and cos(arg ζ) = Re ζ/|ζ|. For s ≤ sec²ϑ all minimizers lie in |y| ≤ R
  (C03d), so m(t) = min over the compact [-R,R], continuous in cos t (IsCompact.continuous_sInf). Hence M is continuous on ℂ
  (at 0: |ζ|^q · bounded → 0). Then ρ ↦ ∫ M(g(ρ e^{iθ})) dθ is continuous, and ρ < 1 close to 1 avoids every root of g.
-/
import HVFalse.Proofs.Coercive
import HVFalse.Proofs.Discs
import HVFalse.Defs.Minimum
import HVFalse.Defs.Saddle

open Real Set Filter Topology

namespace P18

/-- `Γ` written with `c = cos t`. -/
noncomputable def Gamc (p s y c : ℝ) : ℝ :=
  ((cosh y + c) / (1 + cos (π / p))) ^ (p / 2) - cosh (s * y / 2) ^ (p / s)

theorem gam_eq_gamc {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (y t : ℝ) : Gam p s y t = Gamc p s y (cos t) :=
  gam_eq_div p s y t hp1 hp2

theorem continuous_gamc {p s : ℝ} (hp : 0 < p) (hs : 0 < s) : Continuous fun x : ℝ × ℝ => Gamc p s x.1 x.2 := by
  unfold Gamc
  apply Continuous.sub
  · exact ((continuous_cosh.comp continuous_fst).add continuous_snd |>.div_const _).rpow_const
      fun _ => Or.inr (by linarith)
  · exact (continuous_cosh.comp ((continuous_const.mul continuous_fst).div_const 2)).rpow_const
      fun _ => Or.inr (div_nonneg hp.le hs.le)

/-- `m` as a minimum over the compact `[-R, R]`, as a function of `c = cos t`. -/
noncomputable def mK (p s R c : ℝ) : ℝ := sInf ((fun y => Gamc p s y c) '' Icc (-R) R)

theorem continuous_mK {p s : ℝ} (hp : 0 < p) (hs : 0 < s) (R : ℝ) : Continuous (mK p s R) := by
  have hf : Continuous fun x : ℝ × ℝ => Gamc p s x.2 x.1 := by
    unfold Gamc
    apply Continuous.sub
    · exact ((continuous_cosh.comp continuous_snd).add continuous_fst |>.div_const _).rpow_const
        fun _ => Or.inr (by linarith)
    · exact (continuous_cosh.comp ((continuous_const.mul continuous_snd).div_const 2)).rpow_const
        fun _ => Or.inr (div_nonneg hp.le hs.le)
  have h := IsCompact.continuous_sInf (α := ℝ) (f := fun c y : ℝ => Gamc p s y c) (K := Icc (-R) R)
    isCompact_Icc hf
  unfold mK
  exact h

/-- For `s ≤ sec²ϑ`: one `R` such that `m(t) = mK(cos t)` for every `t`. -/
theorem exists_mfun_eq_mK {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∃ R : ℝ, ∀ t : ℝ, mfun p s t = mK p s R (cos t) ∧
      ∃ y0 ∈ Icc (-R) R, Gam p s y0 t = mfun p s t ∧ ∀ y, mfun p s t ≤ Gam p s y t := by
  obtain ⟨R, hR⟩ := gam_minimizers_bounded hp1 hp2 hs hsS
  refine ⟨R, fun t => ?_⟩
  obtain ⟨y0, hy0⟩ := gam_min_attained hp1 hp2 hs hsS t
  have hy0R : y0 ∈ Icc (-R) R := abs_le.mp (hR t y0 hy0)
  have hleast : IsLeast (range fun y => Gam p s y t) (Gam p s y0 t) :=
    ⟨⟨y0, rfl⟩, by rintro _ ⟨y, rfl⟩; exact hy0 y⟩
  have hm : mfun p s t = Gam p s y0 t := hleast.csInf_eq
  have hleastK : IsLeast ((fun y => Gamc p s y (cos t)) '' Icc (-R) R) (Gam p s y0 t) := by
    refine ⟨⟨y0, hy0R, (gam_eq_gamc hp1 hp2 y0 t).symm⟩, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    dsimp only
    rw [← gam_eq_gamc hp1 hp2]
    exact hy0 y
  refine ⟨by unfold mK; rw [hm, hleastK.csInf_eq], y0, hy0R, hm.symm, fun y => hm ▸ hy0 y⟩

theorem cos_arg_eq (ζ : ℂ) (hζ : ζ ≠ 0) : cos (Complex.arg ζ) = ζ.re / ‖ζ‖ := Complex.cos_arg hζ

/-- `M(ζ) = |ζ|^q mK(Re ζ/|ζ|)` for every `ζ` (both sides vanish at `0`). -/
theorem Mfun_eq {p s R : ℝ} (hp : 0 < p) (hmK : ∀ t, mfun p s t = mK p s R (cos t)) (ζ : ℂ) :
    Mfun p s ζ = ‖ζ‖ ^ (p / 2) * mK p s R (ζ.re / ‖ζ‖) := by
  unfold Mfun
  by_cases h : ζ = 0
  · rw [h, norm_zero, zero_rpow (by positivity), zero_mul, zero_mul]
  · rw [hmK, cos_arg_eq ζ h]

theorem continuous_Mfun {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    Continuous (Mfun p s) := by
  have hp : 0 < p := by linarith
  obtain ⟨R, hR⟩ := exists_mfun_eq_mK hp1 hp2 hs hsS
  have hcont := continuous_mK hp hs R
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont.continuousOn
  have heq : Mfun p s = fun ζ => ‖ζ‖ ^ (p / 2) * mK p s R (ζ.re / ‖ζ‖) :=
    funext (Mfun_eq hp fun t => (hR t).1)
  rw [heq, continuous_iff_continuousAt]
  intro ζ
  by_cases hζ : ζ = 0
  · subst hζ
    rw [ContinuousAt, norm_zero, zero_rpow (by positivity), zero_mul]
    apply squeeze_zero_norm (a := fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * Bd)
    · intro w
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (hBd _ ?_) (by positivity)
      by_cases hw : w = 0
      · simp [hw]
      · exact abs_le.mp (Complex.abs_re_div_norm_le_one w) |> fun h => ⟨h.1, h.2⟩
    · have : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * Bd) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ ^ (p / 2) * Bd)) :=
        ((continuous_norm.rpow_const fun _ => Or.inr (by linarith)).mul continuous_const).tendsto 0
      rwa [norm_zero, zero_rpow (by positivity), zero_mul] at this
  · apply ContinuousAt.mul
    · exact (continuous_norm.rpow_const fun _ => Or.inr (by linarith)).continuousAt
    · exact hcont.continuousAt.comp (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt
        (norm_ne_zero_iff.mpr hζ))

theorem norm_unitPt (θ : ℝ) : ‖unitPt θ‖ = 1 := by
  unfold unitPt; exact Complex.norm_exp_ofReal_mul_I θ

/-- Rescaling: some `ρ ∈ (0,1)` keeps `∫ M(g(ρ e^{iθ})) < 0` and puts no root of `g` on the circle of radius `ρ`. -/
theorem exists_rescale {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (g : Polynomial ℂ)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval (unitPt θ)) < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ (∀ θ : ℝ, g.eval ((ρ : ℂ) * unitPt θ) ≠ 0) ∧
      ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval ((ρ : ℂ) * unitPt θ)) < 0 := by
  have hM := continuous_Mfun hp1 hp2 hs hsS
  set Φ := fun ρ : ℝ => ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval ((ρ : ℂ) * unitPt θ)) with hΦ
  have hΦc : Continuous Φ := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hM.comp ((Polynomial.continuous g).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      (continuous_unitPt.comp continuous_snd)))
  have hΦ1 : Φ 1 < 0 := by simpa [hΦ] using hneg
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.eventually_nhds_iff.mp ((hΦc.tendsto 1).eventually (gt_mem_nhds hΦ1))
  have hg : g ≠ 0 := by
    rintro rfl
    simp [Mfun, zero_rpow (show (p / 2 : ℝ) ≠ 0 by positivity)] at hneg
  obtain ⟨ρ1, hρ1, hρ1b, hbound⟩ : ∃ ρ1 : ℝ, 0 ≤ ρ1 ∧ ρ1 < 1 ∧ ∀ r ∈ g.roots, ‖r‖ < 1 → ‖r‖ ≤ ρ1 := by
    by_cases hS : (g.roots.toFinset.filter fun r => ‖r‖ < 1).Nonempty
    · obtain ⟨r0, hr0, hmax⟩ := Finset.exists_max_image _ (fun r : ℂ => ‖r‖) hS
      exact ⟨‖r0‖, norm_nonneg _, (Finset.mem_filter.mp hr0).2, fun r hr hr1 =>
        hmax r (Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, hr1⟩)⟩
    · exact ⟨0, le_refl _, one_pos, fun r hr hr1 =>
        absurd ⟨r, Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hr, hr1⟩⟩ hS⟩
  set ρ := (max ρ1 (1 - δ / 2) + 1) / 2 with hρ
  have hmax1 : max ρ1 (1 - δ / 2) < 1 := max_lt hρ1b (by linarith)
  have hρpos : 0 < ρ := by have := le_max_left ρ1 (1 - δ / 2); linarith
  have hρ1' : ρ1 < ρ := by have := le_max_left ρ1 (1 - δ / 2); linarith
  have hρlt : ρ < 1 := by linarith
  refine ⟨ρ, hρpos, hρlt, fun θ h0 => ?_, hδΦ ?_⟩
  · have hmem : (ρ : ℂ) * unitPt θ ∈ g.roots := (Polynomial.mem_roots hg).mpr h0
    have hn : ‖(ρ : ℂ) * unitPt θ‖ = ρ := by
      rw [norm_mul, norm_unitPt, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos]
    have := hbound _ hmem (by rw [hn]; exact hρlt)
    rw [hn] at this
    linarith
  · rw [Real.dist_eq, abs_lt]
    have := le_max_right ρ1 (1 - δ / 2)
    constructor <;> linarith

end P18
