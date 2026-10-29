/-
  HVFalse/Proofs/LamCole.lean - Prop. 14 "only if", the Cole step: no feasible φ ≤ m_λ ⇒ a bad disc for M_λ
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  For λ ≥ 1, Γ_λ = Γ + (λ-1)·(first term) ≥ Γ. So Γ_λ is coercive in y uniformly in t, m_λ = min over |y| ≤ R is
  continuous, and M_λ(ζ) = |ζ|^q m_λ(arg ζ) is continuous and q-homogeneous.
  The Cole step itself (a q-homogeneous subharmonic G ≤ M_λ from the disc integrals) is now ColeHom.cole_step' (Cole's
  Thm 2.1 alone + the homogeneity proof); this file has no cited axiom.
  λ = 1: `gamLam_one`, `mlam_one`, `Mlam_one` (Γ_1 = Γ, m_1 = m, M_1 = M).
-/
import HVFalse.Defs.Extra
import HVFalse.Proofs.FailCole

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace LamCole

variable {p s lam : ℝ}

/-- `m_λ(t) = inf_y Γ_λ(y,t)` (paper Sec. 7, l.618). -/
noncomputable def mlam (p s lam t : ℝ) : ℝ := ⨅ y : ℝ, GamLam p s lam y t

/-- `M_λ(ζ) = |ζ|^q m_λ(arg ζ)`. -/
noncomputable def Mlam (p s lam : ℝ) (ζ : ℂ) : ℝ := ‖ζ‖ ^ (p / 2) * mlam p s lam (Complex.arg ζ)

theorem gamLam_one : GamLam p s 1 = Gam p s := by
  funext y t; simp only [GamLam, Gam, one_mul]

theorem mlam_one : mlam p s 1 = mfun p s := by
  funext t; simp only [mlam, mfun, gamLam_one]

theorem Mlam_one : Mlam p s 1 = Mfun p s := by
  funext ζ; simp only [Mlam, Mfun, mlam_one]

/-- The first term of `Γ`. -/
noncomputable def term1 (p y t : ℝ) : ℝ := (cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2)

theorem term1_nonneg (p y t : ℝ) : 0 ≤ term1 p y t := by
  unfold term1
  apply div_nonneg
  · apply rpow_nonneg; nlinarith [one_le_cosh y, neg_one_le_cos t]
  · apply rpow_nonneg; linarith [neg_one_le_cos (2 * (π / (2 * p)))]

theorem gamLam_eq (y t : ℝ) : GamLam p s lam y t = Gam p s y t + (lam - 1) * term1 p y t := by
  simp only [GamLam, Gam, term1]; ring

theorem gam_le_gamLam (hlam : 1 ≤ lam) (y t : ℝ) : Gam p s y t ≤ GamLam p s lam y t := by
  rw [gamLam_eq]
  have := mul_nonneg (sub_nonneg.mpr hlam) (term1_nonneg p y t)
  linarith

theorem gamLam_periodic_t (y t : ℝ) : GamLam p s lam y (t + 2 * π) = GamLam p s lam y t := by
  simp only [GamLam, cos_add_two_pi]

theorem gamLam_even_t (y t : ℝ) : GamLam p s lam y (-t) = GamLam p s lam y t := by
  simp only [GamLam, cos_neg]

/-- `Γ_λ → +∞` as `|y| → ∞`, uniformly in `t` (`λ ≥ 1`, `0 < s ≤ sec²ϑ`). -/
theorem gamLam_tendsto (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ y t : ℝ, R ≤ |y| → M ≤ GamLam p s lam y t := by
  intro M
  obtain ⟨R, hR⟩ := gam_tendsto hp1 hp2 hs hsS M
  exact ⟨R, fun y t hy => (hR y t hy).trans (gam_le_gamLam hlam y t)⟩

theorem gamLam_continuous_ty (hp1 : 1 < p) (hs : 0 < s) :
    Continuous (fun x : ℝ × ℝ => GamLam p s lam x.2 x.1) := by
  have h1 := FailCole.gam_continuous_ty (p := p) (s := s) hp1 hs
  have h2 : Continuous (fun x : ℝ × ℝ => term1 p x.2 x.1) := by
    unfold term1
    exact (((continuous_cosh.comp continuous_snd).add (continuous_cos.comp continuous_fst)).rpow_const
      (fun _ => Or.inr (by linarith))).div_const _
  simp only [gamLam_eq]
  exact h1.add (continuous_const.mul h2)

theorem gamLam_continuous_y (hp1 : 1 < p) (hs : 0 < s) (t : ℝ) : Continuous (fun y => GamLam p s lam y t) := by
  have h2 : Continuous (fun y => term1 p y t) := by
    unfold term1
    exact ((continuous_cosh.add continuous_const).rpow_const (fun _ => Or.inr (by linarith))).div_const _
  simp only [gamLam_eq]
  exact (gam_continuous_y hp1 hs t).add (continuous_const.mul h2)

theorem gamLam_min_attained (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (t : ℝ) :
    ∃ y0, ∀ y, GamLam p s lam y0 t ≤ GamLam p s lam y t := by
  apply (gamLam_continuous_y hp1 hs t).exists_forall_le
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · rw [tendsto_atBot_atTop]
    intro M
    obtain ⟨R, hR⟩ := gamLam_tendsto hp1 hp2 hs hsS hlam M
    exact ⟨-|R|, fun y hy => hR y t (le_trans (le_abs_self R) (by linarith [neg_le_abs y]))⟩
  · rw [tendsto_atTop_atTop]
    intro M
    obtain ⟨R, hR⟩ := gamLam_tendsto hp1 hp2 hs hsS hlam M
    exact ⟨|R|, fun y hy => hR y t (le_trans (le_abs_self R) (hy.trans (le_abs_self y)))⟩

theorem gamLam_zero_le (hp1 : 1 < p) (hlam : 1 ≤ lam) (t : ℝ) :
    GamLam p s lam 0 t ≤ lam * term1 p 0 0 - 1 := by
  have hp0 : (0:ℝ) ≤ p / 2 := by linarith
  have hmono : term1 p 0 t ≤ term1 p 0 0 := by
    unfold term1
    apply div_le_div_of_nonneg_right _ (rpow_nonneg (by linarith [neg_one_le_cos (2 * (π / (2 * p)))]) _)
    apply rpow_le_rpow (by rw [cosh_zero]; linarith [neg_one_le_cos t]) (by rw [cos_zero]; linarith [cos_le_one t]) hp0
  have heq : GamLam p s lam 0 t = lam * term1 p 0 t - 1 := by
    simp only [GamLam, term1, mul_zero, zero_div, cosh_zero, one_rpow]
  rw [heq]
  have : lam * term1 p 0 t ≤ lam * term1 p 0 0 := mul_le_mul_of_nonneg_left hmono (by linarith)
  linarith

theorem gamLam_minimizers_bounded (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    ∃ R, ∀ t y0, (∀ y, GamLam p s lam y0 t ≤ GamLam p s lam y t) → |y0| ≤ R := by
  obtain ⟨R, hR⟩ := gamLam_tendsto hp1 hp2 hs hsS hlam (lam * term1 p 0 0 - 1 + 1)
  refine ⟨R, fun t y0 hmin => ?_⟩
  by_contra h
  push Not at h
  have h1 := hR y0 t h.le
  have h2 := hmin 0
  have h3 := gamLam_zero_le (s := s) hp1 hlam t
  linarith

/-- The minimum is attained and `m_λ` is it. -/
theorem mlam_eq_min (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (t : ℝ) :
    ∃ y0, (∀ y, GamLam p s lam y0 t ≤ GamLam p s lam y t) ∧ mlam p s lam t = GamLam p s lam y0 t := by
  obtain ⟨y0, hy0⟩ := gamLam_min_attained hp1 hp2 hs hsS hlam t
  refine ⟨y0, hy0, le_antisymm (ciInf_le ⟨GamLam p s lam y0 t, ?_⟩ y0) (le_ciInf hy0)⟩
  rintro _ ⟨y, rfl⟩; exact hy0 y

theorem mlam_le (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (y t : ℝ) :
    mlam p s lam t ≤ GamLam p s lam y t := by
  obtain ⟨y0, hy0, heq⟩ := mlam_eq_min hp1 hp2 hs hsS hlam t
  rw [heq]; exact hy0 y

/-- One bound `R` for the minimizers of every `t` (used by the λ-lift). -/
theorem exists_mlam_min (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    ∃ R, ∀ t, ∃ y0 ∈ Icc (-R) R, GamLam p s lam y0 t = mlam p s lam t ∧ ∀ y, GamLam p s lam y0 t ≤ GamLam p s lam y t := by
  obtain ⟨R, hR⟩ := gamLam_minimizers_bounded hp1 hp2 hs hsS hlam
  refine ⟨R, fun t => ?_⟩
  obtain ⟨y0, hy0, hm⟩ := mlam_eq_min hp1 hp2 hs hsS hlam t
  have hy0R := hR t y0 hy0
  exact ⟨y0, ⟨by linarith [neg_abs_le y0], le_trans (le_abs_self y0) hy0R⟩, hm.symm, hy0⟩

theorem mlam_continuous (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    Continuous (mlam p s lam) := by
  obtain ⟨R, hR⟩ := gamLam_minimizers_bounded hp1 hp2 hs hsS hlam
  have heq : mlam p s lam = fun t => sInf ((fun y => GamLam p s lam y t) '' Icc (-R) R) := by
    funext t
    obtain ⟨y0, hy0, hm⟩ := mlam_eq_min hp1 hp2 hs hsS hlam t
    have hy0R := hR t y0 hy0
    rw [hm]
    have hl : IsLeast ((fun y => GamLam p s lam y t) '' Icc (-R) R) (GamLam p s lam y0 t) := by
      refine ⟨⟨y0, ⟨by linarith [neg_abs_le y0], le_trans (le_abs_self y0) hy0R⟩, rfl⟩, ?_⟩
      rintro _ ⟨y, -, rfl⟩; exact hy0 y
    exact hl.csInf_eq.symm
  rw [heq]
  exact isCompact_Icc.continuous_sInf (gamLam_continuous_ty hp1 hs)

theorem mlam_periodic : Function.Periodic (mlam p s lam) (2 * π) := by
  intro t; unfold mlam; simp only [gamLam_periodic_t]

theorem mlam_even (t : ℝ) : mlam p s lam (-t) = mlam p s lam t := by
  unfold mlam; simp only [gamLam_even_t]

theorem Mlam_eq_arccos {ζ : ℂ} (hζ : ζ ≠ 0) :
    Mlam p s lam ζ = ‖ζ‖ ^ (p / 2) * mlam p s lam (Real.arccos (ζ.re / ‖ζ‖)) := by
  unfold Mlam
  congr 1
  rw [← Complex.cos_arg hζ, ← cos_abs (Complex.arg ζ),
    Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi ζ)]
  rcases abs_choice (Complex.arg ζ) with h | h <;> rw [h]
  rw [mlam_even]

theorem Mlam_continuous (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    Continuous (Mlam p s lam) := by
  have hmc := mlam_continuous hp1 hp2 hs hsS hlam
  have hq : 0 < p / 2 := by linarith
  rw [continuous_iff_continuousAt]
  intro ζ0
  by_cases hζ0 : ζ0 = 0
  · subst hζ0
    obtain ⟨B, hB⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hmc.continuousOn
    have hM0 : Mlam p s lam 0 = 0 := by simp [Mlam, zero_rpow hq.ne']
    rw [ContinuousAt, hM0]
    have hbound : ∀ ζ : ℂ, ‖Mlam p s lam ζ‖ ≤ ‖ζ‖ ^ (p / 2) * B := by
      intro ζ
      unfold Mlam
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg (norm_nonneg ζ) _)]
      exact mul_le_mul_of_nonneg_left (hB _ ⟨(Complex.neg_pi_lt_arg ζ).le, Complex.arg_le_pi ζ⟩)
        (rpow_nonneg (norm_nonneg ζ) _)
    have hlim : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * B) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * B) :=
        (continuous_norm.rpow_const (fun _ => Or.inr hq.le)).mul continuous_const
      simpa [zero_rpow hq.ne'] using this.tendsto 0
    exact squeeze_zero_norm hbound hlim
  · have hcont : ContinuousAt (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * mlam p s lam (Real.arccos (ζ.re / ‖ζ‖))) ζ0 := by
      have hn : ‖ζ0‖ ≠ 0 := norm_ne_zero_iff.mpr hζ0
      refine ((continuous_norm.rpow_const (fun _ => Or.inr hq.le)).continuousAt).mul ?_
      exact hmc.continuousAt.comp (Real.continuous_arccos.continuousAt.comp
        (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hn))
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hζ0] with ζ hζ
    exact (Mlam_eq_arccos hζ).symm

theorem Mlam_homog (hq : 0 < p / 2) (r : ℝ) (z : ℂ) (hr : 0 < r) :
    Mlam p s lam ((r : ℂ) * z) = r ^ (p / 2) * Mlam p s lam z := by
  by_cases hz : z = 0
  · subst hz; simp [Mlam, zero_rpow hq.ne']
  · unfold Mlam
    rw [Complex.arg_real_mul z hr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      mul_rpow hr.le (norm_nonneg z)]
    ring

theorem Mlam_exp (t : ℝ) : Mlam p s lam (Complex.exp ((t : ℂ) * Complex.I)) = mlam p s lam t := by
  unfold Mlam
  rw [Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I, toIocMod, mlam_periodic.sub_zsmul_eq]

end LamCole

end P18
