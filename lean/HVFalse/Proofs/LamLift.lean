/-
  HVFalse/Proofs/LamLift.lean - Prop. 14 "only if", the lift: a bad disc for M_λ refutes (HV) with λ^{1/p} C
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  G_λ(z,w) = λ A^p |z + w̄|^p - ((|z|^s + |w|^s)/2)^{p/s} (paper Sec. 7: A replaced by λ^{1/p} A); `Glam_one`: G_1 = G.
  (b3) `discs_lam`: (HV) with λ^{1/p} C_{s,p} ⇔ ∫ G_λ∘h ≥ 0 for polynomial discs h = (z, w), w(0) = 0 (route).
  `lift_lam`: G_λ = |zw|^q Γ_λ(log|z/w|, arg zw), from lift_pointwise (G_λ = λG + (λ-1)X, Γ_λ = λΓ + (λ-1)·2nd term).
  (b2) `not_discIneqLam_of_bad_disc`: the L1 proof verbatim, with Γ, G, M, m replaced by Γ_λ, G_λ, M_λ, m_λ
  (the minimizer bound and the continuity of M_λ come from LamCole).
-/
import HVFalse.Proofs.LamCole
import HVFalse.Proofs.FailLift

open Real Set Filter Topology

namespace P18

namespace LamLift

/-- `G_λ(z,w) = λ A^p |z + w̄|^p - ((|z|^s + |w|^s)/2)^{p/s}`, `A = 1/(2 cos ϑ)`. -/
noncomputable def Glam (p s lam : ℝ) (z w : ℂ) : ℝ :=
  lam * ((1 / (2 * cos (π / (2 * p)))) ^ p * ‖z + (starRingEnd ℂ) w‖ ^ p) - ((‖z‖ ^ s + ‖w‖ ^ s) / 2) ^ (p / s)

theorem Glam_one (p s : ℝ) : Glam p s 1 = G p s := by
  funext z w; simp only [Glam, G, one_mul]

/-- (eq:discs) for `G_λ`: `∫ G_λ∘h ≥ 0` for every polynomial disc `h = (z, w)` with `w(0) = 0`. -/
def DiscIneqLam (p s lam : ℝ) : Prop :=
  ∀ z w : Polynomial ℂ, w.coeff 0 = 0 →
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π),
      Glam p s lam (z.eval (Complex.exp ((θ : ℂ) * Complex.I))) (w.eval (Complex.exp ((θ : ℂ) * Complex.I)))

theorem discIneqLam_one (p s : ℝ) : DiscIneqLam p s 1 ↔ DiscIneq p s := by
  simp only [DiscIneqLam, DiscIneq, Glam_one]

theorem continuous_Glam (p s lam : ℝ) (hp : 0 < p) (hs : 0 < s) : Continuous fun x : ℂ × ℂ => Glam p s lam x.1 x.2 := by
  unfold Glam
  apply Continuous.sub
  · exact continuous_const.mul (continuous_const.mul
      ((continuous_fst.add (Complex.continuous_conj.comp continuous_snd)).norm.rpow_const fun _ => Or.inr hp.le))
  · exact (((continuous_fst.norm.rpow_const fun _ => Or.inr hs.le).add
      (continuous_snd.norm.rpow_const fun _ => Or.inr hs.le)).div_const 2).rpow_const
      fun _ => Or.inr (div_nonneg hp.le hs.le)

/-! ### (b3) (HV) with `λ^{1/p} C` ⇔ `DiscIneqLam` -/

theorem Glam_conj (p s lam : ℝ) (P Q : ℂ) :
    Glam p s lam P ((starRingEnd ℂ) Q) =
      lam * ((1 / (2 * cos (π / (2 * p)))) ^ p * ‖P + Q‖ ^ p) - ((‖P‖ ^ s + ‖Q‖ ^ s) / 2) ^ (p / s) := by
  unfold Glam
  rw [Complex.conj_conj, Complex.norm_conj]

theorem lamConst_rpow {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hlam : 0 < lam) :
    (lam ^ (1 / p) * hvConst p s) ^ p = lam * hvConst p s ^ p := by
  have hc := cos_half_pos hp1 hp2
  have hC : 0 ≤ hvConst p s := by unfold hvConst; positivity
  rw [mul_rpow (rpow_nonneg hlam.le _) hC, ← rpow_mul hlam.le, one_div_mul_cancel (by linarith : p ≠ 0), rpow_one]

theorem hv_integral_iff_lam {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hlam : 0 < lam) {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) :
    (∫ θ in (0 : ℝ)..(2 * π), ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) ^ (1 / s)) ^ p
        ≤ (lam ^ (1 / p) * hvConst p s) ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖P θ + Q θ‖ ^ p) ↔
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), Glam p s lam (P θ) ((starRingEnd ℂ) (Q θ)) := by
  have hk : 0 < (2 : ℝ) ^ (p / s) := by positivity
  have hX : Continuous fun θ => ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) / 2) ^ (p / s) :=
    (((hP.norm.rpow_const fun _ => Or.inr hs.le).add (hQ.norm.rpow_const fun _ => Or.inr hs.le)).div_const 2).rpow_const
      fun _ => Or.inr (div_nonneg (by linarith) hs.le)
  have hY : Continuous fun θ => ‖P θ + Q θ‖ ^ p := (hP.add hQ).norm.rpow_const fun _ => Or.inr (by linarith)
  simp_rw [hv_integrand_eq, Glam_conj]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    (((hY.const_mul _).const_mul _).intervalIntegrable _ _) (hX.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [lamConst_rpow hp1 hp2 hlam, hvConst_rpow hp1 hp2]
  set IX := ∫ θ in (0 : ℝ)..(2 * π), ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) / 2) ^ (p / s)
  set IY := ∫ θ in (0 : ℝ)..(2 * π), ‖P θ + Q θ‖ ^ p
  set Ap := (1 / (2 * cos (π / (2 * p)))) ^ p
  have e : lam * (2 ^ (p / s) * Ap) * IY = 2 ^ (p / s) * (lam * (Ap * IY)) := by ring
  rw [e]
  constructor
  · intro h
    have := le_of_mul_le_mul_left h hk
    linarith
  · intro h
    exact mul_le_mul_of_nonneg_left (by linarith) hk.le

/-- (b3), C01 for `λ`: (HV) with `λ^{1/p} C_{s,p}` ⇔ `DiscIneqLam` (`discs_equiv`, `λ = 1`). -/
theorem discs_lam {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hlam : 0 < lam) :
    HVIneq p s (lam ^ (1 / p) * hvConst p s) ↔ DiscIneqLam p s lam := by
  constructor
  · intro hHV z w hw
    have h := hHV (ofZW z w)
    simp_rw [trig_eq_add] at h
    have h2 := (hv_integral_iff_lam hp1 hp2 hs hlam (continuous_Pplus (ofZW z w)) (continuous_Pminus (ofZW z w))).mp h
    simp_rw [Pplus_ofZW z w hw, Pminus_ofZW z w hw, Complex.conj_conj] at h2
    exact h2
  · intro hD c
    have h := hD (toZ c) (toW c) (toW_coeff_zero c)
    have e : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) = unitPt θ := fun θ => rfl
    simp_rw [e, eval_toZ, eval_toW] at h
    simp_rw [trig_eq_add]
    exact (hv_integral_iff_lam hp1 hp2 hs hlam (continuous_Pplus c) (continuous_Pminus c)).mpr h

/-! ### The pointwise lift for `G_λ` -/

/-- The second term: `((|z|^s + |w|^s)/2)^{p/s} = |zw|^q cosh(s y/2)^{p/s}`, `y = log(|z|/|w|)`. -/
theorem second_term (p s : ℝ) (hs : 0 < s) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    ((‖z‖ ^ s + ‖w‖ ^ s) / 2) ^ (p / s) = ‖z * w‖ ^ (p / 2) * cosh (s * log (‖z‖ / ‖w‖) / 2) ^ (p / s) := by
  have ha : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hb : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [norm_mul, rpow_add_rpow_cosh _ _ s ha hb,
    show 2 * (‖z‖ * ‖w‖) ^ (s / 2) * cosh (s * log (‖z‖ / ‖w‖) / 2) / 2
      = (‖z‖ * ‖w‖) ^ (s / 2) * cosh (s * log (‖z‖ / ‖w‖) / 2) by ring,
    mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity)]
  congr 2
  field_simp

/-- Lemma lift for `G_λ`: `G_λ(z,w) = |zw|^q Γ_λ(log|z/w|, arg zw)` for `z, w ≠ 0`. -/
theorem lift_lam (p s lam : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    Glam p s lam z w = ‖z * w‖ ^ (p / 2) * GamLam p s lam (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) := by
  have hG := lift_pointwise p s hp1 hp2 hs z w hz hw
  have hX := second_term p s hs hz hw
  have hGL : GamLam p s lam (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) =
      lam * Gam p s (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) + (lam - 1) * cosh (s * log (‖z‖ / ‖w‖) / 2) ^ (p / s) := by
    simp only [GamLam, Gam]; ring
  rw [hGL]
  unfold Glam
  linear_combination lam * hG + (lam - 1) * hX

/-! ### `Γ_λ` through `cos t` (for continuity off the slit) -/

/-- `Γ_λ` written with `c = cos t`. -/
noncomputable def GamLamc (p s lam y c : ℝ) : ℝ :=
  lam * ((cosh y + c) / (1 + cos (π / p))) ^ (p / 2) - cosh (s * y / 2) ^ (p / s)

theorem gamLam_eq_c {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (y t : ℝ) :
    GamLam p s lam y t = GamLamc p s lam y (cos t) := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD := (denom_pos p hp1 hp2).le
  have hu : 0 ≤ cosh y + cos t := by nlinarith [one_le_cosh y, neg_one_le_cos t]
  simp only [GamLam, GamLamc, h2]
  rw [div_rpow hu hD]

theorem continuous_gamLamc_comp {α : Type*} [TopologicalSpace α] {p s lam : ℝ} (hp : 0 < p) (hs : 0 < s)
    {f h : α → ℝ} (hf : Continuous f) (hh : Continuous h) : Continuous fun x => GamLamc p s lam (f x) (h x) := by
  unfold GamLamc
  apply Continuous.sub
  · exact continuous_const.mul ((((continuous_cosh.comp hf).add hh).div_const _).rpow_const
      fun _ => Or.inr (by linarith))
  · exact (continuous_cosh.comp ((continuous_const.mul hf).div_const 2)).rpow_const
      fun _ => Or.inr (div_nonneg hp.le hs.le)

/-- On `T`: `G_λ(g₁ e^{Y/2}, ζ e^{-Y/2}) = |g|^q Γ_λ(Re Y + log|g|, arg g)` (`G_lift`, `λ = 1`). -/
theorem Glam_lift {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {g g1 : Polynomial ℂ}
    (hg : ∀ ζ, g.eval ζ = ζ * g1.eval ζ) (y : ℂ) {θ : ℝ} (hne : g.eval (unitPt θ) ≠ 0) :
    Glam p s lam (g1.eval (unitPt θ) * Complex.exp (1 / 2 * y)) (unitPt θ * Complex.exp (-1 / 2 * y)) =
      ‖g.eval (unitPt θ)‖ ^ (p / 2) *
        GamLamc p s lam (y.re + log ‖g.eval (unitPt θ)‖) ((g.eval (unitPt θ)).re / ‖g.eval (unitPt θ)‖) := by
  set e := unitPt θ with he_def
  have he : ‖e‖ = 1 := norm_unitPt θ
  have hg1 : g1.eval e ≠ 0 := by intro h; apply hne; rw [hg, h, mul_zero]
  have hz : g1.eval e * Complex.exp (1 / 2 * y) ≠ 0 := mul_ne_zero hg1 (Complex.exp_ne_zero _)
  have hw : e * Complex.exp (-1 / 2 * y) ≠ 0 := mul_ne_zero (unitPt_ne_zero θ) (Complex.exp_ne_zero _)
  have hexp : Complex.exp (1 / 2 * y) * Complex.exp (-1 / 2 * y) = 1 := by
    rw [← Complex.exp_add, show 1 / 2 * y + -1 / 2 * y = 0 by ring, Complex.exp_zero]
  have hprod : g1.eval e * Complex.exp (1 / 2 * y) * (e * Complex.exp (-1 / 2 * y)) = g.eval e := by
    rw [hg]; linear_combination (g1.eval e * e) * hexp
  have hng : ‖g.eval e‖ = ‖g1.eval e‖ := by rw [hg, norm_mul, he, one_mul]
  have hre1 : (1 / 2 * y).re = y.re / 2 := by simp [Complex.mul_re]; ring
  have hre2 : (-1 / 2 * y).re = -(y.re / 2) := by simp [Complex.mul_re]; ring
  have hratio : ‖g1.eval e * Complex.exp (1 / 2 * y)‖ / ‖e * Complex.exp (-1 / 2 * y)‖ =
      ‖g.eval e‖ * Real.exp y.re := by
    rw [norm_mul, norm_mul, he, one_mul, Complex.norm_exp, Complex.norm_exp, hre1, hre2, hng, mul_div_assoc,
      ← Real.exp_sub]
    congr 2
    ring
  rw [lift_lam p s lam hp1 hp2 hs hz hw, hprod, hratio,
    Real.log_mul (norm_ne_zero_iff.mpr hne) (Real.exp_pos _).ne', Real.log_exp, gamLam_eq_c hp1 hp2,
    cos_arg_eq _ hne, add_comm (log _)]

/-! ### (b2) λ-L1: the proof with `Γ_λ, G_λ, M_λ, m_λ` -/

/-- Rescaling: some `ρ ∈ (0,1)` keeps `∫ M(g(ρ e^{iθ})) < 0` and puts no root of `g` on the circle of radius `ρ`. -/
theorem exists_rescale_lam {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (g : Polynomial ℂ)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (unitPt θ)) < 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ (∀ θ : ℝ, g.eval ((ρ : ℂ) * unitPt θ) ≠ 0) ∧
      ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval ((ρ : ℂ) * unitPt θ)) < 0 := by
  have hM := LamCole.Mlam_continuous hp1 hp2 hs hsS hlam
  set Φ := fun ρ : ℝ => ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval ((ρ : ℂ) * unitPt θ)) with hΦ
  have hΦc : Continuous Φ := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hM.comp ((Polynomial.continuous g).comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      (continuous_unitPt.comp continuous_snd)))
  have hΦ1 : Φ 1 < 0 := by simpa [hΦ] using hneg
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.eventually_nhds_iff.mp ((hΦc.tendsto 1).eventually (gt_mem_nhds hΦ1))
  have hg : g ≠ 0 := by
    rintro rfl
    simp [LamCole.Mlam, zero_rpow (show (p / 2 : ℝ) ≠ 0 by positivity)] at hneg
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

theorem not_discIneqLam_of_nozero (hsel : SelStmt) {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (g g1 : Polynomial ℂ) (hg : ∀ ζ, g.eval ζ = ζ * g1.eval ζ)
    (hnz : ∀ θ, g.eval (unitPt θ) ≠ 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (unitPt θ)) < 0) : ¬ DiscIneqLam p s lam := by
  intro hD
  have hp : 0 < p := by linarith
  have hgc : Continuous fun θ => g.eval (unitPt θ) := (Polynomial.continuous g).comp continuous_unitPt
  have hlogc : Continuous fun θ => Real.log ‖g.eval (unitPt θ)‖ :=
    hgc.norm.log fun θ => norm_ne_zero_iff.mpr (hnz θ)
  obtain ⟨Lb, hLb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hlogc.continuousOn
  obtain ⟨R0, hR0⟩ := LamCole.exists_mlam_min hp1 hp2 hs hsS hlam
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun θ v => ‖g.eval (unitPt θ)‖ ^ (p / 2) *
      GamLamc p s lam (v + Real.log ‖g.eval (unitPt θ)‖) ((g.eval (unitPt θ)).re / ‖g.eval (unitPt θ)‖) := ⟨_, rfl⟩
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun x : ℝ × ℝ => g.eval (unitPt x.1) := hgc.comp continuous_fst
    have h2 : Continuous fun x : ℝ × ℝ => Real.log ‖g.eval (unitPt x.1)‖ := hlogc.comp continuous_fst
    have h3 : Continuous fun x : ℝ × ℝ => (g.eval (unitPt x.1)).re / ‖g.eval (unitPt x.1)‖ :=
      (Complex.continuous_re.comp h1).div h1.norm fun x => norm_ne_zero_iff.mpr (hnz x.1)
    have h4 := (h1.norm.rpow_const (p := p / 2) fun _ => Or.inr (by linarith)).mul
      (continuous_gamLamc_comp (lam := lam) hp hs (continuous_snd.add h2) h3)
    rw [hFdef]
    exact h4
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ → ℝ, μ = fun θ => LamCole.Mlam p s lam (g.eval (unitPt θ)) := ⟨_, rfl⟩
  have hμc : Continuous μ := by rw [hμdef]; exact (LamCole.Mlam_continuous hp1 hp2 hs hsS hlam).comp hgc
  have hFμ : ∀ θ y, F θ (y - Real.log ‖g.eval (unitPt θ)‖) =
      ‖g.eval (unitPt θ)‖ ^ (p / 2) * GamLam p s lam y (Complex.arg (g.eval (unitPt θ))) := by
    intro θ y
    rw [hFdef]
    dsimp only
    rw [sub_add_cancel, gamLam_eq_c hp1 hp2, cos_arg_eq _ (hnz θ)]
  have hmin : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-(R0 + Lb)) (R0 + Lb), F θ v = μ θ := by
    intro θ hθ
    obtain ⟨y0, hy0, hGy0, -⟩ := hR0 (Complex.arg (g.eval (unitPt θ)))
    have hL := abs_le.mp (by simpa [Real.norm_eq_abs] using hLb θ hθ)
    refine ⟨y0 - Real.log ‖g.eval (unitPt θ)‖, ⟨by linarith [hy0.1], by linarith [hy0.2]⟩, ?_⟩
    rw [hFμ, hGy0, hμdef]
    simp only [LamCole.Mlam]
  have hle : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, μ θ ≤ F θ v := by
    intro θ _ v
    rw [hμdef]
    simp only [LamCole.Mlam]
    have h := hFμ θ (v + Real.log ‖g.eval (unitPt θ)‖)
    rw [add_sub_cancel_right] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (LamCole.mlam_le hp1 hp2 hs hsS hlam _ _) (by positivity)
  have hneg' : (∫ θ in (0 : ℝ)..(2 * π), μ θ) < 0 := by rw [hμdef]; exact hneg
  obtain ⟨c, hc⟩ := hsel F hFc μ hμc (R0 + Lb) hmin hle (-(∫ θ in (0 : ℝ)..(2 * π), μ θ) / 2) (by linarith)
  set Y := toZ c + toW c with hYdef
  -- the analytic pair: its integral is negative
  obtain ⟨zf, hzf⟩ : ∃ zf : ℝ → ℂ, zf = fun θ => g1.eval (unitPt θ) * Complex.exp (1 / 2 * Y.eval (unitPt θ)) :=
    ⟨_, rfl⟩
  obtain ⟨wf, hwf⟩ : ∃ wf : ℝ → ℂ, wf = fun θ => unitPt θ * Complex.exp (-1 / 2 * Y.eval (unitPt θ)) := ⟨_, rfl⟩
  have hlift : ∀ θ, Glam p s lam (zf θ) (wf θ) = F θ (trig c θ).re := fun θ => by
    rw [hzf, hwf, hFdef]
    dsimp only
    rw [Glam_lift hp1 hp2 hs hg _ (hnz θ), re_eval_toZ_add_toW]
  have hlim_neg : ∫ θ in (0 : ℝ)..(2 * π), Glam p s lam (zf θ) (wf θ) < 0 := by
    simp_rw [hlift]; linarith
  -- polynomial truncations
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ → Polynomial ℂ, zN = fun N => g1 * expPoly N (1 / 2) Y := ⟨_, rfl⟩
  obtain ⟨wN, hwN⟩ : ∃ wN : ℕ → Polynomial ℂ, wN = fun N => Polynomial.X * expPoly N (-1 / 2) Y := ⟨_, rfl⟩
  have hevz : ∀ N θ, (zN N).eval (unitPt θ) = g1.eval (unitPt θ) * expPartial N (1 / 2 * Y.eval (unitPt θ)) :=
    fun N θ => by rw [hzN]; dsimp only; rw [Polynomial.eval_mul, eval_expPoly]
  have hevw : ∀ N θ, (wN N).eval (unitPt θ) = unitPt θ * expPartial N (-1 / 2 * Y.eval (unitPt θ)) :=
    fun N θ => by rw [hwN]; dsimp only; rw [Polynomial.eval_mul, Polynomial.eval_X, eval_expPoly]
  have hw0 : ∀ N, (wN N).coeff 0 = 0 := fun N => by rw [hwN]; exact Polynomial.coeff_X_mul_zero _
  have hD' : ∀ N, 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), Glam p s lam ((zN N).eval (unitPt θ)) ((wN N).eval (unitPt θ)) :=
    fun N => hD (zN N) (wN N) (hw0 N)
  -- dominated convergence
  have hYc : Continuous fun θ => Y.eval (unitPt θ) := (Polynomial.continuous Y).comp continuous_unitPt
  have hg1c : Continuous fun θ => g1.eval (unitPt θ) := (Polynomial.continuous g1).comp continuous_unitPt
  obtain ⟨BY, hBY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hYc.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hg1c.continuousOn
  set K := (|B1| + 1) * Real.exp |BY| with hK
  obtain ⟨Bd, hBd⟩ := ((isCompact_closedBall (0 : ℂ) K).prod (isCompact_closedBall (0 : ℂ) K)).exists_bound_of_continuousOn
    (continuous_Glam p s lam hp hs).continuousOn
  have hhalf : ∀ N : ℕ, ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ a : ℂ, ‖a‖ ≤ 1 →
      ‖expPartial N (a * Y.eval (unitPt θ))‖ ≤ Real.exp |BY| := by
    intro N θ hθ a ha
    refine (norm_expPartial_le _ _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul]
    calc ‖a‖ * ‖Y.eval (unitPt θ)‖ ≤ 1 * |BY| :=
          mul_le_mul ha ((hBY θ hθ).trans (le_abs_self _)) (norm_nonneg _) zero_le_one
      _ = |BY| := one_mul _
  have hn12 : ‖(1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have hn12' : ‖(-1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have htend : Tendsto (fun N => ∫ θ in (0 : ℝ)..(2 * π), Glam p s lam ((zN N).eval (unitPt θ)) ((wN N).eval (unitPt θ)))
      atTop (𝓝 (∫ θ in (0 : ℝ)..(2 * π), Glam p s lam (zf θ) (wf θ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun N => ?_
      exact ((continuous_Glam p s lam hp hs).comp (((Polynomial.continuous _).comp continuous_unitPt).prodMk
        ((Polynomial.continuous _).comp continuous_unitPt))).aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun θ hθ => ?_
      have hθ' : θ ∈ Icc (0 : ℝ) (2 * π) := by
        rw [uIoc_of_le (by positivity)] at hθ; exact ⟨hθ.1.le, hθ.2⟩
      refine hBd ⟨(zN N).eval (unitPt θ), (wN N).eval (unitPt θ)⟩ ⟨?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, hevz, norm_mul]
        have h1 := (hB1 θ hθ').trans (le_abs_self B1)
        have h2 := hhalf N θ hθ' _ hn12
        calc ‖g1.eval (unitPt θ)‖ * ‖expPartial N (1 / 2 * Y.eval (unitPt θ))‖ ≤ (|B1| + 1) * Real.exp |BY| :=
              mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)
          _ = K := rfl
      · rw [Metric.mem_closedBall, dist_zero_right, hevw, norm_mul, norm_unitPt, one_mul]
        have h2 := hhalf N θ hθ' _ hn12'
        calc ‖expPartial N (-1 / 2 * Y.eval (unitPt θ))‖ ≤ 1 * Real.exp |BY| := by linarith
          _ ≤ (|B1| + 1) * Real.exp |BY| :=
              mul_le_mul_of_nonneg_right (by linarith [abs_nonneg B1]) (Real.exp_pos _).le
          _ = K := rfl
    · refine Eventually.of_forall fun θ _ => ?_
      simp only [hevz, hevw, hzf, hwf]
      have hzt : Tendsto (fun N => g1.eval (unitPt θ) * expPartial N (1 / 2 * Y.eval (unitPt θ))) atTop
          (𝓝 (g1.eval (unitPt θ) * Complex.exp (1 / 2 * Y.eval (unitPt θ)))) :=
        (tendsto_expPartial _).const_mul _
      have hwt : Tendsto (fun N => unitPt θ * expPartial N (-1 / 2 * Y.eval (unitPt θ))) atTop
          (𝓝 (unitPt θ * Complex.exp (-1 / 2 * Y.eval (unitPt θ)))) :=
        (tendsto_expPartial _).const_mul _
      have hGt := ((continuous_Glam p s lam hp hs).continuousAt
        (x := (g1.eval (unitPt θ) * Complex.exp (1 / 2 * Y.eval (unitPt θ)),
          unitPt θ * Complex.exp (-1 / 2 * Y.eval (unitPt θ))))).tendsto.comp (hzt.prodMk_nhds hwt)
      simpa only [Function.comp_def] using hGt
  have := ge_of_tendsto htend (Eventually.of_forall hD')
  linarith

/-- L1 with the selection lemma as a hypothesis: a polynomial `g`, `g(0) = 0`, with `∫ M(g(e^{iθ})) < 0` refutes `DiscIneq`. -/
theorem not_discIneqLam_of_bad_disc_of_sel (hsel : SelStmt) {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) < 0) :
    ¬ DiscIneqLam p s lam := by
  obtain ⟨ρ, -, -, hnz, hnegρ⟩ := exists_rescale_lam hp1 hp2 hs hsS hlam g hneg
  set gρ := g.comp (Polynomial.C (ρ : ℂ) * Polynomial.X) with hgρdef
  have hgρ : ∀ ζ, gρ.eval ζ = g.eval ((ρ : ℂ) * ζ) := fun ζ => by
    rw [hgρdef, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hgρ0 : gρ.IsRoot 0 := by
    show gρ.eval 0 = 0
    rw [hgρ, mul_zero, hg0]
  set g1 := gρ /ₘ (Polynomial.X - Polynomial.C 0)
  have hfac : (Polynomial.X - Polynomial.C 0) * g1 = gρ := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hgρ0
  have hg : ∀ ζ, gρ.eval ζ = ζ * g1.eval ζ := fun ζ => by
    rw [← hfac, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_zero]
  refine not_discIneqLam_of_nozero hsel hp1 hp2 hs hsS hlam gρ g1 hg (fun θ => by rw [hgρ]; exact hnz θ) ?_
  simp_rw [hgρ]
  exact hnegρ

/-- L1: a polynomial `g` with `g(0) = 0` and `∫₀^{2π} M(g(e^{iθ})) dθ < 0` refutes `DiscIneq`
(for `s ≤ sec²ϑ`). With L2 (`exists_bad_disc`) and C01 this is Prop. fail (C09). -/
theorem not_discIneqLam_of_bad_disc {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam)
    (g : Polynomial ℂ) (hg0 : g.eval 0 = 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) < 0) :
    ¬ DiscIneqLam p s lam :=
  not_discIneqLam_of_bad_disc_of_sel (fun F hF μ hμ R hmin hle ε hε => exists_trig_near_min F hF μ hμ R hmin hle ε hε)
    hp1 hp2 hs hsS hlam g hg0 hneg


end LamLift

end P18
