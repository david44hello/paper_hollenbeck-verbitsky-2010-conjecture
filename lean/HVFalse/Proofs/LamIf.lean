/-
  HVFalse/Proofs/LamIf.lean - Prop. 14 (C22a): (HV) with λ^{1/p} C_{s,p} ⇔ a q-subtrigonometric φ ≤ m_λ exists
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  "if": φ q-subtrigonometric means V_φ(ζ) = |ζ|^q φ(arg ζ) is subharmonic (the definition). φ is continuous (C06b), so V_φ
  is continuous (on the negative axis φ(arg ζ) = φ(arg(-ζ) + π)). Take a polynomial disc (z, w) with w(0) = 0. Then
  V_φ∘(zw) is sub-mean on the unit circle (VComp.comp_submean, proved; no Demailly 5.11), so ∫ V_φ(zw) ≥ 2π V_φ(0) = 0. Also V_φ(zw) ≤ G_λ(z, w) pointwise (lift_lam
  where zw ≠ 0, the ε-limit where zw = 0). Hence ∫ G_λ∘h ≥ 0, i.e. (HV) with λ^{1/p} C (discs_lam).
  "only if" and the assembled C22a: ColeHom.truec_iff' (Cole's Thm 2.1 + the paper's homogeneity proof).
-/
import HVFalse.Proofs.LamLift
import HVFalse.Proofs.ThmBIf
import HVFalse.Proofs.TrigCont
import HVFalse.Proofs.VComp

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace LamIf

open VComp

theorem Vfun_ge {q : ℝ} {φ : ℝ → ℝ} {B : ℝ} (hB : ∀ t ∈ Icc (-π) π, ‖φ t‖ ≤ B) (ζ : ℂ) :
    -(B * ‖ζ‖ ^ q) ≤ Vfun q φ ζ := by
  unfold Vfun
  have h1 := hB _ ⟨(Complex.neg_pi_lt_arg ζ).le, Complex.arg_le_pi ζ⟩
  rw [Real.norm_eq_abs] at h1
  have h2 : 0 ≤ ‖ζ‖ ^ q := rpow_nonneg (norm_nonneg ζ) _
  have h3 := mul_le_mul_of_nonneg_left (abs_le.mp h1).1 h2
  linarith

/-- `V_φ(zw) ≤ G_λ(z,w)` everywhere when `φ ≤ Γ_λ` (C16c with `λ`). -/
theorem V_le_Glam {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hle : ∀ y t : ℝ, φ t ≤ GamLam p s lam y t) (z w : ℂ) : Vfun (p / 2) φ (z * w) ≤ LamLift.Glam p s lam z w := by
  have hp : 0 < p := by linarith
  have hq : (p / 2 : ℝ) ≠ 0 := by positivity
  by_cases h : z ≠ 0 ∧ w ≠ 0
  · rw [LamLift.lift_lam p s lam hp1 hp2 hs h.1 h.2]
    unfold Vfun
    exact mul_le_mul_of_nonneg_left (hle _ _) (by positivity)
  have hzw : z * w = 0 := by
    rw [not_and_or, not_not, not_not] at h
    rcases h with h | h <;> simp [h]
  have hV : Vfun (p / 2) φ (z * w) = 0 := by
    unfold Vfun; rw [hzw, norm_zero, zero_rpow hq, zero_mul]
  rw [hV]
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -π) (b := π)).exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨δz, hδz, hz⟩ := exists_add_ofReal_ne_zero z
  obtain ⟨δw, hδw, hw⟩ := exists_add_ofReal_ne_zero w
  have hpath : Continuous fun ε : ℝ => ((z + ε, w + ε) : ℂ × ℂ) :=
    (continuous_const.add Complex.continuous_ofReal).prodMk (continuous_const.add Complex.continuous_ofReal)
  have hF : Tendsto (fun ε : ℝ => LamLift.Glam p s lam (z + ε) (w + ε)) (𝓝[>] 0)
      (𝓝 (LamLift.Glam p s lam z w)) := by
    have := ((LamLift.continuous_Glam p s lam hp hs).comp hpath).tendsto 0
    simp only [Function.comp_def, Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun ε : ℝ => -(B * ‖(z + ε) * (w + ε)‖ ^ (p / 2))) (𝓝[>] 0) (𝓝 0) := by
    have hc' : Continuous fun ε : ℝ => -(B * ‖(z + ε) * (w + ε)‖ ^ (p / 2)) :=
      (continuous_const.mul (((continuous_const.add Complex.continuous_ofReal).mul
        (continuous_const.add Complex.continuous_ofReal)).norm.rpow_const fun _ => Or.inr (by positivity))).neg
    have := hc'.tendsto 0
    simp only [Complex.ofReal_zero, add_zero, hzw, norm_zero, zero_rpow hq, mul_zero, neg_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto hg hF ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδz hδw)] with ε hε
  have hz' := hz ε hε.1 (hε.2.trans_le (min_le_left _ _))
  have hw' := hw ε hε.1 (hε.2.trans_le (min_le_right _ _))
  refine (Vfun_ge hB _).trans ?_
  rw [LamLift.lift_lam p s lam hp1 hp2 hs hz' hw']
  unfold Vfun
  exact mul_le_mul_of_nonneg_left (hle _ _) (by positivity)

/-- `∫₀^{2π} V_φ(g(e^{iθ})) dθ ≥ 0` for a polynomial `g` with `g(0) = 0` (sub-mean value at 0 of `V_φ∘g`,
VComp.comp_submean; no textbook axiom). -/
theorem integral_V_nonneg {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hc : Continuous φ) (hφ : QSubtrig q φ)
    (g : Polynomial ℂ) (hg : g.eval 0 = 0) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π), Vfun q φ (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hq : 0 < q := by linarith
  have h := VComp.comp_submean hq0 hq1 hc hφ (h := fun l => g.eval l) g.differentiable 0 one_pos
  simp only [hg, VComp.Vfun_zero hq] at h
  rw [circleAverage_def, smul_eq_mul] at h
  simp only [circleMap_zero, Complex.ofReal_one, one_mul] at h
  exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr two_pi_pos)).mp h

/-- **Prop. 14 "if"**: a feasible `λ` gives `∫ G_λ∘h ≥ 0` for every polynomial disc. -/
theorem lam_if {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hf : LamFeasible p s lam) :
    LamLift.DiscIneqLam p s lam := by
  obtain ⟨φ, hφ, hle⟩ := hf
  have hq : 0 < p / 2 := by linarith
  have hc : Continuous φ := TrigCont.qsubtrig_continuous (by linarith) (by linarith) hφ
  intro z w hw
  have hw0 : w.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hw
  have hg : (z * w).eval 0 = 0 := by rw [Polynomial.eval_mul, hw0, mul_zero]
  have hV := integral_V_nonneg (by linarith) (by linarith) hc hφ (z * w) hg
  have hp0 : 0 < p := by linarith
  have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by fun_prop
  have hcG : Continuous (fun θ : ℝ => LamLift.Glam p s lam (z.eval (Complex.exp ((θ : ℂ) * Complex.I)))
      (w.eval (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    (LamLift.continuous_Glam p s lam hp0 hs).comp ((z.continuous.comp he).prodMk (w.continuous.comp he))
  have hcV : Continuous (fun θ : ℝ => Vfun (p / 2) φ ((z * w).eval (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    (Vfun_continuous hq hc hφ.1).comp ((z * w).continuous.comp he)
  refine le_trans hV (intervalIntegral.integral_mono_on two_pi_pos.le (hcV.intervalIntegrable _ _)
    (hcG.intervalIntegrable _ _) (fun θ _ => ?_))
  rw [Polynomial.eval_mul]
  exact V_le_Glam hp1 hp2 hs hc hle _ _

end LamIf

end P18
