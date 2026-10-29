/-
  HVFalse/Proofs/R2b.lean - the explicit map g = z·w is starlike (Re(ζg'/g) > 0 in the disc)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Explicit

open Complex

namespace P18.R2b

/-- `Re(ω/(1-ω)) > -1/2` for `|ω| < 1`. -/
theorem re_frac_gt {ω : ℂ} (hω : ‖ω‖ < 1) : -1 / 2 < (ω / (1 - ω)).re := by
  have hn : ω.re ^ 2 + ω.im ^ 2 < 1 := by
    have h := Complex.sq_norm ω
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg ω]
  have hre : ω.re < 1 := by nlinarith [sq_nonneg ω.im]
  have hN : 0 < (1 - ω.re) ^ 2 + ω.im ^ 2 := by nlinarith [sq_nonneg ω.im]
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  rw [← add_div, lt_div_iff₀ (by nlinarith)]
  nlinarith

theorem norm_ePlus (δ : ℝ) : ‖Explicit.ePlus δ‖ = 1 := by
  unfold Explicit.ePlus
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem norm_eMinus (δ : ℝ) : ‖Explicit.eMinus δ‖ = 1 := by
  unfold Explicit.eMinus
  rw [show -(I * ((δ / 2 : ℝ) : ℂ)) = ((-(δ / 2) : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- `1 - ω` has positive real part for `|ω| < 1`. -/
theorem re_one_sub_pos {ω : ℂ} (hω : ‖ω‖ < 1) : 0 < (1 - ω).re := by
  rw [Complex.sub_re, Complex.one_re]
  linarith [Complex.re_le_norm ω]

theorem aA_pos : 0 < Explicit.aA := by
  unfold Explicit.aA Explicit.tS
  positivity

theorem aB_pos : 0 < Explicit.aB := by
  unfold Explicit.aB Explicit.bA Explicit.tS
  apply div_pos _ Real.pi_pos
  nlinarith [Real.pi_gt_three]

theorem aC_pos : 0 < Explicit.aC := by
  have h : Explicit.aA + Explicit.aB = 4 / 3 + 136 / 10000 / Real.pi := by
    unfold Explicit.aA Explicit.aB Explicit.bA Explicit.tS
    have := Real.pi_pos.ne'
    field_simp
    ring
  have h2 : 136 / 10000 / Real.pi < 1 / 100 := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  unfold Explicit.aC
  linarith

/-- The logarithm of `Π`. -/
noncomputable def M (δ : ℝ) (ξ : ℂ) : ℂ :=
  log (1 + ξ) * (-(Explicit.aC : ℂ) / 2) - log (1 - ξ * Explicit.ePlus δ) * ((Explicit.aA : ℂ) / 2)
    - log (1 - ξ * Explicit.eMinus δ) * ((Explicit.aB : ℂ) / 2)

/-- `E = e^{iγ/2}`. -/
noncomputable def E (δ : ℝ) : ℂ := exp (I * ((Explicit.gam δ / 2 : ℝ) : ℂ))

/-- On the disc, `g = zw = ξ E² e^{2M}` (the factors `e^{±Y/2}` cancel). -/
theorem g_eq (δ : ℝ) {ξ : ℂ} (hξ : ‖ξ‖ < 1) :
    Explicit.zf δ ξ * Explicit.wf δ ξ = ξ * E δ * E δ * exp (M δ ξ) * exp (M δ ξ) := by
  have h1 : (1 + ξ) ≠ 0 := by
    intro h
    have : (1 + ξ).re = 0 := by rw [h]; rfl
    rw [Complex.add_re, Complex.one_re] at this
    have hr := Complex.re_le_norm (-ξ)
    rw [Complex.neg_re, norm_neg] at hr
    linarith
  have hp : ‖ξ * Explicit.ePlus δ‖ < 1 := by rwa [norm_mul, norm_ePlus, mul_one]
  have hm : ‖ξ * Explicit.eMinus δ‖ < 1 := by rwa [norm_mul, norm_eMinus, mul_one]
  have h2 : (1 - ξ * Explicit.ePlus δ) ≠ 0 := fun h => by
    have := re_one_sub_pos hp
    rw [h] at this
    exact lt_irrefl _ this
  have h3 : (1 - ξ * Explicit.eMinus δ) ≠ 0 := fun h => by
    have := re_one_sub_pos hm
    rw [h] at this
    exact lt_irrefl _ this
  have hPi : Explicit.Pi δ ξ = exp (M δ ξ) := by
    unfold Explicit.Pi M
    rw [cpow_def_of_ne_zero h1, cpow_def_of_ne_zero h2, cpow_def_of_ne_zero h3, ← exp_add, ← exp_sub]
    congr 1
    ring
  have hY : exp (Explicit.Yf δ ξ / 2) * exp (-(Explicit.Yf δ ξ) / 2) = 1 := by
    rw [← exp_add]
    ring_nf
    exact exp_zero
  unfold Explicit.zf Explicit.wf
  rw [hPi]
  unfold E
  linear_combination (ξ * exp (I * ((Explicit.gam δ / 2 : ℝ) : ℂ)) * exp (I * ((Explicit.gam δ / 2 : ℝ) : ℂ))
    * exp (M δ ξ) * exp (M δ ξ)) * hY

/-- l.462-464: "`Re(ξg'/g) = 1 + Σ_k α_k Re(ω_k/(1-ω_k)) > 1 - ½Σ_k α_k = 0`, so `g` is starlike", for
`g = zw` and every `δ`. -/
theorem C13t_starlike (δ : ℝ) : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, ζ ≠ 0 →
    0 < (ζ * deriv (fun ξ => Explicit.zf δ ξ * Explicit.wf δ ξ) ζ / (Explicit.zf δ ζ * Explicit.wf δ ζ)).re := by
  intro ζ hζ hζ0
  have hζ1 : ‖ζ‖ < 1 := by simpa using hζ
  set ep := Explicit.ePlus δ with hep
  set em := Explicit.eMinus δ with hem
  have hp : ‖ζ * ep‖ < 1 := by rwa [norm_mul, norm_ePlus, mul_one]
  have hm : ‖ζ * em‖ < 1 := by rwa [norm_mul, norm_eMinus, mul_one]
  have hneg : ‖-ζ‖ < 1 := by rwa [norm_neg]
  have hs1 : (1 + ζ) ∈ slitPlane := Or.inl (by
    rw [Complex.add_re, Complex.one_re]
    have hr := Complex.re_le_norm (-ζ)
    rw [Complex.neg_re, norm_neg] at hr
    linarith)
  have hs2 : (1 - ζ * ep) ∈ slitPlane := Or.inl (re_one_sub_pos hp)
  have hs3 : (1 - ζ * em) ∈ slitPlane := Or.inl (re_one_sub_pos hm)
  have hu1 : (1 + ζ) ≠ 0 := slitPlane_ne_zero hs1
  have hu2 : (1 - ζ * ep) ≠ 0 := slitPlane_ne_zero hs2
  have hu3 : (1 - ζ * em) ≠ 0 := slitPlane_ne_zero hs3
  -- the derivative of `M`
  have L1 : HasDerivAt (fun ξ => log (1 + ξ)) (1 / (1 + ζ)) ζ :=
    ((hasDerivAt_id ζ).const_add 1).clog hs1
  have L2 : HasDerivAt (fun ξ => log (1 - ξ * ep)) (-(1 * ep) / (1 - ζ * ep)) ζ :=
    (((hasDerivAt_id ζ).mul_const ep).const_sub 1).clog hs2
  have L3 : HasDerivAt (fun ξ => log (1 - ξ * em)) (-(1 * em) / (1 - ζ * em)) ζ :=
    (((hasDerivAt_id ζ).mul_const em).const_sub 1).clog hs3
  set M' : ℂ := 1 / (1 + ζ) * (-(Explicit.aC : ℂ) / 2) - -(1 * ep) / (1 - ζ * ep) * ((Explicit.aA : ℂ) / 2)
    - -(1 * em) / (1 - ζ * em) * ((Explicit.aB : ℂ) / 2) with hM'
  have hMd : HasDerivAt (M δ) M' ζ :=
    ((L1.mul_const _).sub (L2.mul_const _)).sub (L3.mul_const _)
  have hE := hMd.cexp
  have hG : HasDerivAt (fun ξ => id ξ * E δ * E δ * exp (M δ ξ) * exp (M δ ξ))
      ((1 * E δ * E δ * exp (M δ ζ) + id ζ * E δ * E δ * (exp (M δ ζ) * M')) * exp (M δ ζ)
        + id ζ * E δ * E δ * exp (M δ ζ) * (exp (M δ ζ) * M')) ζ :=
    ((((hasDerivAt_id ζ).mul_const (E δ)).mul_const (E δ)).mul hE).mul hE
  -- `g = G` near `ζ`
  have hev : (fun ξ => Explicit.zf δ ξ * Explicit.wf δ ξ) =ᶠ[nhds ζ]
      (fun ξ => id ξ * E δ * E δ * exp (M δ ξ) * exp (M δ ξ)) :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hζ) fun ξ hξ => by
      simpa using g_eq δ (by simpa using hξ)
  rw [hev.deriv_eq, hG.deriv, g_eq δ hζ1]
  have hEne : E δ ≠ 0 := exp_ne_zero _
  have hX : exp (M δ ζ) ≠ 0 := exp_ne_zero _
  have hkey : ζ * ((1 * E δ * E δ * exp (M δ ζ) + id ζ * E δ * E δ * (exp (M δ ζ) * M')) * exp (M δ ζ)
      + id ζ * E δ * E δ * exp (M δ ζ) * (exp (M δ ζ) * M'))
      / (ζ * E δ * E δ * exp (M δ ζ) * exp (M δ ζ))
      = 1 + (Explicit.aC : ℂ) * (-ζ / (1 - -ζ)) + (Explicit.aA : ℂ) * (ζ * ep / (1 - ζ * ep))
        + (Explicit.aB : ℂ) * (ζ * em / (1 - ζ * em)) := by
    have h1' : (1 - -ζ) ≠ 0 := by rwa [sub_neg_eq_add]
    rw [hM']
    simp only [id]
    field_simp
    ring
  rw [hkey]
  simp only [Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
  have b1 := re_frac_gt hneg
  have b2 := re_frac_gt hp
  have b3 := re_frac_gt hm
  have hsum : Explicit.aA + Explicit.aB + Explicit.aC = 2 := by unfold Explicit.aC; ring
  nlinarith [aA_pos, aB_pos, aC_pos]

end P18.R2b
