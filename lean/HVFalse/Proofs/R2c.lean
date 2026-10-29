/-
  HVFalse/Proofs/R2c.lean - rows of the paper: (0 ≤ Re Y ≤ y₂ in the disc, l.430-433) and the
  omega step of Sec. 7 (l.640-645)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Explicit

open Complex

namespace P18.R2c

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

/-- `e^{iδ/2} e^{-iδ/2} = 1`. -/
theorem ePlus_mul_eMinus (δ : ℝ) : Explicit.ePlus δ * Explicit.eMinus δ = 1 := by
  unfold Explicit.ePlus Explicit.eMinus
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- l.430-433: "`Re Y` is `y₂` times the harmonic measure ... So `0 ≤ Re Y ≤ y₂` in the disc", for
`0 < δ < 2π`. -/
theorem C13u_ReY_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * Real.pi) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (Explicit.Yf δ ζ).re ∧ (Explicit.Yf δ ζ).re ≤ Explicit.y2 := by
  intro ζ hζ
  have hζ1 : ‖ζ‖ < 1 := by simpa using hζ
  have hpa : ‖ζ * Explicit.ePlus δ‖ < 1 := by rwa [norm_mul, norm_ePlus, mul_one]
  have hpb : ‖ζ * Explicit.eMinus δ‖ < 1 := by rwa [norm_mul, norm_eMinus, mul_one]
  have hu2 : (1 - ζ * Explicit.ePlus δ) ≠ 0 := fun h => by
    have := re_one_sub_pos hpa
    rw [h] at this
    exact lt_irrefl _ this
  have hu3 : (1 - ζ * Explicit.eMinus δ) ≠ 0 := fun h => by
    have := re_one_sub_pos hpb
    rw [h] at this
    exact lt_irrefl _ this
  obtain ⟨q, hqd⟩ : ∃ q : ℂ, q = (1 - ζ * Explicit.eMinus δ) / (1 - ζ * Explicit.ePlus δ) := ⟨_, rfl⟩
  have hq : q ≠ 0 := by rw [hqd]; exact div_ne_zero hu3 hu2
  -- `Re Y = y₂ (δ/2π + arg q/π)`
  have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hc : (1 : ℂ) / ((Real.pi : ℂ) * I) = -I / (Real.pi : ℂ) := by
    rw [div_eq_div_iff (mul_ne_zero hpi0 I_ne_zero) hpi0]
    linear_combination (Real.pi : ℂ) * Complex.I_sq
  have hRe : (Explicit.Yf δ ζ).re = Explicit.y2 * ((arg q + δ / 2) / Real.pi) := by
    unfold Explicit.Yf
    rw [← hqd, Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re, hc,
      show -I / (Real.pi : ℂ) * log q = ((1 / Real.pi : ℝ) : ℂ) * (-I * log q) by push_cast; ring,
      Complex.re_ofReal_mul]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.log_im]
    have := Real.pi_pos.ne'
    field_simp
    ring
  -- `Im(e^{iδ/2} q) = sin(δ/2)(1 - |ζ|²)/|1 - ζe^{iδ/2}|² ≥ 0`
  have ha' : Explicit.ePlus δ = exp (((δ / 2 : ℝ) : ℂ) * I) := by unfold Explicit.ePlus; rw [mul_comm]
  have hare : (Explicit.ePlus δ).re = Real.cos (δ / 2) := by rw [ha']; exact exp_ofReal_mul_I_re _
  have haim : (Explicit.ePlus δ).im = Real.sin (δ / 2) := by rw [ha']; exact exp_ofReal_mul_I_im _
  have haq : Explicit.ePlus δ * q = (Explicit.ePlus δ - ζ) / (1 - ζ * Explicit.ePlus δ) := by
    rw [hqd, ← mul_div_assoc]
    congr 1
    linear_combination (-ζ) * ePlus_mul_eMinus δ
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hcs := Real.sin_sq_add_cos_sq (δ / 2)
  have hn : ζ.re ^ 2 + ζ.im ^ 2 < 1 := by
    have h := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg ζ]
  have hIm : 0 ≤ (Explicit.ePlus δ * q).im := by
    rw [haq, Complex.div_im]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
      hare, haim]
    rw [← sub_div]
    apply div_nonneg _ (Complex.normSq_nonneg _)
    have hy := congrArg (· * ζ.im) hcs
    nlinarith [hy, mul_pos hs (by linarith : (0 : ℝ) < 1 - ζ.re ^ 2 - ζ.im ^ 2)]
  -- `Im(e^{iδ/2} q) = |q| sin(arg q + δ/2)`, so `0 ≤ arg q + δ/2 ≤ π`
  have hpolar : (Explicit.ePlus δ * q).im = ‖q‖ * Real.sin (arg q + δ / 2) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I q]
    rw [ha', mul_left_comm, ← Complex.exp_add,
      show ((δ / 2 : ℝ) : ℂ) * I + (arg q : ℂ) * I = ((arg q + δ / 2 : ℝ) : ℂ) * I by push_cast; ring,
      Complex.im_ofReal_mul, exp_ofReal_mul_I_im]
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  have hsin : 0 ≤ Real.sin (arg q + δ / 2) := by
    rw [hpolar] at hIm
    exact (mul_nonneg_iff_of_pos_left hqn).1 hIm
  have hθ1 := Complex.neg_pi_lt_arg q
  have hθ2 := Complex.arg_le_pi q
  have hlo : 0 ≤ arg q + δ / 2 := by
    by_contra h
    have h3 := Real.sin_neg_of_neg_of_neg_pi_lt (not_le.1 h) (by linarith)
    linarith
  have hhi : arg q + δ / 2 ≤ Real.pi := by
    by_contra h
    have h3 : 0 < Real.sin (arg q + δ / 2 - Real.pi) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [not_le.1 h]) (by linarith)
    rw [Real.sin_sub_pi] at h3
    linarith
  have hy2 : 0 < Explicit.y2 := by unfold Explicit.y2; norm_num
  rw [hRe]
  have h01 : 0 ≤ (arg q + δ / 2) / Real.pi := div_nonneg hlo Real.pi_pos.le
  have h11 : (arg q + δ / 2) / Real.pi ≤ 1 := (div_le_one Real.pi_pos).2 hhi
  constructor
  · exact mul_nonneg hy2.le h01
  · nlinarith


/-- Sec. 7 (l.640-645), the omega step: if `ρ'' + q²ρ ≥ 0` on `[a, b]`, `q(b - a) < π` and `ρ(a) = ρ(b) = 0`, then
`ρ ≤ 0` on `[a, b]`. The paper's route: `c(t) = cos(q(t - (a+b)/2)) > 0` solves `c'' + q²c = 0`; `ω = cρ' - c'ρ` has
`ω' = c(ρ'' + q²ρ) ≥ 0`, so `ω` is nondecreasing; `(ρ/c)' = ω/c²` has the sign of `ω`, so `ρ/c ≤ 0`. (The paper applies
this to `ρ` with `ρ'' + q²ρ = μ` a measure; this row is the `C²` case.) -/
theorem omega_step {q a b : ℝ} (hq : 0 < q) (_hab : a < b) (hlen : q * (b - a) < Real.pi) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hμ : ∀ t ∈ Set.Icc a b, 0 ≤ deriv (deriv ρ) t + q ^ 2 * ρ t)
    (ha : ρ a = 0) (hb : ρ b = 0) : ∀ t ∈ Set.Icc a b, ρ t ≤ 0 := by
  -- the comparison function `c` and its derivatives
  have hcpos : ∀ t ∈ Set.Icc a b, 0 < Real.cos (q * (t - (a + b) / 2)) := by
    intro t ht
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [ht.1, ht.2]
  have hc : ∀ t, HasDerivAt (fun s => Real.cos (q * (s - (a + b) / 2)))
      (-(q * Real.sin (q * (t - (a + b) / 2)))) t := by
    intro t
    have h := (((hasDerivAt_id' (x := t)).sub_const ((a + b) / 2)).const_mul q).cos
    convert h using 1
    ring
  have hc' : ∀ t, HasDerivAt (fun s => -(q * Real.sin (q * (s - (a + b) / 2))))
      (-(q ^ 2) * Real.cos (q * (t - (a + b) / 2))) t := by
    intro t
    have h := ((((hasDerivAt_id' (x := t)).sub_const ((a + b) / 2)).const_mul q).sin.const_mul q).neg
    convert h using 1
    ring
  have hc1 : ContDiff ℝ 1 (deriv ρ) := ContDiff.deriv' (n := 1) hρ
  have hd1 : ∀ x, HasDerivAt ρ (deriv ρ x) x := fun x => ((hρ.differentiable (by norm_num)) x).hasDerivAt
  have hd2 : ∀ x, HasDerivAt (deriv ρ) (deriv (deriv ρ) x) x :=
    fun x => ((hc1.differentiable (by norm_num)) x).hasDerivAt
  -- `ω = cρ' - c'ρ` is nondecreasing on `[a, b]`
  have hω : ∀ t, HasDerivAt (fun s => Real.cos (q * (s - (a + b) / 2)) * deriv ρ s
      - -(q * Real.sin (q * (s - (a + b) / 2))) * ρ s)
      (Real.cos (q * (t - (a + b) / 2)) * (deriv (deriv ρ) t + q ^ 2 * ρ t)) t := by
    intro t
    have h := ((hc t).mul (hd2 t)).sub ((hc' t).mul (hd1 t))
    convert h using 1
    ring
  have hωmono : MonotoneOn (fun s => Real.cos (q * (s - (a + b) / 2)) * deriv ρ s
      - -(q * Real.sin (q * (s - (a + b) / 2))) * ρ s) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun t _ => (hω t).continuousAt.continuousWithinAt
    · exact fun t _ => (hω t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hω t).deriv]
      exact mul_nonneg (hcpos t (Set.Ioo_subset_Icc_self ht)).le (hμ t (Set.Ioo_subset_Icc_self ht))
  -- `f = ρ/c` has derivative `ω/c²`
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt (fun s => ρ s / Real.cos (q * (s - (a + b) / 2)))
      ((Real.cos (q * (t - (a + b) / 2)) * deriv ρ t - -(q * Real.sin (q * (t - (a + b) / 2))) * ρ t)
        / Real.cos (q * (t - (a + b) / 2)) ^ 2) t := by
    intro t ht
    have h := (hd1 t).div (hc t) (hcpos t ht).ne'
    convert h using 1
    ring
  have hfc : ContinuousOn (fun s => ρ s / Real.cos (q * (s - (a + b) / 2))) (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  intro t ht
  by_contra hpos
  have hpos' : 0 < ρ t := not_le.1 hpos
  have hft : 0 < ρ t / Real.cos (q * (t - (a + b) / 2)) := div_pos hpos' (hcpos t ht)
  have hta : a < t := lt_of_le_of_ne ht.1 (fun h => by rw [← h, ha] at hpos'; exact lt_irrefl _ hpos')
  have htb : t < b := lt_of_le_of_ne ht.2 (fun h => by rw [h, hb] at hpos'; exact lt_irrefl _ hpos')
  obtain ⟨x1, hx1, h1⟩ := exists_hasDerivAt_eq_slope (fun s => ρ s / Real.cos (q * (s - (a + b) / 2))) _ hta
    (hfc.mono (Set.Icc_subset_Icc le_rfl ht.2)) (fun s hs => hf s ⟨hs.1.le, hs.2.le.trans ht.2⟩)
  obtain ⟨x2, hx2, h2⟩ := exists_hasDerivAt_eq_slope (fun s => ρ s / Real.cos (q * (s - (a + b) / 2))) _ htb
    (hfc.mono (Set.Icc_subset_Icc ht.1 le_rfl)) (fun s hs => hf s ⟨ht.1.trans hs.1.le, hs.2.le⟩)
  simp only [ha, hb, zero_div, sub_zero, zero_sub] at h1 h2
  have hx1m : x1 ∈ Set.Icc a b := ⟨hx1.1.le, hx1.2.le.trans ht.2⟩
  have hx2m : x2 ∈ Set.Icc a b := ⟨ht.1.trans hx2.1.le, hx2.2.le⟩
  have hc1p := pow_pos (hcpos x1 hx1m) 2
  have hc2p := pow_pos (hcpos x2 hx2m) 2
  have hw1 : 0 < Real.cos (q * (x1 - (a + b) / 2)) * deriv ρ x1 - -(q * Real.sin (q * (x1 - (a + b) / 2))) * ρ x1 := by
    have hs : 0 < ρ t / Real.cos (q * (t - (a + b) / 2)) / (t - a) := div_pos hft (by linarith)
    rw [← h1] at hs
    exact (div_pos_iff_of_pos_right hc1p).1 hs
  have hw2 : Real.cos (q * (x2 - (a + b) / 2)) * deriv ρ x2 - -(q * Real.sin (q * (x2 - (a + b) / 2))) * ρ x2 < 0 := by
    have hs : -(ρ t / Real.cos (q * (t - (a + b) / 2))) / (b - t) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [← h2] at hs
    exact lt_of_not_ge fun hge => (not_lt.2 (div_nonneg hge hc2p.le)) hs
  have := hωmono hx1m hx2m (hx1.2.le.trans hx2.1.le)
  simp only at this
  linarith

end P18.R2c
