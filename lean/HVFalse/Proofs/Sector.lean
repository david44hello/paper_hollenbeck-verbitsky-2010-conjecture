/-
  HVFalse/Proofs/Sector.lean - homogeneous subharmonic functions: sector comparison and trig convexity (paper l.235-245)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Why this file exists: the paper (l.244-245) gets q-subtrigonometric ⇒ trigonometrically convex from HKV2003 Prop. 3.3,
  which ASSUMES continuity (the paper shows it just before, l.242-243). We prove the direction we need.
  Maximum principle (part A): for a real upper semicontinuous `v` with the sub-mean-value property and a `w` with the mean-value
  property on discs inside `U`, a maximum of `v - w + δ‖z‖²` at an interior point contradicts
  `circleAverage ‖·‖² c ρ = ‖c‖² + ρ² > ‖c‖²`; so `v - w ≤ 0` on `K` when it is `≤ 0` off the interior.
-/
import HVFalse.Defs.Potential
import HVFalse.Defs.Basic

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace Sector

/-- The circle average of `‖z‖²`: `‖c‖² + ρ²`. -/
theorem circleAverage_normSq (c : ℂ) (ρ : ℝ) : circleAverage (fun z => ‖z‖ ^ 2) c ρ = ‖c‖ ^ 2 + ρ ^ 2 := by
  have h : ∀ θ : ℝ, ‖circleMap c ρ θ‖ ^ 2 = (‖c‖ ^ 2 + ρ ^ 2) + (2 * ρ * c.re) * cos θ + (2 * ρ * c.im) * sin θ := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
    simp only [circleMap, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    nlinarith [sin_sq_add_cos_sq θ]
  rw [circleAverage_def]
  simp_rw [h]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos, integral_sin]
  simp only [sin_two_pi, sin_zero, cos_two_pi, cos_zero, sub_zero, sub_self, mul_zero, add_zero, smul_eq_mul]
  field_simp

/-- **Maximum principle** (perturbed). `v` real, upper semicontinuous, sub-mean-value on every circle; `w` continuous on the
compact `K ⊆ closedBall 0 R` and mean-value on discs inside `U`. If every point of `K` where `v - w > 0` has a closed disc
around it inside `K ∩ U`, then `v - w ≤ 0` on `K`. -/
theorem max_principle {v w : ℂ → ℝ} {K U : Set ℂ} {R : ℝ}
    (hK : IsCompact K) (hKR : K ⊆ closedBall 0 R)
    (hv : UpperSemicontinuous v) (hsub : ∀ c r, 0 < r → v c ≤ circleAverage v c r)
    (hvint : ∀ c r, CircleIntegrable v c r) (hwc : ContinuousOn w K)
    (hw : ∀ c ρ, 0 < ρ → closedBall c ρ ⊆ U → circleAverage w c ρ = w c ∧ CircleIntegrable w c ρ)
    (hint : ∀ z ∈ K, 0 < v z - w z → ∃ ρ > 0, closedBall z ρ ⊆ K ∩ U) :
    ∀ z ∈ K, v z - w z ≤ 0 := by
  intro z0 hz0
  by_contra hneg
  push Not at hneg
  set m0 := v z0 - w z0 with hm0
  have hR0 : 0 ≤ R := by
    have := hKR hz0; rw [mem_closedBall, dist_zero_right] at this; linarith [norm_nonneg z0]
  set δ := m0 / (2 * (R ^ 2 + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδR : δ * R ^ 2 < m0 := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  set u : ℂ → ℝ := fun z => v z + (-w z + δ * ‖z‖ ^ 2) with hu
  have husc : UpperSemicontinuousOn u K :=
    (hv.upperSemicontinuousOn K).add (ContinuousOn.upperSemicontinuousOn
      (hwc.neg.add (continuousOn_const.mul (continuous_norm.pow 2).continuousOn)))
  obtain ⟨c, hcK, hmax⟩ := husc.exists_isMaxOn ⟨z0, hz0⟩ hK
  have hnorm : ∀ z ∈ K, ‖z‖ ^ 2 ≤ R ^ 2 := by
    intro z hz
    have := hKR hz; rw [mem_closedBall, dist_zero_right] at this
    exact pow_le_pow_left₀ (norm_nonneg z) this 2
  have huz0 : m0 ≤ u z0 := by simp only [hu]; nlinarith [sq_nonneg ‖z0‖]
  have hc_pos : 0 < v c - w c := by
    have h1 : u z0 ≤ u c := hmax hz0
    have h2 : δ * ‖c‖ ^ 2 ≤ δ * R ^ 2 := mul_le_mul_of_nonneg_left (hnorm c hcK) hδ0.le
    simp only [hu] at h1 h2 huz0 ⊢; linarith
  obtain ⟨ρ, hρ, hball⟩ := hint c hcK hc_pos
  obtain ⟨hwmean, hwint⟩ := hw c ρ hρ (hball.trans inter_subset_right)
  have hsph : ∀ z ∈ sphere c |ρ|, z ∈ K := by
    intro z hz
    rw [abs_of_pos hρ] at hz
    exact (hball (sphere_subset_closedBall hz)).1
  have hnint : CircleIntegrable (fun z => ‖z‖ ^ 2) c ρ :=
    (continuous_norm.pow 2).continuousOn.circleIntegrable'
  have hnint' : CircleIntegrable (δ • fun z => ‖z‖ ^ 2) c ρ := hnint.const_smul
  have huint : CircleIntegrable u c ρ :=
    (hvint c ρ).add ((hwint.neg).add hnint')
  have hle : circleAverage u c ρ ≤ u c :=
    circleAverage_mono_on_of_le_circle huint (fun z hz => hmax (hsph z hz))
  have hsplit : circleAverage u c ρ = circleAverage v c ρ - circleAverage w c ρ + δ * (‖c‖ ^ 2 + ρ ^ 2) := by
    have e1 : u = (v + δ • (fun z => ‖z‖ ^ 2)) - w := by
      funext z; simp only [hu, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, circleAverage_sub ((hvint c ρ).add hnint') hwint, circleAverage_add (hvint c ρ) hnint',
      circleAverage_smul, circleAverage_normSq, smul_eq_mul]
    ring
  have hvc := hsub c ρ hρ
  rw [hsplit, hwmean] at hle
  simp only [hu] at hle
  nlinarith [sq_pos_of_pos hρ]

/-- `trunc n x ≥ -n` for `x ≠ ⊤`. -/
theorem trunc_ge {x : EReal} (hx : x ≠ ⊤) (n : ℕ) : -(n : ℝ) ≤ trunc n x := by
  unfold trunc
  have hm : -(n : EReal) ≤ max x (-(n : EReal)) := le_max_right _ _
  have hne : max x (-(n : EReal)) ≠ ⊤ := max_ne_top hx (by simp)
  have hnb : max x (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hm
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne hnb]
  simpa using hm

/-- `x ≤ trunc n x` (as `EReal`) for `x ≠ ⊤`. -/
theorem le_trunc {x : EReal} (hx : x ≠ ⊤) (n : ℕ) : x ≤ ((trunc n x : ℝ) : EReal) := by
  unfold trunc
  have hm : -(n : EReal) ≤ max x (-(n : EReal)) := le_max_right _ _
  have hne : max x (-(n : EReal)) ≠ ⊤ := max_ne_top hx (by simp)
  have hnb : max x (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) hm
  rw [EReal.coe_toReal hne hnb]
  exact le_max_left _ _

/-- The truncation of a subharmonic function is upper semicontinuous. -/
theorem trunc_usc {V : ℂ → EReal} (hV : IsSubharmonic V) (n : ℕ) : UpperSemicontinuous (fun z => trunc n (V z)) := by
  intro z y hy
  have hne : max (V z) (-(n : EReal)) ≠ ⊤ := max_ne_top (hV.1 z) (by simp)
  have hnb : max (V z) (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  have hy' : max (V z) (-(n : EReal)) < (y : EReal) := by
    have : ((trunc n (V z) : ℝ) : EReal) < (y : EReal) := EReal.coe_lt_coe_iff.mpr hy
    unfold trunc at this; rwa [EReal.coe_toReal hne hnb] at this
  have h1 : V z < (y : EReal) := lt_of_le_of_lt (le_max_left _ _) hy'
  have h2 : -(n : EReal) < (y : EReal) := lt_of_le_of_lt (le_max_right _ _) hy'
  filter_upwards [hV.2.1 z y h1] with z' hz'
  have hm : max (V z') (-(n : EReal)) < (y : EReal) := max_lt hz' h2
  have hne' : max (V z') (-(n : EReal)) ≠ ⊤ := ne_top_of_lt hm
  have hnb' : max (V z') (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  unfold trunc
  rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne' hnb']
  exact hm

/-- The truncation of a subharmonic function is integrable on every circle. -/
theorem trunc_circleIntegrable {V : ℂ → EReal} (hV : IsSubharmonic V) (n : ℕ) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => trunc n (V z)) c r := by
  have husc := trunc_usc hV n
  have hcomp : UpperSemicontinuous (fun θ : ℝ => trunc n (V (circleMap c r θ))) :=
    fun θ => (husc (circleMap c r θ)).comp (continuous_circleMap c r).continuousAt
  obtain ⟨B, hB⟩ := (hcomp.upperSemicontinuousOn (Icc 0 (2 * π))).bddAbove_of_isCompact isCompact_Icc
  have hmeas : Measurable (fun θ : ℝ => trunc n (V (circleMap c r θ))) := hcomp.measurable
  unfold CircleIntegrable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le two_pi_pos.le]
  refine Measure.integrableOn_of_bounded (M := max B n) measure_Icc_lt_top.ne hmeas.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Eventually.of_forall (fun θ hθ => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hup : trunc n (V (circleMap c r θ)) ≤ B := hB ⟨θ, hθ, rfl⟩
  have hlo := trunc_ge (hV.1 (circleMap c r θ)) n
  constructor
  · have : -(max B (n : ℝ)) ≤ -(n : ℝ) := neg_le_neg (le_max_right _ _)
    linarith
  · exact le_trans hup (le_max_left _ _)


/-! ## Part B: the sector comparison -/

/-- Rotation by `-μ`. -/
noncomputable def rot (μ : ℝ) (z : ℂ) : ℂ := Complex.exp (-(μ : ℂ) * Complex.I) * z

theorem norm_rot (μ : ℝ) (z : ℂ) : ‖rot μ z‖ = ‖z‖ := by
  have : -(μ : ℂ) * Complex.I = ((-μ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [rot, norm_mul, this, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem rot_exp (μ θ : ℝ) : rot μ (Complex.exp ((θ : ℂ) * Complex.I)) = Complex.exp (((θ - μ : ℝ) : ℂ) * Complex.I) := by
  rw [rot, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eq_of_rot (μ : ℝ) (z : ℂ) : z = Complex.exp ((μ : ℂ) * Complex.I) * rot μ z := by
  rw [rot, ← mul_assoc, ← Complex.exp_add]; simp

theorem rot_ne_zero {μ : ℝ} {z : ℂ} (hz : z ≠ 0) : rot μ z ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) hz

/-- `Re(ζ^r) = ‖ζ‖^r cos(r arg ζ)`. -/
theorem cpow_re_eq {ζ : ℂ} (hζ : ζ ≠ 0) (r : ℝ) : (ζ ^ (r : ℂ)).re = ‖ζ‖ ^ r * cos (r * Complex.arg ζ) := by
  rw [Complex.cpow_def_of_ne_zero hζ, Complex.exp_re]
  have h1 : (Complex.log ζ * (r : ℂ)).re = Real.log ‖ζ‖ * r := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  have h2 : (Complex.log ζ * (r : ℂ)).im = r * Complex.arg ζ := by
    simp [Complex.mul_im, Complex.log_re, Complex.log_im]; ring
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ)]

/-- `Im(ζ^r) = ‖ζ‖^r sin(r arg ζ)`. -/
theorem cpow_im_eq {ζ : ℂ} (hζ : ζ ≠ 0) (r : ℝ) : (ζ ^ (r : ℂ)).im = ‖ζ‖ ^ r * sin (r * Complex.arg ζ) := by
  rw [Complex.cpow_def_of_ne_zero hζ, Complex.exp_im]
  have h1 : (Complex.log ζ * (r : ℂ)).re = Real.log ‖ζ‖ * r := by
    simp [Complex.mul_re, Complex.log_re, Complex.log_im]
  have h2 : (Complex.log ζ * (r : ℂ)).im = r * Complex.arg ζ := by
    simp [Complex.mul_im, Complex.log_re, Complex.log_im]; ring
  rw [h1, h2, Real.rpow_def_of_pos (norm_pos_iff.mpr hζ)]

/-- `Re((A - iB) ζ^r) = ‖ζ‖^r (A cos(r arg ζ) + B sin(r arg ζ))`. -/
theorem re_coef_cpow {ζ : ℂ} (hζ : ζ ≠ 0) (A B r : ℝ) :
    (((A : ℂ) - (B : ℂ) * Complex.I) * ζ ^ (r : ℂ)).re
      = ‖ζ‖ ^ r * (A * cos (r * Complex.arg ζ) + B * sin (r * Complex.arg ζ)) := by
  rw [Complex.mul_re, cpow_re_eq hζ, cpow_im_eq hζ]
  simp; ring

/-- The closed cone `{z : ‖z‖ cos α ≤ Re(rot μ z)}`: for `z ≠ 0` in it, `|arg(rot μ z)| ≤ α` (`0 < α < π`). -/
theorem abs_arg_le_of_cone {μ α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α ≤ (rot μ z).re) : |Complex.arg (rot μ z)| ≤ α := by
  have hζ := rot_ne_zero (μ := μ) hz
  have hcos : cos α ≤ cos |Complex.arg (rot μ z)| := by
    rw [Real.cos_abs, Complex.cos_arg hζ, norm_rot, le_div_iff₀ (norm_pos_iff.mpr hz)]; linarith
  by_contra h
  push Not at h
  have := cos_lt_cos_of_nonneg_of_le_pi hα0.le (Complex.abs_arg_le_pi _) h
  linarith

/-- On the boundary of the cone (`z ≠ 0`, equality), `arg(rot μ z) = ±α`. -/
theorem arg_eq_of_cone_bdry {μ α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α = (rot μ z).re) : Complex.arg (rot μ z) = α ∨ Complex.arg (rot μ z) = -α := by
  have hζ := rot_ne_zero (μ := μ) hz
  have hcos : cos |Complex.arg (rot μ z)| = cos α := by
    rw [Real.cos_abs, Complex.cos_arg hζ, norm_rot, div_eq_iff (norm_pos_iff.mpr hz).ne']; linarith
  have habs : |Complex.arg (rot μ z)| = α :=
    injOn_cos ⟨abs_nonneg _, Complex.abs_arg_le_pi _⟩ ⟨hα0.le, hαπ.le⟩ hcos
  rcases abs_eq hα0.le |>.mp habs with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Points of the closed cone other than `0` are in the domain of the principal power. -/
theorem rot_mem_slitPlane {μ α : ℝ} (hα0 : 0 < α) (hαπ : α < π) {z : ℂ} (hz : z ≠ 0)
    (hc : ‖z‖ * cos α ≤ (rot μ z).re) : rot μ z ∈ Complex.slitPlane := by
  have harg := abs_arg_le_of_cone hα0 hαπ hz hc
  rw [Complex.mem_slitPlane_iff]
  by_contra h
  push Not at h
  have hre : (rot μ z).re < 0 := by
    rcases lt_or_eq_of_le h.1 with h1 | h1
    · exact h1
    · exact absurd (Complex.ext h1 h.2) (rot_ne_zero hz)
  have := Complex.arg_eq_pi_iff.mpr ⟨hre, h.2⟩
  rw [this, abs_of_pos pi_pos] at harg
  linarith

/-- `x ≤ B` ⇒ `r x ≤ r B` in `EReal`, for `r > 0`. -/
theorem ereal_mul_le {r : ℝ} (hr : 0 < r) {X : EReal} {B : ℝ} (h : X ≤ (B : EReal)) :
    (r : EReal) * X ≤ ((r * B : ℝ) : EReal) := by
  induction X using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hr]; exact bot_le
  | coe x =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp h) hr.le
  | top => exact absurd h (by simp)

/-- `trunc n X ≤ Y` when `X ≤ Y` and `-n ≤ Y`. -/
theorem trunc_le {X : EReal} (hX : X ≠ ⊤) {Y : ℝ} (h : X ≤ (Y : EReal)) (n : ℕ) (hn : -(n : ℝ) ≤ Y) : trunc n X ≤ Y := by
  have hn' : -(n : EReal) ≤ (Y : EReal) := by
    rw [show (-(n : EReal)) = ((-(n : ℝ) : ℝ) : EReal) by simp]; exact EReal.coe_le_coe_iff.mpr hn
  have hm : max X (-(n : EReal)) ≤ (Y : EReal) := max_le h hn'
  have hne : max X (-(n : EReal)) ≠ ⊤ := max_ne_top hX (by simp)
  have hnb : max X (-(n : EReal)) ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) (le_max_right _ _)
  unfold trunc
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal hne hnb]
  exact hm

/-- A homogeneous `V` (never `⊤`) has `V 0 ≤ 0`. -/
theorem homog_zero_le {q : ℝ} (hq : 0 < q) {V : ℂ → EReal} (hVt : ∀ z, V z ≠ ⊤)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) : V 0 ≤ 0 := by
  have h := hhom 2 0 (by norm_num)
  rw [mul_zero] at h
  induction h' : V 0 using EReal.rec with
  | bot => exact bot_le
  | coe v =>
    rw [h', ← EReal.coe_mul, EReal.coe_eq_coe_iff] at h
    have h2 : (2:ℝ) ^ q - 1 ≠ 0 := by
      have : (1:ℝ) < 2 ^ q := Real.one_lt_rpow (by norm_num) hq
      linarith
    have h3 : ((2:ℝ) ^ q - 1) * v = 0 := by rw [sub_mul, one_mul]; linarith
    have : v = 0 := (mul_eq_zero.mp h3).resolve_left h2
    rw [this]; simp
  | top => exact absurd h' (hVt 0)

/-- A real upper bound for a subharmonic `V` on the unit circle. -/
theorem exists_bound_sphere {V : ℂ → EReal} (hV : IsSubharmonic V) : ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ sphere (0:ℂ) 1, V z ≤ B := by
  obtain ⟨z0, hz0, hmax⟩ := (hV.2.1.upperSemicontinuousOn (sphere (0:ℂ) 1)).exists_isMaxOn
    ⟨1, by simp⟩ (isCompact_sphere 0 1)
  refine ⟨max (V z0).toReal 0, le_max_right _ _, fun z hz => ?_⟩
  refine le_trans (hmax hz) ?_
  induction h : V z0 using EReal.rec with
  | bot => exact bot_le
  | coe v => simp
  | top => exact absurd h (hV.1 z0)

/-- `V z = ‖z‖^q V(z/‖z‖)` for a homogeneous `V`, `z ≠ 0`. -/
theorem homog_split {q : ℝ} {V : ℂ → EReal}
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) {z : ℂ} (hz : z ≠ 0) :
    V z = ((‖z‖ ^ q : ℝ) : EReal) * V ((‖z‖⁻¹ : ℝ) * z) ∧ (‖z‖⁻¹ : ℝ) * z ∈ sphere (0:ℂ) 1 := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨?_, ?_⟩
  · rw [← hhom ‖z‖ _ hn, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_mul]
  · rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hn,
      inv_mul_cancel₀ hn.ne']

/-- The comparison function `w = Re((A - iB)(rot z)^q + ε (rot z)^{q'})`. -/
noncomputable def wfun (μ A B q q' ε : ℝ) (z : ℂ) : ℝ :=
  (((A : ℂ) - (B : ℂ) * Complex.I) * rot μ z ^ (q : ℂ) + (ε : ℂ) * rot μ z ^ (q' : ℂ)).re

/-- Polar form of `wfun`. -/
theorem wfun_polar (μ A B q q' ε : ℝ) {z : ℂ} (hz : z ≠ 0) :
    wfun μ A B q q' ε z = ‖z‖ ^ q * (A * cos (q * Complex.arg (rot μ z)) + B * sin (q * Complex.arg (rot μ z)))
      + ε * (‖z‖ ^ q' * cos (q' * Complex.arg (rot μ z))) := by
  have hζ := rot_ne_zero (μ := μ) hz
  rw [wfun, Complex.add_re, re_coef_cpow hζ, Complex.re_ofReal_mul, cpow_re_eq hζ, norm_rot]

theorem wfun_zero (μ A B : ℝ) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q') (ε : ℝ) : wfun μ A B q q' ε 0 = 0 := by
  have h0 : rot μ 0 = 0 := by simp [rot]
  rw [wfun, h0, Complex.zero_cpow (by exact_mod_cast hq.ne'), Complex.zero_cpow (by exact_mod_cast hq'.ne')]
  simp

theorem analyticAt_rot (μ : ℝ) (z : ℂ) : AnalyticAt ℂ (rot μ) z := by
  unfold rot; exact analyticAt_const.mul analyticAt_id

theorem wfun_analytic (μ A B q q' ε : ℝ) {z : ℂ} (hz : rot μ z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun z => ((A : ℂ) - (B : ℂ) * Complex.I) * rot μ z ^ (q : ℂ) + (ε : ℂ) * rot μ z ^ (q' : ℂ)) z :=
  (analyticAt_const.mul ((analyticAt_rot μ z).cpow analyticAt_const hz)).add
    (analyticAt_const.mul ((analyticAt_rot μ z).cpow analyticAt_const hz))

theorem continuousAt_rot_cpow (μ : ℝ) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z = 0 ∨ rot μ z ∈ Complex.slitPlane) :
    ContinuousAt (fun z => rot μ z ^ (r : ℂ)) z := by
  rcases hz with h | h
  · subst h
    have hc := Complex.continuousAt_cpow_zero_of_re_pos (z := (r : ℂ)) (by simpa using hr)
    exact hc.comp_of_eq ((analyticAt_rot μ 0).continuousAt.prodMk continuousAt_const) (Prod.ext (by simp [rot]) rfl)
  · exact (analyticAt_rot μ z).continuousAt.cpow continuousAt_const h

theorem wfun_continuousAt (μ A B : ℝ) {q q' : ℝ} (hq : 0 < q) (hq' : 0 < q') (ε : ℝ) {z : ℂ}
    (hz : z = 0 ∨ rot μ z ∈ Complex.slitPlane) : ContinuousAt (wfun μ A B q q' ε) z := by
  unfold wfun
  exact Complex.continuous_re.continuousAt.comp ((continuousAt_const.mul (continuousAt_rot_cpow μ hq hz)).add
    (continuousAt_const.mul (continuousAt_rot_cpow μ hq' hz)))

/-- Mean value property of `wfun` on discs inside `{z : rot μ z ∈ slitPlane}`. -/
theorem wfun_mean (μ A B q q' ε : ℝ) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : closedBall c ρ ⊆ {z | rot μ z ∈ Complex.slitPlane}) :
    circleAverage (wfun μ A B q q' ε) c ρ = wfun μ A B q q' ε c ∧ CircleIntegrable (wfun μ A B q q' ε) c ρ := by
  have hh : InnerProductSpace.HarmonicOnNhd (wfun μ A B q q' ε) (closedBall c |ρ|) := by
    intro z hz
    rw [abs_of_pos hρ] at hz
    exact (wfun_analytic μ A B q q' ε (hball hz)).harmonicAt_re
  exact ⟨hh.circleAverage_eq, (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'⟩

/-- The interpolation identity: `A cos(q s) + B sin(q s)` equals the trig-convex chord at `t = μ + s`. -/
theorem chord_identity {q α s a b : ℝ} (hc : cos (q * α) ≠ 0) (hs : sin (q * α) ≠ 0) :
    (a + b) / (2 * cos (q * α)) * cos (q * s) + (b - a) / (2 * sin (q * α)) * sin (q * s)
      = (a * sin (q * (α - s)) + b * sin (q * (α + s))) / sin (q * (2 * α)) := by
  have e1 : q * (α - s) = q * α - q * s := by ring
  have e2 : q * (α + s) = q * α + q * s := by ring
  have e3 : q * (2 * α) = 2 * (q * α) := by ring
  rw [e1, e2, e3, sin_sub, sin_add, sin_two_mul]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
/-- **(E1a) Sector comparison.** A `q`-homogeneous subharmonic `V` (`1/2 < q < 1`) lies below the `q`-sinusoid through its
values at the ends of any arc of length `< π/q`. -/
theorem sector_comparison {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    {x y a b : ℝ} (hxy : x < y) (hlen : q * (y - x) < π)
    (ha : V (Complex.exp ((x : ℂ) * Complex.I)) ≤ (a : EReal)) (hb : V (Complex.exp ((y : ℂ) * Complex.I)) ≤ (b : EReal))
    (t : ℝ) (ht : x < t) (ht' : t < y) :
    V (Complex.exp ((t : ℂ) * Complex.I)) ≤ (((a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) : ℝ) : EReal) := by
  have hq : 0 < q := by linarith
  set μ := (x + y) / 2 with hμ
  set α := (y - x) / 2 with hα
  have hα0 : 0 < α := by rw [hα]; linarith
  have hqα : q * α < π / 2 := by rw [hα]; linarith
  have hαπ : α < π := by
    have h1 : α < π / (2 * q) := by rw [lt_div_iff₀ (by linarith)]; linarith
    have h2 : π / (2 * q) < π := by rw [div_lt_iff₀ (by linarith)]; nlinarith [pi_pos]
    linarith
  have hcqα : 0 < cos (q * α) := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], hqα⟩
  have hsqα : 0 < sin (q * α) := sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [pi_pos])
  set A := (a + b) / (2 * cos (q * α)) with hA
  set B := (b - a) / (2 * sin (q * α)) with hB
  set q' := (q + π / (2 * α)) / 2 with hq'
  have hqq' : q < q' := by
    have : q < π / (2 * α) := by rw [lt_div_iff₀ (by linarith)]; linarith
    rw [hq']; linarith
  have hq'α : q' * α < π / 2 := by
    have : π / (2 * α) * α = π / 2 := by field_simp
    rw [hq']; nlinarith
  have hq'0 : 0 < q' := by linarith
  have hcq' : 0 < cos (q' * α) := cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], hq'α⟩
  obtain ⟨Bv, hBv0, hBv⟩ := exists_bound_sphere hV
  -- the conclusion for every ε > 0
  have key : ∀ ε : ℝ, 0 < ε → V (Complex.exp ((t : ℂ) * Complex.I)) ≤
      (((A * cos (q * (t - μ)) + B * sin (q * (t - μ))) + ε : ℝ) : EReal) := by
    intro ε hε
    set d := q' - q with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    set L := (Bv + |A| + |B|) / (ε * cos (q' * α)) + 1 with hL
    have hL0 : 0 < L := by rw [hL]; positivity
    set R := max 2 (L ^ (1 / d)) with hR
    have hR1 : 1 ≤ R := le_trans (by norm_num) (le_max_left _ _)
    have hR0 : 0 < R := by linarith
    have hRd : L ≤ R ^ d := by
      have h1 : L ^ (1 / d) ≤ R := le_max_right _ _
      have h2 : (L ^ (1 / d)) ^ d ≤ R ^ d := rpow_le_rpow (by positivity) h1 hd0.le
      rwa [← rpow_mul hL0.le, one_div_mul_cancel hd0.ne', rpow_one] at h2
    set n : ℕ := ⌈R ^ q * (|a| + |b|)⌉₊ with hn
    have hn' : R ^ q * (|a| + |b|) ≤ n := Nat.le_ceil _
    set v : ℂ → ℝ := fun z => trunc n (V z) with hv
    set w := wfun μ A B q q' ε with hw
    set K := {z : ℂ | ‖z‖ * cos α ≤ (rot μ z).re} ∩ closedBall 0 R with hK
    set U := {z : ℂ | rot μ z ∈ Complex.slitPlane} with hU
    have hrotc : Continuous (rot μ) := continuous_const.mul continuous_id
    have hKc : IsCompact K := (isCompact_closedBall 0 R).inter_left
      (isClosed_le (continuous_norm.mul continuous_const) (Complex.continuous_re.comp hrotc))
    -- boundary estimates
    have hb0 : v 0 - w 0 ≤ 0 := by
      have h1 : v 0 ≤ 0 := trunc_le (hV.1 0) (by exact_mod_cast homog_zero_le hq hV.1 hhom) n (by simp)
      rw [hw, wfun_zero μ A B hq hq'0 ε]; linarith
    have hcqα' : cos (q * α) ≠ 0 := hcqα.ne'
    have hsqα' : sin (q * α) ≠ 0 := hsqα.ne'
    have hRq0 : 0 < R ^ q := rpow_pos_of_pos hR0 q
    have hn'' : R ^ q * |a| + R ^ q * |b| ≤ n := by rw [← mul_add]; exact hn'
    have hray : ∀ z ∈ K, z ≠ 0 → ‖z‖ * cos α = (rot μ z).re → v z - w z ≤ 0 := by
      intro z hzK hz heq
      have hzR : ‖z‖ ≤ R := by have := hzK.2; rwa [mem_closedBall, dist_zero_right] at this
      have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hRq : ‖z‖ ^ q ≤ R ^ q := rpow_le_rpow (norm_nonneg z) hzR hq.le
      have hzq : 0 < ‖z‖ ^ q := rpow_pos_of_pos hzn q
      have hexp : Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I)
          = Complex.exp ((μ : ℂ) * Complex.I) * Complex.exp ((Complex.arg (rot μ z) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]; push_cast; ring_nf
      have hrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I) := by
        calc z = Complex.exp ((μ : ℂ) * Complex.I) * rot μ z := eq_of_rot μ z
          _ = Complex.exp ((μ : ℂ) * Complex.I) * (((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg (rot μ z) : ℂ) * Complex.I)) := by
              rw [← norm_rot μ z, Complex.norm_mul_exp_arg_mul_I]
          _ = _ := by rw [hexp]; ring
      have hVrep : V z = ((‖z‖ ^ q : ℝ) : EReal) * V (Complex.exp (((μ + Complex.arg (rot μ z) : ℝ) : ℂ) * Complex.I)) := by
        rw [← hhom _ _ hzn, ← hrep]
      rw [hw, wfun_polar μ A B q q' ε hz]
      rcases arg_eq_of_cone_bdry hα0 hαπ hz heq with h | h
      · -- the ray through e^{iy}
        have hy : μ + Complex.arg (rot μ z) = y := by rw [h, hμ, hα]; ring
        rw [hy] at hVrep
        have hVz : V z ≤ ((‖z‖ ^ q * b : ℝ) : EReal) := by rw [hVrep]; exact ereal_mul_le hzq hb
        have h1 : ‖z‖ ^ q * (-|b|) ≤ ‖z‖ ^ q * b := mul_le_mul_of_nonneg_left (neg_abs_le b) hzq.le
        have h2 : ‖z‖ ^ q * |b| ≤ R ^ q * |b| := mul_le_mul_of_nonneg_right hRq (abs_nonneg b)
        have h3 : 0 ≤ R ^ q * |a| := mul_nonneg hRq0.le (abs_nonneg a)
        have hvz : v z ≤ ‖z‖ ^ q * b := trunc_le (hV.1 z) hVz n (by linarith)
        have hAB : A * cos (q * α) + B * sin (q * α) = b := by rw [hA, hB]; field_simp; ring
        rw [h, hAB]
        have : 0 ≤ ε * (‖z‖ ^ q' * cos (q' * α)) := by positivity
        linarith
      · -- the ray through e^{ix}
        have hx : μ + Complex.arg (rot μ z) = x := by rw [h, hμ, hα]; ring
        rw [hx] at hVrep
        have hVz : V z ≤ ((‖z‖ ^ q * a : ℝ) : EReal) := by rw [hVrep]; exact ereal_mul_le hzq ha
        have h1 : ‖z‖ ^ q * (-|a|) ≤ ‖z‖ ^ q * a := mul_le_mul_of_nonneg_left (neg_abs_le a) hzq.le
        have h2 : ‖z‖ ^ q * |a| ≤ R ^ q * |a| := mul_le_mul_of_nonneg_right hRq (abs_nonneg a)
        have h3 : 0 ≤ R ^ q * |b| := mul_nonneg hRq0.le (abs_nonneg b)
        have hvz : v z ≤ ‖z‖ ^ q * a := trunc_le (hV.1 z) hVz n (by linarith)
        have hAB : A * cos (q * -α) + B * sin (q * -α) = a := by
          rw [mul_neg, cos_neg, sin_neg, hA, hB]; field_simp; ring
        rw [h, hAB, mul_neg, cos_neg]
        have : 0 ≤ ε * (‖z‖ ^ q' * cos (q' * α)) := by positivity
        linarith
    have houter : ∀ z ∈ K, ‖z‖ = R → v z - w z ≤ 0 := by
      intro z hzK hzR
      have hz : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hzR; linarith
      obtain ⟨hsplit, hsph⟩ := homog_split hhom hz
      have hzq : 0 < ‖z‖ ^ q := rpow_pos_of_pos (norm_pos_iff.mpr hz) q
      have hVz : V z ≤ ((‖z‖ ^ q * Bv : ℝ) : EReal) := by rw [hsplit]; exact ereal_mul_le hzq (hBv _ hsph)
      have hvz : v z ≤ ‖z‖ ^ q * Bv := trunc_le (hV.1 z) hVz n (by have := mul_nonneg hzq.le hBv0; linarith)
      set θ := Complex.arg (rot μ z) with hθdef
      have hθ : |θ| ≤ α := abs_arg_le_of_cone hα0 hαπ hz hzK.1
      have hcos : cos (q' * α) ≤ cos (q' * θ) := by
        rw [← cos_abs (q' * θ), abs_mul, abs_of_pos hq'0]
        exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by nlinarith [pi_pos])
          (mul_le_mul_of_nonneg_left hθ hq'0.le)
      have hA1 : -|A| ≤ A * cos (q * θ) := by
        have : |A * cos (q * θ)| ≤ |A| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg A) (abs_cos_le_one _)
        linarith [neg_abs_le (A * cos (q * θ))]
      have hB1 : -|B| ≤ B * sin (q * θ) := by
        have : |B * sin (q * θ)| ≤ |B| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg B) (abs_sin_le_one _)
        linarith [neg_abs_le (B * sin (q * θ))]
      have hRsplit : R ^ q' = R ^ q * R ^ d := by rw [← rpow_add hR0]; congr 1; rw [hd]; ring
      have hεL' : ε * cos (q' * α) * L = (Bv + |A| + |B|) + ε * cos (q' * α) := by rw [hL]; field_simp
      have hεL : Bv + |A| + |B| < ε * cos (q' * α) * L := by rw [hεL']; linarith [mul_pos hε hcq']
      rw [hw, wfun_polar μ A B q q' ε hz, hzR]
      rw [hzR] at hvz
      have h3 : ε * (R ^ q' * cos (q' * α)) ≤ ε * (R ^ q' * cos (q' * θ)) := by
        apply mul_le_mul_of_nonneg_left _ hε.le
        exact mul_le_mul_of_nonneg_left hcos (by positivity)
      have h4 : R ^ q * (ε * cos (q' * α) * L) ≤ ε * (R ^ q' * cos (q' * α)) := by
        rw [hRsplit]
        have : ε * cos (q' * α) * L ≤ ε * cos (q' * α) * R ^ d := mul_le_mul_of_nonneg_left hRd (by positivity)
        calc R ^ q * (ε * cos (q' * α) * L) ≤ R ^ q * (ε * cos (q' * α) * R ^ d) :=
              mul_le_mul_of_nonneg_left this hRq0.le
          _ = ε * (R ^ q * R ^ d * cos (q' * α)) := by ring
      have h5 := mul_le_mul_of_nonneg_left (show -(|A| + |B|) ≤ A * cos (q * θ) + B * sin (q * θ) by linarith) hRq0.le
      have h6 := mul_lt_mul_of_pos_left hεL hRq0
      linarith
    have hint : ∀ z ∈ K, 0 < v z - w z → ∃ ρ > 0, closedBall z ρ ⊆ K ∩ U := by
      intro z hzK hpos
      have hz : z ≠ 0 := by intro h0; rw [h0] at hpos; linarith
      have hstrict : ‖z‖ * cos α < (rot μ z).re := by
        rcases lt_or_eq_of_le (show ‖z‖ * cos α ≤ (rot μ z).re from hzK.1) with h | h
        · exact h
        · linarith [hray z hzK hz h]
      have hzR : ‖z‖ < R := by
        have : ‖z‖ ≤ R := by have := hzK.2; rwa [mem_closedBall, dist_zero_right] at this
        rcases lt_or_eq_of_le this with h | h
        · exact h
        · linarith [houter z hzK h]
      set O := {z : ℂ | ‖z‖ * cos α < (rot μ z).re} ∩ ball 0 R with hO
      have hOo : IsOpen O := (isOpen_lt (continuous_norm.mul continuous_const) (Complex.continuous_re.comp hrotc)).inter
        isOpen_ball
      have hzO : z ∈ O := ⟨hstrict, by rw [mem_ball, dist_zero_right]; exact hzR⟩
      obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hOo z hzO
      refine ⟨r / 2, by positivity, fun z' hz' => ?_⟩
      have hz'O : z' ∈ O := hrO (closedBall_subset_ball (by linarith) hz')
      have hz'0 : z' ≠ 0 := by
        intro h0; have := (show ‖z'‖ * cos α < (rot μ z').re from hz'O.1)
        rw [h0, norm_zero, zero_mul] at this; simp [rot] at this
      have hz'c : ‖z'‖ * cos α < (rot μ z').re := hz'O.1
      refine ⟨⟨(show ‖z'‖ * cos α ≤ (rot μ z').re from hz'c.le), ball_subset_closedBall hz'O.2⟩,
        rot_mem_slitPlane hα0 hαπ hz'0 hz'c.le⟩
    have hwc : ContinuousOn w K := by
      intro z hzK
      refine (wfun_continuousAt μ A B hq hq'0 ε ?_).continuousWithinAt
      by_cases hz : z = 0
      · exact Or.inl hz
      · exact Or.inr (rot_mem_slitPlane hα0 hαπ hz hzK.1)
    have hmp := max_principle hKc inter_subset_right (trunc_usc hV n) (fun c r hr => hV.2.2 n c r hr)
      (trunc_circleIntegrable hV n) hwc (fun c ρ hρ hball => wfun_mean μ A B q q' ε hρ hball) hint
    -- the target point
    set zt := Complex.exp ((t : ℂ) * Complex.I) with hzt
    have hzt1 : ‖zt‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    have hzt0 : zt ≠ 0 := Complex.exp_ne_zero _
    have hrotzt : rot μ zt = Complex.exp (((t - μ : ℝ) : ℂ) * Complex.I) := rot_exp μ t
    have htμ : |t - μ| < α := by rw [abs_lt, hμ, hα]; constructor <;> linarith
    have harg : Complex.arg (rot μ zt) = t - μ := by
      rw [hrotzt, Complex.arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [(abs_lt.mp htμ).1, (abs_lt.mp htμ).2]
    have hztK : zt ∈ K := by
      refine ⟨?_, by rw [mem_closedBall, dist_zero_right, hzt1]; exact hR1⟩
      show ‖zt‖ * cos α ≤ (rot μ zt).re
      rw [hzt1, one_mul, hrotzt, Complex.exp_ofReal_mul_I_re, ← cos_abs (t - μ)]
      exact cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hαπ.le htμ.le
    have hle := hmp zt hztK
    rw [hw, wfun_polar μ A B q q' ε hzt0, hzt1, harg, one_rpow, one_rpow, one_mul, one_mul] at hle
    have hcos1 : cos (q' * (t - μ)) ≤ 1 := cos_le_one _
    have hvt : v zt ≤ A * cos (q * (t - μ)) + B * sin (q * (t - μ)) + ε := by nlinarith
    calc V zt ≤ ((v zt : ℝ) : EReal) := le_trunc (hV.1 zt) n
      _ ≤ _ := EReal.coe_le_coe_iff.mpr hvt
  -- ε → 0 and the chord identity
  have hchord : A * cos (q * (t - μ)) + B * sin (q * (t - μ))
      = (a * sin (q * (y - t)) + b * sin (q * (t - x))) / sin (q * (y - x)) := by
    have e1 : y - t = α - (t - μ) := by rw [hμ, hα]; ring
    have e2 : t - x = α + (t - μ) := by rw [hμ, hα]; ring
    have e3 : y - x = 2 * α := by rw [hα]; ring
    rw [e1, e2, e3, hA, hB]
    exact chord_identity hcqα.ne' hsqα.ne'
  rw [← hchord]
  induction hVt : V (Complex.exp ((t : ℂ) * Complex.I)) using EReal.rec with
  | bot => exact bot_le
  | coe vt =>
    rw [EReal.coe_le_coe_iff]
    apply le_of_forall_pos_le_add
    intro ε hε
    have := key ε hε
    rw [hVt, EReal.coe_le_coe_iff] at this
    linarith
  | top => exact absurd hVt (hV.1 _)

/-! ## E1b-E1d -/

theorem exp_mem_sphere (θ : ℝ) : Complex.exp ((θ : ℂ) * Complex.I) ∈ sphere (0:ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]

/-- `sin(q(y-x)) > 0` for `0 < q(y-x) < π`. -/
theorem sin_len_pos {q x y : ℝ} (hq : 0 < q) (hxy : x < y) (hlen : q * (y - x) < π) : 0 < sin (q * (y - x)) :=
  sin_pos_of_pos_of_lt_pi (mul_pos hq (by linarith)) hlen

/-- From the sector comparison with exact end values to the multiplied-out trig convexity inequality. -/
theorem trigConvex_of_comparison {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ}
    (hcmp : ∀ x t y : ℝ, x < t → t < y → q * (y - x) < π →
      φ t ≤ (φ x * sin (q * (y - t)) + φ y * sin (q * (t - x))) / sin (q * (y - x))) : TrigConvex q φ := by
  intro x t y hxt hty hlen
  have hs := sin_len_pos hq (hxt.trans hty) hlen
  have := hcmp x t y hxt hty hlen
  rwa [le_div_iff₀ hs] at this

/-- **(E1b)** A q-subtrigonometric function is trigonometrically convex (`1/2 < q < 1`). -/
theorem qsubtrig_trigConvex {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    TrigConvex q φ := by
  have hq : 0 < q := by linarith
  set V : ℂ → EReal := fun ζ => ((‖ζ‖ ^ q * φ (Complex.arg ζ) : ℝ) : EReal) with hVdef
  have hV : IsSubharmonic V := hφ.2
  have hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z := by
    intro r z hr
    by_cases hz : z = 0
    · subst hz; simp only [hVdef, mul_zero, norm_zero, zero_rpow hq.ne', zero_mul, EReal.coe_zero]
    · simp only [hVdef]
      rw [← EReal.coe_mul, Complex.arg_real_mul z hr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
        mul_rpow hr.le (norm_nonneg z)]
      congr 1; ring
  have hval : ∀ θ : ℝ, V (Complex.exp ((θ : ℂ) * Complex.I)) = ((φ θ : ℝ) : EReal) := by
    intro θ
    simp only [hVdef, Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I]
    rw [toIocMod, hφ.1.sub_zsmul_eq]
  apply trigConvex_of_comparison hq
  intro x t y hxt hty hlen
  have h := sector_comparison hq0 hq1 hV hhom (hxt.trans hty) hlen (le_of_eq (hval x)) (le_of_eq (hval y)) t hxt hty
  rwa [hval t, EReal.coe_le_coe_iff] at h

/-- `V = ⊥` everywhere on an open arc of length `< π/q` to the right of a point where `V = ⊥`. -/
theorem bot_spread_right {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    {t0 : ℝ} (hbot : V (Complex.exp ((t0 : ℂ) * Complex.I)) = ⊥) {t : ℝ} (ht : t0 < t) (ht' : t < t0 + π / q) :
    V (Complex.exp ((t : ℂ) * Complex.I)) = ⊥ := by
  have hq : 0 < q := by linarith
  obtain ⟨Bv, -, hBv⟩ := exists_bound_sphere hV
  set y := (t + (t0 + π / q)) / 2 with hy
  have hty : t < y := by rw [hy]; linarith
  have hlen : q * (y - t0) < π := by
    have : y - t0 < π / q := by rw [hy]; linarith
    rwa [lt_div_iff₀ hq, mul_comm] at this
  have hs1 : 0 < sin (q * (y - t)) := sin_len_pos hq hty (by nlinarith)
  have hs2 : 0 < sin (q * (y - t0)) := sin_len_pos hq (ht.trans hty) hlen
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  set N := ((M - 1) * sin (q * (y - t0)) - Bv * sin (q * (t - t0))) / sin (q * (y - t)) with hN
  have h := sector_comparison hq0 hq1 hV hhom (ht.trans hty) hlen (a := N) (b := Bv) (by rw [hbot]; exact bot_le)
    (hBv _ (exp_mem_sphere y)) t ht hty
  have heq : (N * sin (q * (y - t)) + Bv * sin (q * (t - t0))) / sin (q * (y - t0)) = M - 1 := by
    rw [hN]; field_simp; ring
  rw [heq] at h
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr (by linarith))

/-- The mirror image: `V = ⊥` on an open arc of length `< π/q` to the left. -/
theorem bot_spread_left {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    {t0 : ℝ} (hbot : V (Complex.exp ((t0 : ℂ) * Complex.I)) = ⊥) {t : ℝ} (ht : t0 - π / q < t) (ht' : t < t0) :
    V (Complex.exp ((t : ℂ) * Complex.I)) = ⊥ := by
  have hq : 0 < q := by linarith
  obtain ⟨Bv, -, hBv⟩ := exists_bound_sphere hV
  set x := ((t0 - π / q) + t) / 2 with hx
  have hxt : x < t := by rw [hx]; linarith
  have hlen : q * (t0 - x) < π := by
    have : t0 - x < π / q := by rw [hx]; linarith
    rwa [lt_div_iff₀ hq, mul_comm] at this
  have hs1 : 0 < sin (q * (t - x)) := sin_len_pos hq hxt (by nlinarith)
  have hs2 : 0 < sin (q * (t0 - x)) := sin_len_pos hq (hxt.trans ht') hlen
  rw [EReal.eq_bot_iff_forall_lt]
  intro M
  set N := ((M - 1) * sin (q * (t0 - x)) - Bv * sin (q * (t0 - t))) / sin (q * (t - x)) with hN
  have h := sector_comparison hq0 hq1 hV hhom (hxt.trans ht') hlen (a := Bv) (b := N) (hBv _ (exp_mem_sphere x))
    (by rw [hbot]; exact bot_le) t hxt ht'
  have heq : (Bv * sin (q * (t0 - t)) + N * sin (q * (t - x))) / sin (q * (t0 - x)) = M - 1 := by
    rw [hN]; field_simp; ring
  rw [heq] at h
  exact lt_of_le_of_lt h (EReal.coe_lt_coe_iff.mpr (by linarith))

/-- **(E1c)** A `q`-homogeneous subharmonic `V` with `V 0 ≥ 0` is finite on the unit circle (`1/2 < q < 1`). -/
theorem homog_finite {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z) (h0 : 0 ≤ V 0) :
    ∀ t : ℝ, V (Complex.exp ((t : ℂ) * Complex.I)) ≠ ⊥ := by
  have hq : 0 < q := by linarith
  intro t0 hbot
  have hπq : π < π / q := by rw [lt_div_iff₀ hq]; nlinarith [pi_pos]
  -- ⊥ on the whole unit circle
  have hcirc : ∀ t : ℝ, V (Complex.exp ((t : ℂ) * Complex.I)) = ⊥ := by
    intro t
    set t' := toIocMod two_pi_pos (t0 - π) t with ht'
    have hmem := toIocMod_mem_Ioc two_pi_pos (t0 - π) t
    have hexp : Complex.exp ((t' : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I) := by
      rw [ht', toIocMod]
      have : (((t - toIocDiv two_pi_pos (t0 - π) t • (2 * π) : ℝ) : ℂ) * Complex.I)
          = (t : ℂ) * Complex.I - (toIocDiv two_pi_pos (t0 - π) t : ℂ) * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
    rw [← hexp]
    rcases lt_trichotomy t' t0 with h | h | h
    · exact bot_spread_left hq0 hq1 hV hhom hbot (by linarith [hmem.1]) h
    · rw [h]; exact hbot
    · exact bot_spread_right hq0 hq1 hV hhom hbot h (by linarith [hmem.2])
  -- ⊥ off the origin
  have hoff : ∀ z : ℂ, z ≠ 0 → V z = ⊥ := by
    intro z hz
    have hrep : z = ((‖z‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I z).symm
    rw [hrep, hhom _ _ (norm_pos_iff.mpr hz), hcirc, EReal.coe_mul_bot_of_pos (rpow_pos_of_pos (norm_pos_iff.mpr hz) q)]
  -- the sub-mean-value inequality at 0 fails
  have hsub := hV.2.2 1 0 1 one_pos
  have hconst : circleAverage (fun z => trunc 1 (V z)) 0 1 = -1 := by
    have heq : Set.EqOn (fun z => trunc 1 (V z)) (fun _ => (-1 : ℝ)) (sphere 0 |1|) := by
      intro z hz
      have hz0 : z ≠ 0 := by rintro rfl; simp at hz
      simp only [hoff z hz0, trunc, max_eq_right (bot_le : (⊥ : EReal) ≤ -((1 : ℕ) : EReal))]
      simp
    rw [circleAverage_congr_sphere heq, circleAverage_const]
  have hpos : 0 ≤ trunc 1 (V 0) := by
    have hm : max (V 0) (-((1 : ℕ) : EReal)) = V 0 := max_eq_left (le_trans (by simp) h0)
    unfold trunc; rw [hm]; exact EReal.toReal_nonneg h0
  rw [hconst] at hsub
  linarith

/-- **(E1d)** The angular profile `φ t = V(e^{it})` of a finite homogeneous subharmonic `V`: trigonometrically convex,
`2π`-periodic, and `V ζ = ‖ζ‖^q φ(arg ζ)` off `0`. -/
theorem homog_profile {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {V : ℂ → EReal} (hV : IsSubharmonic V)
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → V ((r : ℂ) * z) = ((r ^ q : ℝ) : EReal) * V z)
    (hfin : ∀ t : ℝ, V (Complex.exp ((t : ℂ) * Complex.I)) ≠ ⊥) :
    TrigConvex q (fun t : ℝ => (V (Complex.exp ((t : ℂ) * Complex.I))).toReal) ∧
    Function.Periodic (fun t : ℝ => (V (Complex.exp ((t : ℂ) * Complex.I))).toReal) (2 * π) ∧
    ∀ ζ : ℂ, ζ ≠ 0 → V ζ = ((‖ζ‖ ^ q * (V (Complex.exp ((Complex.arg ζ : ℂ) * Complex.I))).toReal : ℝ) : EReal) := by
  have hq : 0 < q := by linarith
  have hcoe : ∀ t : ℝ, V (Complex.exp ((t : ℂ) * Complex.I)) = (((V (Complex.exp ((t : ℂ) * Complex.I))).toReal : ℝ) : EReal) :=
    fun t => (EReal.coe_toReal (hV.1 _) (hfin t)).symm
  refine ⟨?_, ?_, ?_⟩
  · apply trigConvex_of_comparison hq
    intro x t y hxt hty hlen
    have h := sector_comparison hq0 hq1 hV hhom (hxt.trans hty) hlen (le_of_eq (hcoe x)) (le_of_eq (hcoe y)) t hxt hty
    rwa [hcoe t, EReal.coe_le_coe_iff] at h
  · intro t
    have he : Complex.exp (((t + 2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I) := by
      rw [show (((t + 2 * π : ℝ) : ℂ) * Complex.I) = (t : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    dsimp only
    rw [he]
  · intro ζ hζ
    have hrep : ζ = ((‖ζ‖ : ℝ) : ℂ) * Complex.exp ((Complex.arg ζ : ℂ) * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I ζ).symm
    conv_lhs => rw [hrep, hhom _ _ (norm_pos_iff.mpr hζ), hcoe]
    rw [← EReal.coe_mul]

end Sector

end P18
