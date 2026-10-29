/-
  HVFalse/Proofs/IntervalH.lean - C10e: the paper's three interval steps for H(p, u(p)) (Prop. 5, l.373-378), by hand
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper checks with Arb/mpmath: (a) d/dp H(p,u(p)) > 0 on [4/3, 403/300]; (b) H > 0 on [403/300, 199/100];
  (c) d²/dp² H(p,u(p)) > 0 on [199/100, 2]. Here (b) is SaddleSigns.H_pos. For (a) and (c) put T = tan(π/2p): u = T²,
  u' = -π T(1+T²)/p² (ThresholdB.up), u'' = 2πT(1+T²)/p³ + π²(1+3T²)(1+T²)/(2p⁴). With tan(π/4+η) = (cos η + sin η)/(cos η - sin η)
  and Mathlib's sin_bound / cos_bound: T ∈ [2.34, 2.4143] on (a)'s interval, T ∈ [1, 1.0081] on (c)'s. Then crude box bounds:
  d/dp H = X·Y - Z ≥ 26.3·3.28 - 83.7 > 0 (X = π T(1+T²)/p²), and d²/dp² H ≥ 12.56 - 27.44 + 6 - 6.45 + 16.07 + 6 > 0.
-/
import HVFalse.Proofs.ThresholdB
import HVFalse.Proofs.SaddleSigns

open Real Set Filter Topology

namespace P18

namespace IntervalH

open ThresholdB

/-- `T(p) = tan(π/2p)`, so `u(p) = T(p)²`. -/
noncomputable def Tf (p : ℝ) : ℝ := tan (π / (2 * p))

theorem uu_eq_Tf (p : ℝ) : uu p = Tf p ^ 2 := rfl

theorem theta_mem {p : ℝ} (hp : 1 < p) : π / (2 * p) ∈ Ioo (-(π / 2)) (π / 2) := by
  have hp0 : 0 < p := by linarith
  constructor
  · have : 0 < π / (2 * p) := by positivity
    linarith [pi_pos]
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]

theorem cos_theta_pos {p : ℝ} (hp : 1 < p) : 0 < cos (π / (2 * p)) :=
  cos_pos_of_mem_Ioo (theta_mem hp)

theorem up_eq {p : ℝ} (hp : 1 < p) : up p = -(π / p ^ 2) * (Tf p * (1 + Tf p ^ 2)) := by
  have hc := (cos_theta_pos hp).ne'
  have hinv : (cos (π / (2 * p)) ^ 2)⁻¹ = 1 + tan (π / (2 * p)) ^ 2 := by
    rw [← inv_one_add_tan_sq hc, inv_inv]
  unfold up Tf
  rw [hinv]
  have hp0 : p ≠ 0 := by linarith
  field_simp

/-- `T` is antitone in `p` on `(1, ∞)`. -/
theorem Tf_le_Tf {p p' : ℝ} (hp : 1 < p) (hpp : p ≤ p') : Tf p' ≤ Tf p := by
  have hp0 : 0 < p := by linarith
  unfold Tf
  refine strictMonoOn_tan.monotoneOn (theta_mem (by linarith)) (theta_mem hp) ?_
  exact div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith)

theorem tan_pi_div_four_add {η : ℝ} (h : cos η - sin η ≠ 0) :
    tan (π / 4 + η) = (cos η + sin η) / (cos η - sin η) := by
  rw [tan_eq_sin_div_cos, sin_add, cos_add, sin_pi_div_four, cos_pi_div_four]
  have h2 : √2 / 2 ≠ 0 := by positivity
  have hd : √2 / 2 * cos η - √2 / 2 * sin η ≠ 0 := by rw [← mul_sub]; exact mul_ne_zero h2 h
  rw [div_eq_div_iff hd h]
  ring

/-! ## Boxes for `T` -/

/-- `T(403/300) ≥ 2.34` (`π/(2·403/300) = π/4 + 197π/1612`). -/
theorem Tf_lo : 2.34 ≤ Tf (403 / 300) := by
  set η := 197 * π / 1612 with hη
  have hη1 : 0.3839 ≤ η := by rw [hη]; nlinarith [pi_gt_d6]
  have hη2 : η ≤ 0.384 := by rw [hη]; nlinarith [pi_lt_d6]
  have habs : |η| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hs := (abs_le.mp (Real.sin_bound habs)).1
  have hc := (abs_le.mp (Real.cos_bound habs)).2
  rw [abs_of_nonneg (by linarith)] at hs hc
  have h3 : η ^ 3 ≤ 0.384 ^ 3 := pow_le_pow_left₀ (by linarith) hη2 3
  have h5 : η ^ 5 ≤ 0.384 ^ 5 := pow_le_pow_left₀ (by linarith) hη2 5
  have h4 : η ^ 4 ≤ 0.384 ^ 4 := pow_le_pow_left₀ (by linarith) hη2 4
  have h2 : 0.3839 ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (by norm_num) hη1 2
  have hsin : 0.37437 ≤ sin η := by nlinarith
  have hcos : cos η ≤ 0.92745 := by nlinarith
  have hsin' : sin η ≤ η := sin_le (by linarith)
  have hcos' := one_sub_sq_div_two_le_cos (x := η)
  have hpos : 0 < cos η - sin η := by nlinarith
  have e : π / (2 * (403 / 300)) = π / 4 + η := by rw [hη]; ring
  unfold Tf
  rw [e, tan_pi_div_four_add hpos.ne', le_div_iff₀ hpos]
  nlinarith

/-- `T(199/100) ≤ 1.0081` (`π/(2·199/100) = π/4 + π/796`). -/
theorem Tf_hi2 : Tf (199 / 100) ≤ 1.0081 := by
  set ε := π / 796 with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε2 : ε ≤ 0.0039468 := by rw [hε]; nlinarith [pi_lt_d6]
  have hsin : sin ε ≤ ε := sin_le hε0.le
  have hsin0 : 0 ≤ sin ε := sin_nonneg_of_nonneg_of_le_pi hε0.le (by linarith [pi_gt_three])
  have hcos := one_sub_sq_div_two_le_cos (x := ε)
  have hcos1 := cos_le_one ε
  have hpos : 0 < cos ε - sin ε := by nlinarith
  have e : π / (2 * (199 / 100)) = π / 4 + ε := by rw [hε]; ring
  unfold Tf
  rw [e, tan_pi_div_four_add hpos.ne', div_le_iff₀ hpos]
  nlinarith

theorem Tf_four_thirds_sq : Tf (4 / 3) ^ 2 ≤ 5.82844 := by
  have h : Tf (4 / 3) = tan (3 * π / 8) := by unfold Tf; congr 1; ring
  rw [h, tan_three_pi_div_eight_sq]
  have hs : √2 ≤ 1.41422 := by rw [sqrt_le_left (by norm_num)]; norm_num
  linarith

theorem Tf_two : Tf 2 = 1 := by
  unfold Tf; rw [show π / (2 * 2) = π / 4 by ring, tan_pi_div_four]

/-! ## (a): `d/dp H(p,u(p)) > 0` on `[4/3, 403/300]` -/

theorem Dfun_eq {p : ℝ} (hp : 1 < p) :
    Dfun p = π / p ^ 2 * (Tf p * (1 + Tf p ^ 2)) * (4 * (p - 1) * Tf p ^ 2 - 3 * (2 - p) ^ 2 - 2 * p)
      - (2 * Tf p ^ 4 + (10 - 6 * p) * Tf p ^ 2 + (12 - 6 * p)) := by
  unfold Dfun
  rw [up_eq hp, uu_eq_Tf]
  ring

theorem Dfun_pos {p : ℝ} (hp1 : 4 / 3 ≤ p) (hp2 : p ≤ 403 / 300) : 0 < Dfun p := by
  have hp : 1 < p := by linarith
  have hTlo : 2.34 ≤ Tf p := Tf_lo.trans (Tf_le_Tf hp hp2)
  have hThi2 : Tf p ^ 2 ≤ 5.82844 := by
    have h := Tf_le_Tf (p := 4 / 3) (by norm_num) hp1
    have h0 : 0 ≤ Tf p := by linarith
    nlinarith [Tf_four_thirds_sq]
  rw [Dfun_eq hp]
  set T := Tf p with hT
  have hpi : 1.74 ≤ π / p ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [pi_gt_d6]
  have hcube : 15.15 ≤ T * (1 + T ^ 2) := by nlinarith
  have hX : 26.3 ≤ π / p ^ 2 * (T * (1 + T ^ 2)) := by nlinarith
  have hT2 : 5.4756 ≤ T ^ 2 := by nlinarith
  have hY : 3.28 ≤ 4 * (p - 1) * T ^ 2 - 3 * (2 - p) ^ 2 - 2 * p := by nlinarith
  have hZ : 2 * T ^ 4 + (10 - 6 * p) * T ^ 2 + (12 - 6 * p) ≤ 83.7 := by
    have h4 : T ^ 4 ≤ 5.82844 ^ 2 := by
      rw [show T ^ 4 = (T ^ 2) ^ 2 by ring]; exact pow_le_pow_left₀ (by positivity) hThi2 2
    nlinarith
  nlinarith

/-! ## (c): `d²/dp² H(p,u(p)) > 0` on `[199/100, 2]` -/

/-- `u''`, written with `T`. -/
noncomputable def upp (p : ℝ) : ℝ :=
  2 * π * (Tf p * (1 + Tf p ^ 2)) / p ^ 3 + π ^ 2 * ((1 + 3 * Tf p ^ 2) * (1 + Tf p ^ 2)) / (2 * p ^ 4)

theorem hasDerivAt_Tf {p : ℝ} (hp : 1 < p) : HasDerivAt Tf ((1 + Tf p ^ 2) * (-(π / (2 * p ^ 2)))) p := by
  have hc := (cos_theta_pos hp).ne'
  have h := (Real.hasDerivAt_tan hc).comp p (hasDerivAt_theta (p := p) (by linarith))
  have hinv : 1 / cos (π / (2 * p)) ^ 2 = 1 + Tf p ^ 2 := by
    rw [one_div, ← inv_one_add_tan_sq hc, inv_inv]; rfl
  rw [hinv] at h
  exact h

theorem hasDerivAt_up {p : ℝ} (hp : 1 < p) : HasDerivAt up (upp p) p := by
  have hp0 : p ≠ 0 := by linarith
  have hT := hasDerivAt_Tf hp
  have hcube : HasDerivAt (fun q => Tf q * (1 + Tf q ^ 2))
      ((1 + 3 * Tf p ^ 2) * ((1 + Tf p ^ 2) * (-(π / (2 * p ^ 2))))) p := by
    have h2 : HasDerivAt (fun q => 1 + Tf q ^ 2) (2 * Tf p * ((1 + Tf p ^ 2) * (-(π / (2 * p ^ 2))))) p :=
      ((hT.pow 2).const_add 1).congr_deriv (by simp)
    exact (hT.mul h2).congr_deriv (by ring)
  have hcoef : HasDerivAt (fun q : ℝ => -(π / q ^ 2)) (2 * π / p ^ 3) p := by
    have h := ((hasDerivAt_const p π).div (hasDerivAt_pow 2 p) (pow_ne_zero 2 hp0)).neg
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  have hW := hcoef.mul hcube
  have heq : up =ᶠ[𝓝 p] fun q => -(π / q ^ 2) * (Tf q * (1 + Tf q ^ 2)) := by
    filter_upwards [Ioi_mem_nhds hp] with q hq
    exact up_eq hq
  refine (hW.congr_deriv ?_).congr_of_eventuallyEq heq
  unfold upp
  field_simp

/-- `d/dp Dfun`, as the combinators give it. -/
noncomputable def D2 (p : ℝ) : ℝ :=
  -2 * (2 * uu p * up p) + ((-2) * (2 * uu p * up p) + (-2 * (p - 1)) * (2 * (up p * up p + uu p * upp p)))
    + ((6 * uu p + (-6 * (2 - p) + 2) * up p) + ((-6 * (2 - p) + 2) * up p + (3 * (2 - p) ^ 2 + 2 * p) * upp p)) + 6

theorem hasDerivAt_Dfun {p : ℝ} (hp : 1 < p) : HasDerivAt Dfun (D2 p) p := by
  have hu := hasDerivAt_uu hp
  have hu2 := hasDerivAt_up hp
  have hsq : HasDerivAt (fun p => uu p ^ 2) (2 * uu p * up p) p := (hu.pow 2).congr_deriv (by simp)
  have hprod : HasDerivAt (fun p => 2 * uu p * up p) (2 * (up p * up p + uu p * upp p)) p := by
    have h := (hu.mul hu2).const_mul 2
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp only [Pi.mul_apply]; ring
  have hD := (((hsq.const_mul (-2)).add ((hd_lin (-2) 1 p).mul hprod)).add
    (((hd_lin2 p).mul hu).add ((hd_quad p).mul hu2))).add (hd_quad2 p)
  refine (hD.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  · unfold D2; ring
  · simp only [Dfun, Pi.add_apply, Pi.mul_apply]

theorem D2_pos {p : ℝ} (hp1 : 199 / 100 ≤ p) (hp2 : p ≤ 2) : 0 < D2 p := by
  have hp : 1 < p := by linarith
  have hTlo : 1 ≤ Tf p := Tf_two ▸ Tf_le_Tf hp hp2
  have hThi : Tf p ≤ 1.0081 := (Tf_le_Tf (by norm_num) hp1).trans Tf_hi2
  have hD : D2 p = 8 * Tf p ^ 2 * (π / p ^ 2 * (Tf p * (1 + Tf p ^ 2)))
      - 4 * (p - 1) * ((π / p ^ 2 * (Tf p * (1 + Tf p ^ 2))) ^ 2 + Tf p ^ 2 * upp p) + 6 * Tf p ^ 2
      - 2 * (6 * p - 10) * (π / p ^ 2 * (Tf p * (1 + Tf p ^ 2))) + (3 * (2 - p) ^ 2 + 2 * p) * upp p + 6 := by
    unfold D2; rw [up_eq hp, uu_eq_Tf]; ring
  have hVeq : upp p = π * (2 * (Tf p * (1 + Tf p ^ 2)) / p ^ 3)
      + π ^ 2 * (((1 + 3 * Tf p ^ 2) * (1 + Tf p ^ 2)) / (2 * p ^ 4)) := by
    unfold upp; ring
  rw [hD]
  generalize Tf p = T at hTlo hThi hVeq ⊢
  generalize upp p = V at hVeq ⊢
  have hpi1 := pi_gt_d6
  have hpi2 := pi_lt_d6
  have hp2lo : (199 / 100) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by norm_num) hp1 2
  have hp2hi : p ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by linarith) hp2 2
  have hp3lo : (199 / 100) ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ (by norm_num) hp1 3
  have hp3hi : p ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) hp2 3
  have hp4lo : (199 / 100) ^ 4 ≤ p ^ 4 := pow_le_pow_left₀ (by norm_num) hp1 4
  have hp4hi : p ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) hp2 4
  have hT0 : 0 ≤ T := by linarith
  have hT2lo : 1 ≤ T ^ 2 := one_le_pow₀ hTlo
  have hT3lo : 1 ≤ T ^ 3 := one_le_pow₀ hTlo
  have hT4lo : 1 ≤ T ^ 4 := one_le_pow₀ hTlo
  have hT2hi : T ^ 2 ≤ 1.0163 := (pow_le_pow_left₀ hT0 hThi 2).trans (by norm_num)
  have hT3hi : T ^ 3 ≤ 1.0245 := (pow_le_pow_left₀ hT0 hThi 3).trans (by norm_num)
  have hT4hi : T ^ 4 ≤ 1.03281 := (pow_le_pow_left₀ hT0 hThi 4).trans (by norm_num)
  have ec : T * (1 + T ^ 2) = T + T ^ 3 := by ring
  have eb : (1 + 3 * T ^ 2) * (1 + T ^ 2) = 1 + 4 * T ^ 2 + 3 * T ^ 4 := by ring
  have hclo : 2 ≤ T * (1 + T ^ 2) := by rw [ec]; linarith
  have hchi : T * (1 + T ^ 2) ≤ 2.0326 := by rw [ec]; linarith
  have hc0 : 0 ≤ T * (1 + T ^ 2) := by linarith
  -- bounds for X = π T(1+T²)/p² = -u'
  have hq1 : 0.785398 ≤ π / p ^ 2 := by rw [le_div_iff₀ (by positivity)]; norm_num at hp2hi; linarith
  have hq2 : π / p ^ 2 ≤ 0.7934 := by rw [div_le_iff₀ (by positivity)]; norm_num at hp2lo; linarith
  have hXlo : 1.5707 ≤ π / p ^ 2 * (T * (1 + T ^ 2)) := by
    have := mul_le_mul hq1 hclo (by norm_num) (by linarith); linarith
  have hXhi : π / p ^ 2 * (T * (1 + T ^ 2)) ≤ 1.6127 := by
    have := mul_le_mul hq2 hchi hc0 (by norm_num); linarith
  -- bounds for V = u''
  have ha1 : 1 / 2 ≤ 2 * (T * (1 + T ^ 2)) / p ^ 3 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; norm_num at hp3hi; linarith
  have hb1 : 1 / 4 ≤ ((1 + 3 * T ^ 2) * (1 + T ^ 2)) / (2 * p ^ 4) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity), eb]; norm_num at hp4hi; linarith
  have ha2 : 2 * (T * (1 + T ^ 2)) / p ^ 3 ≤ 0.5159 := by
    rw [div_le_iff₀ (by positivity)]; norm_num at hp3lo; linarith
  have hb2 : ((1 + 3 * T ^ 2) * (1 + T ^ 2)) / (2 * p ^ 4) ≤ 0.2604 := by
    rw [div_le_iff₀ (by positivity), eb]; norm_num at hp4lo; linarith
  have hpi2lo : 9.8695 ≤ π ^ 2 := by nlinarith only [hpi1]
  have hpi2hi : π ^ 2 ≤ 9.86961 := by nlinarith only [hpi2, pi_pos]
  generalize 2 * (T * (1 + T ^ 2)) / p ^ 3 = A at ha1 ha2 hVeq
  generalize ((1 + 3 * T ^ 2) * (1 + T ^ 2)) / (2 * p ^ 4) = B at hb1 hb2 hVeq
  have hVlo : 4.0381 ≤ V := by
    have h1 := mul_le_mul hpi1.le ha1 (by norm_num) pi_pos.le
    have h2 := mul_le_mul hpi2lo hb1 (by norm_num) (by positivity)
    rw [hVeq]; linarith
  have hVhi : V ≤ 4.192 := by
    have h1 := mul_le_mul hpi2.le ha2 (by linarith) (by norm_num)
    have h2 := mul_le_mul hpi2hi hb2 (by linarith) (by norm_num)
    rw [hVeq]; linarith
  generalize π / p ^ 2 * (T * (1 + T ^ 2)) = X at hXlo hXhi ⊢
  -- the terms
  have t1 : 12.5656 ≤ 8 * T ^ 2 * X := by
    have := mul_le_mul hT2lo hXlo (by norm_num) (by linarith); linarith
  have t2 : -27.45 ≤ -4 * (p - 1) * (X ^ 2 + T ^ 2 * V) := by
    have hX2 : X ^ 2 ≤ 1.6127 ^ 2 := pow_le_pow_left₀ (by linarith) hXhi 2
    have hTV : T ^ 2 * V ≤ 1.0163 * 4.192 := mul_le_mul hT2hi hVhi (by linarith) (by norm_num)
    have hS : X ^ 2 + T ^ 2 * V ≤ 6.8612 := by norm_num at hX2 hTV; linarith
    have hnn : 0 ≤ X ^ 2 + T ^ 2 * V := by nlinarith only [hT2lo, hVlo]
    have := mul_le_mul (show p - 1 ≤ 1 by linarith) hS hnn (by norm_num)
    linarith
  have t3 : -6.451 ≤ -2 * (6 * p - 10) * X := by
    have := mul_le_mul (show 6 * p - 10 ≤ 2 by linarith) hXhi (by linarith) (by norm_num); linarith
  have t4 : 16.0716 ≤ (3 * (2 - p) ^ 2 + 2 * p) * V := by
    have hw : 3.98 ≤ 3 * (2 - p) ^ 2 + 2 * p := by nlinarith only [hp1, sq_nonneg (2 - p)]
    have := mul_le_mul hw hVlo (by norm_num) (by nlinarith only [hp2, sq_nonneg (2 - p)]); linarith
  linarith

/-! ## C10e -/

/-- **C10e** (Prop. 5 proof, l.373-378): the paper's three interval steps. -/
theorem H_interval_steps :
    (∀ p ∈ Icc (4 / 3 : ℝ) (403 / 300), 0 < deriv (fun p => H p (uu p)) p) ∧
      (∀ p ∈ Icc (403 / 300 : ℝ) (199 / 100), 0 < H p (uu p)) ∧
      (∀ p ∈ Icc (199 / 100 : ℝ) 2, 0 < deriv (deriv (fun p => H p (uu p))) p) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [(hasDerivAt_Hu (by linarith [hp.1])).deriv]
    exact Dfun_pos hp.1 hp.2
  · exact H_pos (by linarith [hp.1]) (by linarith [hp.2])
  · have hp1 : 1 < p := by linarith [hp.1]
    have hev : deriv (fun p => H p (uu p)) =ᶠ[𝓝 p] Dfun := by
      filter_upwards [Ioi_mem_nhds hp1] with q hq
      exact (hasDerivAt_Hu hq).deriv
    rw [hev.deriv_eq, (hasDerivAt_Dfun hp1).deriv]
    exact D2_pos hp.1 hp.2

end IntervalH

end P18
