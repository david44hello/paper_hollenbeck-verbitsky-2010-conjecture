/-
  HVFalse/Proofs/ThmBIf.lean - Theorem B "if" (the paper) and E plurisubharmonic (C16a)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The three local cases for U(ζ) = tanϑ Re(ζ^q) (principal power, q = p/2 ∈ (1/2,1)):
  (a) ζ ∉ (-∞, 0]: U is the real part of an analytic function, so it has the mean-value property on small circles;
  (b) ζ < 0: U ≥ h near ζ and U(ζ) = h(ζ), where h(ζ) = tanϑ Re(e^{iqπ}(-ζ)^q) is harmonic there (the other branch);
  (c) ζ = 0: the circle average of U on |ζ| = r is tanϑ r^q sin(qπ)/(qπ) > 0 = U(0).
  Local ⇒ global (LocGlob.subharmonic_of_continuous_local) and the rest of Theorem B "if" are in ThmBIfLG / LocGlob
; no textbook axiom is used here.
-/
import HVFalse.Defs.HV
import HVFalse.Defs.PotentialOn
import HVFalse.Proofs.Minorant
import HVFalse.Proofs.Discs
import HVFalse.Proofs.Sector
import HVFalse.Proofs.FailCole

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace ThmBIf

variable {p : ℝ}

/-- `U(ζ) = ‖ζ‖^q e(arg ζ)`, so that `E(z,w) = U(zw)`. -/
noncomputable def Ufun (p : ℝ) (ζ : ℂ) : ℝ := ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ)

theorem Efun_eq_U (p : ℝ) (z w : ℂ) : Efun p z w = Ufun p (z * w) := rfl

theorem Ufun_eq_re (hp1 : 1 < p) (hp2 : p < 2) (ζ : ℂ) :
    Ufun p ζ = ((tan (π / (2 * p)) : ℂ) * ζ ^ ((p / 2 : ℝ) : ℂ)).re := by
  have h := Efun_eq_re hp1 hp2 ζ 1
  rw [Efun_eq_U, mul_one] at h
  rw [Complex.re_ofReal_mul]
  exact h

theorem tan_th_pos (hp1 : 1 < p) (hp2 : p < 2) : 0 < tan (π / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  apply tan_pos_of_pos_of_lt_pi_div_two (by positivity)
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith [pi_pos]

/-- `U` is continuous (arccos form off `0`, as for `M`). -/
theorem Ufun_continuous (hp1 : 1 < p) (hp2 : p < 2) : Continuous (Ufun p) := by
  have hq : 0 < p / 2 := by linarith
  have hform : ∀ ζ : ℂ, ζ ≠ 0 →
      Ufun p ζ = ‖ζ‖ ^ (p / 2) * (tan (π / (2 * p)) * cos (p / 2 * Real.arccos (ζ.re / ‖ζ‖))) := by
    intro ζ hζ
    unfold Ufun ee
    rw [← Complex.cos_arg hζ, ← cos_abs (Complex.arg ζ), Real.arccos_cos (abs_nonneg _) (Complex.abs_arg_le_pi ζ),
      ← cos_abs (p / 2 * Complex.arg ζ), abs_mul, abs_of_pos hq]
  rw [continuous_iff_continuousAt]
  intro ζ0
  by_cases hζ0 : ζ0 = 0
  · subst hζ0
    have hU0 : Ufun p 0 = 0 := by simp [Ufun, zero_rpow hq.ne']
    rw [ContinuousAt, hU0]
    have hbound : ∀ ζ : ℂ, ‖Ufun p ζ‖ ≤ ‖ζ‖ ^ (p / 2) * |tan (π / (2 * p))| := by
      intro ζ
      unfold Ufun ee
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rpow_nonneg (norm_nonneg ζ) _), abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
        (rpow_nonneg (norm_nonneg ζ) _)
    have hlim : Tendsto (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * |tan (π / (2 * p))|) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * |tan (π / (2 * p))|) :=
        (continuous_norm.rpow_const (fun _ => Or.inr hq.le)).mul continuous_const
      simpa [zero_rpow hq.ne'] using this.tendsto 0
    exact squeeze_zero_norm hbound hlim
  · have hn : ‖ζ0‖ ≠ 0 := norm_ne_zero_iff.mpr hζ0
    have hcont : ContinuousAt (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * (tan (π / (2 * p)) *
        cos (p / 2 * Real.arccos (ζ.re / ‖ζ‖)))) ζ0 := by
      refine ((continuous_norm.rpow_const (fun _ => Or.inr hq.le)).continuousAt).mul (continuousAt_const.mul ?_)
      exact continuous_cos.continuousAt.comp (continuousAt_const.mul (Real.continuous_arccos.continuousAt.comp
        (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt hn)))
    refine hcont.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hζ0] with ζ hζ
    exact (hform ζ hζ).symm

/-- Truncated sub-mean from a harmonic minorant touching at the centre. -/
theorem trunc_submean {v h : ℂ → ℝ} (hv : Continuous v) {a : ℂ} {r : ℝ} (hhint : CircleIntegrable h a r)
    (hmean : circleAverage h a r = h a) (hle : ∀ z ∈ sphere a |r|, h z ≤ v z) (heq : h a = v a) (n : ℕ) :
    trunc n ((v a : ℝ) : EReal) ≤ circleAverage (fun z => trunc n ((v z : ℝ) : EReal)) a r := by
  simp only [FailCole.trunc_coe]
  have hvint : CircleIntegrable v a r := hv.continuousOn.circleIntegrable'
  have hmint : CircleIntegrable (fun z => max (v z) (-(n : ℝ))) a r :=
    (hv.max continuous_const).continuousOn.circleIntegrable'
  have h1 : v a ≤ circleAverage (fun z => max (v z) (-(n : ℝ))) a r := by
    rw [← heq, ← hmean]
    exact circleAverage_mono hhint hmint (fun z hz => le_trans (hle z hz) (le_max_left _ _))
  have h2 : -(n : ℝ) ≤ circleAverage (fun z => max (v z) (-(n : ℝ))) a r := by
    have := circleAverage_mono (circleIntegrable_const (-(n : ℝ)) a r) hmint (fun z _ => le_max_right (v z) _)
    rwa [circleAverage_const] at this
  exact max_le h1 h2

/-- Case (a): off the cut, `U` has the mean-value property on small circles. -/
theorem local_slit (hp1 : 1 < p) (hp2 : p < 2) {a : ℂ} (ha : a ∈ Complex.slitPlane) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → ∀ n : ℕ,
      trunc n ((Ufun p a : ℝ) : EReal) ≤ circleAverage (fun z => trunc n ((Ufun p z : ℝ) : EReal)) a r := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_slitPlane a ha
  refine ⟨ρ, hρ, fun r hr hrρ n => ?_⟩
  have hfun : Ufun p = fun z => ((tan (π / (2 * p)) : ℂ) * z ^ ((p / 2 : ℝ) : ℂ)).re := funext (Ufun_eq_re hp1 hp2)
  have hh : InnerProductSpace.HarmonicOnNhd (Ufun p) (closedBall a |r|) := by
    intro z hz
    rw [abs_of_pos hr] at hz
    have hzs : z ∈ Complex.slitPlane := hball (lt_of_le_of_lt hz hrρ)
    rw [hfun]
    exact (analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hzs)).harmonicAt_re
  exact trunc_submean (Ufun_continuous hp1 hp2) ((hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable')
    hh.circleAverage_eq (fun _ _ => le_refl _) rfl n

/-- The other branch near the negative axis: `h(ζ) = tanϑ Re(e^{iqπ}(-ζ)^q)`. -/
noncomputable def hbranch (p : ℝ) (ζ : ℂ) : ℝ :=
  ((((tan (π / (2 * p)) * cos (p / 2 * π) : ℝ) : ℂ) - ((-(tan (π / (2 * p)) * sin (p / 2 * π)) : ℝ) : ℂ) * Complex.I)
    * (-ζ) ^ ((p / 2 : ℝ) : ℂ)).re

theorem hbranch_polar {ζ : ℂ} (hζ : ζ ≠ 0) :
    hbranch p ζ = tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * Complex.arg (-ζ) + p / 2 * π)) := by
  unfold hbranch
  rw [Sector.re_coef_cpow (neg_ne_zero.mpr hζ), norm_neg, cos_add]
  ring

/-- Case (b): at a negative real point, `U` dominates the harmonic branch `h`, with equality at the point. -/
theorem local_neg (hp1 : 1 < p) (hp2 : p < 2) {a : ℂ} (ha : a ∉ Complex.slitPlane) (ha0 : a ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → ∀ n : ℕ,
      trunc n ((Ufun p a : ℝ) : EReal) ≤ circleAverage (fun z => trunc n ((Ufun p z : ℝ) : EReal)) a r := by
  have hq : 0 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  have hT := tan_th_pos hp1 hp2
  -- a is a negative real
  rw [Complex.mem_slitPlane_iff] at ha
  push Not at ha
  have hare : a.re < 0 := by
    rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · exact absurd (Complex.ext h ha.2) ha0
  set γ := min (π / (p / 2) - π) (π / 2) with hγ
  have hγ1 : π < π / (p / 2) := by rw [lt_div_iff₀ hq]; nlinarith [pi_pos]
  have hγ0 : 0 < γ := lt_min (by linarith) (by positivity)
  have hγπ2 : γ ≤ π / 2 := min_le_right _ _
  have hγq : γ ≤ π / (p / 2) - π := min_le_left _ _
  have hcγ : cos γ < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [pi_pos]) hγ0; rwa [cos_zero] at this
  have hcγ0 : 0 ≤ cos γ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hγπ2⟩
  -- a neighbourhood where -ζ lies in the cone of half-angle γ
  have hev : ∀ᶠ ζ in 𝓝 a, ‖ζ‖ * cos γ < (-ζ).re := by
    have h1 : ContinuousAt (fun ζ : ℂ => ‖ζ‖ * cos γ) a := (continuous_norm.mul continuous_const).continuousAt
    have h2 : ContinuousAt (fun ζ : ℂ => (-ζ).re) a := (Complex.continuous_re.comp continuous_neg).continuousAt
    refine h1.eventually_lt h2 ?_
    have hna : ‖a‖ = -a.re := by
      rw [show a = ((a.re : ℝ) : ℂ) from Complex.ext rfl (by simpa using ha.2), Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by simpa using hare)]
      simp
    show ‖a‖ * cos γ < (-a).re
    rw [hna, Complex.neg_re]
    nlinarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨ρ, hρ, fun r hr hrρ n => ?_⟩
  have hcone : ∀ ζ ∈ closedBall a r, ζ ≠ 0 ∧ -ζ ∈ Complex.slitPlane ∧ |Complex.arg (-ζ)| ≤ γ := by
    intro ζ hζ
    have hc := hball (lt_of_le_of_lt (mem_closedBall.mp hζ) hrρ)
    have hz : ζ ≠ 0 := by rintro rfl; simp at hc
    have hre : 0 < (-ζ).re := lt_of_le_of_lt (mul_nonneg (norm_nonneg ζ) hcγ0) hc
    refine ⟨hz, Complex.mem_slitPlane_iff.mpr (Or.inl hre), ?_⟩
    have hrot : Sector.rot 0 (-ζ) = -ζ := by simp [Sector.rot]
    have := Sector.abs_arg_le_of_cone (μ := 0) hγ0 (by linarith [pi_pos]) (neg_ne_zero.mpr hz)
      (by rw [hrot, norm_neg]; exact hc.le)
    rwa [hrot] at this
  -- U ≥ h on the ball, equality at a
  have hle : ∀ ζ ∈ closedBall a r, hbranch p ζ ≤ Ufun p ζ := by
    intro ζ hζ
    obtain ⟨hz, -, hβ⟩ := hcone ζ hζ
    rw [hbranch_polar hz]
    unfold Ufun ee
    set β := Complex.arg (-ζ)
    have hβq : p / 2 * (|β| + π) ≤ π := by
      have : |β| + π ≤ π / (p / 2) := by linarith
      calc p / 2 * (|β| + π) ≤ p / 2 * (π / (p / 2)) := mul_le_mul_of_nonneg_left this hq.le
        _ = π := by field_simp
    have hkey : cos (p / 2 * β + p / 2 * π) ≤ cos (p / 2 * Complex.arg ζ) := by
      rcases lt_trichotomy ζ.im 0 with him | him | him
      · -- Im ζ < 0: arg ζ = β - π, β > 0
        have hb : Complex.arg ζ = β - π := by
          have := Complex.arg_neg_eq_arg_sub_pi_of_im_pos (x := -ζ) (by simpa using him); simpa using this
        have hβpos : 0 ≤ β := by
          have := Complex.arg_nonneg_iff.mpr (show 0 ≤ (-ζ).im by simp; linarith); exact this
        rw [hb, ← cos_abs (p / 2 * (β - π)), abs_mul, abs_of_pos hq, abs_sub_comm, abs_of_nonneg (by linarith [abs_le.mp hβ])]
        apply cos_le_cos_of_nonneg_of_le_pi (by nlinarith [abs_le.mp hβ]) (by rw [abs_of_nonneg hβpos] at hβq; nlinarith)
        nlinarith
      · -- Im ζ = 0: ζ negative real, β = 0, arg ζ = π
        have hζre : ζ.re < 0 := by
          obtain ⟨-, hs, -⟩ := hcone ζ hζ
          rcases Complex.mem_slitPlane_iff.mp hs with h | h
          · simpa using h
          · exact absurd (by simpa using him) h
        have hζr : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
        have hb0 : β = 0 := by
          show Complex.arg (-ζ) = 0
          rw [hζr, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith)]
        have hpi : Complex.arg ζ = π := by rw [hζr, Complex.arg_ofReal_of_neg hζre]
        rw [hb0, hpi, mul_zero, zero_add]
      · -- Im ζ > 0: arg ζ = β + π
        have hb : Complex.arg ζ = β + π := by
          have := Complex.arg_neg_eq_arg_add_pi_of_im_neg (x := -ζ) (by simpa using him); simpa using this
        rw [hb]; ring_nf; exact le_refl _
    have hn : 0 ≤ ‖ζ‖ ^ (p / 2) := rpow_nonneg (norm_nonneg ζ) _
    calc tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * β + p / 2 * π))
        ≤ tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * Complex.arg ζ)) := by gcongr
      _ = ‖ζ‖ ^ (p / 2) * (tan (π / (2 * p)) * cos (p / 2 * Complex.arg ζ)) := by ring
  have heq : hbranch p a = Ufun p a := by
    have har : a = ((a.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using ha.2)
    rw [hbranch_polar ha0]
    unfold Ufun ee
    have hb0 : Complex.arg (-a) = 0 := by rw [har, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith)]
    have hpi : Complex.arg a = π := by rw [har, Complex.arg_ofReal_of_neg hare]
    rw [hb0, hpi]; ring_nf
  -- h harmonic on the closed ball
  have hh : InnerProductSpace.HarmonicOnNhd (hbranch p) (closedBall a |r|) := by
    intro z hz
    rw [abs_of_pos hr] at hz
    obtain ⟨-, hs, -⟩ := hcone z hz
    unfold hbranch
    exact (analyticAt_const.mul ((analyticAt_id.neg).cpow analyticAt_const hs)).harmonicAt_re
  exact trunc_submean (Ufun_continuous hp1 hp2) ((hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable')
    hh.circleAverage_eq (fun z hz => hle z (sphere_subset_closedBall (by rwa [abs_of_pos hr] at hz))) heq n

/-- Case (c): at `0`, the circle averages of `U` are positive. -/
theorem local_zero (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → ∀ n : ℕ,
      trunc n ((Ufun p 0 : ℝ) : EReal) ≤ circleAverage (fun z => trunc n ((Ufun p z : ℝ) : EReal)) 0 r := by
  have hq : 0 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  have hT := tan_th_pos hp1 hp2
  refine ⟨1, one_pos, fun r hr _ n => ?_⟩
  have hU0 : Ufun p 0 = 0 := by simp [Ufun, zero_rpow hq.ne']
  have hUc := Ufun_continuous hp1 hp2
  -- the circle average of U on |ζ| = r
  have hpt : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), Ufun p (circleMap 0 r (θ + -π))
      = tan (π / (2 * p)) * r ^ (p / 2) * cos (p / 2 * (θ - π)) := by
    intro θ hθ
    rw [uIcc_of_le two_pi_pos.le] at hθ
    rw [circleMap_zero]
    unfold Ufun ee
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I]
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      have : toIocMod two_pi_pos (-π) (0 + -π) = π := by
        rw [zero_add, toIocMod_eq_iff]; exact ⟨⟨by linarith [pi_pos], by linarith⟩, -1, by simp; ring⟩
      rw [this, show p / 2 * ((0:ℝ) - π) = -(p / 2 * π) by ring, cos_neg]; ring
    · rw [(toIocMod_eq_self two_pi_pos).mpr ⟨by linarith, by linarith [hθ.2]⟩]
      ring_nf
  have hint : ∫ θ in (0 : ℝ)..(2 * π), tan (π / (2 * p)) * r ^ (p / 2) * cos (p / 2 * (θ - π))
      = tan (π / (2 * p)) * r ^ (p / 2) * (2 * sin (p / 2 * π) / (p / 2)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have e : (fun θ : ℝ => cos (p / 2 * (θ - π))) = fun θ => cos (p / 2 * θ - p / 2 * π) := by funext θ; ring_nf
    rw [e, intervalIntegral.integral_comp_mul_sub (fun x => cos x) hq.ne', integral_cos, smul_eq_mul]
    rw [show p / 2 * (2 * π) - p / 2 * π = p / 2 * π by ring, show p / 2 * 0 - p / 2 * π = -(p / 2 * π) by ring, sin_neg]
    field_simp; ring
  have hsin : 0 < sin (p / 2 * π) := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  have havg : 0 ≤ circleAverage (Ufun p) 0 r := by
    rw [circleAverage_eq_integral_add (-π), intervalIntegral.integral_congr hpt, hint, smul_eq_mul]
    have : 0 < tan (π / (2 * p)) * r ^ (p / 2) * (2 * sin (p / 2 * π) / (p / 2)) := by positivity
    positivity
  simp only [FailCole.trunc_coe, hU0]
  have hmint : CircleIntegrable (fun z => max (Ufun p z) (-(n : ℝ))) 0 r :=
    (hUc.max continuous_const).continuousOn.circleIntegrable'
  have : circleAverage (Ufun p) 0 r ≤ circleAverage (fun z => max (Ufun p z) (-(n : ℝ))) 0 r :=
    circleAverage_mono hUc.continuousOn.circleIntegrable' hmint (fun z _ => le_max_left _ _)
  have hn : (0 : ℝ) ≥ -(n : ℝ) := by simp
  rw [max_eq_left hn]
  linarith

end ThmBIf

end P18
