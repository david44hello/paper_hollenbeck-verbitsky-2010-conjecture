/-
  HVFalse/Proofs/UComp.lean - U∘h is locally sub-mean for every entire h (no Demailly 5.11)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  U(ζ) = tanϑ Re ζ^q (q = p/2 ∈ (1/2,1)). For h entire and a ∈ ℂ, U(h(a)) ≤ mean of U∘h on small circles about a:
  (a) h(a) ≠ 0: take a holomorphic B near h(a) with Re B ≤ U everywhere and Re B(h(a)) = U(h(a)). Off the cut B is the
      principal branch (Re B = U). On the cut B is `hbranch`, and hbranch ≤ U on all of ℂ (`hbranch_le`). Re(B∘h) is
      harmonic near the closed disc, so U(h(a)) = mean Re(B∘h) ≤ mean U∘h.
  (b) h(a) = 0 and h ≢ 0 near a: h = (z-a)^m g̃ with g̃ continuous, g̃(a) ≠ 0, m ≥ 1 (isolated zeros). On |z-a| = r the
      mean of U∘h is r^{mq} I(r)/2π with I continuous and I(0) = |g̃(a)|^q ∫_{-π}^{π} tanϑ cos(qt) dt > 0.
  (c) h ≡ 0 near a: the mean is 0 = U(0).
-/
import HVFalse.Proofs.ThmBIf
import HVFalse.Proofs.ColeHom

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace UComp

open ThmBIf

variable {p : ℝ}

/-- `U` is `q`-homogeneous. -/
theorem Ufun_homog (t : ℝ) (ht : 0 < t) (w : ℂ) : Ufun p ((t : ℂ) * w) = t ^ (p / 2) * Ufun p w := by
  unfold Ufun
  rw [Complex.arg_real_mul w ht, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    mul_rpow ht.le (norm_nonneg w)]
  ring

theorem hbranch_zero (hq : 0 < p / 2) : hbranch p 0 = 0 := by
  unfold hbranch
  rw [neg_zero, Complex.zero_cpow (by exact_mod_cast hq.ne' : ((p / 2 : ℝ) : ℂ) ≠ 0), mul_zero, Complex.zero_re]

/-- On ALL of ℂ, the other branch lies below `U` (`1/2 < q < 1`). -/
theorem hbranch_le (hp1 : 1 < p) (hp2 : p < 2) (ζ : ℂ) : hbranch p ζ ≤ Ufun p ζ := by
  have hq : 0 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  have hT := tan_th_pos hp1 hp2
  by_cases hz : ζ = 0
  · subst hz; rw [hbranch_zero hq]; simp [Ufun, zero_rpow hq.ne']
  rw [hbranch_polar hz]
  unfold Ufun ee
  set β := Complex.arg (-ζ) with hβ
  have hkey : cos (p / 2 * β + p / 2 * π) ≤ cos (p / 2 * Complex.arg ζ) := by
    rcases lt_trichotomy ζ.im 0 with him | him | him
    · -- Im ζ < 0: arg ζ = β - π with β ∈ [0, π]
      have hb : Complex.arg ζ = β - π := by
        have := Complex.arg_neg_eq_arg_sub_pi_of_im_pos (x := -ζ) (by simpa using him); simpa using this
      have hβ0 : 0 ≤ β := Complex.arg_nonneg_iff.mpr (by simp; linarith)
      have hβπ : β ≤ π := Complex.arg_le_pi _
      rw [hb, show p / 2 * (β - π) = -(p / 2 * (π - β)) by ring, cos_neg]
      have hu0 : 0 ≤ p / 2 * (π - β) := mul_nonneg hq.le (by linarith)
      by_cases hv : p / 2 * β + p / 2 * π ≤ π
      · exact cos_le_cos_of_nonneg_of_le_pi hu0 hv (by nlinarith [mul_nonneg hq.le hβ0])
      · push Not at hv
        have hw : cos (p / 2 * β + p / 2 * π) = cos (2 * π - (p / 2 * β + p / 2 * π)) := by
          rw [cos_sub, cos_two_pi, sin_two_pi]; ring
        rw [hw]
        have hqπ : p / 2 * π ≤ 1 * π := mul_le_mul_of_nonneg_right hq1.le pi_pos.le
        exact cos_le_cos_of_nonneg_of_le_pi hu0 (by linarith) (by nlinarith)
    · -- Im ζ = 0
      have hζr : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
      have hre0 : ζ.re ≠ 0 := fun h0 => hz (Complex.ext h0 him)
      rcases lt_or_gt_of_ne hre0 with hneg | hpos
      · have hb0 : β = 0 := by
          rw [hβ, hζr, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith)]
        have hpi : Complex.arg ζ = π := by rw [hζr, Complex.arg_ofReal_of_neg hneg]
        rw [hb0, hpi, mul_zero, zero_add]
      · have hbπ : β = π := by
          rw [hβ, hζr, ← Complex.ofReal_neg, Complex.arg_ofReal_of_neg (by linarith)]
        have h0 : Complex.arg ζ = 0 := by rw [hζr, Complex.arg_ofReal_of_nonneg hpos.le]
        rw [hbπ, h0, mul_zero, cos_zero]
        exact cos_le_one _
    · -- Im ζ > 0: arg ζ = β + π
      have hb : Complex.arg ζ = β + π := by
        have := Complex.arg_neg_eq_arg_add_pi_of_im_neg (x := -ζ) (by simpa using him); simpa using this
      rw [hb]
      exact le_of_eq (by congr 1; ring)
  have hn : 0 ≤ ‖ζ‖ ^ (p / 2) := rpow_nonneg (norm_nonneg ζ) _
  calc tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * β + p / 2 * π))
      ≤ tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * Complex.arg ζ)) := by gcongr
    _ = ‖ζ‖ ^ (p / 2) * (tan (π / (2 * p)) * cos (p / 2 * Complex.arg ζ)) := by ring

/-- On the negative axis the branch touches `U`. -/
theorem hbranch_eq_of_neg {ζ : ℂ} (hre : ζ.re < 0) (him : ζ.im = 0) : hbranch p ζ = Ufun p ζ := by
  have hζ0 : ζ ≠ 0 := fun h0 => by simp [h0] at hre
  have har : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using him)
  rw [hbranch_polar hζ0]
  unfold Ufun ee
  have hb0 : Complex.arg (-ζ) = 0 := by rw [har, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith)]
  have hpi : Complex.arg ζ = π := by rw [har, Complex.arg_ofReal_of_neg hre]
  rw [hb0, hpi]; ring_nf

/-- A harmonic minorant touching at the centre gives the sub-mean inequality. -/
theorem submean_of_minorant {v k : ℂ → ℝ} (hv : Continuous v) {a : ℂ} {r : ℝ}
    (hk : InnerProductSpace.HarmonicOnNhd k (closedBall a |r|)) (hle : ∀ z, k z ≤ v z) (heq : k a = v a) :
    v a ≤ circleAverage v a r := by
  rw [← heq, ← hk.circleAverage_eq]
  exact circleAverage_mono ((hk.continuousOn.mono sphere_subset_closedBall).circleIntegrable')
    hv.continuousOn.circleIntegrable' (fun z _ => hle z)

/-- Case (a): `h(a) ≠ 0`. -/
theorem local_ne (hp1 : 1 < p) (hp2 : p < 2) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {a : ℂ} (ha : h a ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → Ufun p (h a) ≤ circleAverage (fun z => Ufun p (h z)) a r := by
  have hUc : Continuous (fun z => Ufun p (h z)) := (Ufun_continuous hp1 hp2).comp hh.continuous
  by_cases hs : h a ∈ Complex.slitPlane
  · have hopen : IsOpen (h ⁻¹' Complex.slitPlane) := Complex.isOpen_slitPlane.preimage hh.continuous
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen a hs
    refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
    have hk : InnerProductSpace.HarmonicOnNhd
        (fun z => ((tan (π / (2 * p)) : ℂ) * h z ^ ((p / 2 : ℝ) : ℂ)).re) (closedBall a |r|) := by
      intro z hz
      rw [abs_of_pos hr] at hz
      have hzs : h z ∈ Complex.slitPlane := hball (lt_of_le_of_lt hz hrρ)
      exact (analyticAt_const.mul ((hh.analyticAt z).cpow analyticAt_const hzs)).harmonicAt_re
    exact submean_of_minorant hUc hk (fun z => (Ufun_eq_re hp1 hp2 (h z)).symm.le) (Ufun_eq_re hp1 hp2 (h a)).symm
  · rw [Complex.mem_slitPlane_iff] at hs
    push Not at hs
    have hre : (h a).re < 0 := lt_of_le_of_ne hs.1 (fun h0 => ha (Complex.ext h0 hs.2))
    have hneg : -h a ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
    have hopen : IsOpen ((fun z => -h z) ⁻¹' Complex.slitPlane) :=
      Complex.isOpen_slitPlane.preimage hh.continuous.neg
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hopen a hneg
    refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
    have hk : InnerProductSpace.HarmonicOnNhd (fun z => hbranch p (h z)) (closedBall a |r|) := by
      intro z hz
      rw [abs_of_pos hr] at hz
      have hzs : -h z ∈ Complex.slitPlane := hball (lt_of_le_of_lt hz hrρ)
      unfold hbranch
      exact (analyticAt_const.mul (((hh.analyticAt z).neg).cpow analyticAt_const hzs)).harmonicAt_re
    exact submean_of_minorant hUc hk (fun z => hbranch_le hp1 hp2 (h z)) (hbranch_eq_of_neg hre hs.2)

/-- `U(e^{iψ})`, a `2π`-periodic continuous function equal to `tanϑ cos(qψ)` on `[-π, π]`. -/
noncomputable def Ecirc (p ψ : ℝ) : ℝ := Ufun p (Complex.exp ((ψ : ℂ) * Complex.I))

theorem Ecirc_periodic : Function.Periodic (Ecirc p) (2 * π) := by
  intro ψ
  unfold Ecirc
  congr 1
  rw [show (((ψ + 2 * π : ℝ) : ℂ)) * Complex.I = (ψ : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem Ecirc_continuous (hp1 : 1 < p) (hp2 : p < 2) : Continuous (Ecirc p) :=
  (Ufun_continuous hp1 hp2).comp (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))

theorem Ecirc_eq {ψ : ℝ} (hψ : ψ ∈ Icc (-π) π) : Ecirc p ψ = tan (π / (2 * p)) * cos (p / 2 * ψ) := by
  unfold Ecirc Ufun ee
  rw [Complex.norm_exp_ofReal_mul_I, one_rpow, one_mul, Complex.arg_exp_mul_I]
  rcases eq_or_lt_of_le hψ.1 with h0 | h0
  · subst h0
    have : toIocMod two_pi_pos (-π) (-π) = π := by
      rw [toIocMod_eq_iff]; exact ⟨⟨by linarith [pi_pos], by linarith⟩, -1, by simp; ring⟩
    rw [this, show p / 2 * -π = -(p / 2 * π) by ring, cos_neg]
  · rw [(toIocMod_eq_self two_pi_pos).mpr ⟨h0, by linarith [hψ.2]⟩]

theorem integral_Ecirc (hp1 : 1 < p) (hp2 : p < 2) :
    ∫ ψ in (-π)..π, Ecirc p ψ = tan (π / (2 * p)) * (2 * sin (p / 2 * π) / (p / 2)) := by
  have hq : 0 < p / 2 := by linarith
  rw [intervalIntegral.integral_congr (g := fun ψ => tan (π / (2 * p)) * cos (p / 2 * ψ))
    (fun ψ hψ => Ecirc_eq (by rwa [uIcc_of_le (by linarith [pi_pos])] at hψ)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun x => cos x) hq.ne',
    integral_cos, smul_eq_mul, show p / 2 * -π = -(p / 2 * π) by ring, sin_neg]
  field_simp
  ring

/-- `∫₀^{2π} U(e^{i(mθ+β)}) dθ = ∫_{-π}^{π} U(e^{iψ}) dψ` for `m ≥ 1`. -/
theorem integral_Ecirc_comp (hp1 : 1 < p) (hp2 : p < 2) {m : ℕ} (hm : m ≠ 0) (β : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), Ecirc p (m * θ + β) = ∫ ψ in (-π)..π, Ecirc p ψ := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hint : ∀ t₁ t₂ : ℝ, IntervalIntegrable (Ecirc p) volume t₁ t₂ :=
    fun _ _ => (Ecirc_continuous hp1 hp2).intervalIntegrable _ _
  rw [intervalIntegral.integral_comp_mul_add (fun x => Ecirc p x) hm' β, mul_zero, zero_add,
    show (m : ℝ) * (2 * π) + β = β + (m : ℤ) • (2 * π) by rw [zsmul_eq_mul]; push_cast; ring,
    Ecirc_periodic.intervalIntegral_add_zsmul_eq (m : ℤ) β hint, zsmul_eq_mul,
    Ecirc_periodic.intervalIntegral_add_eq β (-π), show -π + 2 * π = π by ring, smul_eq_mul]
  push_cast
  field_simp

/-- Case (b)/(c): `h(a) = 0`. -/
theorem local_zero_comp (hp1 : 1 < p) (hp2 : p < 2) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {a : ℂ} (ha : h a = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → Ufun p (h a) ≤ circleAverage (fun z => Ufun p (h z)) a r := by
  have hq : 0 < p / 2 := by linarith
  have hT := tan_th_pos hp1 hp2
  have hU0 : Ufun p 0 = 0 := by simp [Ufun, zero_rpow hq.ne']
  rw [ha, hU0]
  by_cases hz : ∀ᶠ z in 𝓝 a, h z = 0
  · obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hz
    refine ⟨ρ, hρ, fun r hr hrρ => ?_⟩
    have heq : Set.EqOn (fun z => Ufun p (h z)) (fun _ => (0 : ℝ)) (sphere a |r|) := by
      intro z hzs
      rw [abs_of_pos hr, mem_sphere] at hzs
      show Ufun p (h z) = 0
      rw [hball (show dist z a < ρ by rw [hzs]; exact hrρ), hU0]
    rw [circleAverage_congr_sphere heq, circleAverage_const]
  obtain ⟨m, g, hg, hga, hfac⟩ := ((hh.analyticAt a).exists_eventuallyEq_pow_smul_nonzero_iff).mpr hz
  have hm : m ≠ 0 := by
    rintro rfl
    have := hfac.self_of_nhds
    rw [ha, pow_zero, one_smul] at this
    exact hga this.symm
  -- a global continuous cofactor g̃ with h = (z-a)^m g̃
  set gt : ℂ → ℂ := fun z => if z = a then g a else h z / (z - a) ^ m with hgt
  have hgt_eq : ∀ᶠ z in 𝓝 a, g z = gt z := by
    filter_upwards [hfac] with z hz
    by_cases hza : z = a
    · subst hza; simp [hgt]
    · have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hgt, if_neg hza, hz, smul_eq_mul]
      field_simp
  have hgt_cont : Continuous gt := by
    rw [continuous_iff_continuousAt]
    intro z0
    by_cases hz0 : z0 = a
    · subst hz0; exact hg.continuousAt.congr hgt_eq
    · have hne : (z0 - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz0)
      have hc : ContinuousAt (fun z => h z / (z - a) ^ m) z0 :=
        hh.continuous.continuousAt.div ((continuous_id.sub continuous_const).pow m).continuousAt hne
      refine hc.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hz0] with z hz
      simp only [hgt, if_neg hz]
  have hfac_all : ∀ z, h z = (z - a) ^ m * gt z := by
    intro z
    by_cases hza : z = a
    · subst hza; rw [ha, sub_self, zero_pow hm, zero_mul]
    · have hne : (z - a) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hgt, if_neg hza]
      field_simp
  have hgta : gt a ≠ 0 := by simpa [hgt] using hga
  -- the parametric integral I(r)
  set Φ : ℝ → ℝ → ℝ := fun r θ => Ufun p (Complex.exp ((θ : ℂ) * Complex.I) ^ m * gt (circleMap a r θ)) with hΦ
  have hcm : Continuous (fun x : ℝ × ℝ => circleMap a x.1 x.2) := by
    unfold circleMap; fun_prop
  have hΦc : Continuous (Function.uncurry Φ) := by
    have h1 : Continuous (fun x : ℝ × ℝ => Complex.exp ((x.2 : ℂ) * Complex.I) ^ m) := by fun_prop
    exact (Ufun_continuous hp1 hp2).comp (h1.mul (hgt_cont.comp hcm))
  set I : ℝ → ℝ := fun r => ∫ θ in (0 : ℝ)..(2 * π), Φ r θ with hI
  have hIc : Continuous I := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hΦc 0 (2 * π)
  have hI0 : 0 < I 0 := by
    have hpt : ∀ θ : ℝ, Φ 0 θ = ‖gt a‖ ^ (p / 2) * Ecirc p (m * θ + Complex.arg (gt a)) := by
      intro θ
      have hw : Complex.exp ((θ : ℂ) * Complex.I) ^ m * gt a =
          ((‖gt a‖ : ℝ) : ℂ) * Complex.exp (((m * θ + Complex.arg (gt a) : ℝ) : ℂ) * Complex.I) := by
        conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (gt a), ← Complex.exp_nat_mul]
        rw [show (((m * θ + Complex.arg (gt a) : ℝ) : ℂ)) * Complex.I
            = (m : ℂ) * ((θ : ℂ) * Complex.I) + (Complex.arg (gt a) : ℂ) * Complex.I by push_cast; ring,
          Complex.exp_add]
        ring
      simp only [hΦ, circleMap_zero_radius, Function.const_apply, Ecirc]
      rw [hw, Ufun_homog _ (norm_pos_iff.mpr hgta)]
    simp only [hI, hpt, intervalIntegral.integral_const_mul, integral_Ecirc_comp hp1 hp2 hm, integral_Ecirc hp1 hp2]
    have hsin : 0 < sin (p / 2 * π) := sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
    have hn : 0 < ‖gt a‖ := norm_pos_iff.mpr hgta
    exact mul_pos (rpow_pos_of_pos hn _) (mul_pos hT (div_pos (mul_pos two_pos hsin) hq))
  obtain ⟨δ, hδ, hδI⟩ := Metric.eventually_nhds_iff.mp ((hIc.tendsto 0).eventually (lt_mem_nhds hI0))
  refine ⟨δ, hδ, fun r hr hrδ => ?_⟩
  have hIr : 0 < I r := hδI (by rw [Real.dist_eq, sub_zero, abs_of_pos hr]; exact hrδ)
  have hpt : ∀ θ : ℝ, Ufun p (h (circleMap a r θ)) = (r ^ m) ^ (p / 2) * Φ r θ := by
    intro θ
    rw [hfac_all, circleMap_sub_center, circleMap_zero, mul_pow, ← Complex.ofReal_pow, mul_assoc,
      Ufun_homog _ (pow_pos hr m)]
  rw [circleAverage_def, smul_eq_mul]
  simp only [hpt, intervalIntegral.integral_const_mul]
  have : 0 < (2 * π)⁻¹ * ((r ^ m) ^ (p / 2) * I r) :=
    mul_pos (inv_pos.mpr two_pi_pos) (mul_pos (rpow_pos_of_pos (pow_pos hr m) _) hIr)
  exact this.le

/-- **`U∘h` is locally sub-mean** for every entire `h` (no textbook axiom). -/
theorem Ufun_comp_local (hp1 : 1 < p) (hp2 : p < 2) {h : ℂ → ℂ} (hh : Differentiable ℂ h) (a : ℂ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → Ufun p (h a) ≤ circleAverage (fun z => Ufun p (h z)) a r := by
  by_cases ha : h a = 0
  · exact local_zero_comp hp1 hp2 hh ha
  · exact local_ne hp1 hp2 hh ha

theorem Ufun_comp_continuous (hp1 : 1 < p) (hp2 : p < 2) {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    Continuous (fun z => Ufun p (h z)) :=
  (Ufun_continuous hp1 hp2).comp hh.continuous

/-- The truncated form (used by `IsSubharmonic`) follows from the plain sub-mean inequality for continuous `v`. -/
theorem trunc_of_submean {v : ℂ → ℝ} (hv : Continuous v) {a : ℂ} {r : ℝ} (h : v a ≤ circleAverage v a r) (n : ℕ) :
    trunc n ((v a : ℝ) : EReal) ≤ circleAverage (fun z => trunc n ((v z : ℝ) : EReal)) a r := by
  simp only [FailCole.trunc_coe]
  exact ColeHom.max_const_submean hv.continuousOn.circleIntegrable' h

end UComp

end P18
