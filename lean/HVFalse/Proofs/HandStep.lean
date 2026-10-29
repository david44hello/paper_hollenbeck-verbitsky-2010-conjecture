/-
  HVFalse/Proofs/HandStep.lean - C13m_hand_step: the hand step of Prop. 8 (l.444-446) from C13b and C13c to C13m
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route: at the regular points of the circle `z`, `w` (and `u = w/ζ`) are continuous, so they are the radial limits;
  the domination bound of HardyBound gives `|z|, |w| ≤ K|Π|` on the circle, so the boundary functions are in `L^{3/2}`.
  Fourier: `∫₀^{2π} e^{imθ} G(re^{iθ}) dθ = 0` for `m ≥ 1` (Cauchy on `|ζ| = r`), and `r → 1⁻` by dominated convergence.
-/
import HVFalse.Proofs.HardyBound
import HVFalse.Proofs.DensityLpA

open Real MeasureTheory Filter Topology Set AddCircle
open scoped Interval ENNReal NNReal

namespace P18.HandStep

open HardyBound

/-! ### Regular points of the circle -/

/-- `1 - u` has positive real part for `|u| = 1`, `u ≠ 1`. -/
theorem re_one_sub_pos_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) (h : 0 < ‖1 - u‖) : 0 < (1 - u).re := by
  have hre : u.re ≤ 1 := by have := Complex.re_le_norm u; rwa [hu] at this
  by_contra hle
  have h1 : u.re = 1 := by rw [Complex.sub_re, Complex.one_re] at hle; linarith [not_lt.1 hle]
  have hsq := Complex.sq_norm u
  rw [hu, Complex.normSq_apply, h1] at hsq
  have him : u.im = 0 := mul_self_eq_zero.1 (by linarith)
  have hu1 : u = 1 := Complex.ext (by rw [h1, Complex.one_re]) (by rw [him, Complex.one_im])
  rw [hu1, sub_self, norm_zero] at h
  exact lt_irrefl 0 h

/-- At a regular point of the circle the three bases of `Π` have positive real part. -/
theorem good_of_regular {δ : ℝ} {ζ₀ : ℂ} (h0 : ‖ζ₀‖ = 1) (hreg : Regular δ ζ₀) : Good δ ζ₀ := by
  refine ⟨?_, re_one_sub_pos_of_norm_one (by rw [norm_mul, h0, R2c.norm_ePlus, mul_one]) hreg.hB,
    re_one_sub_pos_of_norm_one (by rw [norm_mul, h0, R2c.norm_eMinus, mul_one]) hreg.hC⟩
  have h := re_one_sub_pos_of_norm_one (u := -ζ₀) (by rw [norm_neg, h0]) (by rw [sub_neg_eq_add]; exact hreg.hA)
  rwa [sub_neg_eq_add] at h

/-! ### `u = w/ζ` -/

/-- `u = e^{iγ/2} Π e^{-Y/2}`, so that `w = ζ u`. -/
noncomputable def uf (δ : ℝ) (ζ : ℂ) : ℂ :=
  Complex.exp (Complex.I * ((Explicit.gam δ / 2 : ℝ) : ℂ)) * Explicit.Pi δ ζ * Complex.exp (-(Explicit.Yf δ ζ) / 2)

theorem wf_eq (δ : ℝ) (ζ : ℂ) : Explicit.wf δ ζ = ζ * uf δ ζ := by
  unfold Explicit.wf uf; ring

theorem differentiableAt_uf {δ : ℝ} {ζ : ℂ} (hg : Good δ ζ) : DifferentiableAt ℂ (uf δ) ζ :=
  ((differentiableAt_const _).mul (differentiableAt_Pi hg)).mul ((differentiableAt_Yf hg).neg.div_const 2).cexp

theorem differentiableOn_uf (δ : ℝ) : DifferentiableOn ℂ (uf δ) (Metric.ball 0 1) := fun ζ hζ =>
  (differentiableAt_uf (good_of_norm_lt δ (by simpa using hζ))).differentiableWithinAt

theorem norm_uf (δ : ℝ) (ζ : ℂ) : ‖uf δ ζ‖ = ‖Explicit.Pi δ ζ‖ * Real.exp (-(Explicit.Yf δ ζ).re / 2) := by
  unfold uf
  rw [norm_mul, norm_mul, norm_exp_I_mul, one_mul, Complex.norm_exp]
  congr 2
  simp

theorem norm_uf_radial_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {ζ₀ : ℂ} (h0 : ‖ζ₀‖ = 1)
    (hreg : Regular δ ζ₀) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ‖uf δ ((r : ℂ) * ζ₀)‖ ≤ HardyBound.K * ‖Explicit.Pi δ ζ₀‖ := by
  have hnorm : ‖(r : ℂ) * ζ₀‖ = r := by
    rw [norm_mul, h0, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]
  have hball : (r : ℂ) * ζ₀ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, hnorm]; exact hr1
  obtain ⟨hY0, -⟩ := R2c.C13u_ReY_bounds hδ0 hδ1 _ hball
  have hP := norm_Pi_radial_le δ h0 hr0.le hr1.le hreg.hA hreg.hB hreg.hC
  have hy2 : 0 < Explicit.y2 := by unfold Explicit.y2; norm_num
  have he1 : 1 ≤ Real.exp (Explicit.y2 / 2) := Real.one_le_exp (by linarith)
  have he3 : Real.exp (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have he3' := (Real.exp_pos (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2)).le
  have hPn := norm_nonneg (Explicit.Pi δ ((r : ℂ) * ζ₀))
  have hP0 := norm_nonneg (Explicit.Pi δ ζ₀)
  rw [norm_uf]
  unfold HardyBound.K
  calc ‖Explicit.Pi δ ((r : ℂ) * ζ₀)‖ * Real.exp (-(Explicit.Yf δ ((r : ℂ) * ζ₀)).re / 2)
      ≤ (2 * ‖Explicit.Pi δ ζ₀‖) * 1 := mul_le_mul hP he3 he3' (by positivity)
    _ ≤ 2 * Real.exp (Explicit.y2 / 2) * ‖Explicit.Pi δ ζ₀‖ := by nlinarith

/-! ### Measurability -/

theorem measurable_Pi (δ : ℝ) : Measurable (Explicit.Pi δ) := by
  unfold Explicit.Pi; fun_prop

theorem measurable_Yf (δ : ℝ) : Measurable (Explicit.Yf δ) := by
  unfold Explicit.Yf; fun_prop

theorem measurable_zf (δ : ℝ) : Measurable (Explicit.zf δ) := by
  have h1 := measurable_Pi δ
  have h2 := measurable_Yf δ
  unfold Explicit.zf; fun_prop

theorem measurable_wf (δ : ℝ) : Measurable (Explicit.wf δ) := by
  have h1 := measurable_Pi δ
  have h2 := measurable_Yf δ
  unfold Explicit.wf; fun_prop

theorem measurable_uf (δ : ℝ) : Measurable (uf δ) := by
  have h1 := measurable_Pi δ
  have h2 := measurable_Yf δ
  unfold uf; fun_prop

/-! ### Radial limits and the bound on the circle -/

theorem tendsto_radial {F : ℂ → ℂ} {ζ₀ : ℂ} (hF : ContinuousAt F ζ₀) :
    Tendsto (fun r : ℝ => F ((r : ℂ) * ζ₀)) (𝓝[<] 1) (𝓝 (F ζ₀)) := by
  have hc : Continuous fun r : ℝ => (r : ℂ) * ζ₀ := by fun_prop
  have h1 := hc.tendsto 1
  simp only [Complex.ofReal_one, one_mul] at h1
  exact (hF.tendsto.comp h1).mono_left nhdsWithin_le_nhds

theorem norm_le_of_radial {F : ℂ → ℂ} {ζ₀ : ℂ} {B : ℝ} (hF : ContinuousAt F ζ₀)
    (hb : ∀ r : ℝ, 0 < r → r < 1 → ‖F ((r : ℂ) * ζ₀)‖ ≤ B) : ‖F ζ₀‖ ≤ B :=
  le_of_tendsto (tendsto_radial hF).norm (eventually_of_mem (Ioo_mem_nhdsLT one_pos) fun r hr => hb r hr.1 hr.2)

/-! ### Fourier coefficients: Cauchy on `|ζ| = r`, then `r → 1⁻` -/

/-- Cauchy on the circle `|ζ| = r < 1`: `∫₀^{2π} e^{imθ} G(re^{iθ}) dθ = 0` for `m ≥ 1` and `G` holomorphic in the disc. -/
theorem integral_exp_mul_eq_zero {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) {m : ℕ} (hm : 1 ≤ m)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
      G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  have hd : DifferentiableOn ℂ (fun ζ => ζ ^ (m - 1) * G ζ) (Metric.ball 0 1) :=
    (differentiableOn_id.pow (m - 1)).mul hG
  have hc := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr0.le Set.countable_empty
    ((hd.mono (Metric.closedBall_subset_ball hr1)).continuousOn)
    (fun ζ hζ => hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hr1.le hζ.1)))
  unfold circleIntegral at hc
  have key : ∀ θ : ℝ, deriv (circleMap 0 r) θ • ((circleMap 0 r θ) ^ (m - 1) * G (circleMap 0 r θ)) =
      (Complex.I * (r : ℂ) ^ m) * (Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
        G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ
    rw [deriv_circleMap, circleMap_zero, smul_eq_mul]
    have he : Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) = Complex.exp ((θ : ℂ) * Complex.I) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [he]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, pow_succ]
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => key θ), intervalIntegral.integral_const_mul] at hc
  have hI : Complex.I * (r : ℂ) ^ m ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hr0.ne'))
  exact (mul_eq_zero.1 hc).resolve_left hI

/-- Dominated convergence `r → 1⁻`: if `G` is holomorphic in the disc and measurable, and for a.e. `θ` has radial
limit `G(e^{iθ})` with `|G(re^{iθ})| ≤ B(θ)` (`B` integrable), then `∫₀^{2π} e^{imθ} G(e^{iθ}) dθ = 0` for `m ≥ 1`. -/
theorem integral_boundary_eq_zero {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 1)) (hGm : Measurable G)
    {B : ℝ → ℝ} (hB : IntervalIntegrable B volume 0 (2 * π))
    (hlim : ∀ᵐ θ : ℝ ∂volume, Tendsto (fun r : ℝ => G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] 1)
      (𝓝 (G (Complex.exp ((θ : ℂ) * Complex.I)))) ∧
      ∀ r : ℝ, 0 < r → r < 1 → ‖G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ B θ)
    {m : ℕ} (hm : 1 ≤ m) :
    ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
      G (Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  have hmeas : ∀ᶠ r : ℝ in 𝓝[<] 1, AEStronglyMeasurable (fun θ : ℝ => Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) *
      Complex.I) * G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (volume.restrict (Ι 0 (2 * π))) :=
    Eventually.of_forall fun r => (by fun_prop : Measurable fun θ : ℝ => Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) *
      Complex.I) * G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))).aestronglyMeasurable
  have hbound : ∀ᶠ r : ℝ in 𝓝[<] 1, ∀ᵐ θ : ℝ ∂volume, θ ∈ Ι 0 (2 * π) →
      ‖Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) * G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ B θ :=
    eventually_of_mem (Ioo_mem_nhdsLT one_pos) fun r hr => hlim.mono fun θ hθ _ => by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hθ.2 r hr.1 hr.2
  have hl : ∀ᵐ θ : ℝ ∂volume, θ ∈ Ι 0 (2 * π) →
      Tendsto (fun r : ℝ => Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
        G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] 1)
        (𝓝 (Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) * G (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    hlim.mono fun θ hθ _ => tendsto_const_nhds.mul hθ.1
  have hT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence B hmeas hbound hB hl
  have h0 : Tendsto (fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((((m : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
      G ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] 1) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsLT one_pos) fun r hr =>
      (integral_exp_mul_eq_zero hG hm hr.1 hr.2).symm)
  exact tendsto_nhds_unique hT h0

/-! ### The boundary functions are in `L^{3/2}(T)` -/

theorem onT_coe (F : ℂ → ℂ) (θ : ℝ) : Paper.onT F (θ : Circ) = F (Complex.exp ((θ : ℂ) * Complex.I)) := by
  unfold Paper.onT
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_self (by positivity : (2 * π : ℝ) ≠ 0), one_mul]

theorem measurable_onT {F : ℂ → ℂ} (hF : Measurable F) : Measurable (Paper.onT F) :=
  hF.comp (continuous_subtype_val.comp AddCircle.continuous_toCircle).measurable

/-- On the circle (at regular points), `|z|, |w|, |u| ≤ K|Π|`: the radial bounds pass to the limit. -/
theorem boundary_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {θ : ℝ}
    (hreg : Regular δ (Complex.exp ((θ : ℂ) * Complex.I))) :
    ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        HardyBound.K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ∧
      ‖Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
        HardyBound.K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ := by
  have h0 := Complex.norm_exp_ofReal_mul_I θ
  have hg := good_of_regular h0 hreg
  exact ⟨norm_le_of_radial (differentiableAt_zf hg).continuousAt fun r hr0 hr1 =>
      (norm_zw_radial_le hδ0 hδ1 h0 hreg hr0 hr1).1,
    norm_le_of_radial (differentiableAt_wf hg).continuousAt fun r hr0 hr1 =>
      (norm_zw_radial_le hδ0 hδ1 h0 hreg hr0 hr1).2⟩

theorem le_one_add_rpow {x : ℝ} (hx : 0 ≤ x) : x ≤ 1 + x ^ (3 / 2 : ℝ) := by
  rcases le_or_gt x 1 with h | h
  · have := Real.rpow_nonneg hx (3 / 2 : ℝ); linarith
  · have h2 : x ^ (1 : ℝ) ≤ x ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
    rw [Real.rpow_one] at h2; linarith

theorem measurable_circ_comp {F : ℂ → ℂ} (hF : Measurable F) :
    Measurable fun θ : ℝ => F (Complex.exp ((θ : ℂ) * Complex.I)) :=
  hF.comp (by fun_prop)

/-- `|Π(e^{iθ})|` is integrable on `[0, 2π]` (`|Π| ≤ 1 + |Π|^{3/2}`). -/
theorem normPi_integrable {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    IntervalIntegrable (fun θ : ℝ => ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖) volume 0 (2 * π) := by
  refine ((intervalIntegrable_const (c := (1 : ℝ))).add (P_integrable hδ0 hδ1)).mono_fun'
    (measurable_circ_comp (measurable_Pi δ)).norm.aestronglyMeasurable (ae_of_all _ fun θ => ?_)
  simp only [norm_norm]
  rw [← norm_Pi_circle_rpow]
  exact le_one_add_rpow (norm_nonneg _)

/-- The dominating function `K|Π(e^{iθ})|` is integrable on `[0, 2π]`. -/
theorem bound_integrable {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    IntervalIntegrable (fun θ : ℝ => HardyBound.K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖) volume 0
      (2 * π) :=
  (normPi_integrable hδ0 hδ1).const_mul _

/-- A function on `[0, 2π]` with `|F| ≤ c|Π(e^{iθ})|` a.e. has `|F|^{3/2}` integrable. -/
theorem rpow_integrable_of_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {E : Type*} [NormedAddCommGroup E]
    {F : ℝ → E} (hF : AEStronglyMeasurable F volume) {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ᵐ θ : ℝ ∂volume, ‖F θ‖ ≤ c * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖) :
    IntervalIntegrable (fun θ => ‖F θ‖ ^ (3 / 2 : ℝ)) volume 0 (2 * π) := by
  refine ((P_integrable hδ0 hδ1).const_mul (c ^ (3 / 2 : ℝ))).mono_fun'
    ((Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable hF.norm).restrict
    (ae_restrict_of_ae (hle.mono fun θ hθ => ?_))
  show ‖‖F θ‖ ^ (3 / 2 : ℝ)‖ ≤
    c ^ (3 / 2 : ℝ) * R2e.P δ (3 / 4 * Explicit.aA) (3 / 4 * Explicit.aB) (3 / 4 * Explicit.aC) θ
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), ← norm_Pi_circle_rpow,
    ← Real.mul_rpow hc (norm_nonneg _)]
  exact Real.rpow_le_rpow (norm_nonneg _) hθ (by norm_num)

/-- `‖F‖_p` on `T` as an interval integral, for an a.e. strongly measurable `F` with `|F|^p` integrable on `[0, 2π]`
(DensityLp.eLpNorm_circ without continuity). -/
theorem eLpNorm_circ' {E : Type*} [NormedAddCommGroup E] {p : ℝ} (hp : 0 < p) {F : Circ → E}
    (hF : AEStronglyMeasurable F volume) (hI : IntervalIntegrable (fun θ : ℝ => ‖F θ‖ ^ p) volume 0 (2 * π)) :
    eLpNorm F (ENNReal.ofReal p) volume = ENNReal.ofReal ((∫ θ in (0 : ℝ)..(2 * π), ‖F θ‖ ^ p) ^ (1 / p)) := by
  have hp0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hF, ENNReal.toReal_ofReal hp.le]
  have hI' : ∫⁻ x : Circ, ‖F x‖ₑ ^ p = ENNReal.ofReal (∫ θ in (0 : ℝ)..(2 * π), ‖F θ‖ ^ p) := by
    rw [← AddCircle.lintegral_preimage (2 * π) 0 (fun x => ‖F x‖ₑ ^ p), zero_add,
      intervalIntegral.integral_of_le two_pi_pos.le,
      ofReal_integral_eq_lintegral_ofReal hI.1 (ae_of_all _ fun θ => rpow_nonneg (norm_nonneg _) _)]
    refine lintegral_congr fun θ => ?_
    show ‖F θ‖ₑ ^ p = ENNReal.ofReal (‖F θ‖ ^ p)
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [hI', ENNReal.ofReal_rpow_of_nonneg
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => rpow_nonneg (norm_nonneg _) _) (by positivity)]

theorem memLp_circ {F : Circ → ℂ} (hF : AEStronglyMeasurable F volume)
    (hI : IntervalIntegrable (fun θ : ℝ => ‖F θ‖ ^ (3 / 2 : ℝ)) volume 0 (2 * π)) :
    MemLp F (ENNReal.ofReal (3 / 2)) volume := by
  show eLpNorm F (ENNReal.ofReal (3 / 2)) volume < ⊤
  rw [eLpNorm_circ' (by norm_num) hF hI]
  exact ENNReal.ofReal_lt_top

theorem memLp_z {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    MemLp (Paper.onT (Explicit.zf δ)) (ENNReal.ofReal (3 / 2)) volume := by
  have hm := measurable_onT (measurable_zf δ)
  refine memLp_circ hm.aestronglyMeasurable (rpow_integrable_of_le hδ0 hδ1
    (hm.comp AddCircle.measurable_mk').aestronglyMeasurable HardyBound.K_pos.le ((ae_regular δ).mono fun θ hreg => ?_))
  show ‖Paper.onT (Explicit.zf δ) (θ : Circ)‖ ≤ _
  rw [onT_coe]
  exact (boundary_le hδ0 hδ1 hreg).1

theorem memLp_wbar {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    MemLp (Paper.onT fun ζ => (starRingEnd ℂ) (Explicit.wf δ ζ)) (ENNReal.ofReal (3 / 2)) volume := by
  have hm := measurable_onT (Complex.continuous_conj.measurable.comp (measurable_wf δ))
  refine memLp_circ hm.aestronglyMeasurable (rpow_integrable_of_le hδ0 hδ1
    (hm.comp AddCircle.measurable_mk').aestronglyMeasurable HardyBound.K_pos.le ((ae_regular δ).mono fun θ hreg => ?_))
  show ‖Paper.onT (fun ζ => (starRingEnd ℂ) (Explicit.wf δ ζ)) (θ : Circ)‖ ≤ _
  rw [onT_coe, Complex.norm_conj]
  exact (boundary_le hδ0 hδ1 hreg).2

/-! ### Fourier coefficients of the boundary functions -/

theorem fourierCoeff_congr_ae {F G : Circ → ℂ} (h : F =ᵐ[volume] G) (n : ℤ) :
    fourierCoeff F n = fourierCoeff G n := by
  unfold fourierCoeff
  exact integral_congr_ae ((DensityLp.ae_haar_iff.1 h).mono fun x hx => by simp only [hx])

theorem fourierCoeff_onT (F : ℂ → ℂ) (n : ℤ) :
    fourierCoeff (Paper.onT F) n = (1 / (2 * π) : ℝ) • ∫ θ in (0 : ℝ)..(2 * π),
      Complex.exp (((((-n : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) * F (Complex.exp ((θ : ℂ) * Complex.I)) := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [DensityLp.fourier_coe_two_pi, onT_coe, smul_eq_mul]

theorem lim_zf {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) : ∀ᵐ θ : ℝ ∂volume,
    Tendsto (fun r : ℝ => Explicit.zf δ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] 1)
      (𝓝 (Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)))) ∧
    ∀ r : ℝ, 0 < r → r < 1 → ‖Explicit.zf δ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      HardyBound.K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ :=
  (ae_regular δ).mono fun θ hreg =>
    ⟨tendsto_radial (differentiableAt_zf (good_of_regular (Complex.norm_exp_ofReal_mul_I θ) hreg)).continuousAt,
      fun _ hr0 hr1 => (norm_zw_radial_le hδ0 hδ1 (Complex.norm_exp_ofReal_mul_I θ) hreg hr0 hr1).1⟩

theorem lim_uf {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) : ∀ᵐ θ : ℝ ∂volume,
    Tendsto (fun r : ℝ => uf δ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) (𝓝[<] 1)
      (𝓝 (uf δ (Complex.exp ((θ : ℂ) * Complex.I)))) ∧
    ∀ r : ℝ, 0 < r → r < 1 → ‖uf δ ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      HardyBound.K * ‖Explicit.Pi δ (Complex.exp ((θ : ℂ) * Complex.I))‖ :=
  (ae_regular δ).mono fun θ hreg =>
    ⟨tendsto_radial (differentiableAt_uf (good_of_regular (Complex.norm_exp_ofReal_mul_I θ) hreg)).continuousAt,
      fun _ hr0 hr1 => norm_uf_radial_le hδ0 hδ1 (Complex.norm_exp_ofReal_mul_I θ) hreg hr0 hr1⟩

/-- `ẑ(n) = 0` for `n < 0` (l.445: "the Fourier coefficients of `z` vanish for `n < 0`"). -/
theorem zf_coeff_neg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {n : ℤ} (hn : n < 0) :
    fourierCoeff (Paper.onT (Explicit.zf δ)) n = 0 := by
  have hm1 : 1 ≤ (-n).toNat := by omega
  have hmc : ((-n : ℤ) : ℝ) = (((-n).toNat : ℕ) : ℝ) := by
    have h := Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -n)
    exact_mod_cast h.symm
  rw [fourierCoeff_onT]
  simp only [hmc]
  rw [integral_boundary_eq_zero (differentiableOn_zf δ) (measurable_zf δ) (bound_integrable hδ0 hδ1)
    (lim_zf hδ0 hδ1) hm1, smul_zero]

theorem conj_exp (x : ℝ) :
    (starRingEnd ℂ) (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

theorem intervalIntegral_conj (F : ℝ → ℂ) :
    ∫ θ in (0 : ℝ)..(2 * π), (starRingEnd ℂ) (F θ) = (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * π), F θ) := by
  rw [intervalIntegral.integral_of_le two_pi_pos.le, intervalIntegral.integral_of_le two_pi_pos.le]
  exact integral_conj

/-- `(w̄)^(n) = 0` for `n ≥ 0` (l.445: "those of `w̄` vanish for `n ≥ 0`"; `w = ζu`, `w(0) = 0`). -/
theorem wbar_coeff_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {n : ℤ} (hn : 0 ≤ n) :
    fourierCoeff (Paper.onT fun ζ => (starRingEnd ℂ) (Explicit.wf δ ζ)) n = 0 := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [fourierCoeff_onT]
  have key : ∀ θ : ℝ, Complex.exp (((((-(m : ℤ) : ℤ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
      (starRingEnd ℂ) (Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))) =
      (starRingEnd ℂ) (Complex.exp (((((m + 1 : ℕ) : ℝ) * θ : ℝ) : ℂ) * Complex.I) *
        uf δ (Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro θ
    rw [wf_eq, map_mul, map_mul, conj_exp, conj_exp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [intervalIntegral.integral_congr (fun θ _ => key θ), intervalIntegral_conj,
    integral_boundary_eq_zero (differentiableOn_uf δ) (measurable_uf δ) (bound_integrable hδ0 hδ1)
      (lim_uf hδ0 hδ1) (by omega : 1 ≤ m + 1), map_zero, smul_zero]

/-! ### (HV) with `C = C_HV` fails: `∫ G ≥ 0` would follow -/

/-- `(|z|^s + |w|^s)^{1/s}` on `T` (`s = 3.98`). -/
noncomputable def hvL (δ : ℝ) (x : Circ) : ℝ :=
  (‖Paper.onT (Explicit.zf δ) x‖ ^ (398 / 100 : ℝ) + ‖Paper.onT (Explicit.wf δ) x‖ ^ (398 / 100 : ℝ)) ^
    (1 / (398 / 100 : ℝ))

/-- `f = z + w̄` on `T`. -/
noncomputable def fB (δ : ℝ) : Circ → ℂ := Paper.onT fun ζ => Explicit.zf δ ζ + (starRingEnd ℂ) (Explicit.wf δ ζ)

theorem hvL_nonneg (δ : ℝ) (x : Circ) : 0 ≤ hvL δ x := by unfold hvL; positivity

theorem hvL_coe (δ θ : ℝ) : ‖hvL δ (θ : Circ)‖ = (‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (398 / 100 : ℝ) +
    ‖Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (398 / 100 : ℝ)) ^ (1 / (398 / 100 : ℝ)) := by
  rw [Real.norm_of_nonneg (hvL_nonneg δ θ)]
  unfold hvL
  rw [onT_coe, onT_coe]

theorem fB_coe (δ θ : ℝ) : fB δ (θ : Circ) = Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) +
    (starRingEnd ℂ) (Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))) := by
  unfold fB
  rw [onT_coe]

theorem measurable_hvL (δ : ℝ) : Measurable (hvL δ) := by
  have hz := measurable_onT (measurable_zf δ)
  have hw := measurable_onT (measurable_wf δ)
  unfold hvL
  fun_prop

theorem measurable_fB (δ : ℝ) : Measurable (fB δ) :=
  measurable_onT ((measurable_zf δ).add (Complex.continuous_conj.measurable.comp (measurable_wf δ)))

theorem hv_le {a b : ℂ} {X s : ℝ} (hs : 0 < s) (ha : ‖a‖ ≤ X) (hb : ‖b‖ ≤ X) :
    (‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s) ≤ 2 ^ (1 / s) * X := by
  have hX : 0 ≤ X := (norm_nonneg a).trans ha
  have h1 : ‖a‖ ^ s ≤ X ^ s := Real.rpow_le_rpow (norm_nonneg _) ha hs.le
  have h2 : ‖b‖ ^ s ≤ X ^ s := Real.rpow_le_rpow (norm_nonneg _) hb hs.le
  calc (‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s) ≤ (2 * X ^ s) ^ (1 / s) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
    _ = 2 ^ (1 / s) * X := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hX _), ← Real.rpow_mul hX, mul_one_div_cancel hs.ne',
        Real.rpow_one]

theorem hvL_int {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    IntervalIntegrable (fun θ : ℝ => ‖hvL δ θ‖ ^ (3 / 2 : ℝ)) volume 0 (2 * π) :=
  rpow_integrable_of_le hδ0 hδ1 ((measurable_hvL δ).comp AddCircle.measurable_mk').aestronglyMeasurable
    (c := 2 ^ (1 / (398 / 100 : ℝ)) * HardyBound.K) (mul_nonneg (by positivity) HardyBound.K_pos.le)
    ((ae_regular δ).mono fun θ hreg => by
      have hb := boundary_le hδ0 hδ1 hreg
      show ‖hvL δ (θ : Circ)‖ ≤ _
      rw [hvL_coe, mul_assoc]
      exact hv_le (by norm_num) hb.1 hb.2)

theorem fB_int {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    IntervalIntegrable (fun θ : ℝ => ‖fB δ θ‖ ^ (3 / 2 : ℝ)) volume 0 (2 * π) :=
  rpow_integrable_of_le hδ0 hδ1 ((measurable_fB δ).comp AddCircle.measurable_mk').aestronglyMeasurable
    (c := 2 * HardyBound.K) (by linarith [HardyBound.K_pos])
    ((ae_regular δ).mono fun θ hreg => by
      have hb := boundary_le hδ0 hδ1 hreg
      show ‖fB δ (θ : Circ)‖ ≤ _
      rw [fB_coe]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_conj]
      linarith [hb.1, hb.2])

/-- `G(a, b) = A^p |a + b̄|^p - 2^{-p/s} ((|a|^s + |b|^s)^{1/s})^p` (`A = 1/(2 cos(π/2p))`). -/
theorem G_eq (p s : ℝ) (a b : ℂ) :
    G p s a b = (1 / (2 * cos (π / (2 * p)))) ^ p * ‖a + (starRingEnd ℂ) b‖ ^ p -
      (2 : ℝ) ^ (-(p / s)) * ((‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s)) ^ p := by
  have hX : 0 ≤ ‖a‖ ^ s + ‖b‖ ^ s := by positivity
  unfold G
  rw [Real.div_rpow hX (by norm_num), ← Real.rpow_mul hX, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    show 1 / s * p = p / s by ring]
  ring

/-- `C_HV^p = 2^{p/s} A^p`. -/
theorem hvConst_rpow {p s : ℝ} (hc : 0 < cos (π / (2 * p))) :
    hvConst p s ^ p = (2 : ℝ) ^ (p / s) * (1 / (2 * cos (π / (2 * p)))) ^ p := by
  unfold hvConst
  rw [div_eq_mul_one_div, Real.mul_rpow (by positivity) (one_div_pos.2 (mul_pos two_pos hc)).le,
    ← Real.rpow_mul (by norm_num), show 1 / s * p = p / s by ring]

/-- If (HV) with `C = C_HV` held for `f = z + w̄` (`P₊f = z`, `P₋f = w̄`), then `∫_T G(z, w) ≥ 0`. -/
theorem integral_G_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) {g h : LpT (3 / 2)}
    (hg : (g : Circ → ℂ) =ᵐ[volume] Paper.onT (Explicit.zf δ))
    (hh : (h : Circ → ℂ) =ᵐ[volume] Paper.onT fun ζ => (starRingEnd ℂ) (Explicit.wf δ ζ))
    (hHV : eLpNorm (fun x => (‖g x‖ ^ (398 / 100 : ℝ) + ‖h x‖ ^ (398 / 100 : ℝ)) ^ (1 / (398 / 100 : ℝ)))
          (ENNReal.ofReal (3 / 2)) volume
        ≤ ENNReal.ofReal (hvConst (3 / 2) (398 / 100)) * eLpNorm (⇑(g + h)) (ENNReal.ofReal (3 / 2)) volume) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π), G (3 / 2) (398 / 100) (Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)))
        (Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))) := by
  have e1 : (fun x => (‖g x‖ ^ (398 / 100 : ℝ) + ‖h x‖ ^ (398 / 100 : ℝ)) ^ (1 / (398 / 100 : ℝ)))
      =ᵐ[volume] hvL δ := by
    filter_upwards [hg, hh] with x hx1 hx2
    rw [hx1, hx2]
    simp only [hvL, Paper.onT, Complex.norm_conj]
  have e2 : (⇑(g + h) : Circ → ℂ) =ᵐ[volume] fB δ := by
    filter_upwards [Lp.coeFn_add g h, hg, hh] with x hx hx1 hx2
    rw [hx, Pi.add_apply, hx1, hx2]
    rfl
  rw [eLpNorm_congr_ae e1, eLpNorm_congr_ae e2,
    eLpNorm_circ' (by norm_num) (measurable_hvL δ).aestronglyMeasurable (hvL_int hδ0 hδ1),
    eLpNorm_circ' (by norm_num) (measurable_fB δ).aestronglyMeasurable (fB_int hδ0 hδ1)] at hHV
  have hcos : 0 < cos (π / (2 * (3 / 2 : ℝ))) := by
    rw [show π / (2 * (3 / 2 : ℝ)) = π / 3 by ring, Real.cos_pi_div_three]; norm_num
  have hC : 0 ≤ hvConst (3 / 2) (398 / 100) := by
    unfold hvConst; exact div_nonneg (by positivity) (by linarith)
  have hA0 := intervalIntegral.integral_nonneg (μ := volume) two_pi_pos.le fun θ _ =>
    Real.rpow_nonneg (norm_nonneg (hvL δ θ)) (3 / 2 : ℝ)
  have hB0 := intervalIntegral.integral_nonneg (μ := volume) two_pi_pos.le fun θ _ =>
    Real.rpow_nonneg (norm_nonneg (fB δ θ)) (3 / 2 : ℝ)
  have hAB := (DensityLp.rpow_ineq_iff (by norm_num) hA0 hB0 hC).2 hHV
  rw [hvConst_rpow hcos] at hAB
  have hGi : ∫ θ in (0 : ℝ)..(2 * π), G (3 / 2) (398 / 100) (Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)))
        (Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))) =
      (1 / (2 * cos (π / (2 * (3 / 2 : ℝ))))) ^ (3 / 2 : ℝ) * (∫ θ in (0 : ℝ)..(2 * π), ‖fB δ θ‖ ^ (3 / 2 : ℝ)) -
        (2 : ℝ) ^ (-((3 / 2 : ℝ) / (398 / 100))) * ∫ θ in (0 : ℝ)..(2 * π), ‖hvL δ θ‖ ^ (3 / 2 : ℝ) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((fB_int hδ0 hδ1).const_mul _) ((hvL_int hδ0 hδ1).const_mul _)]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [G_eq, fB_coe, hvL_coe]
  rw [hGi]
  have h22 : (2 : ℝ) ^ (-((3 / 2 : ℝ) / (398 / 100))) * (2 : ℝ) ^ ((3 / 2 : ℝ) / (398 / 100)) = 1 := by
    rw [← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero]
  have key := mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-((3 / 2 : ℝ) / (398 / 100))))
  have hr : (2 : ℝ) ^ (-((3 / 2 : ℝ) / (398 / 100))) * ((2 : ℝ) ^ ((3 / 2 : ℝ) / (398 / 100)) *
      (1 / (2 * cos (π / (2 * (3 / 2 : ℝ))))) ^ (3 / 2 : ℝ) * ∫ θ in (0 : ℝ)..(2 * π), ‖fB δ θ‖ ^ (3 / 2 : ℝ)) =
      (1 / (2 * cos (π / (2 * (3 / 2 : ℝ))))) ^ (3 / 2 : ℝ) * ∫ θ in (0 : ℝ)..(2 * π), ‖fB δ θ‖ ^ (3 / 2 : ℝ) := by
    rw [← mul_assoc, ← mul_assoc, h22, one_mul]
  linarith

/-! ### C13m_hand_step -/

theorem delta0_lt : Real.exp (-2500) < 2 * π := by
  have : Real.exp (-2500) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  linarith [pi_gt_three]

/-- The arithmetic of C13c: `|(1/2π) X - (-1.391990813)| ≤ 2.6·10⁻¹⁰` gives `X < 0`. -/
theorem neg_of_abs_le {X : ℝ} (h : |1 / (2 * π) * X - -1391990813 / 10 ^ 9| ≤ 26 / 10 ^ 11) : X < 0 := by
  have hab := (abs_le.1 h).2
  by_contra hX
  have hm := mul_nonneg (one_div_pos.2 two_pi_pos).le (not_lt.1 hX)
  linarith

/-- C13c (`|∫_T G(z,w) dθ/2π + 1.391990813| ≤ 2.6·10⁻¹⁰`) gives `∫_T G(z,w) dθ < 0`. -/
theorem C13c_integral_neg (hc : Paper.C13c_explicit_integral) :
    ∫ θ in (0 : ℝ)..(2 * π), G (3 / 2) (398 / 100) (Explicit.zf (Real.exp (-2500)) (Complex.exp ((θ : ℂ) * Complex.I)))
      (Explicit.wf (Real.exp (-2500)) (Complex.exp ((θ : ℂ) * Complex.I))) < 0 :=
  neg_of_abs_le hc

/-- C13m_hand_step, Prop. 8 proof (l.444-446): "So `f ∈ L^p(T)`; as `w(0) = 0`, the Fourier coefficients of `z`
vanish for `n < 0` and those of `w̄` vanish for `n ≥ 0`, so `P₊f = z` and `P₋f = w̄`, and ... `f` violates (HV) ...
if ... `∫_T G(z,w) dθ/2π < 0`": from C13b and C13c, C13m. (C13b is not used: the bounds come from C13u directly.) -/
theorem C13m_hand_step_proved : Paper.C13m_hand_step := by
  intro _ hc
  have hδ0 : 0 < Real.exp (-2500) := Real.exp_pos _
  have hδ1 := delta0_lt
  have : Fact (1 ≤ ENNReal.ofReal (3 / 2 : ℝ)) :=
    ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)⟩
  obtain ⟨g, hg⟩ : ∃ g : LpT (3 / 2), (g : Circ → ℂ) =ᵐ[volume] Paper.onT (Explicit.zf (Real.exp (-2500))) :=
    ⟨(memLp_z hδ0 hδ1).toLp _, (memLp_z hδ0 hδ1).coeFn_toLp⟩
  obtain ⟨h, hh⟩ : ∃ h : LpT (3 / 2), (h : Circ → ℂ) =ᵐ[volume]
      Paper.onT fun ζ => (starRingEnd ℂ) (Explicit.wf (Real.exp (-2500)) ζ) :=
    ⟨(memLp_wbar hδ0 hδ1).toLp _, (memLp_wbar hδ0 hδ1).coeFn_toLp⟩
  have hadd : ∀ n, fourierCoeff (⇑(g + h)) n = fourierCoeff (⇑g) n + fourierCoeff (⇑h) n := fun n => by
    rw [fourierCoeff_congr_ae (Lp.coeFn_add g h) n,
      fourierCoeff.add (DensityLp.integrable_haar_of_lp g) (DensityLp.integrable_haar_of_lp h), Pi.add_apply]
  have hgc : ∀ n, fourierCoeff (⇑g) n = fourierCoeff (Paper.onT (Explicit.zf (Real.exp (-2500)))) n :=
    fun n => fourierCoeff_congr_ae hg n
  have hhc : ∀ n, fourierCoeff (⇑h) n =
      fourierCoeff (Paper.onT fun ζ => (starRingEnd ℂ) (Explicit.wf (Real.exp (-2500)) ζ)) n :=
    fun n => fourierCoeff_congr_ae hh n
  refine ⟨g + h, g, h, ?_, hg, hh, fun n => ?_, fun n => ?_, fun hHV => ?_⟩
  · filter_upwards [Lp.coeFn_add g h, hg, hh] with x hx hx1 hx2
    rw [hx, Pi.add_apply, hx1, hx2]
    rfl
  · split_ifs with hn
    · rw [hadd, hhc, wbar_coeff_nonneg hδ0 hδ1 hn, add_zero]
    · rw [hgc, zf_coeff_neg hδ0 hδ1 (not_le.1 hn)]
  · split_ifs with hn
    · rw [hadd, hgc, zf_coeff_neg hδ0 hδ1 hn, zero_add]
    · rw [hhc, wbar_coeff_nonneg hδ0 hδ1 (not_lt.1 hn)]
  · exact absurd (integral_G_nonneg hδ0 hδ1 hg hh hHV) (not_le.2 (C13c_integral_neg hc))

/-- C13m is PROVED GIVEN C13c alone (the computer check): C13b is proved (`HardyBound.C13b_proved`). -/
theorem C13m_given_C13c : Paper.C13c_explicit_integral → Paper.C13m_explicit_violates :=
  C13m_hand_step_proved HardyBound.C13b_proved

end P18.HandStep
