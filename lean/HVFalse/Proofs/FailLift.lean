/-
  HVFalse/Proofs/FailLift.lean - L1 of Prop. fail (the paper): a bad disc g gives a bad polynomial pair
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route (differs from the paper's Fejér means + Lemma lift with a Blaschke product; AUDIT route difference):
  (a) FailLiftA: rescale g(ρζ) so g ≠ 0 on T, keeping ∫ M(g) < 0 (M continuous).
  (b) Select (selection lemma, statement `SelStmt`): a polynomial Y with ∫ |g|^q Γ(Re Y + log|g|, arg g) < 0.
  (c) On T: z = g₁ e^{Y/2}, w = ζ e^{-Y/2} have zw = g and |z/w| = |g| e^{Re Y}, so G(z,w) = |g|^q Γ(Re Y + log|g|, arg g).
  (d) z_N = g₁·Σ_{k<N}(Y/2)^k/k!, w_N = X·Σ_{k<N}(-Y/2)^k/k! are polynomials with w_N(0) = 0; dominated convergence gives
      ∫ G(z_N, w_N) → ∫ G(z, w) < 0, contradicting `DiscIneq`.
-/
import HVFalse.Proofs.FailLiftA
import HVFalse.Proofs.Minorant
import HVFalse.Proofs.Select

open Real Set Filter Topology

namespace P18

/-- The statement of the selection lemma `exists_trig_near_min` (HVFalse/Proofs/Select.lean). -/
def SelStmt : Prop :=
  ∀ (F : ℝ → ℝ → ℝ), Continuous (Function.uncurry F) → ∀ μ : ℝ → ℝ, Continuous μ → ∀ R : ℝ,
    (∀ θ ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-R) R, F θ v = μ θ) →
    (∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, μ θ ≤ F θ v) →
    ∀ ε : ℝ, 0 < ε → ∃ c : ℤ →₀ ℂ,
      ∫ θ in (0 : ℝ)..(2 * π), F θ (trig c θ).re ≤ (∫ θ in (0 : ℝ)..(2 * π), μ θ) + ε

/-! ### exp partial sums -/

/-- `S_N(x) = Σ_{k<N} x^k/k!`. -/
noncomputable def expPartial (N : ℕ) (x : ℂ) : ℂ := ∑ k ∈ Finset.range N, x ^ k / (k.factorial : ℂ)

theorem tendsto_expPartial (x : ℂ) : Tendsto (fun N => expPartial N x) atTop (𝓝 (Complex.exp x)) := by
  unfold expPartial
  rw [Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp x).tendsto_sum_nat

theorem norm_expPartial_le (N : ℕ) (x : ℂ) : ‖expPartial N x‖ ≤ Real.exp ‖x‖ := by
  unfold expPartial
  calc ‖∑ k ∈ Finset.range N, x ^ k / (k.factorial : ℂ)‖
        ≤ ∑ k ∈ Finset.range N, ‖x‖ ^ k / (k.factorial : ℝ) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ Real.exp ‖x‖ := Real.sum_le_exp_of_nonneg (norm_nonneg x) N

/-- The polynomial `Σ_{k<N} (a·Y)^k/k!`. -/
noncomputable def expPoly (N : ℕ) (a : ℂ) (Y : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, Polynomial.C (1 / (k.factorial : ℂ)) * (Polynomial.C a * Y) ^ k

theorem eval_expPoly (N : ℕ) (a : ℂ) (Y : Polynomial ℂ) (ζ : ℂ) :
    (expPoly N a Y).eval ζ = expPartial N (a * Y.eval ζ) := by
  unfold expPoly expPartial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-! ### (c) the lift -/

theorem unitPt_ne_zero (θ : ℝ) : unitPt θ ≠ 0 := by
  intro h
  have := norm_unitPt θ
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- On `T`: `G(g₁ e^{Y/2}, ζ e^{-Y/2}) = |g|^q Γ(Re Y + log|g|, arg g)` (with `Γ` written through `cos(arg g) = Re g/|g|`). -/
theorem G_lift {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {g g1 : Polynomial ℂ}
    (hg : ∀ ζ, g.eval ζ = ζ * g1.eval ζ) (y : ℂ) {θ : ℝ} (hne : g.eval (unitPt θ) ≠ 0) :
    G p s (g1.eval (unitPt θ) * Complex.exp (1 / 2 * y)) (unitPt θ * Complex.exp (-1 / 2 * y)) =
      ‖g.eval (unitPt θ)‖ ^ (p / 2) *
        Gamc p s (y.re + log ‖g.eval (unitPt θ)‖) ((g.eval (unitPt θ)).re / ‖g.eval (unitPt θ)‖) := by
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
  unfold G
  rw [lift_pointwise p s hp1 hp2 hs _ _ hz hw, hprod, hratio,
    Real.log_mul (norm_ne_zero_iff.mpr hne) (Real.exp_pos _).ne', Real.log_exp, gam_eq_gamc hp1 hp2,
    cos_arg_eq _ hne, add_comm (log _)]

theorem continuous_gamc_comp {α : Type*} [TopologicalSpace α] {p s : ℝ} (hp : 0 < p) (hs : 0 < s)
    {f h : α → ℝ} (hf : Continuous f) (hh : Continuous h) : Continuous fun x => Gamc p s (f x) (h x) := by
  unfold Gamc
  apply Continuous.sub
  · exact ((continuous_cosh.comp hf).add hh |>.div_const _).rpow_const fun _ => Or.inr (by linarith)
  · exact (continuous_cosh.comp ((continuous_const.mul hf).div_const 2)).rpow_const
      fun _ => Or.inr (div_nonneg hp.le hs.le)

/-! ### (d) the main argument, for `g` without zeros on `T` -/

theorem re_eval_toZ_add_toW (c : ℤ →₀ ℂ) (θ : ℝ) :
    ((toZ c + toW c).eval (unitPt θ)).re = (trig c θ).re := by
  rw [Polynomial.eval_add, eval_toZ, eval_toW, trig_eq_add, Complex.add_re, Complex.add_re, Complex.conj_re]

theorem not_discIneq_of_nozero (hsel : SelStmt) {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ Ssec p) (g g1 : Polynomial ℂ) (hg : ∀ ζ, g.eval ζ = ζ * g1.eval ζ)
    (hnz : ∀ θ, g.eval (unitPt θ) ≠ 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval (unitPt θ)) < 0) : ¬ DiscIneq p s := by
  intro hD
  have hp : 0 < p := by linarith
  have hgc : Continuous fun θ => g.eval (unitPt θ) := (Polynomial.continuous g).comp continuous_unitPt
  have hlogc : Continuous fun θ => Real.log ‖g.eval (unitPt θ)‖ :=
    hgc.norm.log fun θ => norm_ne_zero_iff.mpr (hnz θ)
  obtain ⟨Lb, hLb⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hlogc.continuousOn
  obtain ⟨R0, hR0⟩ := exists_mfun_eq_mK hp1 hp2 hs hsS
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ → ℝ → ℝ, F = fun θ v => ‖g.eval (unitPt θ)‖ ^ (p / 2) *
      Gamc p s (v + Real.log ‖g.eval (unitPt θ)‖) ((g.eval (unitPt θ)).re / ‖g.eval (unitPt θ)‖) := ⟨_, rfl⟩
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun x : ℝ × ℝ => g.eval (unitPt x.1) := hgc.comp continuous_fst
    have h2 : Continuous fun x : ℝ × ℝ => Real.log ‖g.eval (unitPt x.1)‖ := hlogc.comp continuous_fst
    have h3 : Continuous fun x : ℝ × ℝ => (g.eval (unitPt x.1)).re / ‖g.eval (unitPt x.1)‖ :=
      (Complex.continuous_re.comp h1).div h1.norm fun x => norm_ne_zero_iff.mpr (hnz x.1)
    have h4 := (h1.norm.rpow_const (p := p / 2) fun _ => Or.inr (by linarith)).mul
      (continuous_gamc_comp hp hs (continuous_snd.add h2) h3)
    rw [hFdef]
    exact h4
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ → ℝ, μ = fun θ => Mfun p s (g.eval (unitPt θ)) := ⟨_, rfl⟩
  have hμc : Continuous μ := by rw [hμdef]; exact (continuous_Mfun hp1 hp2 hs hsS).comp hgc
  have hFμ : ∀ θ y, F θ (y - Real.log ‖g.eval (unitPt θ)‖) =
      ‖g.eval (unitPt θ)‖ ^ (p / 2) * Gam p s y (Complex.arg (g.eval (unitPt θ))) := by
    intro θ y
    rw [hFdef]
    dsimp only
    rw [sub_add_cancel, gam_eq_gamc hp1 hp2, cos_arg_eq _ (hnz θ)]
  have hmin : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∃ v ∈ Icc (-(R0 + Lb)) (R0 + Lb), F θ v = μ θ := by
    intro θ hθ
    obtain ⟨-, y0, hy0, hGy0, -⟩ := hR0 (Complex.arg (g.eval (unitPt θ)))
    have hL := abs_le.mp (by simpa [Real.norm_eq_abs] using hLb θ hθ)
    refine ⟨y0 - Real.log ‖g.eval (unitPt θ)‖, ⟨by linarith [hy0.1], by linarith [hy0.2]⟩, ?_⟩
    rw [hFμ, hGy0, hμdef]
    simp only [Mfun]
  have hle : ∀ θ ∈ Icc (0 : ℝ) (2 * π), ∀ v : ℝ, μ θ ≤ F θ v := by
    intro θ _ v
    obtain ⟨-, -, -, -, hall⟩ := hR0 (Complex.arg (g.eval (unitPt θ)))
    rw [hμdef]
    simp only [Mfun]
    have h := hFμ θ (v + Real.log ‖g.eval (unitPt θ)‖)
    rw [add_sub_cancel_right] at h
    rw [h]
    exact mul_le_mul_of_nonneg_left (hall _) (by positivity)
  have hneg' : (∫ θ in (0 : ℝ)..(2 * π), μ θ) < 0 := by rw [hμdef]; exact hneg
  obtain ⟨c, hc⟩ := hsel F hFc μ hμc (R0 + Lb) hmin hle (-(∫ θ in (0 : ℝ)..(2 * π), μ θ) / 2) (by linarith)
  set Y := toZ c + toW c with hYdef
  -- the analytic pair: its integral is negative
  obtain ⟨zf, hzf⟩ : ∃ zf : ℝ → ℂ, zf = fun θ => g1.eval (unitPt θ) * Complex.exp (1 / 2 * Y.eval (unitPt θ)) :=
    ⟨_, rfl⟩
  obtain ⟨wf, hwf⟩ : ∃ wf : ℝ → ℂ, wf = fun θ => unitPt θ * Complex.exp (-1 / 2 * Y.eval (unitPt θ)) := ⟨_, rfl⟩
  have hlift : ∀ θ, G p s (zf θ) (wf θ) = F θ (trig c θ).re := fun θ => by
    rw [hzf, hwf, hFdef]
    dsimp only
    rw [G_lift hp1 hp2 hs hg _ (hnz θ), re_eval_toZ_add_toW]
  have hlim_neg : ∫ θ in (0 : ℝ)..(2 * π), G p s (zf θ) (wf θ) < 0 := by
    simp_rw [hlift]; linarith
  -- polynomial truncations
  obtain ⟨zN, hzN⟩ : ∃ zN : ℕ → Polynomial ℂ, zN = fun N => g1 * expPoly N (1 / 2) Y := ⟨_, rfl⟩
  obtain ⟨wN, hwN⟩ : ∃ wN : ℕ → Polynomial ℂ, wN = fun N => Polynomial.X * expPoly N (-1 / 2) Y := ⟨_, rfl⟩
  have hevz : ∀ N θ, (zN N).eval (unitPt θ) = g1.eval (unitPt θ) * expPartial N (1 / 2 * Y.eval (unitPt θ)) :=
    fun N θ => by rw [hzN]; dsimp only; rw [Polynomial.eval_mul, eval_expPoly]
  have hevw : ∀ N θ, (wN N).eval (unitPt θ) = unitPt θ * expPartial N (-1 / 2 * Y.eval (unitPt θ)) :=
    fun N θ => by rw [hwN]; dsimp only; rw [Polynomial.eval_mul, Polynomial.eval_X, eval_expPoly]
  have hw0 : ∀ N, (wN N).coeff 0 = 0 := fun N => by rw [hwN]; exact Polynomial.coeff_X_mul_zero _
  have hD' : ∀ N, 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), G p s ((zN N).eval (unitPt θ)) ((wN N).eval (unitPt θ)) :=
    fun N => hD (zN N) (wN N) (hw0 N)
  -- dominated convergence
  have hYc : Continuous fun θ => Y.eval (unitPt θ) := (Polynomial.continuous Y).comp continuous_unitPt
  have hg1c : Continuous fun θ => g1.eval (unitPt θ) := (Polynomial.continuous g1).comp continuous_unitPt
  obtain ⟨BY, hBY⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hYc.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn hg1c.continuousOn
  set K := (|B1| + 1) * Real.exp |BY| with hK
  obtain ⟨Bd, hBd⟩ := ((isCompact_closedBall (0 : ℂ) K).prod (isCompact_closedBall (0 : ℂ) K)).exists_bound_of_continuousOn
    (continuous_G p s hp hs).continuousOn
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
  have htend : Tendsto (fun N => ∫ θ in (0 : ℝ)..(2 * π), G p s ((zN N).eval (unitPt θ)) ((wN N).eval (unitPt θ)))
      atTop (𝓝 (∫ θ in (0 : ℝ)..(2 * π), G p s (zf θ) (wf θ))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => Bd) ?_ ?_
      intervalIntegrable_const ?_
    · refine Eventually.of_forall fun N => ?_
      exact ((continuous_G p s hp hs).comp (((Polynomial.continuous _).comp continuous_unitPt).prodMk
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
      have hGt := ((continuous_G p s hp hs).continuousAt
        (x := (g1.eval (unitPt θ) * Complex.exp (1 / 2 * Y.eval (unitPt θ)),
          unitPt θ * Complex.exp (-1 / 2 * Y.eval (unitPt θ))))).tendsto.comp (hzt.prodMk_nhds hwt)
      simpa only [Function.comp_def] using hGt
  have := ge_of_tendsto htend (Eventually.of_forall hD')
  linarith

/-- L1 with the selection lemma as a hypothesis: a polynomial `g`, `g(0) = 0`, with `∫ M(g(e^{iθ})) < 0` refutes `DiscIneq`. -/
theorem not_discIneq_of_bad_disc_of_sel (hsel : SelStmt) {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (hsS : s ≤ Ssec p) (g : Polynomial ℂ) (hg0 : g.eval 0 = 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) < 0) :
    ¬ DiscIneq p s := by
  obtain ⟨ρ, -, -, hnz, hnegρ⟩ := exists_rescale hp1 hp2 hs hsS g hneg
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
  refine not_discIneq_of_nozero hsel hp1 hp2 hs hsS gρ g1 hg (fun θ => by rw [hgρ]; exact hnz θ) ?_
  simp_rw [hgρ]
  exact hnegρ

/-- L1: a polynomial `g` with `g(0) = 0` and `∫₀^{2π} M(g(e^{iθ})) dθ < 0` refutes `DiscIneq`
(for `s ≤ sec²ϑ`). With L2 (`exists_bad_disc`) and C01 this is Prop. fail (C09). -/
theorem not_discIneq_of_bad_disc {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (g : Polynomial ℂ) (hg0 : g.eval 0 = 0)
    (hneg : ∫ θ in (0 : ℝ)..(2 * π), Mfun p s (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) < 0) :
    ¬ DiscIneq p s :=
  not_discIneq_of_bad_disc_of_sel (fun F hF μ hμ R hmin hle ε hε => exists_trig_near_min F hF μ hμ R hmin hle ε hε)
    hp1 hp2 hs hsS g hg0 hneg

end P18
