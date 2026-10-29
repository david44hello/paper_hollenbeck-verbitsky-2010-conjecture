/-
  HVFalse/Proofs/Lift.lean - C08, Lemma 3 lift (the paper, Lemma 3), as the paper states it
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The square root of g₀: g₀(ζ) = g₀(0) Π_a (1 - ζ/a) over the roots a of g₀ (|a| ≥ 1, as g₀ ≠ 0 in the open disc). On the
  closed disc Re(1 - ζ/a) ≥ 0 (> 0 inside), so the principal power (1 - ζ/a)^{1/2} is continuous there and holomorphic
  inside, and r² = g₀ on all of ℂ. On T: |B| = 1 (|1 - āζ| = |ζ - a| for |ζ| = 1), |ζ^k| = 1, |e^{±Y/2}| = e^{±Re Y/2}, so
  |z|/|w| = e^{y} and zw = g; then lift_pointwise gives G(z,w) = |g|^q Γ(y, arg g) (where r = 0 on T both sides are 0).
-/
import HVFalse.Proofs.Bridges
import HVFalse.Defs.Extra

open Real

namespace P18

namespace Lift

/-! ## The square root -/

/-- The principal square root `x^{1/2}`. -/
noncomputable def csqrt (x : ℂ) : ℂ := x ^ (((2 : ℕ) : ℂ)⁻¹)

theorem csqrt_sq (x : ℂ) : csqrt x ^ 2 = x := Complex.cpow_nat_inv_pow x two_ne_zero

theorem re_half_pos : 0 < (((2 : ℕ) : ℂ)⁻¹).re := by norm_num

/-- `r = √g₀(0) · Π_a (1 - ζ/a)^{1/2}`, `a` over the roots of `g₀` with multiplicity. -/
noncomputable def rfun (g0p : Polynomial ℂ) (ζ : ℂ) : ℂ :=
  csqrt (g0p.eval 0) * (g0p.roots.map fun a => csqrt (1 - ζ / a)).prod

theorem one_le_norm_root {g0p : Polynomial ℂ} (hh : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, g0p.eval ζ ≠ 0) {a : ℂ}
    (ha : a ∈ g0p.roots) : 1 ≤ ‖a‖ := by
  by_contra h
  push_neg at h
  exact hh a (mem_ball_zero_iff.mpr h) (Polynomial.mem_roots'.mp ha).2

theorem eval_eq_prod (g0p : Polynomial ℂ) (hz : ∀ a ∈ g0p.roots, a ≠ 0) (ζ : ℂ) :
    g0p.eval ζ = g0p.eval 0 * (g0p.roots.map fun a => 1 - ζ / a).prod := by
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := g0p))
  have hev : ∀ x, g0p.eval x = g0p.leadingCoeff * (g0p.roots.map fun a => x - a).prod := fun x => by
    conv_lhs => rw [← hfac]
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl fun a _ => by simp
  rw [hev ζ, hev 0, mul_assoc, ← Multiset.prod_map_mul]
  congr 1
  refine congr_arg _ (Multiset.map_congr rfl fun a ha => ?_)
  field_simp [hz a ha]
  ring

theorem rfun_sq (g0p : Polynomial ℂ) (hz : ∀ a ∈ g0p.roots, a ≠ 0) (ζ : ℂ) : rfun g0p ζ ^ 2 = g0p.eval ζ := by
  unfold rfun
  rw [mul_pow, csqrt_sq, ← Multiset.prod_map_pow]
  simp only [csqrt_sq]
  exact (eval_eq_prod g0p hz ζ).symm

theorem re_one_sub_div_nonneg {ζ a : ℂ} (hζ : ‖ζ‖ ≤ 1) (ha : 1 ≤ ‖a‖) : 0 ≤ (1 - ζ / a).re := by
  have h1 : ‖ζ / a‖ ≤ 1 := by rw [norm_div]; exact div_le_one_of_le₀ (hζ.trans ha) (by linarith)
  have h2 := Complex.re_le_norm (ζ / a)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem re_one_sub_div_pos {ζ a : ℂ} (hζ : ‖ζ‖ < 1) (ha : 1 ≤ ‖a‖) : 0 < (1 - ζ / a).re := by
  have h1 : ‖ζ / a‖ < 1 := by rw [norm_div, div_lt_one (by linarith)]; linarith
  have h2 := Complex.re_le_norm (ζ / a)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem continuousOn_mprod {s : Multiset ℂ} {F : ℂ → ℂ → ℂ} {U : Set ℂ} (h : ∀ a ∈ s, ContinuousOn (F a) U) :
    ContinuousOn (fun ζ => (s.map fun a => F a ζ).prod) U := by
  induction s using Multiset.induction_on with
  | empty => simpa using continuousOn_const
  | cons b s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h b (Multiset.mem_cons_self b s)).mul (ih fun a ha => h a (Multiset.mem_cons_of_mem ha))

theorem differentiableOn_mprod {s : Multiset ℂ} {F : ℂ → ℂ → ℂ} {U : Set ℂ}
    (h : ∀ a ∈ s, DifferentiableOn ℂ (F a) U) : DifferentiableOn ℂ (fun ζ => (s.map fun a => F a ζ).prod) U := by
  induction s using Multiset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | cons b s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (h b (Multiset.mem_cons_self b s)).mul (ih fun a ha => h a (Multiset.mem_cons_of_mem ha))

theorem continuousOn_rfun {g0p : Polynomial ℂ} (h1 : ∀ a ∈ g0p.roots, 1 ≤ ‖a‖) :
    ContinuousOn (rfun g0p) (Metric.closedBall 0 1) := by
  refine continuousOn_const.mul (continuousOn_mprod fun a ha => fun ζ hζ => ?_)
  have hre := re_one_sub_div_nonneg (mem_closedBall_zero_iff.mp hζ) (h1 a ha)
  have hin : ContinuousAt (fun ζ : ℂ => 1 - ζ / a) ζ := continuousAt_const.sub (continuousAt_id.div_const a)
  have hout : ContinuousAt (fun x : ℂ => x ^ (((2 : ℕ) : ℂ)⁻¹)) (1 - ζ / a) :=
    Complex.continuousAt_cpow_const_of_re_pos (Or.inl hre) re_half_pos
  show ContinuousWithinAt (fun ζ : ℂ => (1 - ζ / a) ^ (((2 : ℕ) : ℂ)⁻¹)) _ ζ
  exact (ContinuousAt.comp (f := fun ζ : ℂ => 1 - ζ / a) hout hin).continuousWithinAt

theorem differentiableOn_rfun {g0p : Polynomial ℂ} (h1 : ∀ a ∈ g0p.roots, 1 ≤ ‖a‖) :
    DifferentiableOn ℂ (rfun g0p) (Metric.ball 0 1) := by
  refine (differentiableOn_const _).mul (differentiableOn_mprod fun a ha => fun ζ hζ => ?_)
  have hre := re_one_sub_div_pos (mem_ball_zero_iff.mp hζ) (h1 a ha)
  have hd : DifferentiableAt ℂ (fun ζ : ℂ => 1 - ζ / a) ζ :=
    (differentiableAt_const _).sub (differentiableAt_id.div_const a)
  exact (hd.cpow_const (Complex.mem_slitPlane_iff.mpr (Or.inl hre))).differentiableWithinAt

/-! ## The Blaschke product -/

theorem blaschke_cons (a : ℂ) (zs : List ℂ) (ζ : ℂ) :
    blaschke (a :: zs) ζ = (ζ - a) / (1 - starRingEnd ℂ a * ζ) * blaschke zs ζ := by
  simp [blaschke, List.map_cons, List.prod_cons]

theorem denom_ne_zero {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ ≤ 1) : 1 - starRingEnd ℂ a * ζ ≠ 0 := by
  intro h
  have h1 : ‖starRingEnd ℂ a * ζ‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg ζ]
  rw [show starRingEnd ℂ a * ζ = 1 by linear_combination -h, norm_one] at h1
  exact lt_irrefl _ h1

theorem blaschke_cont_diff {zs : List ℂ} (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1) :
    ContinuousOn (blaschke zs) (Metric.closedBall 0 1) ∧ DifferentiableOn ℂ (blaschke zs) (Metric.ball 0 1) := by
  induction zs with
  | nil =>
    have e : blaschke [] = fun _ => (1 : ℂ) := funext fun ζ => by simp [blaschke]
    rw [e]
    exact ⟨continuousOn_const, differentiableOn_const _⟩
  | cons a zs ih =>
    have ha := (hzs a (List.mem_cons_self ..)).2
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hzs b (List.mem_cons_of_mem a hb)
    have e : blaschke (a :: zs) = fun ζ => (ζ - a) / (1 - starRingEnd ℂ a * ζ) * blaschke zs ζ :=
      funext (blaschke_cons a zs)
    rw [e]
    constructor
    · exact ((continuousOn_id.sub continuousOn_const).div (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
        fun ζ hζ => denom_ne_zero ha (mem_closedBall_zero_iff.mp hζ)).mul ih1
    · exact ((differentiableOn_id.sub (differentiableOn_const _)).div
        ((differentiableOn_const _).sub ((differentiableOn_const _).mul differentiableOn_id))
        fun ζ hζ => denom_ne_zero ha (mem_ball_zero_iff.mp hζ).le).mul ih2

theorem norm_blaschke_circle {zs : List ℂ} (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖blaschke zs ζ‖ = 1 := by
  induction zs with
  | nil => simp [blaschke]
  | cons a zs ih =>
    have ha := (hzs a (List.mem_cons_self ..)).2
    rw [blaschke_cons, norm_mul, norm_div, ih fun b hb => hzs b (List.mem_cons_of_mem a hb)]
    have hcz : ζ * starRingEnd ℂ ζ = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; norm_num
    have e : 1 - starRingEnd ℂ a * ζ = ζ * starRingEnd ℂ (ζ - a) := by
      rw [map_sub]; linear_combination (-1 : ℂ) * hcz
    have hne : ζ - a ≠ 0 := by
      intro h0
      rw [sub_eq_zero] at h0
      rw [h0] at hζ
      linarith
    rw [e, norm_mul, hζ, one_mul, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne), mul_one]

/-! ## Lemma lift -/

/-- **C08, Lemma 3 lift** (paper l.267-281), with the statement. -/
theorem lift {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (gp g0p : Polynomial ℂ) (hgp : gp ≠ 0) (hg0 : gp.eval 0 = 0) (k : ℕ) (hk : 1 ≤ k) (zs : List ℂ)
    (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1) (hh_ne : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, g0p.eval ζ ≠ 0)
    (hfac : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, gp.eval ζ = ζ ^ k * blaschke zs ζ * g0p.eval ζ)
    (cy : ℤ →₀ ℂ) (Y : Polynomial ℂ)
    (hY : ∀ θ : ℝ, (Y.eval (Complex.exp ((θ : ℂ) * Complex.I))).re = (trig cy θ).re) (hY0 : (Y.eval 0).im = 0) :
    let g : ℂ → ℂ := fun ζ => gp.eval ζ
    ∃ r : ℂ → ℂ, (∀ ζ ∈ Metric.ball (0 : ℂ) 1, r ζ ^ 2 = g0p.eval ζ) ∧
      DifferentiableOn ℂ (fun ζ => blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (Metric.ball 0 1) ∧
      ContinuousOn (fun ζ => blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun ζ => ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) (Metric.ball 0 1) ∧
      ContinuousOn (fun ζ => ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) (Metric.closedBall 0 1) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
        (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) * (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = g ζ) ∧
      (∀ θ : ℝ, G p s (blaschke zs (Complex.exp ((θ : ℂ) * Complex.I)) * r (Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (Y.eval (Complex.exp ((θ : ℂ) * Complex.I)) / 2))
          ((Complex.exp ((θ : ℂ) * Complex.I)) ^ k * r (Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-(Y.eval (Complex.exp ((θ : ℂ) * Complex.I))) / 2))
        = ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
            Gam p s (trig cy θ).re (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I))))) := by
  intro g
  have hp : 0 < p := by linarith
  have hroot1 : ∀ a ∈ g0p.roots, 1 ≤ ‖a‖ := fun a ha => one_le_norm_root hh_ne ha
  have hrootne : ∀ a ∈ g0p.roots, a ≠ 0 := fun a ha h => by
    have := hroot1 a ha
    rw [h, norm_zero] at this
    linarith
  obtain ⟨hBc, hBd⟩ := blaschke_cont_diff hzs
  have hrc := continuousOn_rfun hroot1
  have hrd := differentiableOn_rfun hroot1
  have hYd : Differentiable ℂ fun ζ => Complex.exp (Y.eval ζ / 2) :=
    ((Polynomial.differentiable Y).div_const 2).cexp
  have hYd' : Differentiable ℂ fun ζ => Complex.exp (-(Y.eval ζ) / 2) :=
    ((Polynomial.differentiable Y).neg.div_const 2).cexp
  have hprod : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      (blaschke zs ζ * rfun g0p ζ * Complex.exp (Y.eval ζ / 2)) *
        (ζ ^ k * rfun g0p ζ * Complex.exp (-(Y.eval ζ) / 2)) = gp.eval ζ := by
    intro ζ hζ
    have hE : Complex.exp (Y.eval ζ / 2) * Complex.exp (-(Y.eval ζ) / 2) = 1 := by
      rw [← Complex.exp_add, show Y.eval ζ / 2 + -(Y.eval ζ) / 2 = 0 by ring, Complex.exp_zero]
    calc (blaschke zs ζ * rfun g0p ζ * Complex.exp (Y.eval ζ / 2)) *
          (ζ ^ k * rfun g0p ζ * Complex.exp (-(Y.eval ζ) / 2))
        = ζ ^ k * blaschke zs ζ * rfun g0p ζ ^ 2 *
            (Complex.exp (Y.eval ζ / 2) * Complex.exp (-(Y.eval ζ) / 2)) := by ring
      _ = gp.eval ζ := by rw [rfun_sq g0p hrootne, hE, mul_one, ← hfac ζ hζ]
  refine ⟨rfun g0p, fun ζ _ => rfun_sq g0p hrootne ζ,
    (hBd.mul hrd).mul hYd.differentiableOn, (hBc.mul hrc).mul hYd.continuous.continuousOn,
    ((differentiable_pow k).differentiableOn.mul hrd).mul hYd'.differentiableOn,
    ((continuous_pow k).continuousOn.mul hrc).mul hYd'.continuous.continuousOn, hprod, fun θ => ?_⟩
  -- on the unit circle
  set e := Complex.exp ((θ : ℂ) * Complex.I) with he
  have hne : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hemem : e ∈ Metric.closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr hne.le
  have hg : g e = gp.eval e := rfl
  rw [hg, ← hprod e hemem]
  by_cases hr : rfun g0p e = 0
  · have hp0 : (p : ℝ) ≠ 0 := hp.ne'
    simp only [hr, mul_zero, zero_mul, norm_zero, zero_rpow (show p / 2 ≠ 0 by positivity)]
    unfold G
    simp [zero_rpow hp0, zero_rpow hs.ne', zero_rpow (show p / s ≠ 0 by positivity)]
  · have hB : blaschke zs e ≠ 0 := by
      intro h0; have := norm_blaschke_circle hzs hne; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hek : e ^ k ≠ 0 := pow_ne_zero _ (by intro h0; rw [h0, norm_zero] at hne; exact zero_ne_one hne)
    have hz : blaschke zs e * rfun g0p e * Complex.exp (Y.eval e / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hB hr) (Complex.exp_ne_zero _)
    have hw : e ^ k * rfun g0p e * Complex.exp (-(Y.eval e) / 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero hek hr) (Complex.exp_ne_zero _)
    have hre1 : (Y.eval e / 2).re = (Y.eval e).re / 2 := by simp [Complex.div_re]
    have hre2 : (-(Y.eval e) / 2).re = -((Y.eval e).re / 2) := by simp [Complex.div_re]; ring
    have hratio : ‖blaschke zs e * rfun g0p e * Complex.exp (Y.eval e / 2)‖ /
        ‖e ^ k * rfun g0p e * Complex.exp (-(Y.eval e) / 2)‖ = Real.exp (Y.eval e).re := by
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_blaschke_circle hzs hne, norm_pow, hne, one_pow, one_mul,
        Complex.norm_exp, Complex.norm_exp, hre1, hre2, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr hr),
        ← Real.exp_sub]
      congr 1
      ring
    unfold G
    rw [lift_pointwise p s hp1 hp2 hs _ _ hz hw, hratio, Real.log_exp, hY θ]
