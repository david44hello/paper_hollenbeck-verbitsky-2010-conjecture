/-
  HVFalse/Proofs/Discs.lean - (eq:discs) on trigonometric polynomials (the paper)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route (the paper's own, l.168-171, made exact on trigonometric polynomials):
  (1) coefficients c ↦ polynomials z = Σ_{n≥0} c_n ζ^n, w = Σ_{n<0} conj(c_n) ζ^{-n} (`toZ`, `toW`); w(0) = 0, and on the circle
      P₊f = z(e^{iθ}), P₋f = conj w(e^{iθ}).  Conversely (z, w) with w(0) = 0 ↦ c (`ofZW`) with the same two identities.
  (2) pointwise ((|P₊f|^s + |P₋f|^s)^{1/s})^p = 2^{p/s} ((|z|^s + |w|^s)/2)^{p/s} and hvConst^p = 2^{p/s} A^p, so
      (HV) ⇔ ∫ ((|z|^s+|w|^s)/2)^{p/s} ≤ A^p ∫ |z + w̄|^p ⇔ 0 ≤ ∫ G(z, w).
-/
import HVFalse.Defs.HV
import HVFalse.Proofs.Coercive

open Real

namespace P18

/-- The point `e^{iθ}` of the unit circle (the form used in `DiscIneq`). -/
noncomputable def unitPt (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem continuous_unitPt : Continuous unitPt :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem mode_natCast (k : ℕ) (a : ℂ) (θ : ℝ) : mode (k : ℤ) a θ = a * unitPt θ ^ k := by
  unfold mode unitPt
  rw [← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem mode_neg_natCast (k : ℕ) (a : ℂ) (θ : ℝ) :
    mode (-(k : ℤ)) a θ = a * (starRingEnd ℂ) (unitPt θ) ^ k := by
  unfold mode unitPt
  rw [← Complex.exp_conj, ← Complex.exp_nat_mul]
  congr 2
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem mode_add (n : ℤ) (a b : ℂ) (θ : ℝ) : mode n (a + b) θ = mode n a θ + mode n b θ := by
  unfold mode; ring

theorem mode_zero (n : ℤ) (θ : ℝ) : mode n 0 θ = 0 := by
  unfold mode; ring

/-- `P₋f = Σ_{n<0} c_n e^{inθ}`. -/
theorem Pminus_eq_sum (c : ℤ →₀ ℂ) (θ : ℝ) :
    Pminus c θ = c.sum fun n a => if n < 0 then mode n a θ else 0 := by
  unfold Pminus trig Pplus Finsupp.sum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs <;> first | (exfalso; omega) | ring1

theorem trig_eq_add (c : ℤ →₀ ℂ) (θ : ℝ) : trig c θ = Pplus c θ + Pminus c θ := by
  unfold Pminus; ring

/-! ### (1a) coefficients ↦ polynomials -/

/-- `z = Σ_{n ≥ 0} c_n ζ^n`. -/
noncomputable def toZ (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  c.sum fun n a => if 0 ≤ n then Polynomial.monomial n.toNat a else 0

/-- `w = Σ_{n < 0} conj(c_n) ζ^{-n}`. -/
noncomputable def toW (c : ℤ →₀ ℂ) : Polynomial ℂ :=
  c.sum fun n a => if n < 0 then Polynomial.monomial (-n).toNat ((starRingEnd ℂ) a) else 0

theorem toW_coeff_zero (c : ℤ →₀ ℂ) : (toW c).coeff 0 = 0 := by
  unfold toW Finsupp.sum
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.coeff_monomial]
    split_ifs with h' <;> first | rfl | (exfalso; omega)
  · rw [Polynomial.coeff_zero]

theorem eval_toZ (c : ℤ →₀ ℂ) (θ : ℝ) : (toZ c).eval (unitPt θ) = Pplus c θ := by
  unfold toZ Pplus Finsupp.sum
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.eval_monomial]
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [mode_natCast, Int.toNat_natCast]
  · rw [Polynomial.eval_zero]

theorem conj_eval_toW (c : ℤ →₀ ℂ) (θ : ℝ) : (starRingEnd ℂ) ((toW c).eval (unitPt θ)) = Pminus c θ := by
  rw [Pminus_eq_sum]
  unfold toW Finsupp.sum
  rw [Polynomial.eval_finsetSum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  dsimp only
  split_ifs with h
  · rw [Polynomial.eval_monomial, map_mul, map_pow, Complex.conj_conj]
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
    rw [mode_neg_natCast, neg_neg, Int.toNat_natCast]
  · rw [Polynomial.eval_zero, map_zero]

theorem eval_toW (c : ℤ →₀ ℂ) (θ : ℝ) : (toW c).eval (unitPt θ) = (starRingEnd ℂ) (Pminus c θ) := by
  rw [← conj_eval_toW, Complex.conj_conj]

theorem continuous_Pplus (c : ℤ →₀ ℂ) : Continuous (Pplus c) := by
  have h : Pplus c = fun θ => (toZ c).eval (unitPt θ) := funext fun θ => (eval_toZ c θ).symm
  rw [h]
  exact (Polynomial.continuous _).comp continuous_unitPt

theorem continuous_Pminus (c : ℤ →₀ ℂ) : Continuous (Pminus c) := by
  have h : Pminus c = fun θ => (starRingEnd ℂ) ((toW c).eval (unitPt θ)) :=
    funext fun θ => (conj_eval_toW c θ).symm
  rw [h]
  exact Complex.continuous_conj.comp ((Polynomial.continuous _).comp continuous_unitPt)

/-! ### (1b) polynomials ↦ coefficients -/

/-- `c_n = z_n` for `n ≥ 0`, `c_{-k} = conj(w_k)` for `k ≥ 1`. -/
noncomputable def ofZW (z w : Polynomial ℂ) : ℤ →₀ ℂ :=
  (∑ k ∈ z.support, Finsupp.single (k : ℤ) (z.coeff k)) +
    ∑ k ∈ w.support, Finsupp.single (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k))

theorem sum_ofZW (z w : Polynomial ℂ) (F : ℤ → ℂ → ℂ) (h0 : ∀ n, F n 0 = 0)
    (hadd : ∀ n a b, F n (a + b) = F n a + F n b) :
    (ofZW z w).sum F =
      ∑ k ∈ z.support, F k (z.coeff k) + ∑ k ∈ w.support, F (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k)) := by
  unfold ofZW
  rw [Finsupp.sum_add_index' h0 hadd, ← Finsupp.sum_finsetSum_index h0 hadd,
    ← Finsupp.sum_finsetSum_index h0 hadd]
  simp only [Finsupp.sum_single_index, h0]

theorem mem_support_ne_zero {w : Polynomial ℂ} (hw : w.coeff 0 = 0) {k : ℕ} (hk : k ∈ w.support) : k ≠ 0 := by
  rintro rfl
  exact (Polynomial.mem_support_iff.mp hk) hw

theorem Pplus_ofZW (z w : Polynomial ℂ) (hw : w.coeff 0 = 0) (θ : ℝ) :
    Pplus (ofZW z w) θ = z.eval (unitPt θ) := by
  unfold Pplus
  rw [sum_ofZW z w _ (fun n => by simp [mode_zero])
    (fun n a b => by by_cases h : 0 ≤ n <;> simp [h, mode_add])]
  have hz : ∀ k ∈ w.support,
      (if 0 ≤ -(k : ℤ) then mode (-(k : ℤ)) ((starRingEnd ℂ) (w.coeff k)) θ else 0) = 0 := by
    intro k hk
    have := mem_support_ne_zero hw hk
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, add_zero, Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with h
  · rw [mode_natCast]
  · exfalso; omega

theorem Pminus_ofZW (z w : Polynomial ℂ) (hw : w.coeff 0 = 0) (θ : ℝ) :
    Pminus (ofZW z w) θ = (starRingEnd ℂ) (w.eval (unitPt θ)) := by
  rw [Pminus_eq_sum, sum_ofZW z w _ (fun n => by simp [mode_zero])
    (fun n a b => by by_cases h : n < 0 <;> simp [h, mode_add])]
  have hz : ∀ k ∈ z.support, (if (k : ℤ) < 0 then mode (k : ℤ) (z.coeff k) θ else 0) = 0 := by
    intro k _
    split_ifs <;> first | rfl | (exfalso; omega)
  rw [Finset.sum_congr rfl hz, Finset.sum_const_zero, zero_add, Polynomial.eval_eq_sum, Polynomial.sum_def,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have := mem_support_ne_zero hw hk
  split_ifs with h
  · rw [mode_neg_natCast, map_mul, map_pow]
  · exfalso; omega

/-! ### (2) the integral identity -/

theorem G_conj (p s : ℝ) (P Q : ℂ) :
    G p s P ((starRingEnd ℂ) Q) =
      (1 / (2 * cos (π / (2 * p)))) ^ p * ‖P + Q‖ ^ p - ((‖P‖ ^ s + ‖Q‖ ^ s) / 2) ^ (p / s) := by
  unfold G
  rw [Complex.conj_conj, Complex.norm_conj]

theorem hvConst_rpow {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    hvConst p s ^ p = 2 ^ (p / s) * (1 / (2 * cos (π / (2 * p)))) ^ p := by
  have hc := cos_half_pos hp1 hp2
  unfold hvConst
  rw [div_eq_mul_one_div, mul_rpow (by positivity) (by positivity), ← rpow_mul (by norm_num),
    show 1 / s * p = p / s by ring]

theorem hv_integrand_eq (p s : ℝ) (P Q : ℂ) :
    ((‖P‖ ^ s + ‖Q‖ ^ s) ^ (1 / s)) ^ p = 2 ^ (p / s) * ((‖P‖ ^ s + ‖Q‖ ^ s) / 2) ^ (p / s) := by
  have ha : 0 ≤ ‖P‖ ^ s + ‖Q‖ ^ s := by positivity
  rw [← rpow_mul ha, show 1 / s * p = p / s by ring, ← mul_rpow (by norm_num) (by positivity)]
  congr 1
  ring

/-- (HV) for one pair of continuous boundary functions `P = P₊f`, `Q = P₋f` ⇔ `∫ G(P, conj Q) ≥ 0`. -/
theorem hv_integral_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {P Q : ℝ → ℂ}
    (hP : Continuous P) (hQ : Continuous Q) :
    (∫ θ in (0 : ℝ)..(2 * π), ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) ^ (1 / s)) ^ p
        ≤ hvConst p s ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖P θ + Q θ‖ ^ p) ↔
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), G p s (P θ) ((starRingEnd ℂ) (Q θ)) := by
  have hk : 0 < (2 : ℝ) ^ (p / s) := by positivity
  have hX : Continuous fun θ => ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) / 2) ^ (p / s) :=
    (((hP.norm.rpow_const fun _ => Or.inr hs.le).add (hQ.norm.rpow_const fun _ => Or.inr hs.le)).div_const 2).rpow_const
      fun _ => Or.inr (div_nonneg (by linarith) hs.le)
  have hY : Continuous fun θ => ‖P θ + Q θ‖ ^ p := (hP.add hQ).norm.rpow_const fun _ => Or.inr (by linarith)
  simp_rw [hv_integrand_eq, G_conj]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
    ((hY.const_mul _).intervalIntegrable _ _) (hX.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    hvConst_rpow hp1 hp2]
  set IX := ∫ θ in (0 : ℝ)..(2 * π), ((‖P θ‖ ^ s + ‖Q θ‖ ^ s) / 2) ^ (p / s)
  set IY := ∫ θ in (0 : ℝ)..(2 * π), ‖P θ + Q θ‖ ^ p
  set Ap := (1 / (2 * cos (π / (2 * p)))) ^ p
  constructor
  · intro h
    have h' : 2 ^ (p / s) * IX ≤ 2 ^ (p / s) * (Ap * IY) := by linarith [mul_assoc ((2 : ℝ) ^ (p / s)) Ap IY]
    linarith [le_of_mul_le_mul_left h' hk]
  · intro h
    have := mul_le_mul_of_nonneg_left (show IX ≤ Ap * IY by linarith) hk.le
    linarith [mul_assoc ((2 : ℝ) ^ (p / s)) Ap IY]

/-- C01 (eq:discs, l.168-174) on trigonometric polynomials: (HV) at `(p,s)` with the conjectured constant ⇔ `DiscIneq`. -/
theorem discs_equiv {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    HVIneq p s (hvConst p s) ↔ DiscIneq p s := by
  constructor
  · intro hHV z w hw
    have h := hHV (ofZW z w)
    simp_rw [trig_eq_add] at h
    have h2 := (hv_integral_iff hp1 hp2 hs (continuous_Pplus (ofZW z w)) (continuous_Pminus (ofZW z w))).mp h
    simp_rw [Pplus_ofZW z w hw, Pminus_ofZW z w hw, Complex.conj_conj] at h2
    exact h2
  · intro hD c
    have h := hD (toZ c) (toW c) (toW_coeff_zero c)
    have e : ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) = unitPt θ := fun θ => rfl
    simp_rw [e, eval_toZ, eval_toW] at h
    simp_rw [trig_eq_add]
    exact (hv_integral_iff hp1 hp2 hs (continuous_Pplus c) (continuous_Pminus c)).mpr h

end P18
