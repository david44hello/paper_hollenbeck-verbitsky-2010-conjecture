/-
  HVFalse/Proofs/SmallB.lean - small exact and numeric claims of the paper (C24, C10a6, C13a/d/f/g/k, C10c4, C10b3,
  C04d, C22b, C12c, C15c)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Numeric claims use exact rational bounds through integer powers (rpow_le_of_pow_le / le_rpow_of_pow_le) and
  Mathlib's π bounds; exp/cos from Taylor bounds (Real.exp_bound, Complex.exp_bound'). No interval arithmetic, no native
  code. `exponentiation.threshold` is raised for ONE theorem (jaguzovic_neg_39777: powers 2^39777, x^20000, x^13259).
-/
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV
import HVFalse.Defs.Extra
import HVFalse.Defs.Explicit
import HVFalse.Proofs.Bridges
import HVFalse.Proofs.SaddleSigns
import HVFalse.Proofs.SaddleValley
import HVFalse.Proofs.Small
import HVFalse.Proofs.Threshold

open Real Set

namespace P18

/-! ## Exact values -/

/-- C24, l.344: at `p = 3/2`: `u = 3`, `K = 1/2`, `H = 1` and `Q₄ = -3/32`. -/
theorem three_halves_values :
    uu (3 / 2) = 3 ∧ K (3 / 2) (uu (3 / 2)) = 1 / 2 ∧ H (3 / 2) (uu (3 / 2)) = 1 ∧ Acoef (3 / 2) = -3 / 32 := by
  have e : π / (2 * (3 / 2 : ℝ)) = π / 3 := by ring
  have hu : uu (3 / 2) = 3 := by
    unfold uu; rw [e, tan_pi_div_three, sq_sqrt (by norm_num)]
  refine ⟨hu, ?_, ?_, Acoef_three_halves⟩
  · rw [hu]; unfold K; norm_num
  · rw [hu]; unfold H; norm_num

/-- C10a6, l.386-387: `H(4/3, u(4/3)) = 0` (`u(4/3) = tan²(3π/8) = 3 + 2√2`, a root of `u² - 6u + 1`). -/
theorem H_at_four_thirds : H (4 / 3) (uu (4 / 3)) = 0 := by
  have e : π / (2 * (4 / 3 : ℝ)) = 3 * π / 8 := by ring
  have hu : uu (4 / 3) = 3 + 2 * √2 := by
    unfold uu; rw [e]; exact tan_three_pi_div_eight_sq
  rw [hu, H_four_thirds, u43_root, mul_zero]

/-- C13a, l.450: `w(0) = 0`. -/
theorem explicit_w0 (δ : ℝ) : Explicit.wf δ 0 = 0 := by
  simp [Explicit.wf]

/-- C13d, l.457: `zw = e^{iγ} ζ Π²`. -/
theorem explicit_product (δ : ℝ) (ζ : ℂ) :
    Explicit.zf δ ζ * Explicit.wf δ ζ =
      Complex.exp (Complex.I * ((Explicit.gam δ : ℝ) : ℂ)) * ζ * Explicit.Pi δ ζ ^ 2 := by
  have h1 : Complex.exp (Complex.I * ((Explicit.gam δ / 2 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * ((Explicit.gam δ / 2 : ℝ) : ℂ)) = Complex.exp (Complex.I * ((Explicit.gam δ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (Explicit.Yf δ ζ / 2) * Complex.exp (-(Explicit.Yf δ ζ) / 2) = 1 := by
    rw [← Complex.exp_add, show Explicit.Yf δ ζ / 2 + -(Explicit.Yf δ ζ) / 2 = 0 by ring, Complex.exp_zero]
  unfold Explicit.zf Explicit.wf
  linear_combination
    (ζ * Explicit.Pi δ ζ ^ 2 * Complex.exp (Complex.I * ((Explicit.gam δ / 2 : ℝ) : ℂ)) ^ 2) * h2 +
      (ζ * Explicit.Pi δ ζ ^ 2) * h1

/-- The exponents in terms of `1/π`: `α_A = (179/100)/π + 2/3`, `α_A + α_B = 4/3 + (136/10000)/π`. -/
theorem explicit_exps_eq :
    Explicit.aA = 179 / 100 * (1 / π) + 2 / 3 ∧ Explicit.aB = 2 / 3 + (136 / 10000 - 179 / 100) * (1 / π) ∧
      Explicit.aC = 2 / 3 - 136 / 10000 * (1 / π) := by
  have hpi : π ≠ 0 := pi_ne_zero
  have hA : Explicit.aA = 179 / 100 * (1 / π) + 2 / 3 := by
    unfold Explicit.aA Explicit.tS; ring
  have hB : Explicit.aB = 2 / 3 + (136 / 10000 - 179 / 100) * (1 / π) := by
    unfold Explicit.aB Explicit.bA Explicit.tS; field_simp; ring
  refine ⟨hA, hB, ?_⟩
  unfold Explicit.aC; rw [hA, hB]; ring

/-- C13f, l.472: `qα₋, qα₊, qα_π < 1` (`q = 3/4`). -/
theorem explicit_exponents : 3 / 4 * Explicit.aA < 1 ∧ 3 / 4 * Explicit.aB < 1 ∧ 3 / 4 * Explicit.aC < 1 := by
  obtain ⟨hA, hB, hC⟩ := explicit_exps_eq
  have hx0 : 0 < 1 / π := by positivity
  have hx : 1 / π < 1 / 3 := one_div_lt_one_div_of_lt (by norm_num) pi_gt_three
  rw [hA, hB, hC]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

/-- C13g, l.498: `ξ = qα_A + qα_B - 1 = 0.0032468 > 0` (5 significant digits); `ξ = (102/10000)/π`. -/
theorem explicit_e1 :
    0 < 3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 ∧
      |3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 - 32468 / 10 ^ 7| ≤ 5 / 10 ^ 8 := by
  obtain ⟨hA, hB, -⟩ := explicit_exps_eq
  have hx0 : 0 < 1 / π := by positivity
  have hlo : 1 / (3.141593 : ℝ) < 1 / π := one_div_lt_one_div_of_lt pi_pos pi_lt_d6
  have hhi : 1 / π < 1 / (3.141592 : ℝ) := one_div_lt_one_div_of_lt (by norm_num) pi_gt_d6
  norm_num at hlo hhi
  have e : 3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 = 102 / 10000 * π⁻¹ := by rw [hA, hB]; ring
  rw [e, abs_le]
  refine ⟨by positivity, by nlinarith, by nlinarith⟩

/-! ## Signs -/

open SaddleSigns in
/-- C10c4, l.373-375: `K > 0` on all of `(1, 2)` (the Jordan argument for `K_pos` needs only `1 < p`). -/
theorem K_pos_wide {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 < K p (uu p) := by
  have hp0 : 0 < p := by linarith
  have hd := denom_pos p hp1 hp2
  rw [uu_eq hp1 hp2, K_eq hd.ne']
  apply div_pos _ hd
  have hj := mul_lt_mul_of_pos_left (jordan_c hp1 hp2) hp0
  have e : p * (2 / p - 1) = 2 - p := by field_simp
  linarith

/-- C10b3, l.342-344, l.375-377: `Γ < e` on the valley for small `y ≠ 0` (from `Γ - e = Q₄ y⁴ + O(y⁶)` and `Q₄ < 0`). -/
theorem valley_negative {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ 0 → |y| < δ →
      Gam p (Ssec p) y (π / p - valleyC p * y ^ 2) < ee p (π / p - valleyC p * y ^ 2) := by
  obtain ⟨C, δ, hδ, hb⟩ := SaddleValley.saddle_valley_proved hp1 hp2
  have hA := SaddleValley.Acoef_neg hp1 hp2
  set M := max C 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hCM : C ≤ M := le_max_left _ _
  have hr : 0 < -Acoef p / (2 * M) := div_pos (by linarith) (by linarith)
  refine ⟨min δ (min 1 (-Acoef p / (2 * M))), lt_min hδ (lt_min one_pos hr), fun y hy0 hy => ?_⟩
  have hyδ : |y| < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy1 : |y| < 1 := lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_left _ _))
  have hyA : |y| < -Acoef p / (2 * M) := lt_of_lt_of_le hy (le_trans (min_le_right _ _) (min_le_right _ _))
  have hy2 : y ^ 2 ≤ |y| := by nlinarith [abs_nonneg y, sq_abs y]
  have hy4 : 0 < y ^ 4 := by positivity
  have hMy : M * y ^ 2 < -Acoef p / 2 := by
    have h1 : M * y ^ 2 ≤ M * |y| := mul_le_mul_of_nonneg_left hy2 (by linarith)
    have h2 : M * |y| < M * (-Acoef p / (2 * M)) := mul_lt_mul_of_pos_left hyA (by linarith)
    have e : M * (-Acoef p / (2 * M)) = -Acoef p / 2 := by field_simp
    linarith
  have hup := (abs_le.mp (hb y hyδ)).2
  have h6 : C * y ^ 6 ≤ M * y ^ 2 * y ^ 4 := by
    calc C * y ^ 6 ≤ M * y ^ 6 := mul_le_mul_of_nonneg_right hCM (by positivity)
      _ = M * y ^ 2 * y ^ 4 := by ring
  have h7 : M * y ^ 2 * y ^ 4 < -Acoef p / 2 * y ^ 4 := mul_lt_mul_of_pos_right hMy hy4
  have h8 : Acoef p * y ^ 4 < 0 := mul_neg_of_neg_of_pos hA hy4
  linarith

/-- C04d, l.205-211: `s₀(p) ≤ sec²ϑ`, `s₀(p) ≥ p/(p-1)` for `4/3 < p < 2` [Jag2026], `s₀(p) = sec²ϑ` for `p ≤ 4/3`
[Mel2023, (37)]. -/
theorem threshold_bounds {p s0 : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 ≤ Ssec p ∧ (4 / 3 < p → p / (p - 1) ≤ s0) ∧ (p ≤ 4 / 3 → s0 = Ssec p) := by
  have hS := Ssec_pos hp1
  have h1 : s0 ≤ Ssec p := by
    by_contra hc
    have hlt : Ssec p < s0 := not_le.mp hc
    exact twoVar_fails_above hp1 hp2 hlt ((hs0 s0 (lt_trans hS hlt)).mpr le_rfl)
  refine ⟨h1, fun h43 => (hs0 _ (div_pos (by linarith) (by linarith))).mp (twoVar_jag h43 hp2), fun h43 => ?_⟩
  exact le_antisymm h1 ((hs0 _ hS).mp (twoVar_mel hp1 h43))

set_option linter.unusedVariables false in
/-- C22b, l.629-630: the feasible `λ` form an up-set (`Γ_λ` increases with `λ`: its first term is `≥ 0`). -/
theorem feasible_upset {p s lam lam' : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hlam : 0 < lam)
    (hll : lam ≤ lam') (hf : LamFeasible p s lam) : LamFeasible p s lam' := by
  obtain ⟨φ, hφ, hle⟩ := hf
  refine ⟨φ, hφ, fun y t => (hle y t).trans ?_⟩
  unfold GamLam
  have hT : 0 ≤ (cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2) := by
    apply div_nonneg
    · apply rpow_nonneg; nlinarith [one_le_cosh y, neg_one_le_cos t]
    · apply rpow_nonneg; linarith [neg_one_le_cos (2 * (π / (2 * p)))]
  have := mul_le_mul_of_nonneg_right hll hT
  linarith

/-- C13k (first part), l.459: `Γ(0, -2π/3) = 0` at `p = 3/2` (a contact point, `2π/3 = π/p`). -/
theorem explicit_arc_contact : Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 := by
  rw [show 2 * π / 3 = π / (3 / 2) by ring]
  exact gam_contact_neg (3 / 2) (398 / 100) (by norm_num) (by norm_num)

/-! ## Rational enclosures of closed forms (C12c, C15c) -/

/-- Two-sided rational bounds of `x^(m/n)` from integer powers (the bridge lemmas). -/
theorem rpow_encl {x lo hi : ℝ} {m n : ℕ} (hx : 0 ≤ x) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (hn : n ≠ 0)
    (h1 : lo ^ n ≤ x ^ m) (h2 : x ^ m ≤ hi ^ n) : lo ≤ x ^ ((m : ℝ) / n) ∧ x ^ ((m : ℝ) / n) ≤ hi :=
  ⟨le_rpow_of_pow_le hx hlo hn h1, rpow_le_of_pow_le hx hhi hn h2⟩

/-- Bounds of `(B + 1/B)/2` from bounds of `B > 0`. -/
theorem mean_encl {B lo hi : ℝ} (hlo : 0 < lo) (hB : lo ≤ B ∧ B ≤ hi) :
    (lo + hi⁻¹) / 2 ≤ (B + B⁻¹) / 2 ∧ (B + B⁻¹) / 2 ≤ (hi + lo⁻¹) / 2 := by
  have hB0 : 0 < B := lt_of_lt_of_le hlo hB.1
  have h1 : hi⁻¹ ≤ B⁻¹ := inv_anti₀ hB0 hB.2
  have h2 : B⁻¹ ≤ lo⁻¹ := inv_anti₀ hlo hB.1
  constructor <;> linarith [hB.1, hB.2]

/-- Bounds of `((B + 1/B)/2)^(m/n)` from bounds of `B` and rational bounds of the mean. -/
theorem meanpow_encl {B Blo Bhi Xlo Xhi Tlo Thi : ℝ} {m n : ℕ} (hn : n ≠ 0) (hBlo : 0 < Blo)
    (hB : Blo ≤ B ∧ B ≤ Bhi) (hXlo0 : 0 ≤ Xlo) (hXlo : Xlo ≤ (Blo + Bhi⁻¹) / 2) (hXhi : (Bhi + Blo⁻¹) / 2 ≤ Xhi)
    (hTlo0 : 0 ≤ Tlo) (hThi0 : 0 ≤ Thi) (h1 : Tlo ^ n ≤ Xlo ^ m) (h2 : Xhi ^ m ≤ Thi ^ n) :
    Tlo ≤ ((B + B⁻¹) / 2) ^ ((m : ℝ) / n) ∧ ((B + B⁻¹) / 2) ^ ((m : ℝ) / n) ≤ Thi := by
  obtain ⟨hX1, hX2⟩ := mean_encl hBlo hB
  have hr : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  have hX0 : 0 ≤ (B + B⁻¹) / 2 := by linarith
  have hXhi0 : 0 ≤ Xhi := by linarith
  exact ⟨(le_rpow_of_pow_le hXlo0 hTlo0 hn h1).trans (rpow_le_rpow hXlo0 (hXlo.trans hX1) hr),
    (rpow_le_rpow hX0 (hX2.trans hXhi) hr).trans (rpow_le_of_pow_le hXhi0 hThi0 hn h2)⟩

/-- Bounds of `√3 · √(2 - √2)` from rational bounds of the square roots. -/
theorem sqrt_prod_encl {l3 u3 lc uc : ℝ} (hl3 : 0 ≤ l3) (h3l : l3 ^ 2 ≤ 3) (hu3 : 0 ≤ u3) (h3u : 3 ≤ u3 ^ 2)
    (hlc : 0 ≤ lc) (hlc1 : 0 ≤ 2 - lc ^ 2) (hlc2 : 2 ≤ (2 - lc ^ 2) ^ 2)
    (huc : 0 ≤ uc) (huc1 : 0 ≤ 2 - uc ^ 2) (huc2 : (2 - uc ^ 2) ^ 2 ≤ 2) :
    l3 * lc ≤ √3 * √(2 - √2) ∧ √3 * √(2 - √2) ≤ u3 * uc := by
  have a1 : l3 ≤ √3 := calc l3 = √(l3 ^ 2) := (Real.sqrt_sq hl3).symm
    _ ≤ √3 := Real.sqrt_le_sqrt h3l
  have a2 : √3 ≤ u3 := calc √3 ≤ √(u3 ^ 2) := Real.sqrt_le_sqrt h3u
    _ = u3 := Real.sqrt_sq hu3
  have b1 : √2 ≤ 2 - lc ^ 2 := calc √2 ≤ √((2 - lc ^ 2) ^ 2) := Real.sqrt_le_sqrt hlc2
    _ = 2 - lc ^ 2 := Real.sqrt_sq hlc1
  have b2 : 2 - uc ^ 2 ≤ √2 := calc 2 - uc ^ 2 = √((2 - uc ^ 2) ^ 2) := (Real.sqrt_sq huc1).symm
    _ ≤ √2 := Real.sqrt_le_sqrt huc2
  have c1 : lc ≤ √(2 - √2) := calc lc = √(lc ^ 2) := (Real.sqrt_sq hlc).symm
    _ ≤ √(2 - √2) := Real.sqrt_le_sqrt (by linarith)
  have c2 : √(2 - √2) ≤ uc := calc √(2 - √2) ≤ √(uc ^ 2) := Real.sqrt_le_sqrt (by linarith)
    _ = uc := Real.sqrt_sq huc
  exact ⟨mul_le_mul a1 c1 hlc (Real.sqrt_nonneg 3), mul_le_mul a2 c2 (Real.sqrt_nonneg _) hu3⟩

/-- Bounds of `A - T - C/2` from bounds of `A`, `T`, `C`. -/
theorem closed_encl {A T C Alo Ahi Tlo Thi Clo Chi : ℝ} (hA : Alo ≤ A ∧ A ≤ Ahi) (hT : Tlo ≤ T ∧ T ≤ Thi)
    (hC : Clo ≤ C ∧ C ≤ Chi) : Alo - Thi - Chi / 2 ≤ A - T - C / 2 ∧ A - T - C / 2 ≤ Ahi - Tlo - Clo / 2 :=
  ⟨by linarith [hA.1, hT.2, hC.2], by linarith [hA.2, hT.1, hC.1]⟩

theorem abs_sub_le_of_encl {v lo hi c e : ℝ} (h : lo ≤ v ∧ v ≤ hi) (h1 : c - e ≤ lo) (h2 : hi ≤ c + e) :
    |v - c| ≤ e :=
  abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- C12c, l.420: `Γ - e ∈ -4.17314647396549·10⁻⁴ + [-10⁻¹⁸, 10⁻¹⁸]` at `p = 3/2, s = 3.98, y = log(9/5), t = π/2`
(25-digit rational bounds of each term of the closed form). -/
theorem point_enclosure :
    |Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) - (-417314647396549 / 10 ^ 18)| ≤ 1 / 10 ^ 18 := by
  have hinv : (5 / 9 : ℝ) ^ ((199 : ℝ) / 100) = ((9 / 5 : ℝ) ^ ((199 : ℝ) / 100))⁻¹ := by
    rw [show (5 / 9 : ℝ) = (9 / 5 : ℝ)⁻¹ by norm_num, inv_rpow (by norm_num)]
  have hA := rpow_encl (x := 106 / 45) (lo := (19013847818514229560753549 / 10000000000000000000000000 : ℝ)) (hi := (380276956370284591215071 / 200000000000000000000000 : ℝ)) (m := 3) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB := rpow_encl (x := 9 / 5) (lo := (3221011572449414195336791 / 1000000000000000000000000 : ℝ)) (hi := (32210115724494141953367911 / 10000000000000000000000000 : ℝ)) (m := 199) (n := 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hA hB
  have hT := meanpow_encl (B := (9 / 5 : ℝ) ^ ((199 : ℝ) / 100)) (Xlo := (17657365231387553851292627 / 10000000000000000000000000 : ℝ)) (Xhi := (4414341307846888462823157 / 2500000000000000000000000 : ℝ))
    (Tlo := (6194874742138179661837751 / 5000000000000000000000000 : ℝ)) (Thi := (12389749484276359323675503 / 10000000000000000000000000 : ℝ)) (m := 75) (n := 199)
    (by norm_num) (by norm_num) hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hT
  have hC := sqrt_prod_encl (l3 := (17320508075688772935274463 / 10000000000000000000000000 : ℝ)) (u3 := (541265877365274154227327 / 312500000000000000000000 : ℝ)) (lc := (7653668647301795434569199 / 10000000000000000000000000 : ℝ)) (uc := (19134171618254488586423 / 25000000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have key := closed_encl hA hT hC
  rw [point_closed_form, hinv]
  exact abs_sub_le_of_encl key (by norm_num) (by norm_num)

/-- `cosh(s log 2 / 2) = (2^(s/2) + 2^(-s/2))/2`. -/
theorem cosh_log_two_mul (s : ℝ) : cosh (s * log 2 / 2) = ((2 : ℝ) ^ (s / 2) + ((2 : ℝ) ^ (s / 2))⁻¹) / 2 := by
  rw [cosh_eq, show s * log 2 / 2 = log 2 * (s / 2) by ring, exp_neg, ← rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Jaguzović's point `(log 2, π/2)` at `p = 3/2` and any `s`: the closed form of `Γ - e`. -/
theorem jag_closed_form_s (s : ℝ) :
    Gam (3 / 2) s (log 2) (π / 2) - ee (3 / 2) (π / 2) =
      (5 / 2 : ℝ) ^ ((3 : ℝ) / 4) - (((2 : ℝ) ^ (s / 2) + ((2 : ℝ) ^ (s / 2))⁻¹) / 2) ^ ((3 / 2 : ℝ) / s)
        - √3 * √(2 - √2) / 2 := by
  obtain ⟨hθ, h2θ, hqt, -⟩ := angle_facts
  have hc2 : cosh (log 2) = 5 / 4 := by rw [cosh_log (by norm_num)]; norm_num
  unfold Gam ee
  rw [hθ, h2θ, hqt, hc2, cosh_log_two_mul, cos_pi_div_two, tan_pi_div_three,
    ← div_rpow (by norm_num : (0 : ℝ) ≤ 5 / 4 + 0) (by norm_num : (0 : ℝ) ≤ 1 + -1 / 2)]
  have hq : (3 / 2 : ℝ) / 2 = 3 / 4 := by norm_num
  have hb : ((5 / 4 + 0 : ℝ) / (1 + -1 / 2)) = 5 / 2 := by norm_num
  rw [hq, hb]
  ring

/-- C15c (second part), l.411: at Jaguzović's point, `Γ - e = -1.398·10⁻⁴` at `s = 3.98` (within `5·10⁻⁸`). -/
theorem jaguzovic_value_398 :
    |Gam (3 / 2) (398 / 100) (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-1398 / 10 ^ 7)| ≤ 5 / 10 ^ 8 := by
  have hA := rpow_encl (x := 5 / 2) (lo := (994088410958813 / 500000000000000 : ℝ)) (hi := (1988176821917627 / 1000000000000000 : ℝ)) (m := 3) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB := rpow_encl (x := 2) (lo := (3972369981748143 / 1000000000000000 : ℝ)) (hi := (248273123859259 / 62500000000000 : ℝ)) (m := 199) (n := 100)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hA hB
  have hT := meanpow_encl (B := (2 : ℝ) ^ ((199 : ℝ) / 100)) (Xlo := (2112054434631161 / 1000000000000000 : ℝ)) (Xhi := (1056027217315581 / 500000000000000 : ℝ))
    (Tlo := (1325489514994971 / 1000000000000000 : ℝ)) (Thi := (1325489514994973 / 1000000000000000 : ℝ)) (m := 75) (n := 199)
    (by norm_num) (by norm_num) hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hT
  have hC := sqrt_prod_encl (l3 := (1732050807568877 / 1000000000000000 : ℝ)) (u3 := (866025403784439 / 500000000000000 : ℝ)) (lc := (765366864730179 / 1000000000000000 : ℝ)) (uc := (38268343236509 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have key := closed_encl hA hT hC
  rw [jag_closed_form_s, show (398 / 100 : ℝ) / 2 = 199 / 100 by norm_num,
    show (3 / 2 : ℝ) / (398 / 100) = 75 / 199 by norm_num]
  exact abs_sub_le_of_encl key (by norm_num) (by norm_num)

set_option exponentiation.threshold 100000 in
/-- At Jaguzović's point, `Γ - e < 0` at `s = 3.9777` (value `-4.903·10⁻⁶`; 9-digit bounds, exponents `39777/20000`
and `5000/13259` through integer powers). -/
theorem jaguzovic_neg_39777 : Gam (3 / 2) (39777 / 10000) (log 2) (π / 2) - ee (3 / 2) (π / 2) < 0 := by
  have hA := rpow_encl (x := 5 / 2) (lo := (1988176821 / 1000000000 : ℝ)) (hi := (994088411 / 500000000 : ℝ)) (m := 3) (n := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hB := rpow_encl (x := 2) (lo := (396920479 / 100000000 : ℝ)) (hi := (3969204791 / 1000000000 : ℝ)) (m := 39777) (n := 20000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hA hB
  have hT := meanpow_encl (B := (2 : ℝ) ^ ((39777 : ℝ) / 20000)) (Xlo := (2110572211 / 1000000000 : ℝ)) (Xhi := (2110572213 / 1000000000 : ℝ))
    (Tlo := (1325354577 / 1000000000 : ℝ)) (Thi := (662677289 / 500000000 : ℝ)) (m := 5000) (n := 13259)
    (by norm_num) (by norm_num) hB (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [Nat.cast_ofNat] at hT
  have hC := sqrt_prod_encl (l3 := (1732050807 / 1000000000 : ℝ)) (u3 := (216506351 / 125000000 : ℝ)) (lc := (47835429 / 62500000 : ℝ)) (uc := (153073373 / 200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have key := closed_encl hA hT hC
  rw [jag_closed_form_s, show (39777 / 10000 : ℝ) / 2 = 39777 / 20000 by norm_num,
    show (3 / 2 : ℝ) / (39777 / 10000) = 5000 / 13259 by norm_num]
  exact lt_of_le_of_lt key.2 (by norm_num)

/-- C15c (first part), l.411: at Jaguzović's point, `Γ < e` for every `s ∈ (3.9777, 4]` (`Γ` decreases in `s`). -/
theorem jaguzovic_range_lt :
    ∀ s : ℝ, 39777 / 10000 < s → s ≤ 4 → Gam (3 / 2) s (log 2) (π / 2) < ee (3 / 2) (π / 2) := by
  intro s hs _
  have h := gam_antitone_s (3 / 2) (39777 / 10000) s (log 2) (π / 2) (by norm_num) (by norm_num) hs.le
  linarith [jaguzovic_neg_39777]

/-- The statement of C09 (Prop. fail, in an earlier draft: a failure point anywhere in `[-π, π]`), as a hypothesis. -/
def PropFailIcc : Prop :=
  ∀ {p s : ℝ}, 1 < p → p < 2 → 0 < s → s ≤ Ssec p →
    (∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p s y t < ee p t) → ¬ HVIneq p s (hvConst p s)

/-- C15c, l.410-412, from Prop. fail (C09): all three parts; the third is (HV) failing for every `s ∈ [3.978, 4]`. -/
theorem jaguzovic_range_of_fail (h9 : PropFailIcc) :
    (∀ s : ℝ, 39777 / 10000 < s → s ≤ 4 → Gam (3 / 2) s (log 2) (π / 2) < ee (3 / 2) (π / 2)) ∧
      |Gam (3 / 2) (398 / 100) (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-1398 / 10 ^ 7)| ≤ 5 / 10 ^ 8 ∧
      ∀ s ∈ Icc (3978 / 1000 : ℝ) 4, ¬ HVIneq (3 / 2) s (hvConst (3 / 2) s) := by
  refine ⟨jaguzovic_range_lt, jaguzovic_value_398, fun s hs => ?_⟩
  have hS : Ssec (3 / 2) = 4 := by linarith [point_location.2]
  have hpi := pi_pos
  exact h9 (by norm_num) (by norm_num) (by linarith [hs.1]) (by rw [hS]; exact hs.2)
    ⟨log 2, π / 2, ⟨by linarith, by linarith⟩, jaguzovic_range_lt s (by linarith [hs.1]) hs.2⟩

/-! ## Taylor enclosures of `exp` and `cos` (C13k) -/

/-- `cos` to 8 Taylor terms: `|cos a - Σ_{k<8} (-1)^k a^(2k)/(2k)!| ≤ 2|a|^16/16!` for `|a| ≤ 2` (`Complex.exp_bound'` at
`a·i`; the real part of the partial sum is the cosine polynomial). -/
theorem cos_taylor16 (a : ℝ) (ha : |a| ≤ 2) :
    |cos a - (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
      - a ^ 14 / 87178291200)| ≤ |a| ^ 16 / 20922789888000 * 2 := by
  have hS : ∑ m ∈ Finset.range 16, ((a : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      (((1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
        - a ^ 14 / 87178291200 : ℝ)) : ℂ) +
      (((a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040 + a ^ 9 / 362880 - a ^ 11 / 39916800 + a ^ 13 / 6227020800
        - a ^ 15 / 1307674368000 : ℝ)) : ℂ) * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast
    linear_combination ((a : ℂ)^15*Complex.I^13/1307674368000 - (a : ℂ)^15*Complex.I^11/1307674368000 + (a : ℂ)^15*Complex.I^9/1307674368000 - (a : ℂ)^15*Complex.I^7/1307674368000 + (a : ℂ)^15*Complex.I^5/1307674368000 - (a : ℂ)^15*Complex.I^3/1307674368000 + (a : ℂ)^15*Complex.I/1307674368000 + (a : ℂ)^14*Complex.I^12/87178291200 - (a : ℂ)^14*Complex.I^10/87178291200 + (a : ℂ)^14*Complex.I^8/87178291200 - (a : ℂ)^14*Complex.I^6/87178291200 + (a : ℂ)^14*Complex.I^4/87178291200 - (a : ℂ)^14*Complex.I^2/87178291200 + (a : ℂ)^14/87178291200 + (a : ℂ)^13*Complex.I^11/6227020800 - (a : ℂ)^13*Complex.I^9/6227020800 + (a : ℂ)^13*Complex.I^7/6227020800 - (a : ℂ)^13*Complex.I^5/6227020800 + (a : ℂ)^13*Complex.I^3/6227020800 - (a : ℂ)^13*Complex.I/6227020800 + (a : ℂ)^12*Complex.I^10/479001600 - (a : ℂ)^12*Complex.I^8/479001600 + (a : ℂ)^12*Complex.I^6/479001600 - (a : ℂ)^12*Complex.I^4/479001600 + (a : ℂ)^12*Complex.I^2/479001600 - (a : ℂ)^12/479001600 + (a : ℂ)^11*Complex.I^9/39916800 - (a : ℂ)^11*Complex.I^7/39916800 + (a : ℂ)^11*Complex.I^5/39916800 - (a : ℂ)^11*Complex.I^3/39916800 + (a : ℂ)^11*Complex.I/39916800 + (a : ℂ)^10*Complex.I^8/3628800 - (a : ℂ)^10*Complex.I^6/3628800 + (a : ℂ)^10*Complex.I^4/3628800 - (a : ℂ)^10*Complex.I^2/3628800 + (a : ℂ)^10/3628800 + (a : ℂ)^9*Complex.I^7/362880 - (a : ℂ)^9*Complex.I^5/362880 + (a : ℂ)^9*Complex.I^3/362880 - (a : ℂ)^9*Complex.I/362880 + (a : ℂ)^8*Complex.I^6/40320 - (a : ℂ)^8*Complex.I^4/40320 + (a : ℂ)^8*Complex.I^2/40320 - (a : ℂ)^8/40320 + (a : ℂ)^7*Complex.I^5/5040 - (a : ℂ)^7*Complex.I^3/5040 + (a : ℂ)^7*Complex.I/5040 + (a : ℂ)^6*Complex.I^4/720 - (a : ℂ)^6*Complex.I^2/720 + (a : ℂ)^6/720 + (a : ℂ)^5*Complex.I^3/120 - (a : ℂ)^5*Complex.I/120 + (a : ℂ)^4*Complex.I^2/24 - (a : ℂ)^4/24 + (a : ℂ)^3*Complex.I/6 + (a : ℂ)^2/2) * Complex.I_sq
  have hn : ‖(a : ℂ) * Complex.I‖ = |a| := by simp
  have hb := Complex.exp_bound' (x := (a : ℂ) * Complex.I) (n := 16)
    (by rw [hn, div_le_iff₀ (by positivity)]; norm_num; linarith)
  rw [hS, hn] at hb
  refine le_trans ?_ (le_of_le_of_eq hb (by norm_num [Nat.factorial]))
  refine le_of_eq_of_le ?_ (Complex.abs_re_le_norm _)
  congr 1
  simp only [Complex.sub_re, Complex.add_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Complex.re_ofReal_mul,
    Complex.I_re, mul_zero, add_zero]

/-- Two-sided bounds of `cos a` from the 8-term Taylor polynomial. -/
theorem cos_taylor_encl {a lo hi : ℝ} (ha : |a| ≤ 2)
    (hlo : lo ≤ (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
      - a ^ 14 / 87178291200) - |a| ^ 16 / 20922789888000 * 2)
    (hhi : (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
      - a ^ 14 / 87178291200) + |a| ^ 16 / 20922789888000 * 2 ≤ hi) : lo ≤ cos a ∧ cos a ≤ hi := by
  have h := abs_le.mp (cos_taylor16 a ha)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Two-sided bounds of `exp x` from `Real.exp_bound`. -/
theorem exp_taylor_encl {x lo hi : ℝ} {n : ℕ} (hx : |x| ≤ 1) (hn : 0 < n)
    (hlo : lo ≤ ∑ m ∈ Finset.range n, x ^ m / m.factorial - |x| ^ n * (n.succ / (n.factorial * n)))
    (hhi : ∑ m ∈ Finset.range n, x ^ m / m.factorial + |x| ^ n * (n.succ / (n.factorial * n)) ≤ hi) :
    lo ≤ exp x ∧ exp x ≤ hi := by
  have h := abs_le.mp (Real.exp_bound hx hn)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Bounds of `Y^(m/n)` from bounds of `Y ≥ 0` and integer powers. -/
theorem rpow_mono_encl {Y Ylo Yhi Flo Fhi : ℝ} {m n : ℕ} (hn : n ≠ 0) (hYlo0 : 0 ≤ Ylo) (hY : Ylo ≤ Y ∧ Y ≤ Yhi)
    (hFlo0 : 0 ≤ Flo) (hFhi0 : 0 ≤ Fhi) (h1 : Flo ^ n ≤ Ylo ^ m) (h2 : Yhi ^ m ≤ Fhi ^ n) :
    Flo ≤ Y ^ ((m : ℝ) / n) ∧ Y ^ ((m : ℝ) / n) ≤ Fhi := by
  have hr : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  have hY0 : 0 ≤ Y := hYlo0.trans hY.1
  exact ⟨(le_rpow_of_pow_le hYlo0 hFlo0 hn h1).trans (rpow_le_rpow hYlo0 hY.1 hr),
    (rpow_le_rpow hY0 hY.2 hr).trans (rpow_le_of_pow_le (hY0.trans hY.2) hFhi0 hn h2)⟩

/-- The closed form of `Γ(y₂,t₂) - e(t₂)` at `(p, s) = (3/2, 3.98)`: `(2(cosh y₂ + cos t₂))^(3/4) - cosh(s y₂/2)^(75/199)
- √3 cos(3t₂/4)`. -/
theorem explicit_arc_closed_form :
    Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS =
      (2 * (cosh (4865 / 10000) + cos (179 / 100))) ^ ((3 : ℝ) / 4) - cosh (193627 / 200000) ^ ((75 : ℝ) / 199)
        - √3 * cos (537 / 400) := by
  obtain ⟨hθ, h2θ, -, -⟩ := angle_facts
  have hW : (0 : ℝ) ≤ cosh (4865 / 10000) + cos (179 / 100) := by
    linarith [one_le_cosh (4865 / 10000 : ℝ), neg_one_le_cos (179 / 100 : ℝ)]
  unfold Gam ee Explicit.y2 Explicit.tS
  rw [hθ, h2θ, tan_pi_div_three, ← div_rpow hW (by norm_num : (0 : ℝ) ≤ 1 + -1 / 2),
    show (cosh (4865 / 10000) + cos (179 / 100)) / (1 + -1 / 2) = 2 * (cosh (4865 / 10000) + cos (179 / 100)) by ring,
    show (3 / 2 : ℝ) / 2 = 3 / 4 by norm_num, show (398 / 100 : ℝ) * (4865 / 10000) / 2 = 193627 / 200000 by norm_num,
    show (3 / 2 : ℝ) / (398 / 100) = 75 / 199 by norm_num, show (3 / 4 : ℝ) * (179 / 100) = 537 / 400 by norm_num]

/-- C13k (second part), l.504-505: `Γ(y₂,t₂) - e(t₂) = -7.7·10⁻⁴` (2 digits: within `5·10⁻⁶`) at `(p, s) = (3/2, 3.98)`
(true value `-7.68887·10⁻⁴`; 12-digit Taylor bounds of `exp`, `cos`). -/
theorem explicit_arc_value :
    |Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS - (-77 / 10 ^ 5)| ≤ 5 / 10 ^ 6 := by
  have hcosh : ∀ x : ℝ, cosh x = (exp x + (exp x)⁻¹) / 2 := fun x => by rw [cosh_eq, exp_neg]
  have ha1 : |(4865 / 10000 : ℝ)| = 4865 / 10000 := abs_of_pos (by norm_num)
  have ha2 : |(193627 / 200000 : ℝ)| = 193627 / 200000 := abs_of_pos (by norm_num)
  have ha3 : |(179 / 100 : ℝ)| = 179 / 100 := abs_of_pos (by norm_num)
  have ha4 : |(537 / 400 : ℝ)| = 537 / 400 := abs_of_pos (by norm_num)
  -- cosh y₂ + cos t₂, and the first term
  have hE1 := exp_taylor_encl (x := 4865 / 10000) (lo := (406653274867 / 250000000000 : ℝ)) (hi := (1626613099469 / 1000000000000 : ℝ)) (n := 14)
    (by rw [ha1]; norm_num) (by norm_num) (by rw [ha1]; norm_num [Finset.sum_range_succ, Nat.factorial])
    (by rw [ha1]; norm_num [Finset.sum_range_succ, Nat.factorial])
  have hC1 := mean_encl (by norm_num) hE1
  rw [← hcosh] at hC1
  have hc1 := cos_taylor_encl (a := 179 / 100) (lo := (-217452422269 / 1000000000000 : ℝ)) (hi := (-13590776259 / 62500000000 : ℝ))
    (by rw [ha3]; norm_num) (by rw [ha3]; norm_num) (by rw [ha3]; norm_num)
  have hY : (451620649553 / 250000000000 : ℝ) ≤ 2 * (cosh (4865 / 10000) + cos (179 / 100)) ∧
      2 * (cosh (4865 / 10000) + cos (179 / 100)) ≤ (56452581327 / 31250000000 : ℝ) := by
    have k1 : (451620649553 / 250000000000 : ℝ) ≤ 2 * (((406653274867 / 250000000000 : ℝ) + (1626613099469 / 1000000000000 : ℝ)⁻¹) / 2 + (-217452422269 / 1000000000000 : ℝ)) := by norm_num
    have k2 : 2 * (((1626613099469 / 1000000000000 : ℝ) + (406653274867 / 250000000000 : ℝ)⁻¹) / 2 + (-13590776259 / 62500000000 : ℝ)) ≤ (56452581327 / 31250000000 : ℝ) := by norm_num
    exact ⟨by linarith [hC1.1, hc1.1], by linarith [hC1.2, hc1.2]⟩
  have hF := rpow_mono_encl (Flo := (389551916629 / 250000000000 : ℝ)) (Fhi := (389551917317 / 250000000000 : ℝ)) (m := 3) (n := 4)
    (by norm_num) (by norm_num) hY (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- the second term
  have hE2 := exp_taylor_encl (x := 193627 / 200000) (lo := (2633029277753 / 1000000000000 : ℝ)) (hi := (2633029277769 / 1000000000000 : ℝ)) (n := 14)
    (by rw [ha2]; norm_num) (by norm_num) (by rw [ha2]; norm_num [Finset.sum_range_succ, Nat.factorial])
    (by rw [ha2]; norm_num [Finset.sum_range_succ, Nat.factorial])
  have hT := meanpow_encl (B := exp (193627 / 200000)) (Xlo := (15064099827 / 10000000000 : ℝ)) (Xhi := (150640998271 / 100000000000 : ℝ))
    (Tlo := (583490807989 / 500000000000 : ℝ)) (Thi := (583490807991 / 500000000000 : ℝ)) (m := 75) (n := 199)
    (by norm_num) (by norm_num) hE2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [← hcosh] at hT
  simp only [Nat.cast_ofNat] at hF hT
  -- the third term e(t₂) = √3 cos(3t₂/4)
  have hc2 := cos_taylor_encl (a := 537 / 400) (lo := (226318384121 / 1000000000000 : ℝ)) (hi := (226318384143 / 1000000000000 : ℝ))
    (by rw [ha4]; norm_num) (by rw [ha4]; norm_num) (by rw [ha4]; norm_num)
  have h3l : (108253175473 / 62500000000 : ℝ) ≤ √3 := calc (108253175473 / 62500000000 : ℝ) = √((108253175473 / 62500000000 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ √3 := Real.sqrt_le_sqrt (by norm_num)
  have h3u : √3 ≤ (1732050807569 / 1000000000000 : ℝ) := calc √3 ≤ √((1732050807569 / 1000000000000 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
    _ = (1732050807569 / 1000000000000 : ℝ) := Real.sqrt_sq (by norm_num)
  have hR1 : (108253175473 / 62500000000 : ℝ) * (226318384121 / 1000000000000 : ℝ) ≤ √3 * cos (537 / 400) := mul_le_mul h3l hc2.1 (by norm_num) (Real.sqrt_nonneg 3)
  have hR2 : √3 * cos (537 / 400) ≤ (1732050807569 / 1000000000000 : ℝ) * (226318384143 / 1000000000000 : ℝ) :=
    mul_le_mul h3u hc2.2 (le_trans (by norm_num) hc2.1) (by norm_num)
  rw [explicit_arc_closed_form]
  exact abs_sub_le_of_encl (lo := (389551916629 / 250000000000 : ℝ) - (583490807991 / 500000000000 : ℝ) - (1732050807569 / 1000000000000 : ℝ) * (226318384143 / 1000000000000 : ℝ))
    (hi := (389551917317 / 250000000000 : ℝ) - (583490807989 / 500000000000 : ℝ) - (108253175473 / 62500000000 : ℝ) * (226318384121 / 1000000000000 : ℝ))
    ⟨by linarith [hF.1, hT.2, hR2], by linarith [hF.2, hT.1, hR1]⟩ (by norm_num) (by norm_num)

/-- C13k, l.459, l.504-505: `Γ(0, -2π/3) = 0` and `Γ(y₂,t₂) - e(t₂) = -7.7·10⁻⁴` (within `5·10⁻⁶`) at `(3/2, 3.98)`. -/
theorem explicit_arc_values :
    Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 ∧
      |Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS - (-77 / 10 ^ 5)| ≤ 5 / 10 ^ 6 :=
  ⟨explicit_arc_contact, explicit_arc_value⟩

end P18
