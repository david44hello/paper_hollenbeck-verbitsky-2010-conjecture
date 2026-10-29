/-
  HVFalse/Proofs/R2Mine.lean - sentences of Sec. 2 and of the proof of Prop. 5 of the paper
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Sec. 2 (l.199-204): "always s₀(p) ≤ sec²ϑ. Indeed, e(π/p) = tanϑ cos(π/2) = 0, cos(π/p) = cos 2ϑ and
  1 + cos 2ϑ = 2/sec²ϑ, so for every 1 < p < 2 and s > 0, Γ(y,π/p) - e(π/p) = (1 + (sec²ϑ/2)(cosh y - 1))^q
  - cosh(sy/2)^{p/s} = (p/8)(sec²ϑ - s)y² + O(y⁴), which is negative for small y ≠ 0 when s > sec²ϑ."
  (the y² expansion is NewRows12.gam_expansion_pi_p). Here s₀ ≤ sec²ϑ is proved from the expansion alone, with no
  cited result. Prop. 5 proof (l.374-375): u'(p) = -(π/p²)√u (1+u) for u = tan²(π/2p).
-/
import HVFalse.Proofs.NewRows12
import HVFalse.Proofs.Small
import HVFalse.Proofs.Coercive

open Real

namespace P18.R2Mine

/-- Sec. 2: the closed form of `Γ(y,π/p) - e(π/p)`, for every `s`. -/
theorem gam_closed_pi_p {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (y : ℝ) :
    Gam p s y (π / p) - ee p (π / p) =
      (1 + Ssec p / 2 * (cosh y - 1)) ^ (p / 2) - cosh (s * y / 2) ^ (p / s) := by
  have hp0 : 0 < p := by linarith
  have hc := P18.cos_half_pos hp1 hp2
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hcp : cos (π / p) = 2 * cos (π / (2 * p)) ^ 2 - 1 := by rw [← h2, cos_two_mul]
  have hpos : 0 < 1 + cos (π / p) := by rw [hcp]; nlinarith
  have hnum : 0 ≤ cosh y + cos (π / p) := by linarith [one_le_cosh y, neg_one_le_cos (π / p)]
  have key : (cosh y + cos (π / p)) / (1 + cos (π / p)) = 1 + Ssec p / 2 * (cosh y - 1) := by
    rw [hcp, Ssec]
    field_simp
    ring
  unfold Gam
  rw [(P18.ee_contact_zero hp0).1, h2, ← div_rpow hnum hpos.le, key, sub_zero]

/-- Sec. 2: `Γ(y,π/p) - e(π/p) < 0` for small `y ≠ 0` when `s > sec²ϑ`. -/
theorem gam_neg_pi_p {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : Ssec p < s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ 0 → |y| < δ → Gam p s y (π / p) < ee p (π / p) := by
  have hS := P18.Ssec_pos hp1
  obtain ⟨C, δ, hδ, hb⟩ := P18.NewRows12.gam_expansion_pi_p hp1 hp2 (hS.trans hs)
  have ha : 0 < p / 8 * (s - Ssec p) := by
    have : 0 < p := by linarith
    have : 0 < s - Ssec p := by linarith
    positivity
  set a := p / 8 * (s - Ssec p) with ha_def
  have hC1 : 0 < |C| + 1 := by positivity
  refine ⟨min δ (min 1 (a / (|C| + 1))), by positivity, ?_⟩
  intro y hy0 hy
  have hy1 : |y| < δ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy2 : |y| < 1 := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_left _ _))
  have hy3 : |y| < a / (|C| + 1) := lt_of_lt_of_le hy ((min_le_right _ _).trans (min_le_right _ _))
  have hyy : 0 < y ^ 2 := by positivity
  have hyle : y ^ 2 ≤ |y| := by rw [← sq_abs]; nlinarith [abs_nonneg y]
  have hCy : |C| * y ^ 2 < a := by
    have h1 : |C| * y ^ 2 ≤ |C| * (a / (|C| + 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg C)
    have h2 : |C| * (a / (|C| + 1)) < a := by
      rw [mul_div_assoc', div_lt_iff₀ hC1]; nlinarith [abs_nonneg C]
    linarith
  have h4 : C * y ^ 4 ≤ |C| * y ^ 2 * y ^ 2 := by
    have := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity : (0 : ℝ) ≤ y ^ 4)
    nlinarith
  have h5 : |C| * y ^ 2 * y ^ 2 < a * y ^ 2 := mul_lt_mul_of_pos_right hCy hyy
  have hb' := (abs_le.mp (hb y hy1)).2
  have : p / 8 * (Ssec p - s) * y ^ 2 = -(a * y ^ 2) := by rw [ha_def]; ring
  linarith

/-- Sec. 2: "always `s₀(p) ≤ sec²ϑ`", for every `1 < p < 2`, from the expansion alone (no cited result). -/
theorem s0_le_sec {p s0 : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 ≤ Ssec p := by
  by_contra hn
  have h := not_le.mp hn
  have hS := P18.Ssec_pos hp1
  have htwo : TwoVar p s0 := (hs0 s0 (hS.trans h)).2 le_rfl
  obtain ⟨δ, hδ, hneg⟩ := gam_neg_pi_p hp1 hp2 h
  have hp0 : 0 < p := by linarith
  have hmem : π / p ∈ Set.Icc (-π) π := by
    constructor
    · have : 0 < π / p := by positivity
      linarith [pi_pos]
    · rw [div_le_iff₀ hp0]; nlinarith [pi_pos]
  have hge := htwo (δ / 2) (π / p) hmem
  have hlt := hneg (δ / 2) (by positivity) (by rw [abs_of_pos (by positivity)]; linarith)
  linarith

/-- Prop. 5 proof: `u'(p) = -(π/p²) √u (1 + u)` for `u(p) = tan²(π/2p)`, `1 < p < 2`. -/
theorem uu_hasDerivAt {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt uu (-(π / p ^ 2) * √(uu p) * (1 + uu p)) p := by
  have hp0 : p ≠ 0 := by linarith
  have hc := P18.cos_half_pos hp1 hp2
  have hin : HasDerivAt (fun x : ℝ => π / (2 * x)) ((0 * (2 * p) - π * (2 * 1)) / (2 * p) ^ 2) p :=
    (hasDerivAt_const p π).div ((hasDerivAt_id p).const_mul 2) (by simpa using hp0)
  have htan := ((Real.hasDerivAt_tan hc.ne').comp p hin).pow 2
  have hpos : 0 < tan (π / (2 * p)) := by
    rw [tan_eq_sin_div_cos]
    apply div_pos _ hc
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hsq : √(uu p) = tan (π / (2 * p)) := by rw [uu, sqrt_sq hpos.le]
  have hone : 1 + uu p = 1 / cos (π / (2 * p)) ^ 2 := by
    rw [uu, ← inv_one_add_tan_sq hc.ne', one_div, inv_inv]
  convert htan using 1
  · funext x
    simp only [uu, Pi.pow_apply, Function.comp]
  · rw [hsq, hone]
    simp only [Function.comp, Nat.cast_ofNat]
    field_simp
    ring

/-- Prop. 5 proof: `u''(p) = (2π/p³) √u (1+u) + (π²/(2p⁴)) (1+u)(1+3u)`, i.e. the derivative at `p` of the function
`x ↦ -(π/x²) √u(x) (1 + u(x))` of `uu_hasDerivAt`, `1 < p < 2`. -/
theorem uu_hasDerivAt2 {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (fun x => -(π / x ^ 2) * √(uu x) * (1 + uu x))
      (2 * π / p ^ 3 * √(uu p) * (1 + uu p) + π ^ 2 / (2 * p ^ 4) * (1 + uu p) * (1 + 3 * uu p)) p := by
  have hp0 : p ≠ 0 := by linarith
  have hc := P18.cos_half_pos hp1 hp2
  have hin : HasDerivAt (fun x : ℝ => π / (2 * x)) ((0 * (2 * p) - π * (2 * 1)) / (2 * p) ^ 2) p :=
    (hasDerivAt_const p π).div ((hasDerivAt_id p).const_mul 2) (by simpa using hp0)
  have hT := (Real.hasDerivAt_tan hc.ne').comp p hin
  have hA := ((hasDerivAt_const p π).div ((hasDerivAt_id p).pow 2) (by simpa using pow_ne_zero 2 hp0)).neg
  have hG := (hA.mul hT).mul ((hasDerivAt_const p (1 : ℝ)).add (hT.pow 2))
  have tan_pos : ∀ x : ℝ, 1 < x → x < 2 → 0 < tan (π / (2 * x)) := by
    intro x hx1 hx2
    rw [tan_eq_sin_div_cos]
    apply div_pos _ (P18.cos_half_pos hx1 hx2)
    apply sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  refine (hG.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hp1 hp2] with x hx
    simp only [uu, sqrt_sq (tan_pos x hx.1 hx.2).le, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq]
  · have hsec : 1 / cos (π / (2 * p)) ^ 2 = 1 + tan (π / (2 * p)) ^ 2 := by
      rw [← inv_one_add_tan_sq hc.ne', one_div, inv_inv]
    simp only [uu, sqrt_sq (tan_pos p hp1 hp2).le, Pi.div_apply, Pi.pow_apply, Pi.neg_apply, Pi.mul_apply, Pi.add_apply, Function.comp_apply, id_eq, Nat.cast_ofNat, hsec]
    field_simp
    ring

end P18.R2Mine
