/-
  HVFalse/Proofs/SaddleTaylor.lean - Prop. 5 eq:taylor at s = S: the two-variable Taylor expansion of Γ - e at (0, π/p)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Method. All remainders are `=O[𝓝 0]` on `ℝ × ℝ` (`z = (y, τ)`) against the paper's weight
  `N = |τ|³ + y²τ² + y⁴|τ| + |y|⁶`, and the auxiliary gauge `g = y² + |τ|` (`g³ = O(N)`, `N = O(g²)`).
  With `ξ = (cosh y + cos(π/p+τ))/D - 1`, `D = 1 + cos 2ϑ`:
    ξ = P₂ + P₄ + O(N),  P₂ = (y²/2 - sin(π/p) τ)/D,  P₄ = (y⁴/24 - cos(π/p) τ²/2)/D;
    (1+ξ)^q = 1 + qξ + q(q-1)/2 ξ² + O(ξ³),  ξ² = P₂² + O(g³),  ξ³ = O(g³);
    cosh(Sy/2)^(p/S) and e(π/p+τ) = -tanϑ sin(qτ) are one-variable (reused from SaddleValley).
  The polynomial parts cancel to `a₀₂τ² + a₂₁y²τ + a₄₀y⁴` (an identity in `T = tan ϑ`).
-/
import HVFalse.Proofs.SaddleValley

open Real Asymptotics Filter Topology

namespace P18

namespace SaddleTaylor

/-- The paper's remainder weight (eq:taylor): `N(y,τ) = |τ|³ + y²τ² + y⁴|τ| + |y|⁶`. -/
noncomputable def nn (z : ℝ × ℝ) : ℝ := |z.2| ^ 3 + z.1 ^ 2 * z.2 ^ 2 + z.1 ^ 4 * |z.2| + |z.1| ^ 6

/-- The auxiliary gauge `g(y,τ) = y² + |τ|`. -/
noncomputable def gg (z : ℝ × ℝ) : ℝ := z.1 ^ 2 + |z.2|

theorem nn_nonneg (z : ℝ × ℝ) : 0 ≤ nn z := by unfold nn; positivity

theorem gg_nonneg (z : ℝ × ℝ) : 0 ≤ gg z := by unfold gg; positivity

/-- `N` and `g` in terms of `Y = |y|`, `T = |τ|`. -/
theorem nn_abs (z : ℝ × ℝ) :
    nn z = |z.2| ^ 3 + |z.1| ^ 2 * |z.2| ^ 2 + |z.1| ^ 4 * |z.2| + |z.1| ^ 6 := by
  simp only [nn, Even.pow_abs (by decide : Even 2), Even.pow_abs (by decide : Even 4)]

theorem gg_abs (z : ℝ × ℝ) : gg z = |z.1| ^ 2 + |z.2| := by
  simp only [gg, Even.pow_abs (by decide : Even 2)]

theorem small_eventually : ∀ᶠ z : ℝ × ℝ in 𝓝 0, |z.1| ≤ 1 ∧ |z.2| ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) one_pos] with z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  have h1 := norm_fst_le z
  have h2 := norm_snd_le z
  rw [Real.norm_eq_abs] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem tendsto_fst0 : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_fst (X := ℝ) (Y := ℝ)).tendsto 0

theorem tendsto_snd0 : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (𝓝 0) (𝓝 0) := by
  simpa using (continuous_snd (X := ℝ) (Y := ℝ)).tendsto 0

/-! ### Comparisons between the gauges -/

theorem fst6_nn : (fun z : ℝ × ℝ => z.1 ^ 6) =O[𝓝 0] nn := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg z), one_mul, abs_pow, nn_abs]
  have := abs_nonneg z.1; have := abs_nonneg z.2
  have : 0 ≤ |z.2| ^ 3 + |z.1| ^ 2 * |z.2| ^ 2 + |z.1| ^ 4 * |z.2| := by positivity
  linarith

theorem snd3_nn : (fun z : ℝ × ℝ => z.2 ^ 3) =O[𝓝 0] nn := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg z), one_mul, abs_pow, nn_abs]
  have : 0 ≤ |z.1| ^ 2 * |z.2| ^ 2 + |z.1| ^ 4 * |z.2| + |z.1| ^ 6 := by positivity
  linarith

theorem snd4_nn : (fun z : ℝ × ℝ => z.2 ^ 4) =O[𝓝 0] nn := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [small_eventually] with z ⟨_, ht⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg z), one_mul, abs_pow, nn_abs]
  have h43 : |z.2| ^ 4 ≤ |z.2| ^ 3 := pow_le_pow_of_le_one (abs_nonneg _) ht (by norm_num)
  have : 0 ≤ |z.1| ^ 2 * |z.2| ^ 2 + |z.1| ^ 4 * |z.2| + |z.1| ^ 6 := by positivity
  linarith

theorem gg3_nn : (fun z : ℝ × ℝ => gg z ^ 3) =O[𝓝 0] nn := by
  refine IsBigO.of_bound 3 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg z), abs_of_nonneg (pow_nonneg (gg_nonneg z) 3),
    nn_abs, gg_abs]
  have hY := abs_nonneg z.1; have hT := abs_nonneg z.2
  nlinarith [pow_nonneg hT 3, pow_nonneg hY 6]

theorem nn_gg2 : nn =O[𝓝 0] (fun z : ℝ × ℝ => gg z ^ 2) := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [small_eventually] with z ⟨hy, ht⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg z), abs_of_nonneg (pow_nonneg (gg_nonneg z) 2),
    nn_abs, gg_abs]
  set Y := |z.1|
  set T := |z.2|
  have hY : 0 ≤ Y := abs_nonneg _
  have hT : 0 ≤ T := abs_nonneg _
  have h1 : T ^ 3 ≤ T ^ 2 := pow_le_pow_of_le_one hT ht (by norm_num)
  have h2 : Y ^ 2 * T ^ 2 ≤ T ^ 2 := by
    have : Y ^ 2 ≤ 1 := pow_le_one₀ hY hy
    nlinarith [sq_nonneg T]
  have h3 : Y ^ 4 * T ≤ Y ^ 4 := by nlinarith [pow_nonneg hY 4]
  have h4 : Y ^ 6 ≤ Y ^ 4 := pow_le_pow_of_le_one hY hy (by norm_num)
  nlinarith [mul_nonneg (pow_nonneg hY 2) hT]

theorem gg2_gg : (fun z : ℝ × ℝ => gg z ^ 2) =O[𝓝 0] gg := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [small_eventually] with z ⟨hy, ht⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gg_nonneg z), abs_of_nonneg (pow_nonneg (gg_nonneg z) 2)]
  have hg : gg z ≤ 2 := by
    rw [gg_abs]; have : |z.1| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hy; linarith
  nlinarith [gg_nonneg z]

theorem fst2_gg : (fun z : ℝ × ℝ => z.1 ^ 2) =O[𝓝 0] gg := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gg_nonneg z), one_mul, abs_pow, gg_abs]
  linarith [abs_nonneg z.2]

theorem snd_gg : (fun z : ℝ × ℝ => z.2) =O[𝓝 0] gg := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gg_nonneg z), one_mul, gg_abs]
  linarith [pow_nonneg (abs_nonneg z.1) 2]

theorem fst4_gg2 : (fun z : ℝ × ℝ => z.1 ^ 4) =O[𝓝 0] (fun z => gg z ^ 2) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (gg_nonneg z) 2), one_mul, abs_pow, gg_abs]
  have := abs_nonneg z.1; have := abs_nonneg z.2
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg z.1) 2) (abs_nonneg z.2)]

theorem snd2_gg2 : (fun z : ℝ × ℝ => z.2 ^ 2) =O[𝓝 0] (fun z => gg z ^ 2) := by
  refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (gg_nonneg z) 2), one_mul, abs_pow, gg_abs]
  have := abs_nonneg z.1; have := abs_nonneg z.2
  nlinarith [mul_nonneg (pow_nonneg (abs_nonneg z.1) 2) (abs_nonneg z.2)]

/-! ### The expansion -/

section Specific

variable {p : ℝ}

/-- `ξ = (cosh y + cos(π/p + τ))/D - 1`, `D = 1 + cos 2ϑ`. -/
noncomputable def xi (p : ℝ) (z : ℝ × ℝ) : ℝ :=
  (cosh z.1 + cos (π / p + z.2)) / (1 + cos (2 * (π / (2 * p)))) - 1

/-- `P₂ = (y²/2 - sin(π/p) τ)/D` (weight 2). -/
noncomputable def P2 (p : ℝ) (z : ℝ × ℝ) : ℝ := (z.1 ^ 2 / 2 - sin (π / p) * z.2) / (1 + cos (2 * (π / (2 * p))))

/-- `P₄ = (y⁴/24 - cos(π/p) τ²/2)/D` (weight 4). -/
noncomputable def P4 (p : ℝ) (z : ℝ × ℝ) : ℝ := (z.1 ^ 4 / 24 - cos (π / p) * z.2 ^ 2 / 2) / (1 + cos (2 * (π / (2 * p))))

/-- `ξ = P₂ + P₄ + O(N)`. -/
theorem xi_expand (hp1 : 1 < p) (hp2 : p < 2) :
    (fun z => xi p z - (P2 p z + P4 p z)) =O[𝓝 0] nn := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD : 0 < 1 + cos (π / p) := denom_pos p hp1 hp2
  have hc6 : (fun y : ℝ => (cosh y - 1) - (1 / 2 * y ^ 2 + 1 / 24 * y ^ 4)) =O[𝓝 0] (fun y => y ^ 6) := by
    simpa using SaddleValley.cosh6 1
  have hA := (hc6.comp_tendsto tendsto_fst0).trans fst6_nn
  have hB := (SaddleValley.cos4.comp_tendsto tendsto_snd0).trans snd4_nn
  have hC := (SaddleValley.sin3.comp_tendsto tendsto_snd0).trans snd3_nn
  have hsum := ((hA.add (hB.const_mul_left (cos (π / p)))).sub (hC.const_mul_left (sin (π / p)))).const_mul_left
    (1 / (1 + cos (π / p)))
  refine hsum.congr_left (fun z => ?_)
  simp only [Function.comp, xi, P2, P4, h2]
  rw [cos_add]
  field_simp
  ring

theorem P2_gg : P2 p =O[𝓝 0] gg := by
  have h := (fst2_gg.const_mul_left (1 / 2 / (1 + cos (2 * (π / (2 * p)))))).add
    (snd_gg.const_mul_left (-sin (π / p) / (1 + cos (2 * (π / (2 * p))))))
  refine h.congr_left (fun z => ?_)
  simp only [P2]; ring

theorem P4_gg2 : P4 p =O[𝓝 0] (fun z => gg z ^ 2) := by
  have h := (fst4_gg2.const_mul_left (1 / 24 / (1 + cos (2 * (π / (2 * p)))))).add
    (snd2_gg2.const_mul_left (-cos (π / p) / 2 / (1 + cos (2 * (π / (2 * p))))))
  refine h.congr_left (fun z => ?_)
  simp only [P4]; ring

/-- `ξ - P₂ = O(g²)`. -/
theorem xi_sub_P2 (hp1 : 1 < p) (hp2 : p < 2) : (fun z => xi p z - P2 p z) =O[𝓝 0] (fun z => gg z ^ 2) :=
  (((xi_expand hp1 hp2).trans nn_gg2).add P4_gg2).congr_left (fun z => by ring)

theorem xi_gg (hp1 : 1 < p) (hp2 : p < 2) : xi p =O[𝓝 0] gg :=
  (((xi_sub_P2 hp1 hp2).trans gg2_gg).add P2_gg).congr_left (fun z => by ring)

/-- `ξ² - P₂² = O(N)`. -/
theorem xi_sq (hp1 : 1 < p) (hp2 : p < 2) : (fun z => xi p z ^ 2 - P2 p z ^ 2) =O[𝓝 0] nn := by
  have hplus : (fun z => xi p z + P2 p z) =O[𝓝 0] gg :=
    (((xi_sub_P2 hp1 hp2).trans gg2_gg).add (P2_gg.const_mul_left 2)).congr_left (fun z => by ring)
  have h := (xi_sub_P2 hp1 hp2).mul hplus
  exact ((h.congr_right (fun z => by ring)).trans gg3_nn).congr_left (fun z => by ring)

theorem xi_tendsto (hp1 : 1 < p) (hp2 : p < 2) : Tendsto (xi p) (𝓝 0) (𝓝 0) := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD : 0 < 1 + cos (π / p) := denom_pos p hp1 hp2
  have hc : Continuous (xi p) := by unfold xi; fun_prop
  have h0 : xi p 0 = 0 := by
    simp only [xi, Prod.fst_zero, Prod.snd_zero, cosh_zero, add_zero, h2]
    rw [div_self hD.ne']; ring
  simpa [h0] using hc.tendsto 0

/-- Term 1: `(1+ξ)^q = 1 + qξ + q(q-1)/2 ξ² + O(N)`. -/
theorem term1 (hp1 : 1 < p) (hp2 : p < 2) :
    (fun z => (1 + xi p z) ^ (p / 2) - (1 + p / 2 * xi p z + p / 2 * (p / 2 - 1) / 2 * xi p z ^ 2)) =O[𝓝 0] nn :=
  (((SaddleValley.rpow3 (p / 2)).comp_tendsto (xi_tendsto hp1 hp2)).trans ((xi_gg hp1 hp2).pow 3)).trans gg3_nn

/-- `e(π/p + τ) = -tanϑ sin(qτ)` and `sin(qτ) = qτ + O(N)`. -/
theorem sin_term (p : ℝ) :
    (fun z : ℝ × ℝ => sin (p / 2 * z.2) - p / 2 * z.2) =O[𝓝 0] nn := by
  have ht : Tendsto (fun z : ℝ × ℝ => p / 2 * z.2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_snd0.const_mul (p / 2))
  have h := SaddleValley.sin3.comp_tendsto ht
  exact (h.trans ((snd3_nn.const_mul_left ((p / 2) ^ 3)).congr_left (fun z => by simp only [Function.comp]; ring))).congr_left
    (fun z => rfl)

theorem ee_shift (hp0 : p ≠ 0) (τ : ℝ) : ee p (π / p + τ) = -(tan (π / (2 * p)) * sin (p / 2 * τ)) := by
  have harg : p / 2 * (π / p + τ) = p / 2 * τ + π / 2 := by field_simp; ring
  simp only [ee, harg, cos_add_pi_div_two]
  ring

/-- The coefficient identity of eq:taylor. -/
theorem coef_identity (hp1 : 1 < p) (y τ : ℝ) :
    p / 2 * (P2 p (y, τ) + P4 p (y, τ)) + p / 2 * (p / 2 - 1) / 2 * P2 p (y, τ) ^ 2
      - (p / Ssec p * ((Ssec p / 2) ^ 2 / 2) * y ^ 2 + (p / Ssec p * ((Ssec p / 2) ^ 4 / 24)
          + p / Ssec p * (p / Ssec p - 1) / 2 * ((Ssec p / 2) ^ 2 / 2) ^ 2) * y ^ 4)
      + tan (π / (2 * p)) * (p / 2 * τ)
      = a02 p * τ ^ 2 + a21 p * y ^ 2 * τ + p * Ssec p * (Ssec p - 1) * (Ssec p - 2) / 192 * y ^ 4 := by
  obtain ⟨hS, hD, hcP, hsP⟩ := SaddleValley.trig_T hp1
  simp only [P2, P4, a02, a21, uu, K]
  rw [hS, hD, hcP, hsP]
  set T := tan (π / (2 * p))
  have hT1 : 0 < 1 + T ^ 2 := by positivity
  field_simp
  ring

/-- **eq:taylor in O-form.** -/
theorem taylor_isBigO (hp1 : 1 < p) (hp2 : p < 2) :
    (fun z : ℝ × ℝ => Gam p (Ssec p) z.1 (π / p + z.2) - ee p (π / p + z.2)
      - (a02 p * z.2 ^ 2 + a21 p * z.1 ^ 2 * z.2 + p * Ssec p * (Ssec p - 1) * (Ssec p - 2) / 192 * z.1 ^ 4))
      =O[𝓝 0] nn := by
  have hp0 : p ≠ 0 := by linarith
  have h2 : 2 * (π / (2 * p)) = π / p := by field_simp
  have hD : 0 < 1 + cos (2 * (π / (2 * p))) := by rw [h2]; exact denom_pos p hp1 hp2
  have h1 := term1 hp1 hp2
  have hx := (xi_expand hp1 hp2).const_mul_left (p / 2)
  have hsq := (xi_sq hp1 hp2).const_mul_left (p / 2 * (p / 2 - 1) / 2)
  have ht2 := ((SaddleValley.term2_expand (Ssec p) (p / Ssec p)).comp_tendsto tendsto_fst0).trans fst6_nn
  have hs := (sin_term p).const_mul_left (tan (π / (2 * p)))
  refine ((((h1.add hx).add hsq).sub ht2).add hs).congr_left (fun z => ?_)
  obtain ⟨y, τ⟩ := z
  have hu : 0 ≤ cosh y + cos (π / p + τ) := by
    have := one_le_cosh y; have := neg_one_le_cos (π / p + τ); linarith
  have hG : (cosh y + cos (π / p + τ)) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2)
      = (1 + xi p (y, τ)) ^ (p / 2) := by
    simp only [xi]; rw [add_sub_cancel, div_rpow hu hD.le]
  have hc := coef_identity hp1 y τ
  simp only [Function.comp, Gam, ee_shift hp0, hG]
  linear_combination -hc

end Specific

/-- **C10b1, eq:taylor** (tex l.350-352) at `s = S`. -/
theorem taylor_proved {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y τ : ℝ, |y| < δ → |τ| < δ →
      |Gam p (Ssec p) y (π / p + τ) - ee p (π / p + τ)
          - (a02 p * τ ^ 2 + a21 p * y ^ 2 * τ + p * Ssec p * (Ssec p - 1) * (Ssec p - 2) / 192 * y ^ 4)|
        ≤ C * (|τ| ^ 3 + y ^ 2 * τ ^ 2 + y ^ 4 * |τ| + |y| ^ 6) := by
  obtain ⟨C, hC⟩ := (taylor_isBigO (by linarith) hp2).bound
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, δ, hδ, fun y τ hy hτ => ?_⟩
  have hz : dist ((y, τ) : ℝ × ℝ) 0 < δ := by
    rw [Prod.dist_eq]
    simp only [Prod.fst_zero, Prod.snd_zero, Real.dist_eq, sub_zero]
    exact max_lt hy hτ
  have h := hball hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (nn_nonneg _)] at h
  simpa only [nn] using h

end SaddleTaylor

end P18
