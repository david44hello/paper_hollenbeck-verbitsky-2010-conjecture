/-
  HVFalse/Proofs/Forcing.lean - Lemma rigidity (paper l.238-264), from trig convexity alone
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Notation: q = p/2, a = π/p (so q a = π/2), k = tan ϑ, e(t) = k cos(qt). Hypothesis: φ is q-trig-convex (`TrigConvex`)
  and φ ≤ e + C (t ∓ a)^2 for all t (this follows from φ ≤ m ≤ Γ(0,·) and Contact.lean).
  Step 1 (discrete Green formula): three-point inequalities at 0, ±a/2, ±a give φ(a) + φ(-a) ≥ 0.
  Step 2: with φ(±a) ≤ e(±a) = 0, both are 0.
  Step 3: φ ≤ e inside I (points -a < t < a - ε; the quadratic error over sin(qε) → 0).
  Step 4: φ ≥ e inside I (points t < a < a + δ).
  Steps 5-6: φ ≥ e on [a, π] and [-π, -a] (points a/2 < a < t, and t < -a < -a/2).
  The paper's route (measure μ = φ'' + q²φ, Green's formula, one-sided derivatives) is replaced by these steps.
-/
import HVFalse.Proofs.Contact
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Real

namespace P18

/-- If `D sin(qε) ≤ C ε^2` for all small `ε > 0`, then `D ≤ 0` (Jordan: `sin x ≥ 2x/π` on `[0, π/2]`). -/
theorem nonpos_of_sin_le_sq {q D C ε1 : ℝ} (hq : 0 < q) (hε1 : 0 < ε1)
    (h : ∀ ε, 0 < ε → ε < ε1 → D * sin (q * ε) ≤ C * ε ^ 2) : D ≤ 0 := by
  by_contra hD
  push_neg at hD
  have hpi := pi_pos
  have hC1 : 0 < |C| + 1 := by positivity
  set ε := min (min (ε1 / 2) (π / (2 * q))) (D * q / (π * (|C| + 1))) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by linarith) (by positivity)) (by positivity)
  have hεε1 : ε < ε1 := lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (by linarith)
  have hεq : q * ε ≤ π / 2 := by
    calc q * ε ≤ q * (π / (2 * q)) := mul_le_mul_of_nonneg_left
          (le_trans (min_le_left _ _) (min_le_right _ _)) hq.le
      _ = π / 2 := by field_simp
  have hj := mul_le_sin (by positivity : 0 ≤ q * ε) hεq
  have h1 : D * (2 / π * (q * ε)) ≤ C * ε ^ 2 := le_trans (mul_le_mul_of_nonneg_left hj hD.le) (h ε hε hεε1)
  have h2 : C * ε ^ 2 ≤ |C| * ε ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ε)
  have h3 : (|C| + 1) * ε ≤ D * q / π := by
    calc (|C| + 1) * ε ≤ (|C| + 1) * (D * q / (π * (|C| + 1))) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC1.le
      _ = D * q / π := by field_simp
  have h4 := mul_le_mul_of_nonneg_right h3 hε.le
  have h5 : D * (2 / π * (q * ε)) = 2 * (D * q / π * ε) := by ring
  have h6 : 0 < D * q / π * ε := by positivity
  nlinarith [sq_nonneg ε]

/-- Step 1, the discrete Green formula: `φ(a) + φ(-a) ≥ 0` for a q-trig-convex `φ`, when `q a = π/2`. -/
theorem forcing_green {q a : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hqa : q * a = π / 2) (htc : TrigConvex q φ) :
    0 ≤ φ a + φ (-a) := by
  have hpi := pi_pos
  have ha : 0 < a := by by_contra h; push_neg at h; nlinarith
  have e2 : q * (a / 2 - -(a / 2)) = π / 2 := by linear_combination hqa
  have e4 : q * (a / 2 - 0) = π / 4 := by linear_combination hqa / 2
  have e4' : q * (0 - -(a / 2)) = π / 4 := by linear_combination hqa / 2
  have f2 : q * (a - 0) = π / 2 := by linear_combination hqa
  have f4 : q * (a - a / 2) = π / 4 := by linear_combination hqa / 2
  have g2 : q * (0 - -a) = π / 2 := by linear_combination hqa
  have g4 : q * (-(a / 2) - -a) = π / 4 := by linear_combination hqa / 2
  have h1 := htc (-(a / 2)) 0 (a / 2) (by linarith) (by linarith) (by rw [e2]; linarith)
  have h2 := htc 0 (a / 2) a (by linarith) (by linarith) (by rw [f2]; linarith)
  have h3 := htc (-a) (-(a / 2)) 0 (by linarith) (by linarith) (by rw [g2]; linarith)
  rw [e2, e4, e4', sin_pi_div_two, sin_pi_div_four] at h1
  rw [f2, f4, e4, sin_pi_div_two, sin_pi_div_four] at h2
  rw [g2, e4', g4, sin_pi_div_two, sin_pi_div_four] at h3
  have hc : 0 < √2 / 2 := by positivity
  have hcc : √2 / 2 * (√2 / 2) = 1 / 2 := by
    rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have k2 : √2 / 2 * φ (a / 2) ≤ (φ 0 + φ a) / 2 := by
    calc √2 / 2 * φ (a / 2) = √2 / 2 * (φ (a / 2) * 1) := by ring
      _ ≤ √2 / 2 * (φ 0 * (√2 / 2) + φ a * (√2 / 2)) := mul_le_mul_of_nonneg_left h2 hc.le
      _ = (√2 / 2 * (√2 / 2)) * (φ 0 + φ a) := by ring
      _ = (φ 0 + φ a) / 2 := by rw [hcc]; ring
  have k3 : √2 / 2 * φ (-(a / 2)) ≤ (φ (-a) + φ 0) / 2 := by
    calc √2 / 2 * φ (-(a / 2)) = √2 / 2 * (φ (-(a / 2)) * 1) := by ring
      _ ≤ √2 / 2 * (φ (-a) * (√2 / 2) + φ 0 * (√2 / 2)) := mul_le_mul_of_nonneg_left h3 hc.le
      _ = (√2 / 2 * (√2 / 2)) * (φ (-a) + φ 0) := by ring
      _ = (φ (-a) + φ 0) / 2 := by rw [hcc]; ring
  nlinarith

/-- Step 2: `φ(a) = 0` and `φ(-a) = 0`. -/
theorem forcing_ends {q a k C : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hqa : q * a = π / 2) (htc : TrigConvex q φ)
    (hR : ∀ t, φ t ≤ k * cos (q * t) + C * (t - a) ^ 2)
    (hL : ∀ t, φ t ≤ k * cos (q * t) + C * (t + a) ^ 2) : φ a = 0 ∧ φ (-a) = 0 := by
  have hg := forcing_green hq hqa htc
  have h1 := hR a
  have h2 := hL (-a)
  rw [hqa, cos_pi_div_two, sub_self] at h1
  rw [show q * -a = -(π / 2) by linear_combination -hqa, cos_neg, cos_pi_div_two, neg_add_cancel] at h2
  norm_num at h1 h2
  constructor <;> linarith

/-- `cos(qt) > 0` for `-a < t < a`. -/
theorem cos_pos_inside {q a t : ℝ} (hq : 0 < q) (hqa : q * a = π / 2) (ht : -a < t) (ht' : t < a) :
    0 < cos (q * t) := by
  have h1 := mul_lt_mul_of_pos_left ht hq
  have h2 := mul_lt_mul_of_pos_left ht' hq
  apply cos_pos_of_mem_Ioo
  constructor <;> nlinarith

/-- `C ε^2 cos(qt) ≤ |C| ε^2` when `0 ≤ cos(qt)`. -/
theorem sq_err_le {C ε c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : C * ε ^ 2 * c ≤ |C| * ε ^ 2 := by
  have h1 : C * ε ^ 2 * c ≤ |C| * ε ^ 2 * c :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg ε)) hc0
  have h2 : |C| * ε ^ 2 * c ≤ |C| * ε ^ 2 := mul_le_of_le_one_right (by positivity) hc1
  linarith

/-- Step 3: `φ ≤ e` inside `I`. -/
theorem forcing_upper {q a k C : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hqa : q * a = π / 2) (htc : TrigConvex q φ)
    (hR : ∀ t, φ t ≤ k * cos (q * t) + C * (t - a) ^ 2) (hφna : φ (-a) = 0)
    {t : ℝ} (ht : -a < t) (ht' : t < a) : φ t ≤ k * cos (q * t) := by
  have hcos := cos_pos_inside hq hqa ht ht'
  have hD : φ t - k * cos (q * t) ≤ 0 := by
    refine nonpos_of_sin_le_sq (C := |C|) hq (show 0 < a - t by linarith) (fun ε hε hεt => ?_)
    have hx : q * (a - ε - -a) = π - q * ε := by linear_combination 2 * hqa
    have hy : q * (t - -a) = q * t + π / 2 := by linear_combination hqa
    have h := htc (-a) t (a - ε) ht (by linarith) (by rw [hx]; linarith [mul_pos hq hε])
    rw [hx, hy, hφna, sin_pi_sub, sin_add_pi_div_two, zero_mul, zero_add] at h
    have hb := hR (a - ε)
    rw [show q * (a - ε) = π / 2 - q * ε by linear_combination hqa, cos_pi_div_two_sub,
      show a - ε - a = -ε by ring, neg_sq] at hb
    have hbc := mul_le_mul_of_nonneg_right hb hcos.le
    have he := sq_err_le (C := C) (ε := ε) hcos.le (cos_le_one _)
    nlinarith
  linarith

/-- Step 4: `φ ≥ e` inside `I`. -/
theorem forcing_lower {q a k C : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hqa : q * a = π / 2) (htc : TrigConvex q φ)
    (hR : ∀ t, φ t ≤ k * cos (q * t) + C * (t - a) ^ 2) (hφa : φ a = 0)
    {t : ℝ} (ht : -a < t) (ht' : t < a) : k * cos (q * t) ≤ φ t := by
  have hcos := cos_pos_inside hq hqa ht ht'
  have hD : k * cos (q * t) - φ t ≤ 0 := by
    refine nonpos_of_sin_le_sq (C := |C|) hq (show 0 < a + t by linarith) (fun δ hδ hδt => ?_)
    have hm := mul_lt_mul_of_pos_left (show δ - t < a by linarith) hq
    have h := htc t a (a + δ) ht' (by linarith) (by nlinarith)
    rw [hφa, zero_mul, show q * (a + δ - a) = q * δ by ring,
      show q * (a - t) = π / 2 - q * t by linear_combination hqa, sin_pi_div_two_sub] at h
    have hb := hR (a + δ)
    rw [show q * (a + δ) = q * δ + π / 2 by linear_combination hqa, cos_add_pi_div_two,
      show a + δ - a = δ by ring] at hb
    have hbc := mul_le_mul_of_nonneg_right hb hcos.le
    have he := sq_err_le (C := C) (ε := δ) hcos.le (cos_le_one _)
    nlinarith
  linarith

/-- Step 5: `φ ≥ e` on `(a, π]`. -/
theorem forcing_right {q a k : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hq1 : q < 1) (hqa : q * a = π / 2)
    (htc : TrigConvex q φ) (hφa : φ a = 0) (hmid : φ (a / 2) = k * cos (q * (a / 2)))
    {t : ℝ} (ht : a < t) (htπ : t ≤ π) : k * cos (q * t) ≤ φ t := by
  have hpi := pi_pos
  have ha : 0 < a := by by_contra h; push_neg at h; nlinarith
  have hqt := mul_le_mul_of_nonneg_left htπ hq.le
  have h := htc (a / 2) a t (by linarith) ht (by nlinarith)
  rw [hφa, zero_mul, hmid, show q * (a / 2) = π / 4 by linear_combination hqa / 2,
    show q * (a - a / 2) = π / 4 by linear_combination hqa / 2, cos_pi_div_four, sin_pi_div_four] at h
  rw [show q * t = q * (t - a) + π / 2 by linear_combination hqa, cos_add_pi_div_two]
  have hc : 0 < √2 / 2 := by positivity
  have := (mul_nonneg_iff_of_pos_right hc).mp (by linarith : 0 ≤ (φ t - k * -sin (q * (t - a))) * (√2 / 2))
  linarith

/-- Step 6: `φ ≥ e` on `[-π, -a)`. -/
theorem forcing_left {q a k : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hq1 : q < 1) (hqa : q * a = π / 2)
    (htc : TrigConvex q φ) (hφna : φ (-a) = 0) (hmid : φ (-(a / 2)) = k * cos (q * -(a / 2)))
    {t : ℝ} (ht : t < -a) (htπ : -π ≤ t) : k * cos (q * t) ≤ φ t := by
  have hpi := pi_pos
  have ha : 0 < a := by by_contra h; push_neg at h; nlinarith
  have hqt := mul_le_mul_of_nonneg_left htπ hq.le
  have h := htc t (-a) (-(a / 2)) ht (by linarith) (by nlinarith)
  rw [hφna, zero_mul, hmid, show q * -(a / 2) = -(π / 4) by linear_combination -hqa / 2, cos_neg,
    show q * (-(a / 2) - -a) = π / 4 by linear_combination hqa / 2, cos_pi_div_four, sin_pi_div_four] at h
  rw [show q * t = -(q * (-a - t) + π / 2) by linear_combination -hqa, cos_neg, cos_add_pi_div_two]
  have hc : 0 < √2 / 2 := by positivity
  have := (mul_nonneg_iff_of_pos_right hc).mp (by linarith : 0 ≤ (φ t - k * -sin (q * (-a - t))) * (√2 / 2))
  linarith

/-- The forcing lemma, general form: `q`-trig-convex `φ` with quadratic upper contact at `±a` (`q a = π/2`) equals
`k cos(q·)` on `[-a, a]` and lies above it on `[-π, π]`. -/
theorem forcing_core {q a k C : ℝ} {φ : ℝ → ℝ} (hq : 0 < q) (hq1 : q < 1) (hqa : q * a = π / 2)
    (htc : TrigConvex q φ)
    (hR : ∀ t, φ t ≤ k * cos (q * t) + C * (t - a) ^ 2)
    (hL : ∀ t, φ t ≤ k * cos (q * t) + C * (t + a) ^ 2) :
    (∀ t ∈ Set.Icc (-a) a, φ t = k * cos (q * t)) ∧ (∀ t ∈ Set.Icc (-π) π, k * cos (q * t) ≤ φ t) := by
  have hpi := pi_pos
  have ha : 0 < a := by by_contra h; push_neg at h; nlinarith
  obtain ⟨hφa, hφna⟩ := forcing_ends hq hqa htc hR hL
  have hin : ∀ t, -a < t → t < a → φ t = k * cos (q * t) := fun t h1 h2 =>
    le_antisymm (forcing_upper hq hqa htc hR hφna h1 h2) (forcing_lower hq hqa htc hR hφa h1 h2)
  have hcl : ∀ t ∈ Set.Icc (-a) a, φ t = k * cos (q * t) := by
    intro t ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with h | h
    · rw [← h, hφna, show q * -a = -(π / 2) by linear_combination -hqa, cos_neg, cos_pi_div_two, mul_zero]
    rcases eq_or_lt_of_le h2 with h' | h'
    · rw [h', hφa, hqa, cos_pi_div_two, mul_zero]
    exact hin t h h'
  refine ⟨hcl, fun t ⟨h1, h2⟩ => ?_⟩
  rcases lt_or_ge t (-a) with h | h
  · exact forcing_left hq hq1 hqa htc hφna (hin _ (by linarith) (by linarith)) h h1
  rcases le_or_gt t a with h' | h'
  · exact (hcl t ⟨h, h'⟩).symm.le
  · exact forcing_right hq hq1 hqa htc hφa (hin _ (by linarith) (by linarith)) h' h2

/-- C07, Lemma rigidity (paper l.238-264) with trig convexity in place of "q-subtrigonometric" (the bridge is HKV2003
Prop. 3.3, cited elsewhere). `hs` and `hper` are not needed by the proof. -/
theorem forcing_of_trigConvex {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    {φ : ℝ → ℝ} (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex (p / 2) φ)
    (hle : ∀ y t : ℝ, φ t ≤ Gam p s y t) :
    (∀ t ∈ Set.Icc (-(π / p)) (π / p), φ t = ee p t) ∧ (∀ t ∈ Set.Icc (-π) π, ee p t ≤ φ t) := by
  obtain ⟨C, hC⟩ := contact_quadratic_global p s hp1 hp2
  have hqa : p / 2 * (π / p) = π / 2 := by field_simp
  exact forcing_core (k := tan (π / (2 * p))) (by linarith) (by linarith) hqa htc
    (fun t => le_trans (hle 0 t) (hC t).1) (fun t => le_trans (hle 0 t) (hC t).2)

/-- Paper: "In particular e ≤ m on I" (with `m(t) ≤ Γ(y,t)` for every `y`). -/
theorem ee_le_gam_of_forcing {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    {φ : ℝ → ℝ} (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex (p / 2) φ)
    (hle : ∀ y t : ℝ, φ t ≤ Gam p s y t) :
    ∀ t ∈ Set.Icc (-(π / p)) (π / p), ∀ y : ℝ, ee p t ≤ Gam p s y t := fun t ht y =>
  ((forcing_of_trigConvex hp1 hp2 hs hper htc hle).1 t ht).symm.le.trans (hle y t)

end P18
