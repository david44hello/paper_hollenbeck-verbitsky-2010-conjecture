/-
  HVFalse/Proofs/Threshold.lean - the threshold s₀(p) of (eq:two) (the paper): C04b
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route. (A) Γ decreases in s, so (eq:two) at s gives it at every smaller s. (B) Γ is continuous in s > 0, so the set where
  (eq:two) holds is closed. (C) (eq:two) fails for every s > sec²ϑ: at t = π/p, e = 0 and, for small y > 0,
  Γ(y, π/p) ≤ (p/8)(sec²ϑ - s) y² + (p sec²ϑ/18) y³ + (p s³/32) y⁴ < 0 (Bernoulli; cosh y - 1 ≤ y²/2 + (2/9)|y|³ from
  Real.exp_bound; cosh^{p/s} ≥ 1 + (p/s) log cosh ≥ 1 + (p/s)(u²/2 - u⁴/2)). This is the paper's a₂₀ = (p/8)(S - s).
  (D) (eq:two) holds at some s > 0: for p ≤ 4/3 at s = sec²ϑ by [Mel2023, (37)] (+ evenness); for p > 4/3 at s = p/(p-1)
  by [Jag2026, (2)] with r = e^{-|y|}, using r^q (Γ - e) = Jaguzović's Φ(r,t). (E) s₀ = sup of that set.
  CITED (axioms, HVFalse/Cited/MelJag.lean): P18.Cited.mel_eq37, P18.Cited.jag_eq2.
-/
import HVFalse.Proofs.Coercive
import HVFalse.Proofs.Small
import HVFalse.Cited.MelJag

open Real Filter Topology Set

namespace P18

/-! ### (A), (B): monotone and closed in s -/

theorem twoVar_mono {p s s' : ℝ} (hp : 0 < p) (h : TwoVar p s) (hs' : 0 < s') (hle : s' ≤ s) : TwoVar p s' :=
  fun y t ht => (h y t ht).trans (gam_antitone_s p s' s y t hp hs' hle)

theorem gam_continuousAt_s (p y t : ℝ) {s0 : ℝ} (hs0 : 0 < s0) : ContinuousAt (fun s => Gam p s y t) s0 := by
  unfold Gam
  apply continuousAt_const.sub
  exact ((continuous_cosh.comp ((continuous_id.mul continuous_const).div_const 2)).continuousAt).rpow
    (continuousAt_const.div continuousAt_id hs0.ne') (Or.inl (cosh_pos _).ne')

theorem twoVar_of_forall_lt {p s0 : ℝ} (hs0 : 0 < s0) (h : ∀ s, 0 < s → s < s0 → TwoVar p s) : TwoVar p s0 := by
  intro y t ht
  have hT := (gam_continuousAt_s p y t hs0).tendsto.mono_left (nhdsWithin_le_nhds (s := Iio s0))
  refine ge_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsLT (half_lt_self hs0)] with s hs
  exact h s (lt_trans (half_pos hs0) hs.1) hs.2 y t ht

/-! ### (C): failure above sec²ϑ -/

theorem cosh_sub_one_le {y : ℝ} (hy : |y| ≤ 1) : cosh y - 1 ≤ y ^ 2 / 2 + 2 / 9 * |y| ^ 3 := by
  have h1 := Real.exp_bound hy (n := 3) (by norm_num)
  have h2 := Real.exp_bound (x := -y) (by rwa [abs_neg]) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h1 h2
  have e1 := (abs_le.mp h1).2
  have e2 := (abs_le.mp h2).2
  rw [cosh_eq]
  nlinarith [e1, e2]

theorem one_add_sq_half_le_cosh (u : ℝ) : 1 + u ^ 2 / 2 ≤ cosh u := by
  have h := cosh_two_mul (u / 2)
  rw [show 2 * (u / 2) = u by ring, cosh_sq] at h
  have hs : (u / 2) ^ 2 ≤ sinh (u / 2) ^ 2 := by
    rcases le_total 0 (u / 2) with hu | hu
    · have := self_le_sinh_iff.mpr hu; nlinarith
    · have := sinh_le_self_iff.mpr hu; nlinarith
  nlinarith

/-- `cosh(u)^r ≥ 1 + r (u²/2 - u⁴/2)` for `|u| ≤ 1`, `r > 0`. -/
theorem cosh_rpow_ge {r u : ℝ} (hr : 0 < r) (hu : |u| ≤ 1) : 1 + r * (u ^ 2 / 2 - u ^ 4 / 2) ≤ cosh u ^ r := by
  have hc := cosh_pos u
  have hup := cosh_sub_one_le hu
  have hlow := one_add_sq_half_le_cosh u
  have hu3 : |u| ^ 3 ≤ u ^ 2 := by
    rw [show u ^ 2 = |u| ^ 2 by rw [sq_abs]]; nlinarith [abs_nonneg u, pow_le_one₀ (abs_nonneg u) hu (n := 1)]
  have hcu : cosh u ≤ 1 + u ^ 2 := by nlinarith
  have hlog := one_sub_inv_le_log_of_pos hc
  have hfac : 0 ≤ 1 - (u ^ 2 / 2 - u ^ 4 / 2) := by nlinarith [sq_nonneg (u ^ 2 - 1 / 2)]
  have hinv : (cosh u)⁻¹ ≤ 1 - (u ^ 2 / 2 - u ^ 4 / 2) := by
    rw [inv_eq_one_div, div_le_iff₀ hc]
    nlinarith [mul_le_mul_of_nonneg_left hlow hfac, pow_nonneg (sq_nonneg u) 2, pow_nonneg (sq_nonneg u) 3]
  have hfrac : u ^ 2 / 2 - u ^ 4 / 2 ≤ 1 - (cosh u)⁻¹ := by linarith
  rw [rpow_def_of_pos hc]
  nlinarith [add_one_le_exp (log (cosh u) * r), mul_le_mul_of_nonneg_left (hfrac.trans hlog) hr.le]

/-- C04b part (C): (eq:two) fails for every `s > sec²ϑ` (at `t = π/p`, small `y > 0`). -/
theorem twoVar_fails_above {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hsS : Ssec p < s) : ¬ TwoVar p s := by
  intro h2
  have hp : 0 < p := by linarith
  have hS := Ssec_pos hp1
  have hs : 0 < s := hS.trans hsS
  have hc := cos_half_pos hp1 hp2
  set δ := s - Ssec p with hδ
  set K := p * Ssec p / 18 + p * s ^ 3 / 32 with hK
  have hδ0 : 0 < δ := by linarith
  have hK0 : 0 < K := by positivity
  set y := min (min 1 (1 / s)) (p * δ / (16 * K)) with hy
  have hy0 : 0 < y := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hy1 : y ≤ 1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hys : s * y ≤ 1 := by
    have : y ≤ 1 / s := le_trans (min_le_left _ _) (min_le_right _ _)
    calc s * y ≤ s * (1 / s) := mul_le_mul_of_nonneg_left this hs.le
      _ = 1 := by field_simp
  have hyK : K * y ≤ p * δ / 16 := by
    have : y ≤ p * δ / (16 * K) := min_le_right _ _
    calc K * y ≤ K * (p * δ / (16 * K)) := mul_le_mul_of_nonneg_left this hK0.le
      _ = p * δ / 16 := by field_simp
  -- (eq:two) at (y, π/p), where e = 0
  have hpt := h2 y (π / p) ⟨by linarith [div_pos pi_pos hp, pi_pos], by
    rw [div_le_iff₀ hp]; nlinarith [pi_pos]⟩
  rw [(ee_contact_zero hp).1, gam_eq_div p s y (π / p) hp1 hp2] at hpt
  -- first term: Bernoulli
  have hd := denom_pos p hp1 hp2
  have hDS : p / 2 / (1 + cos (π / p)) = p * Ssec p / 4 := by
    unfold Ssec; rw [denom_eq_two_cos_sq p hp.ne']; field_simp; ring
  have hx : (cosh y + cos (π / p)) / (1 + cos (π / p)) = 1 + (cosh y - 1) / (1 + cos (π / p)) := by
    field_simp; ring
  have hge : -1 ≤ (cosh y - 1) / (1 + cos (π / p)) := by
    have : 0 ≤ (cosh y - 1) / (1 + cos (π / p)) := div_nonneg (by linarith [one_le_cosh y]) hd.le
    linarith
  have hB := rpow_one_add_le_one_add_mul_self hge (p := p / 2) (by linarith) (by linarith)
  rw [← hx] at hB
  have hT1 : p / 2 * ((cosh y - 1) / (1 + cos (π / p))) = p * Ssec p / 4 * (cosh y - 1) := by
    rw [← hDS]; ring
  have hcy := cosh_sub_one_le (y := y) (by rw [abs_of_pos hy0]; exact hy1)
  rw [abs_of_pos hy0] at hcy
  -- second term
  have hu : |s * y / 2| ≤ 1 := by rw [abs_of_pos (by positivity)]; linarith
  have hT2 := cosh_rpow_ge (r := p / s) (by positivity) hu
  have hpS : p * Ssec p / 4 * (cosh y - 1) ≤ p * Ssec p / 4 * (y ^ 2 / 2 + 2 / 9 * y ^ 3) :=
    mul_le_mul_of_nonneg_left hcy (by positivity)
  have hexp : p / s * ((s * y / 2) ^ 2 / 2 - (s * y / 2) ^ 4 / 2) = p * s * y ^ 2 / 8 - p * s ^ 3 * y ^ 4 / 32 := by
    field_simp; ring
  rw [hexp] at hT2
  -- combine: 0 ≤ Γ ≤ -(pδ/8) y² + K y³ (y⁴ ≤ y³) ≤ -(pδ/16) y² < 0
  have hy43 : y ^ 4 ≤ y ^ 3 := pow_le_pow_of_le_one hy0.le hy1 (by norm_num)
  have hKy : K * y ^ 3 ≤ p * δ / 16 * y ^ 2 := by
    have := mul_le_mul_of_nonneg_right hyK (sq_nonneg y)
    nlinarith
  have hfin : 0 < p * δ / 16 * y ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hy43 (show 0 ≤ p * s ^ 3 / 32 by positivity)]

/-! ### (D): (eq:two) holds at some s > 0 (cited) -/

/-- For `p ≤ 4/3`: (eq:two) at `s = sec²ϑ`, from [Mel2023, (37)] and evenness. -/
theorem twoVar_mel {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 4 / 3) : TwoVar p (Ssec p) := by
  intro y t ht
  have hp : 0 < p := by linarith
  have hm := Cited.mel_eq37 p hp1 hp2 |y| |t| (abs_nonneg y) (abs_nonneg t) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩)
  have hpa := psi_abs p (Ssec p) y t
  have e1 : 2 * (π / (2 * p)) = π / p := by field_simp
  unfold Gam ee at hpa ⊢
  rw [e1] at hpa ⊢
  rw [show |t| * p / 2 = p / 2 * |t| by ring] at hm
  linarith

/-- Jaguzović's `Φ(r,t)` with `r = e^{-y}` equals `r^q (Γ(y,t) - e(t))`. -/
theorem jag_phi_eq {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (y t : ℝ) :
    exp (-y) ^ (p / 2) * (Gam p s y t - ee p t) =
      -(((1 + exp (-y) ^ s) / 2) ^ (p / s))
        + (1 + exp (-y) ^ 2 + 2 * exp (-y) * cos t) ^ (p / 2) / (2 ^ p * cos (π / (2 * p)) ^ p)
        - exp (-y) ^ (p / 2) * tan (π / (2 * p)) * cos (t * p / 2) := by
  have hp : 0 < p := by linarith
  have hc := cos_half_pos hp1 hp2
  have hE : exp y * exp (-y) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hX : 0 ≤ 1 + exp (-y) ^ 2 + 2 * exp (-y) * cos t := by
    nlinarith [neg_one_le_cos t, exp_pos (-y), sq_nonneg (exp (-y) - 1)]
  -- (cosh y + cos t) = e^y · X/2
  have h1 : cosh y + cos t = exp y * ((1 + exp (-y) ^ 2 + 2 * exp (-y) * cos t) / 2) := by
    rw [cosh_eq]; linear_combination (-(exp (-y)) / 2 - cos t) * hE
  have hD : (1 + cos (2 * (π / (2 * p)))) = 2 * cos (π / (2 * p)) ^ 2 := by rw [cos_two_mul]; ring
  have h2p : (2 : ℝ) ^ p * cos (π / (2 * p)) ^ p = 2 ^ (p / 2) * (2 * cos (π / (2 * p)) ^ 2) ^ (p / 2) := by
    rw [mul_rpow (by norm_num) (by positivity), ← mul_assoc, ← rpow_add (by norm_num),
      ← rpow_natCast, ← rpow_mul hc.le]
    push_cast; ring_nf
  have hrq : exp (-y) ^ (p / 2) * exp y ^ (p / 2) = 1 := by
    rw [← mul_rpow (exp_pos _).le (exp_pos _).le, mul_comm, hE, one_rpow]
  have hC : cosh (s * y / 2) ^ (p / s) = exp y ^ (p / 2) * ((1 + exp (-y) ^ s) / 2) ^ (p / s) := by
    rw [cosh_half_eq, mul_rpow (exp_pos _).le (by positivity), ← exp_mul,
      show s * y / 2 * (p / s) = y * (p / 2) by field_simp, exp_mul]
  unfold Gam ee
  rw [h1, hD, mul_rpow (exp_pos y).le (by positivity), hC, div_rpow hX (by norm_num), h2p,
    show t * p / 2 = p / 2 * t by ring]
  linear_combination ((1 + exp (-y) ^ 2 + 2 * exp (-y) * cos t) ^ (p / 2) /
      (2 ^ (p / 2) * (2 * cos (π / (2 * p)) ^ 2) ^ (p / 2)) - ((1 + exp (-y) ^ s) / 2) ^ (p / s)) * hrq

/-- For `p > 4/3`: (eq:two) at `s = p/(p-1)`, from [Jag2026, (2)] with `r = e^{-|y|}`. -/
theorem twoVar_jag {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : TwoVar p (p / (p - 1)) := by
  intro y t ht
  have hp1' : 1 < p := by linarith
  have hs : 0 < p / (p - 1) := div_pos (by linarith) (by linarith)
  have hj := Cited.jag_eq2 p hp1 hp2 (exp (-|y|)) t (exp_pos _).le
    (exp_le_one_iff.mpr (by linarith [abs_nonneg y])) ht.1 ht.2
  rw [← jag_phi_eq hp1' hp2 hs |y| t] at hj
  have hpos : 0 < exp (-|y|) ^ (p / 2) := by positivity
  have h0 : 0 ≤ Gam p (p / (p - 1)) |y| t - ee p t := nonneg_of_mul_nonneg_right (by linarith) hpos
  have hev : Gam p (p / (p - 1)) |y| t = Gam p (p / (p - 1)) y t := by
    rcases abs_choice y with h | h <;> rw [h]; exact gam_even_y _ _ _ _
  linarith

theorem twoVar_exists {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : ∃ s, 0 < s ∧ TwoVar p s := by
  rcases le_or_gt p (4 / 3) with h | h
  · exact ⟨Ssec p, Ssec_pos hp1, twoVar_mel hp1 h⟩
  · exact ⟨p / (p - 1), div_pos (by linarith) (by linarith), twoVar_jag h hp2⟩

/-! ### (E): the threshold -/

/-- C04b, l.195-197: (eq:two) holds exactly for `s ∈ (0, s₀(p)]`, for some `s₀(p) > 0`. -/
theorem twoVar_threshold {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0) := by
  have hp : 0 < p := by linarith
  obtain ⟨s1, hs1, h1⟩ := twoVar_exists hp1 hp2
  set A := {s : ℝ | 0 < s ∧ TwoVar p s}
  have hne : A.Nonempty := ⟨s1, hs1, h1⟩
  have hbdd : BddAbove A := ⟨Ssec p, fun s ⟨_, h⟩ => by
    by_contra hc
    exact twoVar_fails_above hp1 hp2 (not_le.mp hc) h⟩
  have hs10 : s1 ≤ sSup A := le_csSup hbdd ⟨hs1, h1⟩
  have hs0 : 0 < sSup A := lt_of_lt_of_le hs1 hs10
  have hlt : ∀ s', 0 < s' → s' < sSup A → TwoVar p s' := fun s' hs' hlt' => by
    obtain ⟨s'', ⟨_, hs''⟩, hlt''⟩ := exists_lt_of_lt_csSup hne hlt'
    exact twoVar_mono hp hs'' hs' hlt''.le
  have h0 : TwoVar p (sSup A) := twoVar_of_forall_lt hs0 hlt
  exact ⟨sSup A, hs0, fun s hs => ⟨fun h => le_csSup hbdd ⟨hs, h⟩, fun hle => twoVar_mono hp h0 hs hle⟩⟩

end P18
