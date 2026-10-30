/-
  HVFalse/Proofs/NewRows11.lean - claims of the paper first stated in Lean here (N1-N5)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  N1, N2, N4: `Ssec p = 1/cos²(π/2p)` is enclosed by rational bounds of `cos(π/2p)` (Bracket.cos_theta_encl with
  Mathlib's 20-digit bounds of π, and the 16-term Taylor bounds Numeric2.le_cos16 / cos_le16). Certificates are generated and
  re-checked with exact fractions by a generator script (not shipped); Lean re-checks each by norm_num.
  N2: the fraction (S - m)/(S - p/(p-1)) increases in S, so the two ends of the enclosure bound it (ratio_bounds).
  N3: s₋ ≤ s₀ from the box part C19b_boxes; s₀ < s₊ at p = 19/10 from the proved failure point Bracket.point_19_10.
  N5: Γ(y,t) ≥ e^{p|y|/2} B(e^{-|y|}) (Coercive.gam_ge_factor, evenness), B continuous at 0, B(0) = the bracket.
-/
import HVFalse.Paper.ComputerChecked
import HVFalse.Proofs.Numeric2
import HVFalse.Proofs.Coercive
import HVFalse.Proofs.SaddleValley

open Real Set Filter Topology

namespace P18

namespace NewRows11

/-- Rational enclosure of `Ssec p` from a rational enclosure of `π/(2p)` and the Taylor bounds of `cos`. -/
theorem Ssec_encl {p θlo θhi clo chi : ℝ} (hp : 1 < p) (hθlo0 : 0 ≤ θlo) (hθlo2 : θlo ≤ 2)
    (hθlo : θlo * (2 * p) ≤ 314159265358979323846 / 100000000000000000000)
    (hθhi : 314159265358979323847 / 100000000000000000000 ≤ θhi * (2 * p)) (hθhi0 : 0 ≤ θhi) (hθhi2 : θhi ≤ 2)
    (hclo0 : 0 < clo)
    (hclo : clo ≤ (1 - θhi ^ 2 / 2 + θhi ^ 4 / 24 - θhi ^ 6 / 720 + θhi ^ 8 / 40320 - θhi ^ 10 / 3628800
      + θhi ^ 12 / 479001600 - θhi ^ 14 / 87178291200) - θhi ^ 16 / 20922789888000 * 2)
    (hchi : (1 - θlo ^ 2 / 2 + θlo ^ 4 / 24 - θlo ^ 6 / 720 + θlo ^ 8 / 40320 - θlo ^ 10 / 3628800
      + θlo ^ 12 / 479001600 - θlo ^ 14 / 87178291200) + θlo ^ 16 / 20922789888000 * 2 ≤ chi) :
    1 / chi ^ 2 ≤ Ssec p ∧ Ssec p ≤ 1 / clo ^ 2 := by
  obtain ⟨h1, h2⟩ := Bracket.cos_theta_encl (p := p) (by linarith) hθlo0 hθlo hθhi (by linarith)
    (Numeric2.le_cos16 hθhi0 hθhi2 hclo) (Numeric2.cos_le16 hθlo0 hθlo2 hchi)
  have hc := SaddleValley.cos_th_pos hp
  unfold Ssec
  exact ⟨one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hc.le h2 2),
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hclo0.le h1 2)⟩

theorem encl_7_5 : 1 / (43388373911787 / 100000000000000 : ℝ) ^ 2 ≤ Ssec (7 / 5) ∧
    Ssec (7 / 5) ≤ 1 / (8677674782333 / 20000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (56099868814103 / 50000000000000 : ℝ)) (θhi := (112199737628207 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_3_2 : 1 / (50000000000011 / 100000000000000 : ℝ) ^ 2 ≤ Ssec (3 / 2) ∧
    Ssec (3 / 2) ≤ 1 / (49999999999969 / 100000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (104719755119659 / 100000000000000 : ℝ)) (θhi := (5235987755983 / 5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_8_5 : 1 / (13889255825491 / 25000000000000 : ℝ) ^ 2 ≤ Ssec (8 / 5) ∧
    Ssec (8 / 5) ≤ 1 / (13889255825487 / 25000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (98174770424681 / 100000000000000 : ℝ)) (θhi := (49087385212341 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_17_10 : 1 / (7532932954741 / 12500000000000 : ℝ) ^ 2 ≤ Ssec (17 / 10) ∧
    Ssec (17 / 10) ≤ 1 / (60263463637921 / 100000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (92399783929111 / 100000000000000 : ℝ)) (θhi := (11549972991139 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_9_5 : 1 / (12855752193731 / 20000000000000 : ℝ) ^ 2 ≤ Ssec (9 / 5) ∧
    Ssec (9 / 5) ≤ 1 / (64278760968651 / 100000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (21816615649929 / 25000000000000 : ℝ)) (θhi := (87266462599717 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_19_10 : 1 / (4233009822661 / 6250000000000 : ℝ) ^ 2 ≤ Ssec (19 / 10) ∧
    Ssec (19 / 10) ≤ 1 / (67728157162573 / 100000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (82673490883941 / 100000000000000 : ℝ)) (θhi := (41336745441971 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem encl_cell0 : 1 / (38672239053299 / 100000000000000 : ℝ) ^ 2 ≤ Ssec (4577 / 3420) ∧
    Ssec (4577 / 3420) ≤ 1 / (38672239053049 / 100000000000000 : ℝ) ^ 2 :=
  Ssec_encl (θlo := (29343038221753 / 25000000000000 : ℝ)) (θhi := (117372152887013 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem abs_of_encl {S lo hi b e : ℝ} (h : lo ≤ S ∧ S ≤ hi) (h1 : b - e ≤ lo) (h2 : hi ≤ b + e) : |S - b| ≤ e :=
  abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- `(S - m)/(S - j)` increases in `S` (`m ≥ j`), so an enclosure of `S` encloses it. -/
theorem ratio_bounds {S Slo Shi m j f e : ℝ} (hS : Slo ≤ S ∧ S ≤ Shi) (hj : j < Slo) (hf1 : f - e ≤ 1)
    (hf2 : f + e ≤ 1) (h1 : (f - e) * (Slo - j) ≤ Slo - m) (h2 : Shi - m ≤ (f + e) * (Shi - j)) :
    |(S - m) / (S - j) - f| ≤ e := by
  have hpos : 0 < S - j := by linarith [hS.1]
  have k1 : f - e ≤ (S - m) / (S - j) := by
    rw [le_div_iff₀ hpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS.1) (sub_nonneg.mpr hf1)]
  have k2 : (S - m) / (S - j) ≤ f + e := by
    rw [div_le_iff₀ hpos]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS.2) (sub_nonneg.mpr hf2)]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- N1, table of Prop. 10, column "open window" (l.556-561; 4-decimal rounding). -/
theorem window_ends : ∀ r ∈ ([(7/5, 35000/10000, 53119/10000), (3/2, 30000/10000, 40000/10000),
      (8/5, 26667/10000, 32398/10000), (17/10, 24286/10000, 27535/10000), (9/5, 22500/10000, 24203/10000),
      (19/10, 21111/10000, 21800/10000)] : List (ℝ × ℝ × ℝ)),
      |r.1 / (r.1 - 1) - r.2.1| ≤ 5 / 10 ^ 5 ∧ |Ssec r.1 - r.2.2| ≤ 5 / 10 ^ 5 := by
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_7_5 (by norm_num) (by norm_num)⟩
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_3_2 (by norm_num) (by norm_num)⟩
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_8_5 (by norm_num) (by norm_num)⟩
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_17_10 (by norm_num) (by norm_num)⟩
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_9_5 (by norm_num) (by norm_num)⟩
  · exact ⟨by norm_num [abs_le], abs_of_encl encl_19_10 (by norm_num) (by norm_num)⟩

/-- N2, column "failing fraction" (l.556-561, l.565-566): `(sec² - s̄)/(sec² - p/(p-1))`, `s̄ = (s₋+s₊)/2`, to 0.1%. -/
theorem failing_fractions : ∀ r ∈ ([(7/5, 52986/10000, 52989/10000, 7/1000), (3/2, 39572/10000, 39575/10000, 43/1000),
      (8/5, 31799/10000, 31802/10000, 104/1000), (17/10, 26921/10000, 26925/10000, 188/1000),
      (9/5, 23764/10000, 23767/10000, 257/1000), (19/10, 21588/10000, 21591/10000, 306/1000)] : List (ℝ × ℝ × ℝ × ℝ)),
      |(Ssec r.1 - (r.2.1 + r.2.2.1) / 2) / (Ssec r.1 - r.1 / (r.1 - 1)) - r.2.2.2| ≤ 5 / 10 ^ 4 := by
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ratio_bounds encl_7_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ratio_bounds encl_3_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ratio_bounds encl_8_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ratio_bounds encl_17_10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ratio_bounds encl_9_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · exact ratio_bounds encl_19_10 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A failure point of (eq:two) excludes `TwoVar`. -/
theorem not_twoVar_of_point {p s y t : ℝ} (ht : t ∈ Icc (-π) π) (h : Gam p s y t < ee p t) : ¬ TwoVar p s :=
  fun h2 => absurd (h2 y t ht) (not_le.mpr h)

/-- N3, Introduction (l.110-111): the failing part of the open window is under 1% at `p = 7/5` and about 31% at `p = 19/10`. -/
theorem window_fail_part (hb : Paper.C19b_boxes) :
    (∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar (7/5) s ↔ s ≤ s0)) →
      (Ssec (7/5) - s0) / (Ssec (7/5) - (7/5) / (7/5 - 1)) < 1 / 100) ∧
    (∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar (19/10) s ↔ s ≤ s0)) →
      |(Ssec (19/10) - s0) / (Ssec (19/10) - (19/10) / (19/10 - 1)) - 31 / 100| ≤ 1 / 100) := by
  have h75 : TwoVar (7/5) (52986/10000) := hb (7/5, 52986/10000) (by simp)
  have h1910 : TwoVar (19/10) (21588/10000) := hb (19/10, 21588/10000) (by simp)
  refine ⟨fun s0 hs0 => ?_, fun s0 hs0 => ?_⟩
  · have hlo : (52986 / 10000 : ℝ) ≤ s0 := (hs0 _ (by norm_num)).mp h75
    have hSlo : (5311 / 1000 : ℝ) ≤ Ssec (7/5) := le_trans (by norm_num) encl_7_5.1
    have hShi : Ssec (7/5) ≤ (5312 / 1000 : ℝ) := encl_7_5.2.trans (by norm_num)
    have hj : (7/5 : ℝ) / (7/5 - 1) = 7 / 2 := by norm_num
    rw [hj, div_lt_iff₀ (by linarith)]
    linarith
  · have hlo : (21588 / 10000 : ℝ) ≤ s0 := (hs0 _ (by norm_num)).mp h1910
    have hhi : s0 < 21591 / 10000 := by
      by_contra hcon
      exact not_twoVar_of_point ⟨by linarith [pi_pos], pi_pos.le⟩ Bracket.point_19_10
        ((hs0 _ (by norm_num)).mpr (not_lt.mp hcon))
    have hSlo : (21800 / 10000 : ℝ) ≤ Ssec (19/10) := le_trans (by norm_num) encl_19_10.1
    have hShi : Ssec (19/10) ≤ (21801 / 10000 : ℝ) := encl_19_10.2.trans (by norm_num)
    have hj : (19/10 : ℝ) / (19/10 - 1) = 19 / 9 := by norm_num
    rw [hj]
    have hpos : 0 < Ssec (19/10) - 19 / 9 := by linarith
    have k1 : (30 / 100 : ℝ) ≤ (Ssec (19/10) - s0) / (Ssec (19/10) - 19 / 9) := by
      rw [le_div_iff₀ hpos]; linarith
    have k2 : (Ssec (19/10) - s0) / (Ssec (19/10) - 19 / 9) ≤ 32 / 100 := by
      rw [div_le_iff₀ hpos]; linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- N4, Remark after Prop. 11 (l.591-593): "on the first cell ... for all s ≤ 6.413, while p/(p-1) ≤ 4 there". -/
theorem first_cell : 6413 / 1000 ≤ cellLevel 0 - 2 / 10 ^ 6 ∧
    ∀ p ∈ Set.Icc (cellLeft 0) (cellRight 0), p / (p - 1) ≤ 4 := by
  constructor
  · have hr : cellRight 0 = 4577 / 3420 := by norm_num [cellRight, cellLeft]
    have hk : cellKappa 0 = 9 / 10 := by norm_num [cellKappa]
    have hj : (4577 / 3420 : ℝ) / (4577 / 3420 - 1) = 4577 / 1157 := by norm_num
    have hnum : (6413 / 1000 : ℝ) + 2 / 10 ^ 6 ≤
        4577 / 1157 + 9 / 10 * (1 / (38672239053299 / 100000000000000 : ℝ) ^ 2 - 4577 / 1157) := by norm_num
    have hS := encl_cell0.1
    unfold cellLevel
    rw [hr, hk, hj]
    linarith
  · intro p hp
    have h43 : (4 / 3 : ℝ) ≤ p := by
      have h := hp.1
      norm_num [cellLeft] at h
      exact h
    rw [div_le_iff₀ (by linarith)]
    linarith

/-- N5, footnote of Sec. 2 (l.216-219): `Γ(y,t) ≥ (c - ε) e^{p|y|/2}` for large `|y|`, uniformly in `t`, with
`c = (2 cos(π/2p))^{-p} - 2^{-p/s}`. -/
theorem gam_lower_asymp {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∀ ε > 0, ∃ R : ℝ, ∀ y t : ℝ, R ≤ |y| →
      ((2 * cos (π / (2 * p))) ^ (-p) - (2 : ℝ) ^ (-p / s) - ε) * exp (p / 2 * |y|) ≤ Gam p s y t := by
  intro ε hε
  have hB : Tendsto (fun y => coerB p s (exp (-y))) atTop (𝓝 (coerB p s 0)) :=
    (coerB_continuousAt hp1 hs).tendsto.comp tendsto_exp_neg_atTop_nhds_zero
  rw [coerB_zero hp1 hp2 hs] at hB
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hB.eventually (eventually_gt_nhds (sub_lt_self _ hε)))
  refine ⟨R, fun y t hy => ?_⟩
  have h2 : exp (p / 2 * |y|) * coerB p s (exp (-|y|)) ≤ Gam p s y t := by
    rcases abs_choice y with h | h
    · rw [h]; exact gam_ge_factor hp1 hp2 hs y t
    · rw [h, ← gam_even_y p s y t]; exact gam_ge_factor hp1 hp2 hs (-y) t
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left (hR |y| hy).le (exp_pos _).le).trans h2

/-- N5, footnote of Sec. 2: the bracket is positive iff `2 cos(π/2p) < 2^{1/s}`. -/
theorem bracket_pos_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    0 < (2 * cos (π / (2 * p))) ^ (-p) - (2 : ℝ) ^ (-p / s) ↔ 2 * cos (π / (2 * p)) < (2 : ℝ) ^ (1 / s) := by
  have hA : 0 < 2 * cos (π / (2 * p)) := by linarith [SaddleValley.cos_th_pos hp1]
  have hB : (0 : ℝ) < 2 ^ (1 / s) := rpow_pos_of_pos two_pos _
  have h2 : (2 : ℝ) ^ (-p / s) = ((2 : ℝ) ^ (1 / s)) ^ (-p) := by
    rw [← rpow_mul two_pos.le]; congr 1; ring
  rw [h2, sub_pos, rpow_lt_rpow_iff_of_neg hB hA (by linarith)]

end NewRows11

end P18
