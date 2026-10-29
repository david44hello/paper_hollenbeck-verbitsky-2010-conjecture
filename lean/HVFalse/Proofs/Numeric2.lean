/-
  HVFalse/Proofs/Numeric2.lean - Prop. 10's six exact failure points with margins (C19c) and the 140 cell levels above the
  jag `p/(p-1)` (C20b)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  C19c: at the certificate's exact points (logs/bracket_upper_arb.log) `Γ - e < -δ` is reduced
  (`gam_sub_ee_lt_of_bounds`) to rational checks as in Bracket.lean, except the second term: `c^(p/s)` is bounded below
  by `exp(L·p/s)` with a rational `L ≤ log c` (`exp L ≤ c`), so no margin is lost to a rational exponent `a/b ≤ p/s`.
  C20b: `Ssec p_b ≥ 1/c²` from a rational upper bound `c` of `cos(π/2p_b)` (cos antitone, Taylor at a rational
  `θ ≤ π/2p_b`), one certificate per cell. Certificates generated and re-checked exactly (Python `Fraction`) by
  a generator script (not shipped). No interval arithmetic, no native code.
-/
import HVFalse.Proofs.Bracket
import HVFalse.Defs.Cells

open Real Set

namespace P18

namespace Numeric2

/-- One-sided `cos a ≤ hi` from the 8-term Taylor polynomial, `0 ≤ a ≤ 2`. -/
theorem cos_le16 {a hi : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (h : (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
      - a ^ 14 / 87178291200) + a ^ 16 / 20922789888000 * 2 ≤ hi) : cos a ≤ hi := by
  have h2 := abs_le.mp (cos_taylor16 a (by rw [abs_of_nonneg ha0]; exact ha2))
  rw [abs_of_nonneg ha0] at h2
  linarith [h2.2]

/-- One-sided `lo ≤ cos a` from the 8-term Taylor polynomial, `0 ≤ a ≤ 2`. -/
theorem le_cos16 {a lo : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (h : lo ≤ (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 - a ^ 10 / 3628800 + a ^ 12 / 479001600
      - a ^ 14 / 87178291200) - a ^ 16 / 20922789888000 * 2) : lo ≤ cos a := by
  have h2 := abs_le.mp (cos_taylor16 a (by rw [abs_of_nonneg ha0]; exact ha2))
  rw [abs_of_nonneg ha0] at h2
  linarith [h2.1]

/-- One-sided `exp z ≤ hi` from 16 Taylor terms, `0 ≤ z ≤ 1`. -/
theorem exp_le16 {z hi : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (h : ∑ m ∈ Finset.range 16, z ^ m / m.factorial + z ^ 16 * (17 / 334764638208000) ≤ hi) : exp z ≤ hi :=
  (Bracket.exp_encl16 hz0 hz1 le_rfl h).2

/-- One-sided `lo ≤ exp z` from 16 Taylor terms, `0 ≤ z ≤ 1`. -/
theorem le_exp16 {z lo : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (h : lo ≤ ∑ m ∈ Finset.range 16, z ^ m / m.factorial - z ^ 16 * (17 / 334764638208000)) : lo ≤ exp z :=
  (Bracket.exp_encl16 hz0 hz1 h le_rfl).1

/-- The second term of `Γ` from below without a rational exponent: `exp (L·(p/s)) ≤ c^(p/s)` when `exp L ≤ Xlo ≤ c`. -/
theorem le_rpow_of_exp_le {c Xlo L F2 r : ℝ} (hr : 0 ≤ r) (hX : Xlo ≤ c) (hL : exp L ≤ Xlo)
    (hF2 : F2 ≤ exp (L * r)) : F2 ≤ c ^ r := by
  have hXpos : 0 < Xlo := (exp_pos L).trans_le hL
  have hlog : L ≤ log Xlo := (le_log_iff_exp_le hXpos).2 hL
  calc F2 ≤ exp (L * r) := hF2
    _ ≤ exp (log Xlo * r) := exp_le_exp.2 (mul_le_mul_of_nonneg_right hlog hr)
    _ = Xlo ^ r := (rpow_def_of_pos hXpos r).symm
    _ ≤ c ^ r := rpow_le_rpow hXpos.le hX hr

/-- The reduction with a margin `δ`: `Γ(y,t) - e(t) < -δ` from rational bounds of `cos ϑ`, `cosh y + cos t`,
`cosh(sy/2)` (through `exp L ≤ Xlo`), `cos(pt/2)`, with `p/2 = m/n` (Bracket's `gam_lt_ee_of_bounds`, second term by
`le_rpow_of_exp_le`). -/
theorem gam_sub_ee_lt_of_bounds {p s y t δ clo chi Ahi Yhi F1 Xlo L F2 slo Elo : ℝ} {m n : ℕ}
    (hp1 : 1 < p) (hs : 0 < s) (hn : n ≠ 0) (hpmn : p / 2 = (m : ℝ) / n)
    (hclo : 0 < clo) (hc : clo ≤ cos (π / (2 * p)) ∧ cos (π / (2 * p)) ≤ chi)
    (hA : cosh y + cos t ≤ Ahi) (hY : Ahi / (2 * clo ^ 2) ≤ Yhi) (hF1 : 0 ≤ F1) (hF1' : Yhi ^ m ≤ F1 ^ n)
    (hX : Xlo ≤ cosh (s * y / 2)) (hL : exp L ≤ Xlo) (hF2 : F2 ≤ exp (L * (p / s)))
    (hslo : 0 ≤ slo) (hs2 : slo ^ 2 ≤ 1 - chi ^ 2) (hElo : 0 ≤ Elo) (hE : Elo ≤ cos (p / 2 * t))
    (hfin : F1 - F2 < slo / chi * Elo - δ) : Gam p s y t - ee p t < -δ := by
  have hp0 : 0 < p := by linarith
  have hθ0 : 0 < π / (2 * p) := by positivity
  have hθπ : π / (2 * p) < π := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hc0 : 0 < cos (π / (2 * p)) := hclo.trans_le hc.1
  have hchi : 0 < chi := hc0.trans_le hc.2
  have hAnn : 0 ≤ cosh y + cos t := by linarith [one_le_cosh y, neg_one_le_cos t]
  have hYnn : 0 ≤ Ahi / (2 * clo ^ 2) := div_nonneg (hAnn.trans hA) (by positivity)
  -- the first term of `Γ`
  have hden : 1 + cos (2 * (π / (2 * p))) = 2 * cos (π / (2 * p)) ^ 2 := by rw [cos_two_mul]; ring
  have hcc : 2 * clo ^ 2 ≤ 2 * cos (π / (2 * p)) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hclo.le hc.1 2) (by norm_num)
  have hle : (cosh y + cos t) / (2 * cos (π / (2 * p)) ^ 2) ≤ Ahi / (2 * clo ^ 2) :=
    div_le_div₀ (hAnn.trans hA) hA (mul_pos two_pos (pow_pos hclo 2)) hcc
  have hT1 : (cosh y + cos t) ^ (p / 2) / (1 + cos (2 * (π / (2 * p)))) ^ (p / 2) ≤ F1 := by
    rw [hden, ← div_rpow hAnn (by positivity), hpmn]
    calc ((cosh y + cos t) / (2 * cos (π / (2 * p)) ^ 2)) ^ ((m : ℝ) / n)
        ≤ Yhi ^ ((m : ℝ) / n) := rpow_le_rpow (div_nonneg hAnn (by positivity)) (hle.trans hY) (by positivity)
      _ ≤ F1 := rpow_le_of_pow_le (hYnn.trans hY) hF1 hn hF1'
  -- the second term of `Γ`
  have hT2 : F2 ≤ cosh (s * y / 2) ^ (p / s) := le_rpow_of_exp_le (by positivity) hX hL hF2
  -- `e(t) = tan ϑ cos(pt/2)`, with `sin ϑ ≥ √(1 - chi²)`
  have hsin0 : 0 ≤ sin (π / (2 * p)) := sin_nonneg_of_nonneg_of_le_pi hθ0.le hθπ.le
  have hcos2 : cos (π / (2 * p)) ^ 2 ≤ chi ^ 2 := pow_le_pow_left₀ hc0.le hc.2 2
  have hsin2 : slo ^ 2 ≤ sin (π / (2 * p)) ^ 2 := by nlinarith [sin_sq_add_cos_sq (π / (2 * p))]
  have hsin : slo ≤ sin (π / (2 * p)) := by nlinarith
  have htan : slo / chi ≤ tan (π / (2 * p)) := by
    rw [tan_eq_sin_div_cos]; exact div_le_div₀ hsin0 hsin hc0 hc.2
  have hee : slo / chi * Elo ≤ ee p t := by
    unfold ee; exact mul_le_mul htan hE hElo ((div_nonneg hslo hchi.le).trans htan)
  unfold Gam
  linarith

/-- C20b for one cell: the level `p_b/(p_b-1) + κ(Ssec p_b - p_b/(p_b-1))` is bounded below through `cos(π/2p_b) ≤ c`
(`cos` antitone on `[0, π]`, Taylor at a rational `θ ≤ π/(2p_b)`, Mathlib's 20-digit lower bound of `π`). -/
theorem cell_of_bounds {i : ℕ} {pl pr κ θ c : ℝ} (hl : cellLeft i = pl) (hr : cellRight i = pr)
    (hk : cellKappa i = κ) (hpr : 1 < pr) (hκ : 0 ≤ κ) (hθ0 : 0 ≤ θ)
    (hθ : θ * (2 * pr) ≤ 314159265358979323846 / 100000000000000000000) (hθ2 : θ ≤ 2)
    (hc : (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 + θ ^ 8 / 40320 - θ ^ 10 / 3628800 + θ ^ 12 / 479001600
      - θ ^ 14 / 87178291200) + θ ^ 16 / 20922789888000 * 2 ≤ c)
    (hfin : pl / (pl - 1) ≤ pr / (pr - 1) + κ * (1 / c ^ 2 - pr / (pr - 1)) - 2 / 10 ^ 6) :
    cellLeft i / (cellLeft i - 1) ≤ cellLevel i - 2 / 10 ^ 6 := by
  have hpi : (314159265358979323846 / 100000000000000000000 : ℝ) < π := by
    have := pi_gt_d20; norm_num at this ⊢; linarith
  have hpr0 : 0 < 2 * pr := by linarith
  have hθle : θ ≤ π / (2 * pr) := by rw [le_div_iff₀ hpr0]; linarith
  have hθ' : π / (2 * pr) < π / 2 := by
    rw [div_lt_div_iff₀ hpr0 two_pos]; nlinarith [pi_pos]
  have hcpos : 0 < cos (π / (2 * pr)) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hθ'⟩
  have hcθ : cos (π / (2 * pr)) ≤ cos θ := cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [pi_pos]) hθle
  have hcc : cos (π / (2 * pr)) ≤ c := hcθ.trans (cos_le16 hθ0 hθ2 hc)
  have hS : 1 / c ^ 2 ≤ Ssec pr := by
    unfold Ssec
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hcpos.le hcc 2)
  unfold cellLevel
  rw [hl, hr, hk]
  nlinarith [mul_le_mul_of_nonneg_left hS hκ]

/-- `Γ - e < -23 / 20000000` at `p = 7 / 5`, `s = 52989 / 10000`, `(y, t) = (110877 / 500000, 2144519 / 1000000)` (certified `Γ - e ≤ -1.157641e-06`). -/
theorem point_7_5 : Gam (7 / 5 : ℝ) (52989 / 10000) (110877 / 500000) (2144519 / 1000000) - ee (7 / 5 : ℝ) (2144519 / 1000000) < -(115 / 10 ^ 8) := by
  have hc := Bracket.cos_theta_encl (p := (7 / 5 : ℝ)) (θlo := (112199737628206901373 / 100000000000000000000 : ℝ)) (θhi := (56099868814103450687 / 50000000000000000000 : ℝ)) (clo := (216941869558327467 / 500000000000000000 : ℝ)) (chi := (433883739117860831 / 1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (56099868814103450687 / 50000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (112199737628206901373 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (110877 / 500000 : ℝ)) (C := (1024688340415936901 / 1000000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (110877 / 500000 : ℝ) / 2) (lo := (1117257475733102389 / 1000000000000000000 : ℝ)) (hi := (111725747573310239 / 100000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hct2 := Bracket.cos_encl16 (a := (2144519 / 1000000 : ℝ) / 2) (lo := (478140970576926919 / 1000000000000000000 : ℝ)) (hi := (239070485288755343 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hct := Bracket.cos_upper_half (t := (2144519 / 1000000 : ℝ)) (H := (-13569060612759803 / 25000000000000000 : ℝ)) (hct2.1.trans' (by norm_num)) hct2.2 (by norm_num)
  have hA : cosh (110877 / 500000 : ℝ) + cos (2144519 / 1000000 : ℝ) ≤ (481925915905544781 / 1000000000000000000 : ℝ) := by linarith
  have hX := Bracket.cosh_lower (x := (52989 / 10000 : ℝ) * (110877 / 500000 : ℝ) / 2) (C := (588807855219594491 / 500000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (52989 / 10000 : ℝ) * (110877 / 500000 : ℝ) / 2 / 2) (lo := (1341466029312329349 / 1000000000000000000 : ℝ)) (hi := (26829320586246587 / 20000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (81745904984685447 / 500000000000000000 : ℝ)) (hi := (588807855219594491 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (81745904984685447 / 500000000000000000 : ℝ) * ((7 / 5 : ℝ) / (52989 / 10000 : ℝ))) (lo := (522070992379805821 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE := le_cos16 (a := (7 / 5 : ℝ) / 2 * (2144519 / 1000000 : ℝ)) (lo := (34788384026615267 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  exact gam_sub_ee_lt_of_bounds (m := 7) (n := 10) (Yhi := (639990521221861783 / 500000000000000000 : ℝ)) (F1 := (118861847468564607 / 100000000000000000 : ℝ)) (slo := (225242216975568337 / 250000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

/-- `Γ - e < -23 / 20000000` at `p = 3 / 2`, `s = 1583 / 400`, `(y, t) = (49177 / 100000, 1768641 / 1000000)` (certified `Γ - e ≤ -5.303241e-06`). -/
theorem point_3_2 : Gam (3 / 2 : ℝ) (1583 / 400) (49177 / 100000) (1768641 / 1000000) - ee (3 / 2 : ℝ) (1768641 / 1000000) < -(115 / 10 ^ 8) := by
  have hc := Bracket.cos_theta_encl (p := (3 / 2 : ℝ)) (θlo := (20943951023931954923 / 20000000000000000000 : ℝ)) (θhi := (13089969389957471827 / 12500000000000000000 : ℝ)) (clo := (124999999999925117 / 250000000000000000 : ℝ)) (chi := (3125000000000627 / 6250000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (13089969389957471827 / 12500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (20943951023931954923 / 20000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (49177 / 100000 : ℝ)) (C := (140421936416568047 / 125000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (49177 / 100000 : ℝ) / 2) (lo := (255750501709436039 / 200000000000000000 : ℝ)) (hi := (319688127136795049 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hct2 := Bracket.cos_encl16 (a := (1768641 / 1000000 : ℝ) / 2) (lo := (633815230480394377 / 1000000000000000000 : ℝ)) (hi := (495168148812829 / 781250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hct := Bracket.cos_upper_half (t := (1768641 / 1000000 : ℝ)) (H := (-49139126805525327 / 250000000000000000 : ℝ)) (hct2.1.trans' (by norm_num)) hct2.2 (by norm_num)
  have hA : cosh (49177 / 100000 : ℝ) + cos (1768641 / 1000000 : ℝ) ≤ (231704746027610767 / 250000000000000000 : ℝ) := by linarith
  have hX := Bracket.cosh_lower (x := (1583 / 400 : ℝ) * (49177 / 100000 : ℝ) / 2) (C := (189001346164771329 / 125000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (1583 / 400 : ℝ) * (49177 / 100000 : ℝ) / 2 / 2) (lo := (813343103601833307 / 500000000000000000 : ℝ)) (hi := (203335775900458327 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (413440400296903577 / 1000000000000000000 : ℝ)) (hi := (189001346164771329 / 125000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (413440400296903577 / 1000000000000000000 : ℝ) * ((3 / 2 : ℝ) / (1583 / 400 : ℝ))) (lo := (292412670619843299 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE := le_cos16 (a := (3 / 2 : ℝ) / 2 * (1768641 / 1000000 : ℝ)) (lo := (9675691340758607 / 40000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  exact gam_sub_ee_lt_of_bounds (m := 3) (n := 4) (Yhi := (231704746027888379 / 125000000000000000 : ℝ)) (F1 := (794307552125785447 / 500000000000000000 : ℝ)) (slo := (433012701892190363 / 500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

/-- `Γ - e < -23 / 20000000` at `p = 8 / 5`, `s = 15901 / 5000`, `(y, t) = (837049 / 1000000, 613161 / 500000)` (certified `Γ - e ≤ -1.331494e-05`). -/
theorem point_8_5 : Gam (8 / 5 : ℝ) (15901 / 5000) (837049 / 1000000) (613161 / 500000) - ee (8 / 5 : ℝ) (613161 / 500000) < -(115 / 10 ^ 8) := by
  have hc := Bracket.cos_theta_encl (p := (8 / 5 : ℝ)) (θlo := (98174770424681038701 / 100000000000000000000 : ℝ)) (θhi := (98174770424681038703 / 100000000000000000000 : ℝ)) (clo := (277785116509747777 / 500000000000000000 : ℝ)) (chi := (555570233019637931 / 1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (98174770424681038703 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (98174770424681038701 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (837049 / 1000000 : ℝ)) (C := (10712999361848817 / 7812500000000000 : ℝ))
    (Bracket.exp_encl16 (z := (837049 / 1000000 : ℝ) / 2) (lo := (379929389315056213 / 250000000000000000 : ℝ)) (hi := (1519717557260224853 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hct2 := Bracket.cos_encl16 (a := (613161 / 500000 : ℝ) / 2) (lo := (817833091894007403 / 1000000000000000000 : ℝ)) (hi := (817833091894007481 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hct := Bracket.cos_upper_half (t := (613161 / 500000 : ℝ)) (H := (33770193239382417 / 100000000000000000 : ℝ)) (hct2.1.trans' (by norm_num)) hct2.2 (by norm_num)
  have hA : cosh (837049 / 1000000 : ℝ) + cos (613161 / 500000 : ℝ) ≤ (854482925355236373 / 500000000000000000 : ℝ) := by linarith
  have hX := Bracket.cosh_lower (x := (15901 / 5000 : ℝ) * (837049 / 1000000 : ℝ) / 2) (C := (2024504858894167147 / 1000000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (15901 / 5000 : ℝ) * (837049 / 1000000 : ℝ) / 2 / 2) (lo := (77818194130619461 / 40000000000000000 : ℝ)) (hi := (486363713316371669 / 250000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (70532515653371243 / 100000000000000000 : ℝ)) (hi := (2024504858894167147 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (70532515653371243 / 100000000000000000 : ℝ) * ((8 / 5 : ℝ) / (15901 / 5000 : ℝ))) (lo := (5570228621650761 / 3906250000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE := le_cos16 (a := (8 / 5 : ℝ) / 2 * (613161 / 500000 : ℝ)) (lo := (556143901391041603 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  exact gam_sub_ee_lt_of_bounds (m := 4) (n := 5) (Yhi := (692094599557967653 / 250000000000000000 : ℝ)) (F1 := (2258293379892394957 / 1000000000000000000 : ℝ)) (slo := (415734806151260689 / 500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

/-- `Γ - e < -23 / 20000000` at `p = 17 / 10`, `s = 1077 / 400`, `(y, t) = (298409 / 250000, 0)` (certified `Γ - e ≤ -4.451758e-05`). -/
theorem point_17_10 : Gam (17 / 10 : ℝ) (1077 / 400) (298409 / 250000) (0) - ee (17 / 10 : ℝ) (0) < -(115 / 10 ^ 8) := by
  have hc := Bracket.cos_theta_encl (p := (17 / 10 : ℝ)) (θlo := (92399783929111565837 / 100000000000000000000 : ℝ)) (θhi := (46199891964555782919 / 50000000000000000000 : ℝ)) (clo := (602634636379215947 / 1000000000000000000 : ℝ)) (chi := (3766466477370437 / 6250000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (46199891964555782919 / 50000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (92399783929111565837 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (298409 / 250000 : ℝ)) (C := (360217191352741191 / 200000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (298409 / 250000 : ℝ) / 2) (lo := (363266006636125719 / 200000000000000000 : ℝ)) (hi := (908165016590314311 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hA : cosh (298409 / 250000 : ℝ) + cos 0 ≤ (560217191352741191 / 200000000000000000 : ℝ) := by rw [cos_zero]; linarith
  have hX := Bracket.cosh_lower (x := (1077 / 400 : ℝ) * (298409 / 250000 : ℝ) / 2) (C := (2593995080318372807 / 1000000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (1077 / 400 : ℝ) * (298409 / 250000 : ℝ) / 2 / 2) (lo := (2233268555928432693 / 1000000000000000000 : ℝ)) (hi := (1116634277964217879 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (238299797332632761 / 250000000000000000 : ℝ)) (hi := (2593995080318372807 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (238299797332632761 / 250000000000000000 : ℝ) * ((17 / 10 : ℝ) / (1077 / 400 : ℝ))) (lo := (1825464023645372341 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE : (1 : ℝ) ≤ cos ((17 / 10 : ℝ) / 2 * 0) := by rw [mul_zero, cos_zero]
  exact gam_sub_ee_lt_of_bounds (m := 17) (n := 20) (Yhi := (964113737313917897 / 250000000000000000 : ℝ)) (F1 := (393704189275173901 / 125000000000000000 : ℝ)) (slo := (159603445456045857 / 200000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

/-- `Γ - e < -57 / 1000000` at `p = 9 / 5`, `s = 23767 / 10000`, `(y, t) = (613873 / 500000, 0)` (certified `Γ - e ≤ -5.762342e-05`). -/
theorem point_9_5 : Gam (9 / 5 : ℝ) (23767 / 10000) (613873 / 500000) (0) - ee (9 / 5 : ℝ) (0) < -(57 / 10 ^ 6) := by
  have hc := Bracket.cos_theta_encl (p := (9 / 5 : ℝ)) (θlo := (43633231299858239423 / 50000000000000000000 : ℝ)) (θhi := (87266462599716478847 / 100000000000000000000 : ℝ)) (clo := (642787609686523119 / 1000000000000000000 : ℝ)) (chi := (642787609686544747 / 1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (87266462599716478847 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (43633231299858239423 / 50000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (613873 / 500000 : ℝ)) (C := (1853239458701125569 / 1000000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (613873 / 500000 : ℝ) / 2) (lo := (1847573210780715369 / 1000000000000000000 : ℝ)) (hi := (1847573210780715411 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hA : cosh (613873 / 500000 : ℝ) + cos 0 ≤ (2853239458701125569 / 1000000000000000000 : ℝ) := by rw [cos_zero]; linarith
  have hX := Bracket.cosh_lower (x := (23767 / 10000 : ℝ) * (613873 / 500000 : ℝ) / 2) (C := (141690363389392469 / 62500000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (23767 / 10000 : ℝ) * (613873 / 500000 : ℝ) / 2 / 2) (lo := (2074034988141404987 / 1000000000000000000 : ℝ)) (hi := (2074034988141405641 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (32739103220386679 / 40000000000000000 : ℝ)) (hi := (141690363389392469 / 62500000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (32739103220386679 / 40000000000000000 : ℝ) * ((9 / 5 : ℝ) / (23767 / 10000 : ℝ))) (lo := (1858697827248712399 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE : (1 : ℝ) ≤ cos ((9 / 5 : ℝ) / 2 * 0) := by rw [mul_zero, cos_zero]
  exact gam_sub_ee_lt_of_bounds (m := 9) (n := 10) (Yhi := (3452814384369133479 / 1000000000000000000 : ℝ)) (F1 := (762598449106237697 / 250000000000000000 : ℝ)) (slo := (383022221559486743 / 500000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

/-- `Γ - e < -23 / 20000000` at `p = 19 / 10`, `s = 21591 / 10000`, `(y, t) = (625363 / 500000, 0)` (certified `Γ - e ≤ -4.632028e-05`). -/
theorem point_19_10 : Gam (19 / 10 : ℝ) (21591 / 10000) (625363 / 500000) (0) - ee (19 / 10 : ℝ) (0) < -(115 / 10 ^ 8) := by
  have hc := Bracket.cos_theta_encl (p := (19 / 10 : ℝ)) (θlo := (82673490883941927327 / 100000000000000000000 : ℝ)) (θhi := (82673490883941927329 / 100000000000000000000 : ℝ)) (clo := (2709126286502937 / 4000000000000000 : ℝ)) (chi := (677281571625743357 / 1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (le_cos16 (a := (82673490883941927329 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num)) (cos_le16 (a := (82673490883941927327 / 100000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num))
  have hcy := Bracket.cosh_upper (x := (625363 / 500000 : ℝ)) (C := (377917473637390411 / 200000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (625363 / 500000 : ℝ) / 2) (lo := (467231063454529021 / 250000000000000000 : ℝ)) (hi := (1868924253818116141 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hA : cosh (625363 / 500000 : ℝ) + cos 0 ≤ (577917473637390411 / 200000000000000000 : ℝ) := by rw [cos_zero]; linarith
  have hX := Bracket.cosh_lower (x := (21591 / 10000 : ℝ) * (625363 / 500000 : ℝ) / 2) (C := (2058731001237994069 / 1000000000000000000 : ℝ))
    (Bracket.exp_encl16 (z := (21591 / 10000 : ℝ) * (625363 / 500000 : ℝ) / 2 / 2) (lo := (392850052475416027 / 200000000000000000 : ℝ)) (hi := (78570010495083213 / 40000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial]) (by norm_num [Finset.sum_range_succ, Nat.factorial])) (by norm_num) (by norm_num)
  have hL := exp_le16 (z := (144417954833486541 / 200000000000000000 : ℝ)) (hi := (2058731001237994069 / 1000000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hF2 := le_exp16 (z := (144417954833486541 / 200000000000000000 : ℝ) * ((19 / 10 : ℝ) / (21591 / 10000 : ℝ))) (lo := (943922838727091737 / 500000000000000000 : ℝ)) (by norm_num) (by norm_num) (by norm_num [Finset.sum_range_succ, Nat.factorial])
  have hE : (1 : ℝ) ≤ cos ((19 / 10 : ℝ) / 2 * 0) := by rw [mul_zero, cos_zero]
  exact gam_sub_ee_lt_of_bounds (m := 19) (n := 20) (Yhi := (3149686410401026991 / 1000000000000000000 : ℝ)) (F1 := (594817786456646693 / 200000000000000000 : ℝ)) (slo := (735723910673129523 / 1000000000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hc hA (by norm_num) (by norm_num) (by norm_num) hX hL hF2 (by norm_num) (by norm_num) (by norm_num) hE (by norm_num)

theorem cell_0 : cellLeft 0 / (cellLeft 0 - 1) ≤ cellLevel 0 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4 / 3 : ℝ)) (pr := (4577 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (117372152887 / 100000000000 : ℝ)) (c := (193361195267 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_1 : cellLeft 1 / (cellLeft 1 - 1) ≤ cellLevel 1 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4577 / 3420 : ℝ)) (pr := (2297 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (233875639427 / 200000000000 : ℝ)) (c := (6105064597 / 15625000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_2 : cellLeft 2 / (cellLeft 2 - 1) ≤ cellLevel 2 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2297 / 1710 : ℝ)) (pr := (1537 / 1140 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (582533445851 / 500000000000 : ℝ)) (c := (394689081031 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_3 : cellLeft 3 / (cellLeft 3 - 1) ≤ cellLevel 3 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1537 / 1140 : ℝ)) (pr := (1157 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (232157451929 / 200000000000 : ℝ)) (c := (398617643641 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_4 : cellLeft 4 / (cellLeft 4 - 1) ≤ cellLevel 4 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1157 / 855 : ℝ)) (pr := (929 / 684 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (231307790641 / 200000000000 : ℝ)) (c := (402510229723 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_5 : cellLeft 5 / (cellLeft 5 - 1) ≤ cellLevel 5 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (929 / 684 : ℝ)) (pr := (259 / 190 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (230464325939 / 200000000000 : ℝ)) (c := (81273448411 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_6 : cellLeft 6 / (cellLeft 6 - 1) ≤ cellLevel 6 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (259 / 190 : ℝ)) (pr := (4679 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (71758434463 / 62500000000 : ℝ)) (c := (410189078557 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_7 : cellLeft 7 / (cellLeft 7 - 1) ≤ cellLevel 7 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4679 / 3420 : ℝ)) (pr := (1174 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1143978585527 / 1000000000000 : ℝ)) (c := (206988066171 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_8 : cellLeft 8 / (cellLeft 8 - 1) ≤ cellLevel 8 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1174 / 855 : ℝ)) (pr := (1571 / 1140 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1139852204039 / 1000000000000 : ℝ)) (c := (417728791759 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_9 : cellLeft 9 / (cellLeft 9 - 1) ≤ cellLevel 9 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1571 / 1140 : ℝ)) (pr := (473 / 342 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (283938870911 / 250000000000 : ℝ)) (c := (210723720223 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_10 : cellLeft 10 / (cellLeft 10 - 1) ≤ cellLevel 10 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (473 / 342 : ℝ)) (pr := (4747 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (565844052837 / 500000000000 : ℝ)) (c := (425132457381 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_11 : cellLeft 11 / (cellLeft 11 - 1) ≤ cellLevel 11 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4747 / 3420 : ℝ)) (pr := (397 / 285 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1127649756011 / 1000000000000 : ℝ)) (c := (428784216927 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_12 : cellLeft 12 / (cellLeft 12 - 1) ≤ cellLevel 12 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (397 / 285 : ℝ)) (pr := (4781 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (561820062501 / 500000000000 : ℝ)) (c := (86480617777 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_13 : cellLeft 13 / (cellLeft 13 - 1) ≤ cellLevel 13 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4781 / 3420 : ℝ)) (pr := (2399 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (559829453693 / 500000000000 : ℝ)) (c := (21799471927 / 50000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_14 : cellLeft 14 / (cellLeft 14 - 1) ≤ cellLevel 14 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2399 / 1710 : ℝ)) (pr := (107 / 76 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1115705802209 / 1000000000000 : ℝ)) (c := (439543626713 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_15 : cellLeft 15 / (cellLeft 15 - 1) ≤ cellLevel 15 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (107 / 76 : ℝ)) (pr := (1208 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (277945128189 / 250000000000 : ℝ)) (c := (443066009811 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_16 : cellLeft 16 / (cellLeft 16 - 1) ≤ cellLevel 16 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1208 / 855 : ℝ)) (pr := (4849 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1107882746471 / 1000000000000 : ℝ)) (c := (446556939873 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_17 : cellLeft 17 / (cellLeft 17 - 1) ≤ cellLevel 17 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4849 / 3420 : ℝ)) (pr := (811 / 570 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (552006107443 / 500000000000 : ℝ)) (c := (450016764623 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_18 : cellLeft 18 / (cellLeft 18 - 1) ≤ cellLevel 18 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (811 / 570 : ℝ)) (pr := (257 / 180 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (68760539597 / 62500000000 : ℝ)) (c := (90689165503 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_19 : cellLeft 19 / (cellLeft 19 - 1) ≤ cellLevel 19 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (257 / 180 : ℝ)) (pr := (245 / 171 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1096351721967 / 1000000000000 : ℝ)) (c := (91368893557 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_20 : cellLeft 20 / (cellLeft 20 - 1) ≤ cellLevel 20 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (245 / 171 : ℝ)) (pr := (1639 / 1140 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (218512240701 / 200000000000 : ℝ)) (c := (460213020501 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_21 : cellLeft 21 / (cellLeft 21 - 1) ≤ cellLevel 21 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1639 / 1140 : ℝ)) (pr := (2467 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (544398402679 / 500000000000 : ℝ)) (c := (463551816607 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_22 : cellLeft 22 / (cellLeft 22 - 1) ≤ cellLevel 22 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2467 / 1710 : ℝ)) (pr := (4951 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (54252912923 / 50000000000 : ℝ)) (c := (233430591487 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_23 : cellLeft 23 / (cellLeft 23 - 1) ≤ cellLevel 23 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (4951 / 3420 : ℝ)) (pr := (138 / 95 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1081345297431 / 1000000000000 : ℝ)) (c := (9402828849 / 20000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_24 : cellLeft 24 / (cellLeft 24 - 1) ≤ cellLevel 24 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (138 / 95 : ℝ)) (pr := (997 / 684 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1077657660509 / 1000000000000 : ℝ)) (c := (236696456951 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_25 : cellLeft 25 / (cellLeft 25 - 1) ≤ cellLevel 25 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (997 / 684 : ℝ)) (pr := (2501 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1073995089491 / 1000000000000 : ℝ)) (c := (29788494517 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_26 : cellLeft 26 / (cellLeft 26 - 1) ≤ cellLevel 26 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2501 / 1710 : ℝ)) (pr := (1673 / 1140 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (535178664837 / 500000000000 : ℝ)) (c := (479810748613 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_27 : cellLeft 27 / (cellLeft 27 - 1) ≤ cellLevel 27 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1673 / 1140 : ℝ)) (pr := (1259 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1066744129793 / 1000000000000 : ℝ)) (c := (482977730149 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_28 : cellLeft 28 / (cellLeft 28 - 1) ≤ cellLevel 28 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1259 / 855 : ℝ)) (pr := (5053 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (531577620981 / 500000000000 : ℝ)) (c := (486117160311 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_29 : cellLeft 29 / (cellLeft 29 - 1) ≤ cellLevel 29 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5053 / 3420 : ℝ)) (pr := (169 / 114 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (132448802703 / 125000000000 : ℝ)) (c := (122307334697 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_30 : cellLeft 30 / (cellLeft 30 - 1) ≤ cellLevel 30 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (169 / 114 : ℝ)) (pr := (5087 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1056049427489 / 1000000000000 : ℝ)) (c := (492314561571 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_31 : cellLeft 31 / (cellLeft 31 - 1) ≤ cellLevel 31 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5087 / 3420 : ℝ)) (pr := (1276 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (26313300537 / 25000000000 : ℝ)) (c := (123843280251 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_32 : cellLeft 32 / (cellLeft 32 - 1) ≤ cellLevel 32 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1276 / 855 : ℝ)) (pr := (569 / 380 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (209807593737 / 200000000000 : ℝ)) (c := (249202652909 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_33 : cellLeft 33 / (cellLeft 33 - 1) ≤ cellLevel 33 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (569 / 380 : ℝ)) (pr := (2569 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (522783518649 / 500000000000 : ℝ)) (c := (501411401189 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_34 : cellLeft 34 / (cellLeft 34 - 1) ≤ cellLevel 34 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2569 / 1710 : ℝ)) (pr := (1031 / 684 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1042118998571 / 1000000000000 : ℝ)) (c := (504391688773 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_35 : cellLeft 35 / (cellLeft 35 - 1) ≤ cellLevel 35 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1031 / 684 : ℝ)) (pr := (431 / 285 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (519346813383 / 500000000000 : ℝ)) (c := (15854576461 / 31250000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_36 : cellLeft 36 / (cellLeft 36 - 1) ≤ cellLevel 36 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (431 / 285 : ℝ)) (pr := (5189 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1035290699101 / 1000000000000 : ℝ)) (c := (510275949881 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_37 : cellLeft 37 / (cellLeft 37 - 1) ≤ cellLevel 37 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5189 / 3420 : ℝ)) (pr := (137 / 90 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (128988749463 / 125000000000 : ℝ)) (c := (513180469529 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_38 : cellLeft 38 / (cellLeft 38 - 1) ≤ cellLevel 38 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (137 / 90 : ℝ)) (pr := (1741 / 1140 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1028551299567 / 1000000000000 : ℝ)) (c := (516060273719 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_39 : cellLeft 39 / (cellLeft 39 - 1) ≤ cellLevel 39 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1741 / 1140 : ℝ)) (pr := (262 / 171 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (205042879299 / 200000000000 : ℝ)) (c := (259457813589 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_40 : cellLeft 40 / (cellLeft 40 - 1) ≤ cellLevel 40 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (262 / 171 : ℝ)) (pr := (5257 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1021899075069 / 1000000000000 : ℝ)) (c := (521746791369 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_41 : cellLeft 41 / (cellLeft 41 - 1) ≤ cellLevel 41 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5257 / 3420 : ℝ)) (pr := (293 / 190 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (101860512659 / 100000000000 : ℝ)) (c := (26227701227 / 50000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_42 : cellLeft 42 / (cellLeft 42 - 1) ≤ cellLevel 42 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (293 / 190 : ℝ)) (pr := (5291 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (507666172523 / 500000000000 : ℝ)) (c := (263668790881 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_43 : cellLeft 43 / (cellLeft 43 - 1) ≤ cellLevel 43 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5291 / 3420 : ℝ)) (pr := (1327 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (50604026353 / 50000000000 : ℝ)) (c := (265048857487 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_44 : cellLeft 44 / (cellLeft 44 - 1) ≤ cellLevel 44 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1327 / 855 : ℝ)) (pr := (355 / 228 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1008849471857 / 1000000000000 : ℝ)) (c := (266417336507 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_45 : cellLeft 45 / (cellLeft 45 - 1) ≤ cellLevel 45 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (355 / 228 : ℝ)) (pr := (2671 / 1710 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (251409745303 / 250000000000 : ℝ)) (c := (535548701669 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_46 : cellLeft 46 / (cellLeft 46 - 1) ≤ cellLevel 46 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2671 / 1710 : ℝ)) (pr := (5359 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (1002448859421 / 1000000000000 : ℝ)) (c := (134560010927 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_47 : cellLeft 47 / (cellLeft 47 - 1) ≤ cellLevel 47 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5359 / 3420 : ℝ)) (pr := (448 / 285 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (999278913251 / 1000000000000 : ℝ)) (c := (540908938923 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_48 : cellLeft 48 / (cellLeft 48 - 1) ≤ cellLevel 48 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (448 / 285 : ℝ)) (pr := (5393 / 3420 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (996128951907 / 1000000000000 : ℝ)) (c := (543555624171 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_49 : cellLeft 49 / (cellLeft 49 - 1) ≤ cellLevel 49 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5393 / 3420 : ℝ)) (pr := (541 / 342 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (496499393497 / 500000000000 : ℝ)) (c := (273090166701 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_50 : cellLeft 50 / (cellLeft 50 - 1) ≤ cellLevel 50 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (541 / 342 : ℝ)) (pr := (603 / 380 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (494944116237 / 500000000000 : ℝ)) (c := (54878329771 / 100000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_51 : cellLeft 51 / (cellLeft 51 - 1) ≤ cellLevel 51 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (603 / 380 : ℝ)) (pr := (1361 / 855 : ℝ)) (κ := (9 / 10 : ℝ)) (θ := (246699276159 / 250000000000 : ℝ)) (c := (551364745359 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_52 : cellLeft 52 / (cellLeft 52 - 1) ≤ cellLevel 52 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1361 / 855 : ℝ)) (pr := (5461 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (491862611027 / 500000000000 : ℝ)) (c := (138481225457 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_53 : cellLeft 53 / (cellLeft 53 - 1) ≤ cellLevel 53 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5461 / 3420 : ℝ)) (pr := (913 / 570 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (245168101389 / 250000000000 : ℝ)) (c := (6955799873 / 12500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_54 : cellLeft 54 / (cellLeft 54 - 1) ≤ cellLevel 54 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (913 / 570 : ℝ)) (pr := (1099 / 684 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (977638478187 / 1000000000000 : ℝ)) (c := (558982229403 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_55 : cellLeft 55 / (cellLeft 55 - 1) ≤ cellLevel 55 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1099 / 684 : ℝ)) (pr := (1378 / 855 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (974623265173 / 1000000000000 : ℝ)) (c := (561479837847 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_56 : cellLeft 56 / (cellLeft 56 - 1) ≤ cellLevel 56 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1378 / 855 : ℝ)) (pr := (97 / 60 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (971626593893 / 1000000000000 : ℝ)) (c := (140989257463 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_57 : cellLeft 57 / (cellLeft 57 - 1) ≤ cellLevel 57 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (97 / 60 : ℝ)) (pr := (2773 / 1710 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (12108103673 / 12500000000 : ℝ)) (c := (566414017489 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_58 : cellLeft 58 / (cellLeft 58 - 1) ≤ cellLevel 58 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2773 / 1710 : ℝ)) (pr := (5563 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (965688196591 / 1000000000000 : ℝ)) (c := (284425505127 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_59 : cellLeft 59 / (cellLeft 59 - 1) ≤ cellLevel 59 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5563 / 3420 : ℝ)) (pr := (31 / 19 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (962746135777 / 1000000000000 : ℝ)) (c := (71408526887 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_60 : cellLeft 60 / (cellLeft 60 - 1) ≤ cellLevel 60 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (31 / 19 : ℝ)) (pr := (5597 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (959821947049 / 1000000000000 : ℝ)) (c := (573665836457 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_61 : cellLeft 61 / (cellLeft 61 - 1) ≤ cellLevel 61 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5597 / 3420 : ℝ)) (pr := (2807 / 1710 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (956915468051 / 1000000000000 : ℝ)) (c := (288022038151 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_62 : cellLeft 62 / (cellLeft 62 - 1) ≤ cellLevel 62 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2807 / 1710 : ℝ)) (pr := (1877 / 1140 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (954026538383 / 1000000000000 : ℝ)) (c := (72300391769 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_63 : cellLeft 63 / (cellLeft 63 - 1) ≤ cellLevel 63 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1877 / 1140 : ℝ)) (pr := (1412 / 855 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (951154999581 / 1000000000000 : ℝ)) (c := (580743207117 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_64 : cellLeft 64 / (cellLeft 64 - 1) ≤ cellLevel 64 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1412 / 855 : ℝ)) (pr := (1133 / 684 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (948300695081 / 1000000000000 : ℝ)) (c := (583064489923 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_65 : cellLeft 65 / (cellLeft 65 - 1) ≤ cellLevel 65 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1133 / 684 : ℝ)) (pr := (947 / 570 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (945463470193 / 1000000000000 : ℝ)) (c := (73170896869 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_66 : cellLeft 66 / (cellLeft 66 - 1) ≤ cellLevel 66 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (947 / 570 : ℝ)) (pr := (5699 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (117830396509 / 125000000000 : ℝ)) (c := (117530290453 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_67 : cellLeft 67 / (cellLeft 67 - 1) ≤ cellLevel 67 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5699 / 3420 : ℝ)) (pr := (1429 / 855 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (939839649691 / 1000000000000 : ℝ)) (c := (14747937741 / 25000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_68 : cellLeft 68 / (cellLeft 68 - 1) ≤ cellLevel 68 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1429 / 855 : ℝ)) (pr := (637 / 380 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (937052753817 / 1000000000000 : ℝ)) (c := (592165532591 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_69 : cellLeft 69 / (cellLeft 69 - 1) ≤ cellLevel 69 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (637 / 380 : ℝ)) (pr := (575 / 342 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (46714116849 / 50000000000 : ℝ)) (c := (594395704409 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_70 : cellLeft 70 / (cellLeft 70 - 1) ≤ cellLevel 70 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (575 / 342 : ℝ)) (pr := (5767 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (116441031681 / 125000000000 : ℝ)) (c := (149152051547 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_71 : cellLeft 71 / (cellLeft 71 - 1) ≤ cellLevel 71 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5767 / 3420 : ℝ)) (pr := (482 / 285 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (232197589801 / 250000000000 : ℝ)) (c := (11976064337 / 20000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_72 : cellLeft 72 / (cellLeft 72 - 1) ≤ cellLevel 72 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (482 / 285 : ℝ)) (pr := (5801 / 3420 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (463034255959 / 500000000000 : ℝ)) (c := (600980913179 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_73 : cellLeft 73 / (cellLeft 73 - 1) ≤ cellLevel 73 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5801 / 3420 : ℝ)) (pr := (2909 / 1710 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (230840642731 / 250000000000 : ℝ)) (c := (120628293969 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_74 : cellLeft 74 / (cellLeft 74 - 1) ≤ cellLevel 74 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2909 / 1710 : ℝ)) (pr := (389 / 228 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (184134479439 / 200000000000 : ℝ)) (c := (151321264859 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_75 : cellLeft 75 / (cellLeft 75 - 1) ≤ cellLevel 75 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (389 / 228 : ℝ)) (pr := (77 / 45 : ℝ)) (κ := (4 / 5 : ℝ)) (θ := (917997853321 / 1000000000000 : ℝ)) (c := (607411852479 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_76 : cellLeft 76 / (cellLeft 76 - 1) ≤ cellLevel 76 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (77 / 45 : ℝ)) (pr := (5869 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (457669401741 / 500000000000 : ℝ)) (c := (152380504369 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_77 : cellLeft 77 / (cellLeft 77 - 1) ≤ cellLevel 77 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5869 / 3420 : ℝ)) (pr := (327 / 190 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (228173778357 / 250000000000 : ℝ)) (c := (611615720923 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_78 : cellLeft 78 / (cellLeft 78 - 1) ≤ cellLevel 78 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (327 / 190 : ℝ)) (pr := (5903 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (182013330091 / 200000000000 : ℝ)) (c := (613693127343 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_79 : cellLeft 79 / (cellLeft 79 - 1) ≤ cellLevel 79 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5903 / 3420 : ℝ)) (pr := (296 / 171 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (113431660423 / 125000000000 : ℝ)) (c := (76969299913 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_80 : cellLeft 80 / (cellLeft 80 - 1) ≤ cellLevel 80 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (296 / 171 : ℝ)) (pr := (1979 / 1140 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (904854882539 / 1000000000000 : ℝ)) (c := (617799697451 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_81 : cellLeft 81 / (cellLeft 81 - 1) ≤ cellLevel 81 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1979 / 1140 : ℝ)) (pr := (2977 / 1710 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (225567829931 / 250000000000 : ℝ)) (c := (154957295133 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_82 : cellLeft 82 / (cellLeft 82 - 1) ≤ cellLevel 82 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2977 / 1710 : ℝ)) (pr := (5971 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (449851234101 / 500000000000 : ℝ)) (c := (310921502709 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_83 : cellLeft 83 / (cellLeft 83 - 1) ≤ cellLevel 83 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (5971 / 3420 : ℝ)) (pr := (499 / 285 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (448574101339 / 500000000000 : ℝ)) (c := (623841327129 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_84 : cellLeft 84 / (cellLeft 84 - 1) ≤ cellLevel 84 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (499 / 285 : ℝ)) (pr := (1201 / 684 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (894608399273 / 1000000000000 : ℝ)) (c := (125164859773 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_85 : cellLeft 85 / (cellLeft 85 - 1) ≤ cellLevel 85 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1201 / 684 : ℝ)) (pr := (3011 / 1710 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (892082935509 / 1000000000000 : ℝ)) (c := (627792072019 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_86 : cellLeft 86 / (cellLeft 86 - 1) ≤ cellLevel 86 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (3011 / 1710 : ℝ)) (pr := (671 / 380 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (444785845143 / 500000000000 : ℝ)) (c := (629744796209 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_87 : cellLeft 87 / (cellLeft 87 - 1) ≤ cellLevel 87 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (671 / 380 : ℝ)) (pr := (1514 / 855 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (887074543863 / 1000000000000 : ℝ)) (c := (6316826193 / 10000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_88 : cellLeft 88 / (cellLeft 88 - 1) ≤ cellLevel 88 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1514 / 855 : ℝ)) (pr := (6073 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (442295688921 / 500000000000 : ℝ)) (c := (633605687421 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_89 : cellLeft 89 / (cellLeft 89 - 1) ≤ cellLevel 89 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6073 / 3420 : ℝ)) (pr := (203 / 114 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (176424415029 / 200000000000 : ℝ)) (c := (635514144999 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_90 : cellLeft 90 / (cellLeft 90 - 1) ≤ cellLevel 90 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (203 / 114 : ℝ)) (pr := (6107 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (879666519999 / 1000000000000 : ℝ)) (c := (39838008423 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_91 : cellLeft 91 / (cellLeft 91 - 1) ≤ cellLevel 91 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6107 / 3420 : ℝ)) (pr := (1531 / 855 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (219306149479 / 250000000000 : ℝ)) (c := (639287797803 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_92 : cellLeft 92 / (cellLeft 92 - 1) ≤ cellLevel 92 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1531 / 855 : ℝ)) (pr := (2047 / 1140 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (437398097837 / 500000000000 : ℝ)) (c := (641153273537 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_93 : cellLeft 93 / (cellLeft 93 - 1) ≤ cellLevel 93 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2047 / 1140 : ℝ)) (pr := (3079 / 1710 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (174476240261 / 200000000000 : ℝ)) (c := (643004699777 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_94 : cellLeft 94 / (cellLeft 94 - 1) ≤ cellLevel 94 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (3079 / 1710 : ℝ)) (pr := (65 / 36 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (869979504071 / 1000000000000 : ℝ)) (c := (644842212737 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_95 : cellLeft 95 / (cellLeft 95 - 1) ≤ cellLevel 95 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (65 / 36 : ℝ)) (pr := (172 / 95 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (17351819889 / 20000000000 : ℝ)) (c := (80833243381 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_96 : cellLeft 96 / (cellLeft 96 - 1) ≤ cellLevel 96 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (172 / 95 : ℝ)) (pr := (6209 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (432607782061 / 500000000000 : ℝ)) (c := (324238017893 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_97 : cellLeft 97 / (cellLeft 97 - 1) ≤ cellLevel 97 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6209 / 3420 : ℝ)) (pr := (3113 / 1710 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (862853105949 / 1000000000000 : ℝ)) (c := (130054522097 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_98 : cellLeft 98 / (cellLeft 98 - 1) ≤ cellLevel 98 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (3113 / 1710 : ℝ)) (pr := (2081 / 1140 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (860503513957 / 1000000000000 : ℝ)) (c := (40753487573 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_99 : cellLeft 99 / (cellLeft 99 - 1) ≤ cellLevel 99 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2081 / 1140 : ℝ)) (pr := (313 / 171 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (13408854427 / 15625000000 : ℝ)) (c := (326912868177 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_100 : cellLeft 100 / (cellLeft 100 - 1) ≤ cellLevel 100 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (313 / 171 : ℝ)) (pr := (6277 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (855842510377 / 1000000000000 : ℝ)) (c := (40973908943 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_101 : cellLeft 101 / (cellLeft 101 - 1) ≤ cellLevel 101 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6277 / 3420 : ℝ)) (pr := (1049 / 570 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (426765446269 / 500000000000 : ℝ)) (c := (328663173477 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_102 : cellLeft 102 / (cellLeft 102 - 1) ≤ cellLevel 102 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1049 / 570 : ℝ)) (pr := (6311 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (851231728353 / 1000000000000 : ℝ)) (c := (131811454419 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_103 : cellLeft 103 / (cellLeft 103 - 1) ≤ cellLevel 103 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6311 / 3420 : ℝ)) (pr := (1582 / 855 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (212236229363 / 250000000000 : ℝ)) (c := (165193860309 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_104 : cellLeft 104 / (cellLeft 104 - 1) ≤ cellLevel 104 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1582 / 855 : ℝ)) (pr := (141 / 76 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (846670360541 / 1000000000000 : ℝ)) (c := (662480975697 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_105 : cellLeft 105 / (cellLeft 105 - 1) ≤ cellLevel 105 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (141 / 76 : ℝ)) (pr := (3181 / 1710 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (844407959389 / 1000000000000 : ℝ)) (c := (664173995413 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_106 : cellLeft 106 / (cellLeft 106 - 1) ≤ cellLevel 106 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (3181 / 1710 : ℝ)) (pr := (6379 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (842157616811 / 1000000000000 : ℝ)) (c := (83231827369 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_107 : cellLeft 107 / (cellLeft 107 - 1) ≤ cellLevel 107 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6379 / 3420 : ℝ)) (pr := (533 / 285 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (839919236653 / 1000000000000 : ℝ)) (c := (41720185221 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_108 : cellLeft 108 / (cellLeft 108 - 1) ≤ cellLevel 108 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (533 / 285 : ℝ)) (pr := (6413 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (167538544757 / 200000000000 : ℝ)) (c := (669179145051 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_109 : cellLeft 109 / (cellLeft 109 - 1) ≤ cellLevel 109 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6413 / 3420 : ℝ)) (pr := (643 / 342 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (10443474801 / 12500000000 : ℝ)) (c := (670823278071 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_110 : cellLeft 110 / (cellLeft 110 - 1) ≤ cellLevel 110 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (643 / 342 : ℝ)) (pr := (2149 / 1140 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (208318731101 / 250000000000 : ℝ)) (c := (336227737937 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_111 : cellLeft 111 / (cellLeft 111 - 1) ≤ cellLevel 111 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (2149 / 1140 : ℝ)) (pr := (1616 / 855 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (207770863151 / 250000000000 : ℝ)) (c := (134815170091 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_112 : cellLeft 112 / (cellLeft 112 - 1) ≤ cellLevel 112 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1616 / 855 : ℝ)) (pr := (6481 / 3420 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (828903477493 / 1000000000000 : ℝ)) (c := (21115141017 / 31250000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_113 : cellLeft 113 / (cellLeft 113 - 1) ≤ cellLevel 113 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (6481 / 3420 : ℝ)) (pr := (19 / 10 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (826734908839 / 1000000000000 : ℝ)) (c := (677281571627 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_114 : cellLeft 114 / (cellLeft 114 - 1) ≤ cellLevel 114 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (19 / 10 : ℝ)) (pr := (381 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (412282500471 / 500000000000 : ℝ)) (c := (42429776813 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_115 : cellLeft 115 / (cellLeft 115 - 1) ≤ cellLevel 115 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (381 / 200 : ℝ)) (pr := (191 / 100 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (822406453819 / 1000000000000 : ℝ)) (c := (136091952987 / 200000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_116 : cellLeft 116 / (cellLeft 116 - 1) ≤ cellLevel 116 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (191 / 100 : ℝ)) (pr := (383 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (410129589241 / 500000000000 : ℝ)) (c := (68203168711 / 100000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_117 : cellLeft 117 / (cellLeft 117 - 1) ≤ cellLevel 117 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (383 / 200 : ℝ)) (pr := (48 / 25 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (102265385859 / 125000000000 : ℝ)) (c := (85449037753 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_118 : cellLeft 118 / (cellLeft 118 - 1) ≤ cellLevel 118 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (48 / 25 : ℝ)) (pr := (77 / 40 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (815998091841 / 1000000000000 : ℝ)) (c := (685141714969 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_119 : cellLeft 119 / (cellLeft 119 - 1) ≤ cellLevel 119 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (77 / 40 : ℝ)) (pr := (193 / 100 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (813884107147 / 1000000000000 : ℝ)) (c := (85835003757 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_120 : cellLeft 120 / (cellLeft 120 - 1) ≤ cellLevel 120 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (193 / 100 : ℝ)) (pr := (387 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (811781047439 / 1000000000000 : ℝ)) (c := (172051837557 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_121 : cellLeft 121 / (cellLeft 121 - 1) ≤ cellLevel 121 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (387 / 200 : ℝ)) (pr := (97 / 50 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (202422207061 / 250000000000 : ℝ)) (c := (689723777279 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_122 : cellLeft 122 / (cellLeft 122 - 1) ≤ cellLevel 122 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (97 / 50 : ℝ)) (pr := (389 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (807607365961 / 1000000000000 : ℝ)) (c := (345614705931 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_123 : cellLeft 123 / (cellLeft 123 - 1) ≤ cellLevel 123 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (389 / 200 : ℝ)) (pr := (39 / 20 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (805536577843 / 1000000000000 : ℝ)) (c := (69272435351 / 100000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_124 : cellLeft 124 / (cellLeft 124 - 1) ≤ cellLevel 124 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (39 / 20 : ℝ)) (pr := (391 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (100434547749 / 125000000000 : ℝ)) (c := (86776087581 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_125 : cellLeft 125 / (cellLeft 125 - 1) ≤ cellLevel 125 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (391 / 200 : ℝ)) (pr := (49 / 25 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (6261146073 / 7812500000 : ℝ)) (c := (173920637651 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_126 : cellLeft 126 / (cellLeft 126 - 1) ≤ cellLevel 126 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (49 / 25 : ℝ)) (pr := (393 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (799387443661 / 1000000000000 : ℝ)) (c := (69714599963 / 100000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_127 : cellLeft 127 / (cellLeft 127 - 1) ≤ cellLevel 127 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (393 / 200 : ℝ)) (pr := (197 / 100 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (9966981769 / 12500000000 : ℝ)) (c := (174649785727 / 250000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_128 : cellLeft 128 / (cellLeft 128 - 1) ≤ cellLevel 128 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (197 / 100 : ℝ)) (pr := (79 / 40 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (795339912301 / 1000000000000 : ℝ)) (c := (70004207457 / 100000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_129 : cellLeft 129 / (cellLeft 129 - 1) ≤ cellLevel 129 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (79 / 40 : ℝ)) (pr := (99 / 50 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (793331478179 / 1000000000000 : ℝ)) (c := (701474887707 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_130 : cellLeft 130 / (cellLeft 130 - 1) ≤ cellLevel 130 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (99 / 50 : ℝ)) (pr := (1981 / 1000 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (792931007973 / 1000000000000 : ℝ)) (c := (701760244231 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_131 : cellLeft 131 / (cellLeft 131 - 1) ≤ cellLevel 131 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1981 / 1000 : ℝ)) (pr := (991 / 500 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (396265470937 / 500000000000 : ℝ)) (c := (43877825027 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_132 : cellLeft 132 / (cellLeft 132 - 1) ≤ cellLevel 132 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (991 / 500 : ℝ)) (pr := (1983 / 1000 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (792131279271 / 1000000000000 : ℝ)) (c := (702329757039 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_133 : cellLeft 133 / (cellLeft 133 - 1) ≤ cellLevel 133 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1983 / 1000 : ℝ)) (pr := (248 / 125 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (791732019553 / 1000000000000 : ℝ)) (c := (702613914781 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_134 : cellLeft 134 / (cellLeft 134 - 1) ≤ cellLevel 134 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (248 / 125 : ℝ)) (pr := (397 / 200 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (791333162113 / 1000000000000 : ℝ)) (c := (43931104649 / 62500000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_135 : cellLeft 135 / (cellLeft 135 - 1) ≤ cellLevel 135 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (397 / 200 : ℝ)) (pr := (993 / 500 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (790934706341 / 1000000000000 : ℝ)) (c := (28127241463 / 40000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_136 : cellLeft 136 / (cellLeft 136 - 1) ≤ cellLevel 136 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (993 / 500 : ℝ)) (pr := (1987 / 1000 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (790536651633 / 1000000000000 : ℝ)) (c := (28138560083 / 40000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_137 : cellLeft 137 / (cellLeft 137 - 1) ≤ cellLevel 137 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1987 / 1000 : ℝ)) (pr := (497 / 250 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (790138997381 / 1000000000000 : ℝ)) (c := (703746571609 / 1000000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_138 : cellLeft 138 / (cellLeft 138 - 1) ≤ cellLevel 138 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (497 / 250 : ℝ)) (pr := (1989 / 1000 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (789741742983 / 1000000000000 : ℝ)) (c := (88003593237 / 125000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cell_139 : cellLeft 139 / (cellLeft 139 - 1) ≤ cellLevel 139 - 2 / 10 ^ 6 :=
  cell_of_bounds (pl := (1989 / 1000 : ℝ)) (pr := (199 / 100 : ℝ)) (κ := (13 / 20 : ℝ)) (θ := (197336221959 / 250000000000 : ℝ)) (c := (352155262827 / 500000000000 : ℝ))
    (by norm_num [cellLeft]) (by norm_num [cellRight, cellLeft]) (by norm_num [cellKappa]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Numeric2

/-- C19c, Prop. 10: at the six exact rational failure points of logs/bracket_upper_arb.log, `Γ - e < -1.15·10⁻⁶` at
`s = s₊`, and `< -5.7·10⁻⁵` at `p = 9/5`. The type is exactly `C19c_bracket_points` of Statements.lean. -/
theorem bracket_points :
    (∀ r ∈ ([(7 / 5, 52989 / 10000, 110877 / 500000, 2144519 / 1000000),
             (3 / 2, 1583 / 400, 49177 / 100000, 1768641 / 1000000),
             (8 / 5, 15901 / 5000, 837049 / 1000000, 613161 / 500000), (17 / 10, 1077 / 400, 298409 / 250000, 0),
             (9 / 5, 23767 / 10000, 613873 / 500000, 0), (19 / 10, 21591 / 10000, 625363 / 500000, 0)] :
             List (ℝ × ℝ × ℝ × ℝ)),
        r.2.2.2 ∈ Icc (-π) π ∧ Gam r.1 r.2.1 r.2.2.1 r.2.2.2 - ee r.1 r.2.2.2 < -(115 / 10 ^ 8)) ∧
      Gam (9 / 5) (23767 / 10000) (613873 / 500000) 0 - ee (9 / 5) 0 < -(57 / 10 ^ 6) := by
  have h3 := pi_gt_three
  refine ⟨?_, Numeric2.point_9_5⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_7_5⟩
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_3_2⟩
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_8_5⟩
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_17_10⟩
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_9_5.trans (by norm_num)⟩
  · exact ⟨⟨by linarith, by linarith⟩, Numeric2.point_19_10⟩

/-- C20b: every cell's level (minus `2·10⁻⁶`) is at least `p/(p-1)` at the cell's left end. The type is exactly
`C20b_cells_contain_jag` of Statements.lean. -/
theorem cells_contain_jag :
    ∀ i : ℕ, i < 140 → cellLeft i / (cellLeft i - 1) ≤ cellLevel i - 2 / 10 ^ 6 := by
  intro i hi
  interval_cases i
  · exact Numeric2.cell_0
  · exact Numeric2.cell_1
  · exact Numeric2.cell_2
  · exact Numeric2.cell_3
  · exact Numeric2.cell_4
  · exact Numeric2.cell_5
  · exact Numeric2.cell_6
  · exact Numeric2.cell_7
  · exact Numeric2.cell_8
  · exact Numeric2.cell_9
  · exact Numeric2.cell_10
  · exact Numeric2.cell_11
  · exact Numeric2.cell_12
  · exact Numeric2.cell_13
  · exact Numeric2.cell_14
  · exact Numeric2.cell_15
  · exact Numeric2.cell_16
  · exact Numeric2.cell_17
  · exact Numeric2.cell_18
  · exact Numeric2.cell_19
  · exact Numeric2.cell_20
  · exact Numeric2.cell_21
  · exact Numeric2.cell_22
  · exact Numeric2.cell_23
  · exact Numeric2.cell_24
  · exact Numeric2.cell_25
  · exact Numeric2.cell_26
  · exact Numeric2.cell_27
  · exact Numeric2.cell_28
  · exact Numeric2.cell_29
  · exact Numeric2.cell_30
  · exact Numeric2.cell_31
  · exact Numeric2.cell_32
  · exact Numeric2.cell_33
  · exact Numeric2.cell_34
  · exact Numeric2.cell_35
  · exact Numeric2.cell_36
  · exact Numeric2.cell_37
  · exact Numeric2.cell_38
  · exact Numeric2.cell_39
  · exact Numeric2.cell_40
  · exact Numeric2.cell_41
  · exact Numeric2.cell_42
  · exact Numeric2.cell_43
  · exact Numeric2.cell_44
  · exact Numeric2.cell_45
  · exact Numeric2.cell_46
  · exact Numeric2.cell_47
  · exact Numeric2.cell_48
  · exact Numeric2.cell_49
  · exact Numeric2.cell_50
  · exact Numeric2.cell_51
  · exact Numeric2.cell_52
  · exact Numeric2.cell_53
  · exact Numeric2.cell_54
  · exact Numeric2.cell_55
  · exact Numeric2.cell_56
  · exact Numeric2.cell_57
  · exact Numeric2.cell_58
  · exact Numeric2.cell_59
  · exact Numeric2.cell_60
  · exact Numeric2.cell_61
  · exact Numeric2.cell_62
  · exact Numeric2.cell_63
  · exact Numeric2.cell_64
  · exact Numeric2.cell_65
  · exact Numeric2.cell_66
  · exact Numeric2.cell_67
  · exact Numeric2.cell_68
  · exact Numeric2.cell_69
  · exact Numeric2.cell_70
  · exact Numeric2.cell_71
  · exact Numeric2.cell_72
  · exact Numeric2.cell_73
  · exact Numeric2.cell_74
  · exact Numeric2.cell_75
  · exact Numeric2.cell_76
  · exact Numeric2.cell_77
  · exact Numeric2.cell_78
  · exact Numeric2.cell_79
  · exact Numeric2.cell_80
  · exact Numeric2.cell_81
  · exact Numeric2.cell_82
  · exact Numeric2.cell_83
  · exact Numeric2.cell_84
  · exact Numeric2.cell_85
  · exact Numeric2.cell_86
  · exact Numeric2.cell_87
  · exact Numeric2.cell_88
  · exact Numeric2.cell_89
  · exact Numeric2.cell_90
  · exact Numeric2.cell_91
  · exact Numeric2.cell_92
  · exact Numeric2.cell_93
  · exact Numeric2.cell_94
  · exact Numeric2.cell_95
  · exact Numeric2.cell_96
  · exact Numeric2.cell_97
  · exact Numeric2.cell_98
  · exact Numeric2.cell_99
  · exact Numeric2.cell_100
  · exact Numeric2.cell_101
  · exact Numeric2.cell_102
  · exact Numeric2.cell_103
  · exact Numeric2.cell_104
  · exact Numeric2.cell_105
  · exact Numeric2.cell_106
  · exact Numeric2.cell_107
  · exact Numeric2.cell_108
  · exact Numeric2.cell_109
  · exact Numeric2.cell_110
  · exact Numeric2.cell_111
  · exact Numeric2.cell_112
  · exact Numeric2.cell_113
  · exact Numeric2.cell_114
  · exact Numeric2.cell_115
  · exact Numeric2.cell_116
  · exact Numeric2.cell_117
  · exact Numeric2.cell_118
  · exact Numeric2.cell_119
  · exact Numeric2.cell_120
  · exact Numeric2.cell_121
  · exact Numeric2.cell_122
  · exact Numeric2.cell_123
  · exact Numeric2.cell_124
  · exact Numeric2.cell_125
  · exact Numeric2.cell_126
  · exact Numeric2.cell_127
  · exact Numeric2.cell_128
  · exact Numeric2.cell_129
  · exact Numeric2.cell_130
  · exact Numeric2.cell_131
  · exact Numeric2.cell_132
  · exact Numeric2.cell_133
  · exact Numeric2.cell_134
  · exact Numeric2.cell_135
  · exact Numeric2.cell_136
  · exact Numeric2.cell_137
  · exact Numeric2.cell_138
  · exact Numeric2.cell_139

end P18
