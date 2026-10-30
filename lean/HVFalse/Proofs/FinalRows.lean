/-
  HVFalse/Proofs/FinalRows.lean - rows added at the final paper version (proofs only; imported only by Paper/Statements)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  C20e / C20a_full_given_cells (Prop. 11, l.575-582): for every cell and every s with 0 ≤ L(p_b) - s < 2·10⁻⁶ (the certificate's
  s_cell is such an s), p/(p-1) < s on the whole cell, in particular p_a/(p_a - 1) < s. From NewRows11b.frac_ge: the
  certified part of the window, (s - p/(p-1))/(sec²(π/2p) - p/(p-1)), is at least 16%, and the window has positive length.
  C08 zeros (Lemma lift, l.272-277): zw = g on the closed disc, so at a zero ζ of g with |ζ| = 1, z(ζ)w(ζ) = 0. Here
  w = ζ^k r e^{-Y/2} and z = B r e^{Y/2}, with ζ^k, e^{±Y/2} and B(ζ) nonzero (each Blaschke factor (ζ - a)/(1 - āζ),
  |a| < 1 = |ζ|, is nonzero), so r(ζ) = 0, hence z(ζ) = w(ζ) = 0 and G(z,w) = G(0,0) = 0.
  C19e (Prop. 10, l.546-548): s₀(p) < s₊(p) at the six p, from the proved failure points (no computer part).
  C13n (Prop. 8, l.454): the stated claim C13m (f violates (HV)) implies that (HV) with C = C_HV fails at (3/2, 3.98).
-/
import HVFalse.Proofs.Lift
import HVFalse.Proofs.NewRows11c
import HVFalse.Paper.ComputerChecked

open Real Set

namespace P18.FinalRows

theorem cellLeft_le_right {i : ℕ} (hi : i < 140) : cellLeft i ≤ cellRight i := by
  unfold cellRight cellLeft
  interval_cases i <;> norm_num

theorem cell_beyond_jag : ∀ i : ℕ, i < 140 → ∀ sc : ℝ, cellLevel i - sc < 2 / 10 ^ 6 → sc ≤ cellLevel i →
    cellLeft i / (cellLeft i - 1) < sc ∧ ∀ p ∈ Icc (cellLeft i) (cellRight i), p / (p - 1) < sc := by
  intro i hi sc hlev hle
  have key : ∀ p ∈ Icc (cellLeft i) (cellRight i), p / (p - 1) < sc := by
    intro p hp
    have hfrac := NewRows11b.frac_ge i hi p hp sc (by linarith) hle
    have hWp := NewRows11c.W_pos_cell hi hp
    rw [le_div_iff₀ hWp] at hfrac
    linarith
  exact ⟨key _ ⟨le_rfl, cellLeft_le_right hi⟩, key⟩

/-- Prop. 11 as printed: the computer part `C20a_cells` gives, for each cell, a rational `s_cell` with
`0 ≤ L(p_b) - s_cell < 2·10⁻⁶` and `s_cell > p_a/(p_a - 1)` (so `s_cell > p/(p-1)` on the cell) such that (HV) holds for
every `p` of the cell and every `s ∈ (0, s_cell]`. -/
theorem prop11_full (h : Paper.C20a_cells) : ∀ i : ℕ, i < 140 → ∃ sc : ℚ,
    0 ≤ cellLevel i - (sc : ℝ) ∧ cellLevel i - (sc : ℝ) < 2 / 10 ^ 6 ∧
      cellLeft i / (cellLeft i - 1) < (sc : ℝ) ∧ (∀ p ∈ Icc (cellLeft i) (cellRight i), p / (p - 1) < (sc : ℝ)) ∧
      ∀ p ∈ Icc (cellLeft i) (cellRight i), ∀ s : ℝ, 0 < s → s ≤ sc → HVIneqLp p s (hvConst p s) := by
  intro i hi
  obtain ⟨sc, hlev, hle, hhv⟩ := h i hi
  obtain ⟨ha, hcell⟩ := cell_beyond_jag i hi sc hlev hle
  exact ⟨sc, by linarith, hlev, ha, hcell, hhv⟩

theorem blaschke_ne_zero_of_norm_one {zs : List ℂ} (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    blaschke zs ζ ≠ 0 := by
  unfold blaschke
  rw [Ne, List.prod_eq_zero_iff, List.mem_map]
  rintro ⟨a, ha, h0⟩
  have hlt := (hzs a ha).2
  have h1 : ζ - a ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hζ
    linarith
  have h2 : 1 - (starRingEnd ℂ) a * ζ ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    have := congrArg norm h
    rw [norm_one, norm_mul, Complex.norm_conj, hζ, mul_one] at this
    linarith
  exact div_ne_zero h1 h2 h0

theorem G_zero_zero {p s : ℝ} (hp : 0 < p) (hs : 0 < s) : G p s 0 0 = 0 := by
  have hps : p / s ≠ 0 := (div_pos hp hs).ne'
  simp [G, Real.zero_rpow hp.ne', Real.zero_rpow hs.ne', Real.zero_rpow hps]

/-- At a zero `ζ` of `g` on `T`: `z(ζ) = w(ζ) = 0` and `G(z,w) = 0`, for the `z = B r e^{Y/2}`, `w = ζ^k r e^{-Y/2}` of C08. -/
theorem lift_zeros {p s : ℝ} (hp : 0 < p) (hs : 0 < s) {k : ℕ} {zs : List ℂ} (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1)
    {g r : ℂ → ℂ} {Y : Polynomial ℂ}
    (hprod : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) * (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = g ζ)
    (θ : ℝ) (hg : g (Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    let ζ := Complex.exp ((θ : ℂ) * Complex.I)
    blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2) = 0 ∧ ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2) = 0 ∧
      G p s (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = 0 := by
  intro ζ
  have hζ : ‖ζ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hmem : ζ ∈ Metric.closedBall (0 : ℂ) 1 := by simp [Metric.mem_closedBall, hζ]
  have hζ0 : ζ ≠ 0 := Complex.exp_ne_zero _
  have hB := blaschke_ne_zero_of_norm_one hzs hζ
  have h := hprod ζ hmem
  rw [hg] at h
  have hr : r ζ = 0 := by
    rcases mul_eq_zero.mp h with hz | hw
    · simpa [hB, Complex.exp_ne_zero] using hz
    · simpa [hζ0, Complex.exp_ne_zero] using hw
  have hz : blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2) = 0 := by simp [hr]
  have hw : ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2) = 0 := by simp [hr]
  exact ⟨hz, hw, by rw [hz, hw]; exact G_zero_zero hp hs⟩

theorem s0_lt_splus : ∀ r ∈ ([(7/5, 52989/10000), (3/2, 39575/10000), (8/5, 31802/10000), (17/10, 26925/10000),
    (9/5, 23767/10000), (19/10, 21591/10000)] : List (ℝ × ℝ)),
    ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar r.1 s ↔ s ≤ s0)) → s0 < r.2 := by
  have key : ∀ {p sp y t : ℝ}, t ∈ Icc (-π) π → Gam p sp y t < ee p t → 0 < sp →
      ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) → s0 < sp := by
    intro p sp y t ht hpt hsp s0 hiff
    by_contra hcon
    exact NewRows11.not_twoVar_of_point ht hpt ((hiff sp hsp).mpr (not_lt.mp hcon))
  have hpi := pi_gt_three
  have ht0 : (0 : ℝ) ∈ Icc (-π) π := ⟨by linarith, by linarith⟩
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key ⟨by linarith, by linarith⟩ Bracket.point_7_5 (by norm_num)
  · exact key ⟨by linarith, by linarith⟩ Bracket.point_3_2 (by norm_num)
  · exact key ⟨by linarith, by linarith⟩ Bracket.point_8_5 (by norm_num)
  · exact key ht0 Bracket.point_17_10 (by norm_num)
  · exact key ht0 Bracket.point_9_5 (by norm_num)
  · exact key ht0 Bracket.point_19_10 (by norm_num)

theorem violates_imp_fails (hm : Paper.C13m_explicit_violates) :
    ¬ HVIneqLp (3 / 2) (398 / 100) (hvConst (3 / 2) (398 / 100)) := by
  rintro hHV
  obtain ⟨f, g, h, -, -, -, hg, hh, hnot⟩ := hm
  exact hnot (hHV f g h hg hh)

end P18.FinalRows
