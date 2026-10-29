/-
  HVFalse/Proofs/NewRows11c.lean - rows R2-R4 (claims of the paper)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Notation j(p) = p/(p-1), W(p) = Ssec p - j(p) (antitone on (1,2): NewRows11b.W_antitone).
  R2 (Remark after Prop. 11, l.590-592): for a cell i ≥ 1 and p in it, level_i - j(p) ≤ level_i - j(p_b) = κ_i W(p_b)
     ≤ (9/10) W(cellLeft 2) ≤ 2.374 (W antitone, p_b ≥ cellLeft 2, κ ≤ 9/10), while level_0 - 2e-6 - 4 ≥ 2.413 (N4).
  R3 (l.590-594): s_cell from the box part, and s_cell - j(p) ≥ 0.16 W(p) > 0 (NewRows11b.frac_ge).
  R4 (Prop. 10, l.545): s₋ ≤ s₀ from the box part C19b_boxes; s₀ < s₊ from the proved failure points Bracket.point_*.
-/
import HVFalse.Proofs.NewRows11b
import HVFalse.Proofs.Bracket

open Real Set

namespace P18

namespace NewRows11c

theorem cellLeft_two_le {k : ℕ} (hk : 2 ≤ k) : cellLeft 2 ≤ cellLeft k := by
  have h2 : cellLeft 2 = 2297 / 1710 := by norm_num [cellLeft]
  rw [h2]
  unfold cellLeft
  split_ifs
  · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  · have : (0 : ℝ) ≤ ((k - 114 : ℕ) : ℝ) * (1 / 200) := by positivity
    linarith
  · have : (0 : ℝ) ≤ ((k - 130 : ℕ) : ℝ) * (1 / 1000) := by positivity
    linarith

/-- The window width is positive on every cell. -/
theorem W_pos_cell {i : ℕ} (hi : i < 140) {p : ℝ} (hp : p ∈ Icc (cellLeft i) (cellRight i)) :
    0 < Ssec p - p / (p - 1) := by
  have hab : cellLeft i ≤ cellRight i := hp.1.trans hp.2
  obtain ⟨hp1, hp2⟩ := BoxReductions.cell_p_bounds hi hp
  obtain ⟨hb1, hb2⟩ := BoxReductions.cell_p_bounds hi ⟨hab, le_rfl⟩
  exact lt_of_lt_of_le (NewRows11b.W_right_pos hi hab) (NewRows11b.W_antitone ⟨hp1, hp2⟩ ⟨hb1, hb2⟩ hp.2)

/-- R2 (Remark after Prop. 11, l.590-592): "the gain ... is largest near p = 4/3": on every later cell the gain over
`p/(p-1)` is below the first cell's certified gain over 4. -/
theorem gain_largest_first : ∀ i : ℕ, 1 ≤ i → i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i),
    cellLevel i - p / (p - 1) < cellLevel 0 - 2 / 10 ^ 6 - 4 := by
  intro i hi1 hi p hp
  have hab : cellLeft i ≤ cellRight i := hp.1.trans hp.2
  obtain ⟨hp1, hp2⟩ := BoxReductions.cell_p_bounds hi hp
  obtain ⟨hb1, hb2⟩ := BoxReductions.cell_p_bounds hi ⟨hab, le_rfl⟩
  have hjp : cellRight i / (cellRight i - 1) ≤ p / (p - 1) := CellMono.jag_antitone hp1 hp.2
  have hL : cellLevel i = cellRight i / (cellRight i - 1) +
      cellKappa i * (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) := rfl
  have hκ : cellKappa i ≤ 9 / 10 := by unfold cellKappa; split_ifs <;> norm_num
  have hWb := NewRows11b.W_right_pos hi hab
  have h2le : cellLeft 2 ≤ cellRight i := cellLeft_two_le (by omega : 2 ≤ i + 1)
  have h2 : cellLeft 2 = 2297 / 1710 := by norm_num [cellLeft]
  have h2mem : cellLeft 2 ∈ Ioo (1 : ℝ) 2 := by rw [h2]; constructor <;> norm_num
  have hWmono : Ssec (cellRight i) - cellRight i / (cellRight i - 1) ≤
      Ssec (cellLeft 2) - cellLeft 2 / (cellLeft 2 - 1) := NewRows11b.W_antitone h2mem ⟨hb1, hb2⟩ h2le
  rw [h2] at hWmono
  have hS2 : Ssec (2297 / 1710) ≤ (6551 / 1000 : ℝ) := NewRows11bCells.pt_2.2.trans (by norm_num)
  have hj2 : (2297 / 1710 : ℝ) / (2297 / 1710 - 1) = 2297 / 587 := by norm_num
  rw [hj2] at hWmono
  have h0 := NewRows11.first_cell.1
  have hκW : cellKappa i * (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) ≤
      9 / 10 * (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) := mul_le_mul_of_nonneg_right hκ hWb.le
  rw [hL]
  linarith

/-- R3 (Remark after Prop. 11, l.590-594; box part as a hypothesis): on every cell (eq:two) holds at some `s > p/(p-1)`. -/
theorem beyond_jag (hb : Paper.C20a_boxes) : ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i),
    ∃ s : ℝ, p / (p - 1) < s ∧ TwoVar p s := by
  intro i hi p hp
  obtain ⟨sc, hlev, hle, htwo⟩ := hb i hi
  refine ⟨sc, ?_, htwo p hp⟩
  have hfrac := NewRows11b.frac_ge i hi p hp sc (by linarith) hle
  have hWp := W_pos_cell hi hp
  rw [le_div_iff₀ hWp] at hfrac
  linarith

/-- R4 (Prop. 10, l.545; the `s₋` side from the box part): `s₋(p) ≤ s₀(p) < s₊(p)` at the six `p` of the table. -/
theorem bracket_s0 (hb : Paper.C19b_boxes) : ∀ r ∈ ([(7/5, 52986/10000, 52989/10000), (3/2, 39572/10000, 39575/10000),
    (8/5, 31799/10000, 31802/10000), (17/10, 26921/10000, 26925/10000), (9/5, 23764/10000, 23767/10000),
    (19/10, 21588/10000, 21591/10000)] : List (ℝ × ℝ × ℝ)),
    ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar r.1 s ↔ s ≤ s0)) → r.2.1 ≤ s0 ∧ s0 < r.2.2 := by
  have key : ∀ {p sm sp y t : ℝ}, TwoVar p sm → t ∈ Icc (-π) π → Gam p sp y t < ee p t → 0 < sm → 0 < sp →
      ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) → sm ≤ s0 ∧ s0 < sp := by
    intro p sm sp y t h2 ht hpt hsm hsp s0 hiff
    refine ⟨(hiff sm hsm).mp h2, ?_⟩
    by_contra hcon
    exact NewRows11.not_twoVar_of_point ht hpt ((hiff sp hsp).mpr (not_lt.mp hcon))
  have hpi := pi_gt_three
  have ht0 : (0 : ℝ) ∈ Icc (-π) π := ⟨by linarith, by linarith⟩
  intro r hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact key (hb (7/5, 52986/10000) (by simp)) ⟨by linarith, by linarith⟩ Bracket.point_7_5 (by norm_num) (by norm_num)
  · exact key (hb (3/2, 39572/10000) (by simp)) ⟨by linarith, by linarith⟩ Bracket.point_3_2 (by norm_num) (by norm_num)
  · exact key (hb (8/5, 31799/10000) (by simp)) ⟨by linarith, by linarith⟩ Bracket.point_8_5 (by norm_num) (by norm_num)
  · exact key (hb (17/10, 26921/10000) (by simp)) ht0 Bracket.point_17_10 (by norm_num) (by norm_num)
  · exact key (hb (9/5, 23764/10000) (by simp)) ht0 Bracket.point_9_5 (by norm_num) (by norm_num)
  · exact key (hb (19/10, 21588/10000) (by simp)) ht0 Bracket.point_19_10 (by norm_num) (by norm_num)

end NewRows11c

end P18
