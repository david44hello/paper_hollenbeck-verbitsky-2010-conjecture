/-
  HVFalse/Proofs/NewRows11b.lean - U13, Remark after Prop. 11 (the paper): the certified part of the window
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Paper (l.593-595): "At the right end of a cell the certified part of the window, `(s_cell - p/(p-1))/(sec²(π/2p) - p/(p-1))`,
  is about κ. Inside the cell it is smaller, and its minimum over [4/3, 1.99] is about 16% (at p = 1.975)." Notation j(p) = p/(p-1), W(p) = Ssec p - j(p) (the window width).
  W is antitone on (1, 2): W' = 1/(p-1)² - π sinθ/(p² cos³θ) (θ = π/2p), and W' ≤ 0 reduces with φ = π/2 - θ to
  π sin³φ < 4φ² cos φ on (0, π/4] (sin φ ≤ φ, cos φ ≥ 1 - φ²/2, π < 3.15).
  U13a: j(p) ≥ j(p_b), W(p) ≥ W(p_b) > 0 and s_cell ≥ j(p_b) (C20b) give frac(p) ≤ frac(p_b).
  U13b: rational enclosures of Ssec at 1.975 and 1.98 (NewRows11bCells.pt_129, pt_130) give 0.16 ≤ frac ≤ 0.17.
  U13c: frac(p) ≥ (s_cell - j(p_a))/W(p_a) ≥ 0.16 by the 140 generated cell certificates (NewRows11bCells.cells_16;
  minimum 0.164642 at cell 129, p = 1.975).
-/
import HVFalse.Proofs.NewRows11bCells
import HVFalse.Proofs.BoxReductions
import HVFalse.Proofs.ThresholdB

open Real Set

namespace P18

namespace NewRows11b

/-- `π sin³φ < 4 φ² cos φ` for `0 < φ ≤ π/4`. -/
theorem key_phi {φ : ℝ} (h0 : 0 < φ) (h1 : φ ≤ π / 4) : π * sin φ ^ 3 < 4 * φ ^ 2 * cos φ := by
  have hpi := pi_lt_d2
  have hpi0 := pi_pos
  have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hs1 : sin φ ≤ φ := sin_le h0.le
  have hc : 1 - φ ^ 2 / 2 ≤ cos φ := one_sub_sq_div_two_le_cos
  have h3 : sin φ ^ 3 ≤ φ ^ 3 := pow_le_pow_left₀ hs0.le hs1 3
  have hφ : φ < 79 / 100 := by linarith
  have hlin : π * φ < 4 * (1 - φ ^ 2 / 2) := by nlinarith
  have hφ2 : 0 < φ ^ 2 := by positivity
  calc π * sin φ ^ 3 ≤ π * φ ^ 3 := mul_le_mul_of_nonneg_left h3 hpi0.le
    _ = φ ^ 2 * (π * φ) := by ring
    _ < φ ^ 2 * (4 * (1 - φ ^ 2 / 2)) := mul_lt_mul_of_pos_left hlin hφ2
    _ ≤ φ ^ 2 * (4 * cos φ) := mul_le_mul_of_nonneg_left (by linarith) hφ2.le
    _ = 4 * φ ^ 2 * cos φ := by ring

/-- The derivative inequality: `p² cos³θ ≤ (p-1)² π sin θ` for `1 < p ≤ 2`, `θ = π/(2p)`. -/
theorem key_p {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) :
    p ^ 2 * cos (π / (2 * p)) ^ 3 ≤ (p - 1) ^ 2 * π * sin (π / (2 * p)) := by
  have hp0 : 0 < p := by linarith
  have hpi0 := pi_pos
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = π / 2 - π / (2 * p) := ⟨_, rfl⟩
  have hθ : π / (2 * p) = π / 2 - φ := by rw [hφ]; ring
  have hpm : p - 1 = 2 * p * φ / π := by rw [hφ]; field_simp
  have hθlt : π / (2 * p) < π / 2 := by
    rw [div_lt_div_iff₀ (by positivity) two_pos]; nlinarith
  have hθge : π / 4 ≤ π / (2 * p) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hφ0 : 0 < φ := by rw [hφ]; linarith
  have hφ1 : φ ≤ π / 4 := by rw [hφ]; linarith
  have hk := key_phi hφ0 hφ1
  rw [hθ, cos_pi_div_two_sub, sin_pi_div_two_sub, hpm]
  have hp2' : 0 < p ^ 2 := by positivity
  have e : (2 * p * φ / π) ^ 2 * π * cos φ = p ^ 2 * (4 * φ ^ 2 * cos φ) / π := by field_simp; ring
  rw [e, le_div_iff₀ hpi0]
  nlinarith [mul_lt_mul_of_pos_left hk hp2']

theorem hasDerivAt_W {p : ℝ} (hp1 : 1 < p) :
    HasDerivAt (fun q => Ssec q - q / (q - 1))
      (1 / (p - 1) ^ 2 - π * sin (π / (2 * p)) / (p ^ 2 * cos (π / (2 * p)) ^ 3)) p := by
  have hp0 : p ≠ 0 := by linarith
  have hc := SaddleValley.cos_th_pos hp1
  have hθ := ThresholdB.hasDerivAt_theta hp0
  have hcos := (hasDerivAt_cos (π / (2 * p))).comp p hθ
  have hinv := (hcos.pow 2).inv (pow_ne_zero 2 hc.ne')
  have hS : Ssec = fun q => (cos (π / (2 * q)) ^ 2)⁻¹ := funext fun q => one_div _
  have hj := (hasDerivAt_id' p).div ((hasDerivAt_id' p).sub_const 1) (by linarith : p - 1 ≠ 0)
  rw [hS]
  refine (hinv.sub hj).congr_deriv ?_
  have hpm : p - 1 ≠ 0 := by linarith
  have hcne := hc.ne'
  norm_num
  field_simp
  ring

theorem W_antitone : AntitoneOn (fun q => Ssec q - q / (q - 1)) (Ioo 1 2) := by
  have hd : ∀ x ∈ Ioo (1 : ℝ) 2, HasDerivAt (fun q => Ssec q - q / (q - 1))
      (1 / (x - 1) ^ 2 - π * sin (π / (2 * x)) / (x ^ 2 * cos (π / (2 * x)) ^ 3)) x :=
    fun x hx => hasDerivAt_W hx.1
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 1 2)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro x hx
    rw [(hd x hx).deriv, sub_nonpos]
    have hx1 := hx.1
    have hc := SaddleValley.cos_th_pos hx1
    have hk := key_p hx1 hx.2.le
    rw [div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos (pow_pos (by linarith) 2) (pow_pos hc 3))]
    nlinarith

/-- `W(p_b) > 0` at the right end of every cell (from C20b and `κ ≥ 0`). -/
theorem W_right_pos {i : ℕ} (hi : i < 140) (hab : cellLeft i ≤ cellRight i) :
    0 < Ssec (cellRight i) - cellRight i / (cellRight i - 1) := by
  have hC := cells_contain_jag i hi
  have ha1 : 1 < cellLeft i := by linarith [CellMono.cellLeft_ge i]
  have hjab : cellRight i / (cellRight i - 1) ≤ cellLeft i / (cellLeft i - 1) := CellMono.jag_antitone ha1 hab
  have hκ := (CellMono.cellKappa_mem i).1
  unfold cellLevel at hC
  by_contra hneg
  nlinarith [mul_nonneg hκ (neg_nonneg.mpr (not_lt.mp hneg))]

/-- U13a (Remark after Prop. 11, l.593-594): inside a cell the certified part of the window is at most its value at the
right end. -/
theorem frac_le_right : ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i), ∀ sc : ℝ,
    cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i →
    (sc - p / (p - 1)) / (Ssec p - p / (p - 1))
      ≤ (sc - cellRight i / (cellRight i - 1)) / (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) := by
  intro i hi p hp sc hsc1 _
  have hab : cellLeft i ≤ cellRight i := hp.1.trans hp.2
  obtain ⟨hp1, hp2⟩ := BoxReductions.cell_p_bounds hi hp
  obtain ⟨hb1, hb2⟩ := BoxReductions.cell_p_bounds hi ⟨hab, le_rfl⟩
  have ha1 : 1 < cellLeft i := by linarith [CellMono.cellLeft_ge i]
  have hjp : cellRight i / (cellRight i - 1) ≤ p / (p - 1) := CellMono.jag_antitone hp1 hp.2
  have hja : cellRight i / (cellRight i - 1) ≤ cellLeft i / (cellLeft i - 1) := CellMono.jag_antitone ha1 hab
  have hC := cells_contain_jag i hi
  have hscb : cellRight i / (cellRight i - 1) ≤ sc := by linarith
  have hWb := W_right_pos hi hab
  have hWpb : Ssec (cellRight i) - cellRight i / (cellRight i - 1) ≤ Ssec p - p / (p - 1) :=
    W_antitone ⟨hp1, hp2⟩ ⟨hb1, hb2⟩ hp.2
  have hWp : 0 < Ssec p - p / (p - 1) := lt_of_lt_of_le hWb hWpb
  calc (sc - p / (p - 1)) / (Ssec p - p / (p - 1))
      ≤ (sc - cellRight i / (cellRight i - 1)) / (Ssec p - p / (p - 1)) :=
        div_le_div_of_nonneg_right (by linarith) hWp.le
    _ ≤ (sc - cellRight i / (cellRight i - 1)) / (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) :=
        div_le_div_of_nonneg_left (by linarith) hWb hWpb

/-- U13b (l.594-595): "about 16% (at p = 1.975)": at `p = 1.975 = cellLeft 129` the fraction lies in `[0.16, 0.17]`. -/
theorem frac_at_1975 : ∀ sc : ℝ, cellLevel 129 - 2 / 10 ^ 6 < sc → sc ≤ cellLevel 129 →
    16 / 100 ≤ (sc - 1975 / 1000 / (1975 / 1000 - 1)) / (Ssec (1975 / 1000) - 1975 / 1000 / (1975 / 1000 - 1)) ∧
    (sc - 1975 / 1000 / (1975 / 1000 - 1)) / (Ssec (1975 / 1000) - 1975 / 1000 / (1975 / 1000 - 1)) ≤ 17 / 100 := by
  intro sc hsc1 hsc2
  have hL : cellLevel 129 = 99 / 49 + 13 / 20 * (Ssec (99 / 50) - 99 / 49) := by
    unfold cellLevel
    rw [show cellRight 129 = 99 / 50 by norm_num [cellRight, cellLeft],
      show cellKappa 129 = 13 / 20 by norm_num [cellKappa]]
    norm_num
  have h1975 : (1975 / 1000 : ℝ) = 79 / 40 := by norm_num
  have hj : (79 / 40 : ℝ) / (79 / 40 - 1) = 79 / 39 := by norm_num
  rw [h1975, hj]
  have hA1 : (204057101 / 10 ^ 8 : ℝ) ≤ Ssec (79 / 40) := le_trans (by norm_num) NewRows11bCells.pt_129.1
  have hA2 : Ssec (79 / 40) ≤ (204057102 / 10 ^ 8 : ℝ) := NewRows11bCells.pt_129.2.trans (by norm_num)
  have hB1 : (203224350 / 10 ^ 8 : ℝ) ≤ Ssec (99 / 50) := le_trans (by norm_num) NewRows11bCells.pt_130.1
  have hB2 : Ssec (99 / 50) ≤ (203224351 / 10 ^ 8 : ℝ) := NewRows11bCells.pt_130.2.trans (by norm_num)
  have hW : 0 < Ssec (79 / 40) - 79 / 39 := by linarith
  rw [hL] at hsc1 hsc2
  constructor
  · rw [le_div_iff₀ hW]; linarith
  · rw [div_le_iff₀ hW]; linarith

/-- U13c (l.594-595): "its minimum ... is about 16%": on every cell, for every certified `s_cell`, the fraction is at least 0.16. -/
theorem frac_ge : ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i), ∀ sc : ℝ,
    cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i → 16 / 100 ≤ (sc - p / (p - 1)) / (Ssec p - p / (p - 1)) := by
  intro i hi p hp sc hsc1 _
  have hab : cellLeft i ≤ cellRight i := hp.1.trans hp.2
  obtain ⟨hp1, hp2⟩ := BoxReductions.cell_p_bounds hi hp
  obtain ⟨hb1, hb2⟩ := BoxReductions.cell_p_bounds hi ⟨hab, le_rfl⟩
  obtain ⟨ha1, ha2⟩ := BoxReductions.cell_p_bounds hi ⟨le_rfl, hab⟩
  have hja : p / (p - 1) ≤ cellLeft i / (cellLeft i - 1) := CellMono.jag_antitone ha1 hp.1
  have hWb := W_right_pos hi hab
  have hWpb : Ssec (cellRight i) - cellRight i / (cellRight i - 1) ≤ Ssec p - p / (p - 1) :=
    W_antitone ⟨hp1, hp2⟩ ⟨hb1, hb2⟩ hp.2
  have hWap : Ssec p - p / (p - 1) ≤ Ssec (cellLeft i) - cellLeft i / (cellLeft i - 1) :=
    W_antitone ⟨ha1, ha2⟩ ⟨hp1, hp2⟩ hp.1
  have hWp : 0 < Ssec p - p / (p - 1) := lt_of_lt_of_le hWb hWpb
  have hcell := NewRows11bCells.cells_16 i hi
  rw [le_div_iff₀ hWp]
  linarith

end NewRows11b

end P18
