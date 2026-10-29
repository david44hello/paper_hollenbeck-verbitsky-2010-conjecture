/-
  HVFalse/Proofs/CellMono.lean - Prop. 11 proof (l.583-584): the cell level is attained at the right end of the cell
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Defs.Cells
import HVFalse.Proofs.SaddleValley

open Real Set

namespace P18

namespace CellMono

/-- `p ↦ p/(p-1)` decreases on `(1, ∞)`. -/
theorem jag_antitone {p pb : ℝ} (hp : 1 < p) (hle : p ≤ pb) : pb / (pb - 1) ≤ p / (p - 1) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `p ↦ sec²(π/(2p))` decreases on `(1, ∞)`. -/
theorem Ssec_antitone {p pb : ℝ} (hp : 1 < p) (hle : p ≤ pb) : Ssec pb ≤ Ssec p := by
  have hp0 : 0 < p := by linarith
  have hcp := SaddleValley.cos_th_pos hp
  have hθ : π / (2 * pb) ≤ π / (2 * p) := div_le_div_of_nonneg_left pi_pos.le (by positivity) (by linarith)
  have hpb : 0 < pb := by linarith
  have hθ0 : 0 ≤ π / (2 * pb) := by positivity
  have hθπ : π / (2 * p) ≤ π := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [pi_pos]
  have hcos : cos (π / (2 * p)) ≤ cos (π / (2 * pb)) := cos_le_cos_of_nonneg_of_le_pi hθ0 hθπ hθ
  unfold Ssec
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hcp.le hcos 2)

theorem cellKappa_mem (i : ℕ) : 0 ≤ cellKappa i ∧ cellKappa i ≤ 1 := by
  unfold cellKappa; split_ifs <;> norm_num

theorem cellLeft_ge (i : ℕ) : 4 / 3 ≤ cellLeft i := by
  unfold cellLeft
  split_ifs
  · have : (0:ℝ) ≤ (i : ℝ) * (17 / 3420) := by positivity
    linarith
  · have : (0:ℝ) ≤ ((i - 114 : ℕ) : ℝ) * (1 / 200) := by positivity
    linarith
  · have : (0:ℝ) ≤ ((i - 130 : ℕ) : ℝ) * (1 / 1000) := by positivity
    linarith

/-- **C20c** (Prop. 11 proof, l.583-584): on each cell the level `L(p) = p/(p-1) + κ(sec²(π/2p) - p/(p-1))` is at least its
value at the right end `p_b`, which is `cellLevel i`. (True for every `i`; the claim restricts to `i < 140`.) -/
theorem level_antitone (i : ℕ) (p : ℝ) (hp : p ∈ Icc (cellLeft i) (cellRight i)) :
    cellLevel i ≤ p / (p - 1) + cellKappa i * (Ssec p - p / (p - 1)) := by
  have hp1 : 1 < p := by linarith [cellLeft_ge i, hp.1]
  have hJ := jag_antitone hp1 hp.2
  have hS := Ssec_antitone hp1 hp.2
  obtain ⟨hk0, hk1⟩ := cellKappa_mem i
  unfold cellLevel
  nlinarith [mul_nonneg (sub_nonneg.mpr hk1) (sub_nonneg.mpr hJ), mul_nonneg hk0 (sub_nonneg.mpr hS)]

end CellMono

end P18
