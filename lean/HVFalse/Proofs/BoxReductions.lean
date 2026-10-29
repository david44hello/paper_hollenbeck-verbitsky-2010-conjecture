/-
  HVFalse/Proofs/BoxReductions.lean - the box inequalities of the certificates imply C20a and C21
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Every cell i < 140 lies in [4/3, 199/100], so 1 < p < 2 on it (cell_p_bounds).
  C20a: (eq:two) at s_cell ⇒ (eq:two) at every s ≤ s_cell (twoVar_mono) ⇒ (HV) (Theorem B "if", LocGlob.theoremB_if)
        ⇒ (HV) on L^p (DensityLp.hvIneq_iff_lp).
  C21:  a failure point at S - Δ (S = sec²(π/2p)) is a failure point at every s ∈ [S - Δ, S] (Γ decreases in s,
        gam_antitone_s) ⇒ (HV) fails (Prop. 4, ColeHom.prop_fail') ⇒ fails on L^p. S - Δ > 0 since S ≥ 1 > Δ. As C18.
-/
import HVFalse.Paper.ComputerChecked
import HVFalse.Proofs.LocGlob
import HVFalse.Proofs.Truec
import HVFalse.Proofs.CellMono
import HVFalse.Proofs.Threshold

open Real Set

namespace P18

namespace BoxReductions

theorem cellRight_le {i : ℕ} (hi : i < 140) : cellRight i ≤ 199 / 100 := by
  unfold cellRight cellLeft
  split_ifs with h1 h2
  · have : ((i + 1 : ℕ) : ℝ) ≤ 113 := by exact_mod_cast (by omega : i + 1 ≤ 113)
    linarith
  · have : ((i + 1 - 114 : ℕ) : ℝ) ≤ 15 := by exact_mod_cast (by omega : i + 1 - 114 ≤ 15)
    linarith
  · have : ((i + 1 - 130 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast (by omega : i + 1 - 130 ≤ 10)
    linarith

/-- Every `p` of a cell `i < 140` satisfies `1 < p < 2`. -/
theorem cell_p_bounds {i : ℕ} (hi : i < 140) {p : ℝ} (hp : p ∈ Icc (cellLeft i) (cellRight i)) : 1 < p ∧ p < 2 :=
  ⟨by linarith [CellMono.cellLeft_ge i, hp.1], by linarith [cellRight_le hi, hp.2]⟩

theorem one_le_Ssec {p : ℝ} (hp1 : 1 < p) : 1 ≤ Ssec p := by
  unfold Ssec
  exact one_le_one_div (pow_pos (SaddleValley.cos_th_pos hp1) 2) (cos_sq_le_one _)

theorem falseWidth_lt_one : ∀ j : Fin 115, falseWidth j < 1 := by decide +kernel

/-- C20a from its box part: (eq:two) at `s_cell` on each cell gives (HV) on `L^p` for every `s ≤ s_cell`. -/
theorem C20a_reduction : Paper.C20a_boxes → Paper.C20a_cells := by
  intro hb i hi
  obtain ⟨sc, hlev, hle, htwo⟩ := hb i hi
  refine ⟨sc, hlev, hle, fun p hp s hs hss => ?_⟩
  obtain ⟨hp1, hp2⟩ := cell_p_bounds hi hp
  exact (DensityLp.hvIneq_iff_lp hp1 hp2 hs (Truec.hvConst_pos hp1 hp2)).mp
    (LocGlob.theoremB_if hp1 hp2 hs (twoVar_mono (by linarith) (htwo p hp) hs hss))

/-- C21 from its box part: a failure point at `sec²(π/2p) - Δ_cell` gives failure of (HV) on `L^p` on the whole window. -/
theorem C21_reduction : Paper.C21_boxes → Paper.C21_false_width := by
  intro hb j p hp s hs
  have hi : (j : ℕ) + 25 < 140 := by have := j.isLt; omega
  obtain ⟨hp1, hp2⟩ := cell_p_bounds hi hp
  have hW : (falseWidth j : ℝ) < 1 := by exact_mod_cast falseWidth_lt_one j
  have hsp : 0 < Ssec p - (falseWidth j : ℝ) := by linarith [one_le_Ssec hp1]
  have hs0 : 0 < s := by linarith [hs.1]
  obtain ⟨y, t, ht, hlt⟩ := hb j p hp
  intro hHV
  exact ColeHom.prop_fail' hp1 hp2 hs0 hs.2
    ⟨y, t, ht, lt_of_le_of_lt (gam_antitone_s p _ s y t (by linarith) hsp hs.1) hlt⟩
    ((DensityLp.hvIneq_iff_lp hp1 hp2 hs0 (Truec.hvConst_pos hp1 hp2)).mpr hHV)

end BoxReductions

end P18
