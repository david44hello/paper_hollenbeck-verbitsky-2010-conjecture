/-
  HVFalse/Proofs/R2.lean - rows C21d, the right-end kappa row, isGLB_valid_mem and
  C04f (from Prop. 5 alone, nothing cited)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Proofs.SmallB
import HVFalse.Proofs.Threshold
import HVFalse.Proofs.LocGlob
import HVFalse.Proofs.DensityLp
import HVFalse.Proofs.Truec
import HVFalse.Proofs.CellMono
import HVFalse.Proofs.BoxReductions
import HVFalse.Proofs.NewRows11b
import HVFalse.Proofs.NewRows11bCells

open Real MeasureTheory Set

namespace P18.R2

/-- l.610-611: the first cell contains `p = 4/3`, where (HV) holds at `s = sec²(π/2p)`, so no width
`Δ_cell > 0` exists on it. -/
theorem C21d_no_width_first_cell :
    (4 / 3 : ℝ) ∈ Icc (cellLeft 0) (cellRight 0) ∧
      ∀ Δ > 0, ¬ ∀ p ∈ Icc (cellLeft 0) (cellRight 0), ∀ s ∈ Icc (Ssec p - Δ) (Ssec p),
        ¬ HVIneqLp p s (hvConst p s) := by
  have h0 : cellLeft 0 = 4 / 3 := by norm_num [cellLeft]
  have h1 : cellRight 0 = 4 / 3 + 17 / 3420 := by norm_num [cellRight, cellLeft]
  have hmem : (4 / 3 : ℝ) ∈ Icc (cellLeft 0) (cellRight 0) := by
    rw [h0, h1]
    constructor <;> norm_num
  refine ⟨hmem, fun Δ hΔ hall => ?_⟩
  have hp1 : (1 : ℝ) < 4 / 3 := by norm_num
  have hp2 : (4 / 3 : ℝ) < 2 := by norm_num
  have hS : 0 < Ssec (4 / 3) := lt_of_lt_of_le one_pos (BoxReductions.one_le_Ssec hp1)
  have htwo : TwoVar (4 / 3) (Ssec (4 / 3)) := twoVar_mel hp1 le_rfl
  have hHV : HVIneqLp (4 / 3) (Ssec (4 / 3)) (hvConst (4 / 3) (Ssec (4 / 3))) :=
    (DensityLp.hvIneq_iff_lp hp1 hp2 hS (Truec.hvConst_pos hp1 hp2)).1 (LocGlob.theoremB_if hp1 hp2 hS htwo)
  exact hall (4 / 3) hmem (Ssec (4 / 3)) ⟨by linarith, le_rfl⟩ hHV

/-- l.592-593: "at the right end of a cell the certified part of the window is about κ": within
`4·10⁻⁴` of `κ` for every certified `s_cell` (as `W(p_b) ≥ W(1.99) > 0.0058`). -/
theorem C30f_right_end_kappa : ∀ i : ℕ, i < 140 → ∀ sc : ℝ, cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i →
    |(sc - cellRight i / (cellRight i - 1)) / (Ssec (cellRight i) - cellRight i / (cellRight i - 1))
      - cellKappa i| ≤ 4 / 10 ^ 4 := by
  intro i hi sc hsc1 hsc2
  have hpb1 : 1 < cellRight i := by
    have := CellMono.cellLeft_ge (i + 1)
    unfold cellRight
    linarith
  have hpb2 : cellRight i ≤ 199 / 100 := BoxReductions.cellRight_le hi
  have hW : Ssec (199 / 100) - 199 / 100 / (199 / 100 - 1)
      ≤ Ssec (cellRight i) - cellRight i / (cellRight i - 1) :=
    NewRows11b.W_antitone ⟨hpb1, by linarith⟩ ⟨by norm_num, by norm_num⟩ hpb2
  have h140 := NewRows11bCells.pt_140.1
  have hW0 : (58 / 10000 : ℝ) ≤ Ssec (cellRight i) - cellRight i / (cellRight i - 1) := by
    have : (58 / 10000 : ℝ) + 199 / 100 / (199 / 100 - 1) ≤ 1 / (35215526283 / 50000000000 : ℝ) ^ 2 := by
      norm_num
    linarith
  have hL : cellLevel i = cellRight i / (cellRight i - 1)
      + cellKappa i * (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) := rfl
  rw [hL] at hsc1 hsc2
  have hWpos : 0 < Ssec (cellRight i) - cellRight i / (cellRight i - 1) := by linarith
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hWpos]
    nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hWpos]
    nlinarith

/-- The infimum of the valid constants is itself valid (so `IsGLB` and `IsLeast` agree for "the best
constant"). -/
theorem isGLB_valid_mem {p s c : ℝ} (hglb : IsGLB {C | 0 < C ∧ HVIneqLp p s C} c) : HVIneqLp p s c := by
  intro f g h hg hh
  have hc : 0 ≤ c := hglb.2 fun C hC => hC.1.le
  have hN : eLpNorm f (ENNReal.ofReal p) volume ≠ ⊤ := (Lp.eLpNorm_lt_top f).ne
  have hbound : ∀ C, 0 < C → HVIneqLp p s C →
      eLpNorm (fun x => (‖g x‖ ^ s + ‖h x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal (C * (eLpNorm f (ENNReal.ofReal p) volume).toReal) := by
    intro C hC hv
    rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_toReal hN]
    exact hv f g h hg hh
  obtain ⟨C0, hC0, hv0⟩ : ∃ C, 0 < C ∧ HVIneqLp p s C := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    have hlb : c + 1 ∈ lowerBounds {C | 0 < C ∧ HVIneqLp p s C} := fun C hC => absurd hC.2 (hne C hC.1)
    linarith [hglb.2 hlb]
  have hX : eLpNorm (fun x => (‖g x‖ ^ s + ‖h x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbound C0 hC0 hv0)
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hN, ← ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  have hb' : ∀ C, 0 < C → HVIneqLp p s C →
      (eLpNorm (fun x => (‖g x‖ ^ s + ‖h x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume).toReal
        ≤ C * (eLpNorm f (ENNReal.ofReal p) volume).toReal := fun C hC hv =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hbound C hC hv)
  rcases (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm f (ENNReal.ofReal p) volume).toReal).eq_or_lt with hn | hn
  · have h0 := hb' C0 hC0 hv0
    rw [← hn, mul_zero] at h0 ⊢
    exact h0
  · have hlb : (eLpNorm (fun x => (‖g x‖ ^ s + ‖h x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume).toReal
        / (eLpNorm f (ENNReal.ofReal p) volume).toReal ∈ lowerBounds {C | 0 < C ∧ HVIneqLp p s C} :=
      fun C hC => by
        rw [div_le_iff₀ hn]
        exact hb' C hC.1 hC.2
    have hle := hglb.2 hlb
    rwa [div_le_iff₀ hn] at hle

/-- l.503-504: "Proposition 5 supplies a proof of that observation": (eq:two) fails at `s = sec²ϑ` for every
`p ∈ (4/3, 2)`, from Prop. 5 (`Γ < e` on the valley curve, C10b3) alone - nothing cited. -/
theorem C04f_two_fails_at_sec {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : ¬ TwoVar p (Ssec p) := by
  intro htwo
  obtain ⟨δ, hδ, hv⟩ := valley_negative hp1 hp2
  have hc1 : 0 < |valleyC p| + 1 := by positivity
  set y : ℝ := min (δ / 2) (1 / (4 * (|valleyC p| + 1))) with hy
  have hy0 : 0 < y := lt_min (by linarith) (by positivity)
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hyc : y ≤ 1 / (4 * (|valleyC p| + 1)) := min_le_right _ _
  have hy1 : y ≤ 1 := hyc.trans (by rw [div_le_one (by positivity)]; linarith [abs_nonneg (valleyC p)])
  have hcy : |valleyC p * y ^ 2| < 1 / 4 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < y ^ 2)]
    have hyy : y ^ 2 ≤ y := by nlinarith
    calc |valleyC p| * y ^ 2 ≤ |valleyC p| * y := mul_le_mul_of_nonneg_left hyy (abs_nonneg _)
      _ ≤ |valleyC p| * (1 / (4 * (|valleyC p| + 1))) := mul_le_mul_of_nonneg_left hyc (abs_nonneg _)
      _ < 1 / 4 := by
        rw [mul_one_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (valleyC p)]
  have hpi1 : π / p < 3 * π / 4 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [pi_pos]
  have hpi2 : 0 < π / p := by
    have : 0 < p := by linarith
    positivity
  have hmem : π / p - valleyC p * y ^ 2 ∈ Icc (-π) π := by
    have := abs_lt.1 hcy
    constructor <;> nlinarith [pi_gt_three]
  have h1 := hv y hy0.ne' (by rw [abs_of_pos hy0]; exact hyδ)
  have h2 := htwo y _ hmem
  linarith

end P18.R2
