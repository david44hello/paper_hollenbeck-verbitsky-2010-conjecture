/-
  HVFalse/Proofs/RemarkH.lean - Remark 6 (paper l.399-403): H changes sign at p = 4/3
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper: "By the proof above, H = 0 and dH/dp > 0 at p = 4/3, so H < 0 on an interval (4/3 - ε, 4/3)."
  Here H = H(p, u(p)). H(4/3) = 0 is SmallB.H_at_four_thirds; dH/dp = Dfun (ThresholdB.hasDerivAt_Hu) and Dfun(4/3) > 0
  (IntervalH.Dfun_pos, the paper's step (a)). The slope (H(p) - H(4/3))/(p - 4/3) tends to Dfun(4/3) > 0, so it is
  positive for p < 4/3 close to 4/3, where p - 4/3 < 0 forces H(p) < 0.
-/
import HVFalse.Proofs.IntervalH

open Real Set Filter Topology

namespace P18.RemarkH

theorem H_sign_change :
    H (4 / 3) (uu (4 / 3)) = 0 ∧ 0 < deriv (fun p => H p (uu p)) (4 / 3) ∧
      ∃ ε > 0, ∀ p ∈ Ioo (4 / 3 - ε) (4 / 3), H p (uu p) < 0 := by
  have hd := ThresholdB.hasDerivAt_Hu (p := 4 / 3) (by norm_num)
  have hpos : 0 < ThresholdB.Dfun (4 / 3) := IntervalH.Dfun_pos (le_refl _) (by norm_num)
  have h0 : H (4 / 3) (uu (4 / 3)) = 0 := H_at_four_thirds
  refine ⟨h0, by rw [hd.deriv]; exact hpos, ?_⟩
  have hev : ∀ᶠ y in 𝓝[<] (4 / 3 : ℝ), 0 < slope (fun p => H p (uu p)) (4 / 3) y :=
    ((hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsWithin_mono _ fun y (hy : y < 4 / 3) => hy.ne)).eventually
      (lt_mem_nhds hpos)
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  refine ⟨4 / 3 - l, by simp only [mem_Iio] at hl; linarith, fun p hp => ?_⟩
  have hp' : p ∈ Ioo l (4 / 3) := ⟨by linarith [hp.1], hp.2⟩
  have hslope : 0 < slope (fun p => H p (uu p)) (4 / 3) p := hsub hp'
  rw [slope_def_field, h0, sub_zero] at hslope
  have hneg : p - 4 / 3 < 0 := by linarith [hp.2]
  have := mul_neg_of_pos_of_neg hslope hneg
  rwa [div_mul_cancel₀ _ hneg.ne] at this

end P18.RemarkH
