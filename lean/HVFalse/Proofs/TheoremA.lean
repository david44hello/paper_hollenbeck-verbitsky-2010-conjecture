/-
  HVFalse/Proofs/TheoremA.lean - Theorem A and Prop. fail (Prop. 4) of the paper, assembled
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route (the paper's): at s = sec²ϑ there is a point with 0 < t* < π/p and Γ < e (SaddleValley.saddle_point_proved);
  Γ is continuous in s (Threshold.gam_continuousAt_s), so the strict inequality persists at some s₁ < sec²ϑ; Γ decreases in s,
  so it holds on all of [s₁, sec²ϑ]; Prop. fail turns each such point into a failure of (HV).
-/
import HVFalse.Proofs.FailCole
import HVFalse.Proofs.FailLift
import HVFalse.Proofs.SaddleValley
import HVFalse.Proofs.Threshold
import HVFalse.Proofs.ColeHom

open Real Set Filter Topology

namespace P18

/-- Prop. fail (C09, Prop. 4): one failure point `Γ(y*,t*) < e(t*)`, `t* ∈ [-π, π]`, makes (HV) fail (`s ≤ sec²ϑ`). -/
theorem prop_fail {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p s y t < ee p t) : ¬ HVIneq p s (hvConst p s) :=
  ColeHom.prop_fail' hp1 hp2 hs hsS hpt

/-- C11, Theorem A: for every `p ∈ (4/3, 2)` there is `s₁ ∈ (0, sec²ϑ)` such that (HV) fails with the conjectured constant
for every `s ∈ [s₁, sec²ϑ]`. -/
theorem theoremA {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 < Ssec p ∧ ∀ s ∈ Icc s1 (Ssec p), ¬ HVIneq p s (hvConst p s) := by
  have hp1' : 1 < p := by linarith
  have hp : 0 < p := by linarith
  have hS := Ssec_pos hp1'
  obtain ⟨y, t, ht0, htp, hlt⟩ := SaddleValley.saddle_point_proved hp1 hp2
  have hev : ∀ᶠ s in 𝓝 (Ssec p), Gam p s y t < ee p t :=
    (gam_continuousAt_s p y t hS).eventually (Iio_mem_nhds hlt)
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.mp hev
  set s1 := max (Ssec p - δ / 2) (Ssec p / 2) with hs1
  have hs1pos : 0 < s1 := lt_of_lt_of_le (half_pos hS) (le_max_right _ _)
  have hs1lt : s1 < Ssec p := max_lt (by linarith) (by linarith)
  have hs1pt : Gam p s1 y t < ee p t := by
    apply hδs
    rw [Real.dist_eq, abs_lt]
    have := le_max_left (Ssec p - δ / 2) (Ssec p / 2)
    constructor <;> linarith
  have htI : t ∈ Icc (-π) π := by
    have : π / p < π := by rw [div_lt_iff₀ hp]; nlinarith [pi_pos]
    constructor <;> linarith [pi_pos]
  refine ⟨s1, hs1pos, hs1lt, fun s ⟨h1, h2⟩ => ?_⟩
  exact prop_fail hp1' hp2 (hs1pos.trans_le h1) h2
    ⟨y, t, htI, lt_of_le_of_lt (gam_antitone_s p s1 s y t hp hs1pos h1) hs1pt⟩

end P18
