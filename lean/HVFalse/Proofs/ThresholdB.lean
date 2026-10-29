/-
  HVFalse/Proofs/ThresholdB.lean - the threshold s₀(p): C25 (range correct iff p ≤ 4/3), C17d, C17c; C10a7 (H at p = 2)
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import HVFalse.Proofs.Threshold
import HVFalse.Proofs.TheoremA
import HVFalse.Proofs.ThmBIf
import HVFalse.Proofs.SaddleValley
import HVFalse.Proofs.SmallB
import HVFalse.Proofs.LocGlob

open Real Set Filter Topology

namespace P18

namespace ThresholdB

variable {p : ℝ}

/-- **C25**: the conjectured range is correct exactly for `p ≤ 4/3`. -/
theorem range_correct_iff (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ s : ℝ, 0 < s → s < Ssec p → HVIneq p s (hvConst p s)) ↔ p ≤ 4 / 3 := by
  constructor
  · intro h
    by_contra h43
    push Not at h43
    obtain ⟨s1, hs1, hs1S, hfail⟩ := theoremA h43 hp2
    exact hfail s1 ⟨le_rfl, hs1S.le⟩ (h s1 hs1 hs1S)
  · intro h43 s hs hsS
    exact LocGlob.theoremB_if hp1 hp2 hs (twoVar_mono (by linarith) (twoVar_mel hp1 h43) hs hsS.le)

/-- (eq:two) fails at `s = sec²ϑ` for `p > 4/3` (the saddle point). -/
theorem not_twoVar_sec (hp1 : 4 / 3 < p) (hp2 : p < 2) : ¬ TwoVar p (Ssec p) := by
  intro h2
  obtain ⟨y, t, ht0, htp, hlt⟩ := SaddleValley.saddle_point_proved hp1 hp2
  have hp0 : 0 < p := by linarith
  have htπ : t ≤ π := by
    have : π / p < π := by rw [div_lt_iff₀ hp0]; nlinarith [pi_pos]
    linarith
  have := h2 y t ⟨by linarith [pi_pos], htπ⟩
  linarith

/-- **C17d**: `s₀(p) = sec²(π/2p)` iff `p ≤ 4/3`. -/
theorem s0_eq_sec_iff (hp1 : 1 < p) (hp2 : p < 2) {s0 : ℝ} (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 = Ssec p ↔ p ≤ 4 / 3 := by
  constructor
  · intro heq
    by_contra h43
    push Not at h43
    exact not_twoVar_sec h43 hp2 ((hs0 (Ssec p) (Ssec_pos hp1)).mpr heq.symm.le)
  · intro h43
    have hS := Ssec_pos hp1
    have h1 : s0 ≤ Ssec p := by
      by_contra hc
      have hlt : Ssec p < s0 := not_le.mp hc
      exact twoVar_fails_above hp1 hp2 hlt ((hs0 s0 (lt_trans hS hlt)).mpr le_rfl)
    exact le_antisymm h1 ((hs0 _ hS).mp (twoVar_mel hp1 h43))

/-- (HV) with the conjectured constant iff (eq:two), for `0 < s ≤ sec²ϑ` (Theorem B both ways). -/
theorem hv_iff_twoVar (hp1 : 1 < p) (hp2 : p < 2) {s : ℝ} (hs : 0 < s) (hsS : s ≤ Ssec p) :
    HVIneq p s (hvConst p s) ↔ TwoVar p s := by
  constructor
  · intro hHV
    by_contra h2
    unfold TwoVar at h2
    push Not at h2
    obtain ⟨y, t, ht, hlt⟩ := h2
    exact prop_fail hp1 hp2 hs hsS ⟨y, t, ht, hlt⟩ hHV
  · exact LocGlob.theoremB_if hp1 hp2 hs

/-- **C17c**: (HV) holds with the conjectured constant iff `s ≤ s₀(p)`, for `0 < s ≤ sec²ϑ`. -/
theorem hv_iff_threshold (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ Ssec p → (HVIneq p s (hvConst p s) ↔ s ≤ s0) := by
  obtain ⟨s0, hs0, hiff⟩ := twoVar_threshold hp1 hp2
  exact ⟨s0, hs0, fun s hs hsS => (hv_iff_twoVar hp1 hp2 hs hsS).trans (hiff s hs)⟩

/-! ## C10a7: `H` along `u(p)` at `p = 2` -/

/-- `u'(p)` for `u(p) = tan²(π/(2p))`. -/
noncomputable def up (p : ℝ) : ℝ := 2 * tan (π / (2 * p)) * (cos (π / (2 * p)) ^ 2)⁻¹ * (-(π / (2 * p ^ 2)))

theorem hasDerivAt_theta {p : ℝ} (hp : p ≠ 0) : HasDerivAt (fun p : ℝ => π / (2 * p)) (-(π / (2 * p ^ 2))) p := by
  have h := (hasDerivAt_const p π).div ((hasDerivAt_id p).const_mul 2) (by simpa using hp)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  · simp only [id]; field_simp; ring
  · simp

theorem hasDerivAt_uu {p : ℝ} (hp : 1 < p) : HasDerivAt uu (up p) p := by
  have hp0 : p ≠ 0 := by linarith
  have hc : cos (π / (2 * p)) ≠ 0 := (SaddleValley.cos_th_pos hp).ne'
  have htan := (Real.hasDerivAt_tan hc).comp p (hasDerivAt_theta hp0)
  have h2 := htan.pow 2
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  · simp only [Function.comp, one_div, up]; ring
  · simp [uu]

theorem uu_two : uu 2 = 1 := by
  unfold uu; rw [show π / (2 * 2) = π / 4 by ring, tan_pi_div_four]; norm_num

theorem up_two : up 2 = -(π / 2) := by
  unfold up
  rw [show π / (2 * 2) = π / 4 by ring, tan_pi_div_four, cos_pi_div_four, div_pow, sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- The derivative of `p ↦ H(p, u(p))`, written out. -/
noncomputable def Dfun (p : ℝ) : ℝ :=
  -2 * uu p ^ 2 + (-2 * (p - 1)) * (2 * uu p * up p)
    + ((-6 * (2 - p) + 2) * uu p + (3 * (2 - p) ^ 2 + 2 * p) * up p) + -6 * (2 - p)

/-- Polynomial pieces in `p`. -/
theorem hd_lin (c d x : ℝ) : HasDerivAt (fun p : ℝ => c * (p - d)) c x := by
  have h := ((hasDerivAt_id x).sub_const d).const_mul c
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => by simp)

theorem hd_quad (x : ℝ) : HasDerivAt (fun p : ℝ => 3 * (2 - p) ^ 2 + 2 * p) (-6 * (2 - x) + 2) x := by
  have h := ((((hasDerivAt_id x).const_sub 2).pow 2).const_mul 3).add ((hasDerivAt_id x).const_mul 2)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => by simp)
  simp; ring

theorem hd_quad2 (x : ℝ) : HasDerivAt (fun p : ℝ => -6 * (2 - p)) 6 x := by
  have h := ((hasDerivAt_id x).const_sub 2).const_mul (-6)
  refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => by simp)

theorem hd_quad3 (x : ℝ) : HasDerivAt (fun p : ℝ => 3 * (2 - p) ^ 2 - 2) (-6 * (2 - x)) x := by
  have h := ((((hasDerivAt_id x).const_sub 2).pow 2).const_mul 3).sub_const 2
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => by simp)
  simp; ring

theorem hd_lin2 (x : ℝ) : HasDerivAt (fun p : ℝ => -6 * (2 - p) + 2) 6 x := (hd_quad2 x).add_const 2

theorem hasDerivAt_Hu {p : ℝ} (hp : 1 < p) : HasDerivAt (fun p => H p (uu p)) (Dfun p) p := by
  have hu := hasDerivAt_uu hp
  have b1 : HasDerivAt (fun p => uu p ^ 2) (2 * uu p * up p) p := (hu.pow 2).congr_deriv (by simp)
  have h := (((hd_lin (-2) 1 p).mul b1).add ((hd_quad p).mul hu)).add (hd_quad3 p)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
  · unfold Dfun; ring
  · simp only [H, Pi.add_apply, Pi.mul_apply]; ring

theorem differentiableAt_up : DifferentiableAt ℝ up 2 := by
  have hc : cos (π / (2 * 2)) ≠ 0 := (SaddleValley.cos_th_pos (p := 2) (by norm_num)).ne'
  have d1 : DifferentiableAt ℝ (fun p : ℝ => π / (2 * p)) 2 := (hasDerivAt_theta (by norm_num)).differentiableAt
  have d2 : DifferentiableAt ℝ (fun p => tan (π / (2 * p))) 2 := by
    have h := (Real.hasDerivAt_tan hc).comp 2 (hasDerivAt_theta (p := 2) (by norm_num))
    exact h.differentiableAt
  have dc : DifferentiableAt ℝ (fun p => cos (π / (2 * p))) 2 := by
    have h := (Real.hasDerivAt_cos (π / (2 * 2))).comp 2 (hasDerivAt_theta (p := 2) (by norm_num))
    exact h.differentiableAt
  have d3 : DifferentiableAt ℝ (fun p => (cos (π / (2 * p)) ^ 2)⁻¹) 2 := (dc.pow 2).inv (pow_ne_zero 2 hc)
  have d4 : DifferentiableAt ℝ (fun p : ℝ => -(π / (2 * p ^ 2))) 2 := by
    have : DifferentiableAt ℝ (fun p : ℝ => 2 * p ^ 2) 2 := by fun_prop
    exact (differentiableAt_const _ |>.div this (by norm_num)).neg
  unfold up
  exact ((d2.const_mul 2).mul d3).mul d4

/-- **C10a7** (Prop. 5 (ii)): `u(2) = 1`, `H(2,1) = 0`, both partials of `H` vanish at `(2,1)`, `u'(2) = -π/2`, and
`d²/dp² H(p, u(p))` at `p = 2` is `12 + 2π - π² > 0`. -/
theorem H_at_two :
    uu 2 = 1 ∧ H 2 1 = 0 ∧ HasDerivAt (fun p => H p 1) 0 2 ∧ HasDerivAt (fun u => H 2 u) 0 1 ∧
      HasDerivAt uu (-(π / 2)) 2 ∧ HasDerivAt (deriv (fun p => H p (uu p))) (12 + 2 * π - π ^ 2) 2 ∧
      0 < 12 + 2 * π - π ^ 2 := by
  refine ⟨uu_two, by unfold H; norm_num, ?_, ?_, ?_, ?_, H_second_deriv_pos⟩
  · have h := (((hasDerivAt_id (2:ℝ)).const_sub 2).pow 2).const_mul 6
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp only [H, Pi.pow_apply, id]; ring
  · have h := (((hasDerivAt_id (1:ℝ)).sub_const 1).pow 2).const_mul (-2)
    refine (h.congr_deriv (by simp)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    simp only [H, Pi.pow_apply, id]; ring
  · have h := hasDerivAt_uu (p := 2) (by norm_num)
    rwa [up_two] at h
  · have hev : deriv (fun p => H p (uu p)) =ᶠ[𝓝 2] Dfun := by
      filter_upwards [Ioi_mem_nhds (by norm_num : (1:ℝ) < 2)] with q hq
      exact (hasDerivAt_Hu hq).deriv
    have hu := hasDerivAt_uu (p := 2) (by norm_num)
    have hu2 := differentiableAt_up.hasDerivAt
    have hsq : HasDerivAt (fun p => uu p ^ 2) (2 * uu 2 * up 2) 2 := (hu.pow 2).congr_deriv (by simp)
    have hprod : HasDerivAt (fun p => 2 * uu p * up p) (2 * (up 2 * up 2 + uu 2 * deriv up 2)) 2 := by
      have h := (hu.mul hu2).const_mul 2
      refine (h.congr_deriv (by ring)).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
      simp only [Pi.mul_apply]; ring
    have hD := (((hsq.const_mul (-2)).add ((hd_lin (-2) 1 2).mul hprod)).add
      (((hd_lin2 2).mul hu).add ((hd_quad 2).mul hu2))).add (hd_quad2 2)
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    refine (hD.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun q => ?_)
    · rw [uu_two, up_two]; ring
    · simp only [Dfun, Pi.add_apply, Pi.mul_apply]

end ThresholdB

end P18
