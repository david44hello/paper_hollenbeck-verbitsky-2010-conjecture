/-
  HVFalse/Proofs/Truec.lean - Prop. 14 of the paper: the best constant is C* = λ*^{1/p} C_{s,p} (C22c)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Notation: C0 = hvConst p s > 0, g(λ) = λ^{1/p} C0, F = {λ | 1 ≤ λ ∧ LamFeasible p s λ}, S = {C | 0 < C ∧ HVIneqLp p s C}.
  Route. C22a in L^p form (DensityLp.hvIneq_iff_lp + ColeHom.truec_iff'): for λ ≥ 1, HVIneqLp p s (g λ) ↔ LamFeasible p s λ.
  (1) S = g '' F: for C ∈ S, C ≥ C0 (hMM), so λ(C) = (C/C0)^p ≥ 1 and g(λ(C)) = C; the other inclusion is C22a.
  (2) F is nonempty (from hfin through (1)) and bounded below by 1: λ* = sInf F ≥ 1 and IsGLB F λ*.
  (3) g is monotone on F and continuous at λ*, so IsGLB (g '' F) (g λ*) (Mathlib's IsGLB.isGLB_of_tendsto).
  hv_finite: (a^s + b^s)^{1/s} ≤ 2^{1/s} max(a, b) pointwise and [HV2000] (Cited.hv2000_riesz) give (HV) on trigonometric
  polynomials with C = 2^{1/s}/sin(π/p); DensityLp.hvIneq_iff_lp moves it to L^p. With R572.mm2022_lower_bound_one (the
  cited [MM2022, Sec. 2] bound at t = 1) this removes both hypotheses of C22c (truec_formula').
-/
import HVFalse.Proofs.DensityLp
import HVFalse.Proofs.ColeHom
import HVFalse.Proofs.Discs
import HVFalse.Cited.MM2022
import HVFalse.Proofs.R572

open Real Set Filter Topology

namespace P18

namespace Truec

theorem hvConst_pos {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 < hvConst p s := by
  unfold hvConst
  apply div_pos (Real.rpow_pos_of_pos two_pos _)
  apply mul_pos two_pos
  apply Real.cos_pos_of_mem_Ioo
  have hpi := Real.pi_pos
  have hp0 : 0 < p := by linarith
  constructor
  · have : 0 < π / (2 * p) := by positivity
    linarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- C22a on all of `L^p`: for `λ ≥ 1`, (HV) with constant `λ^{1/p} C_{s,p}` holds iff `λ` is feasible. -/
theorem truec_iff_lp {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    HVIneqLp p s (lam ^ (1 / p) * hvConst p s) ↔ LamFeasible p s lam :=
  (DensityLp.hvIneq_iff_lp hp1 hp2 hs
      (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hvConst_pos hp1 hp2))).symm.trans
    (ColeHom.truec_iff' hp1 hp2 hs hsS hlam)

/-- `g(λ(C)) = C` for `λ(C) = (C/C0)^p`. -/
theorem lam_of_const {p C C0 : ℝ} (hp : 0 < p) (hC : 0 < C) (hC0 : 0 < C0) :
    ((C / C0) ^ p) ^ (1 / p) * C0 = C := by
  rw [one_div, Real.rpow_rpow_inv (div_pos hC hC0).le hp.ne', div_mul_cancel₀ C hC0.ne']

/-- Step (1): the constants for which (HV) holds on `L^p` are exactly `g '' F`. -/
theorem consts_eq_image {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hMM : ∀ C : ℝ, 0 < C → HVIneqLp p s C → hvConst p s ≤ C) :
    {C : ℝ | 0 < C ∧ HVIneqLp p s C} =
      (fun lam => lam ^ (1 / p) * hvConst p s) '' {lam : ℝ | 1 ≤ lam ∧ LamFeasible p s lam} := by
  have hp : 0 < p := by linarith
  have hC0 := hvConst_pos (s := s) hp1 hp2
  ext C
  constructor
  · rintro ⟨hC, hHV⟩
    have hge : 1 ≤ (C / hvConst p s) ^ p :=
      Real.one_le_rpow ((one_le_div hC0).mpr (hMM C hC hHV)) hp.le
    refine ⟨(C / hvConst p s) ^ p, ⟨hge, (truec_iff_lp hp1 hp2 hs hsS hge).mp ?_⟩, lam_of_const hp hC hC0⟩
    rw [lam_of_const hp hC hC0]
    exact hHV
  · rintro ⟨lam, ⟨hlam, hf⟩, rfl⟩
    exact ⟨mul_pos (Real.rpow_pos_of_pos (by linarith) _) hC0, (truec_iff_lp hp1 hp2 hs hsS hlam).mpr hf⟩

/-- C22c, Prop. 14, exactly as Statements states it (CONDITIONAL on `hfin` and `hMM`). -/
theorem truec_formula {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hfin : ∃ C : ℝ, 0 < C ∧ HVIneqLp p s C) (hMM : ∀ C : ℝ, 0 < C → HVIneqLp p s C → hvConst p s ≤ C) :
    ∃ lamStar : ℝ, 1 ≤ lamStar ∧ IsGLB {lam : ℝ | 1 ≤ lam ∧ LamFeasible p s lam} lamStar ∧
      IsGLB {C : ℝ | 0 < C ∧ HVIneqLp p s C} (lamStar ^ (1 / p) * hvConst p s) := by
  have hp : 0 < p := by linarith
  have hC0 := hvConst_pos (s := s) hp1 hp2
  have himg := consts_eq_image hp1 hp2 hs hsS hMM
  set F := {lam : ℝ | 1 ≤ lam ∧ LamFeasible p s lam} with hF
  have hne : F.Nonempty := by
    obtain ⟨C, hC⟩ := hfin
    have hCmem : C ∈ {C : ℝ | 0 < C ∧ HVIneqLp p s C} := hC
    rw [himg] at hCmem
    obtain ⟨lam, hlam, -⟩ := hCmem
    exact ⟨lam, hlam⟩
  have hbdd : (1 : ℝ) ∈ lowerBounds F := fun lam hlam => hlam.1
  have hglb : IsGLB F (sInf F) := isGLB_csInf hne ⟨1, hbdd⟩
  have hone : 1 ≤ sInf F := le_csInf hne hbdd
  refine ⟨sInf F, hone, hglb, ?_⟩
  rw [himg]
  have hmono : MonotoneOn (fun lam : ℝ => lam ^ (1 / p) * hvConst p s) F := fun a ha b _ hab =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by linarith [ha.1]) hab (by positivity)) hC0.le
  have hcont : ContinuousAt (fun lam : ℝ => lam ^ (1 / p) * hvConst p s) (sInf F) :=
    (Real.continuousAt_rpow_const _ _ (Or.inl (by linarith))).mul continuousAt_const
  exact hglb.isGLB_of_tendsto hmono hne (hcont.tendsto.mono_left nhdsWithin_le_nhds)

/-! ## hv_finite: (HV) holds with some finite constant -/

/-- Pointwise: `(a^s + b^s)^{1/s} ≤ 2^{1/s} max(a, b)` for `a, b ≥ 0`, `s > 0`. -/
theorem hv_le_max {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a ^ s + b ^ s) ^ (1 / s) ≤ 2 ^ (1 / s) * max a b := by
  have hm : 0 ≤ max a b := le_max_of_le_left ha
  have h1 : a ^ s ≤ max a b ^ s := Real.rpow_le_rpow ha (le_max_left a b) hs.le
  have h2 : b ^ s ≤ max a b ^ s := Real.rpow_le_rpow hb (le_max_right a b) hs.le
  have hsum : a ^ s + b ^ s ≤ 2 * max a b ^ s := by linarith
  calc (a ^ s + b ^ s) ^ (1 / s) ≤ (2 * max a b ^ s) ^ (1 / s) :=
        Real.rpow_le_rpow (by positivity) hsum (by positivity)
    _ = 2 ^ (1 / s) * max a b := by
        rw [Real.mul_rpow (by norm_num) (by positivity), one_div, Real.rpow_rpow_inv hm hs.ne']

/-- The (HV) integrand raised to `p` is at most `(2^{1/s})^p max(|P₊|, |P₋|)^p`. -/
theorem hv_pow_le_max {p s : ℝ} (hp : 0 < p) (hs : 0 < s) (a b : ℂ) :
    ((‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s)) ^ p ≤ (2 ^ (1 / s)) ^ p * (max ‖a‖ ‖b‖) ^ p := by
  rw [← Real.mul_rpow (by positivity) (le_max_of_le_left (norm_nonneg a))]
  exact Real.rpow_le_rpow (by positivity) (hv_le_max hs (norm_nonneg a) (norm_nonneg b)) hp.le

theorem sin_pi_div_pos {p : ℝ} (hp1 : 1 < p) : 0 < sin (π / p) :=
  Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos (by linarith)) (div_lt_self Real.pi_pos hp1)

/-- (HV) on trigonometric polynomials with the constant `2^{1/s} / sin(π/p)`, from [HV2000]. -/
theorem hvIneq_finite {p s : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hs : 0 < s) :
    HVIneq p s (2 ^ (1 / s) * (1 / sin (π / p))) := by
  have hp : 0 < p := by linarith
  have hsin := sin_pi_div_pos hp1
  intro c
  have hP := continuous_Pplus c
  have hM := continuous_Pminus c
  have hL : Continuous fun θ => ((‖Pplus c θ‖ ^ s + ‖Pminus c θ‖ ^ s) ^ (1 / s)) ^ p :=
    (((hP.norm.rpow_const fun _ => Or.inr hs.le).add (hM.norm.rpow_const fun _ => Or.inr hs.le)).rpow_const
      fun _ => Or.inr (by positivity)).rpow_const fun _ => Or.inr hp.le
  have hR : Continuous fun θ => (2 ^ (1 / s)) ^ p * (max ‖Pplus c θ‖ ‖Pminus c θ‖) ^ p :=
    continuous_const.mul ((hP.norm.max hM.norm).rpow_const fun _ => Or.inr hp.le)
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  calc ∫ θ in (0 : ℝ)..(2 * π), ((‖Pplus c θ‖ ^ s + ‖Pminus c θ‖ ^ s) ^ (1 / s)) ^ p
      ≤ ∫ θ in (0 : ℝ)..(2 * π), (2 ^ (1 / s)) ^ p * (max ‖Pplus c θ‖ ‖Pminus c θ‖) ^ p :=
        intervalIntegral.integral_mono_on h2pi (hL.intervalIntegrable _ _) (hR.intervalIntegrable _ _)
          fun θ _ => hv_pow_le_max hp hs _ _
    _ = (2 ^ (1 / s)) ^ p * ∫ θ in (0 : ℝ)..(2 * π), (max ‖Pplus c θ‖ ‖Pminus c θ‖) ^ p :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (2 ^ (1 / s)) ^ p * ((1 / sin (π / p)) ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖trig c θ‖ ^ p) :=
        mul_le_mul_of_nonneg_left (Cited.hv2000_riesz p hp1 hp2 c) (by positivity)
    _ = (2 ^ (1 / s) * (1 / sin (π / p))) ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖trig c θ‖ ^ p := by
        rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]

/-- hv_finite: for `1 < p < 2`, `s > 0`, (HV) holds on all of `L^p` with some finite constant. -/
theorem hv_finite {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) : ∃ C : ℝ, 0 < C ∧ HVIneqLp p s C := by
  have hC : 0 < 2 ^ (1 / s) * (1 / sin (π / p)) :=
    mul_pos (Real.rpow_pos_of_pos two_pos _) (one_div_pos.mpr (sin_pi_div_pos hp1))
  exact ⟨_, hC, (DensityLp.hvIneq_iff_lp hp1 hp2 hs hC).mp (hvIneq_finite hp1 hp2.le hs)⟩

/-- C22c with no hypothesis: `hfin` from `hv_finite`, `hMM` from [MM2022] (R572.mm2022_lower_bound_one). -/
theorem truec_formula' {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∃ lamStar : ℝ, 1 ≤ lamStar ∧ IsGLB {lam : ℝ | 1 ≤ lam ∧ LamFeasible p s lam} lamStar ∧
      IsGLB {C : ℝ | 0 < C ∧ HVIneqLp p s C} (lamStar ^ (1 / p) * hvConst p s) :=
  truec_formula hp1 hp2 hs hsS (hv_finite hp1 hp2 hs)
    fun C hC hHV => R572.mm2022_lower_bound_one p s hp1 hp2 hs C hC hHV

end Truec

end P18
