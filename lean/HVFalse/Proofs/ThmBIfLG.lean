/-
  HVFalse/Proofs/ThmBIfLG.lean - Theorem B "if" and C16a with NO textbook axiom, given the local⇒global principle
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  With LocGlobStmt (continuous + locally sub-mean ⇒ subharmonic) and UComp.Ufun_comp_local, U∘h is subharmonic for every
  entire h. That replaces Demailly (5.11) in C16a (h = product along a complex line) and in C16 (h = z·w along a disc), and
  Demailly (4.12) in U itself (h = id). When the theorem lands, instantiate `hLG` with it.
  integral_U_nonneg' and theoremB_if' are ThmBIf's proofs verbatim with the subharmonicity of U∘h taken from here.
-/
import HVFalse.Proofs.UComp

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace ThmBIfLG

open ThmBIf

/-- The local ⇒ global principle for continuous functions (statement of `subharmonic_of_continuous_local`). -/
def LocGlobStmt : Prop :=
  ∀ u : ℂ → ℝ, Continuous u → (∀ a, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → u a ≤ circleAverage u a r) →
    IsSubharmonic (fun z => ((u z : ℝ) : EReal))

variable {p : ℝ}

/-- `U∘h` is subharmonic for every entire `h`, given `LocGlobStmt`. -/
theorem Ufun_comp_subharmonic (hLG : LocGlobStmt) (hp1 : 1 < p) (hp2 : p < 2) {h : ℂ → ℂ} (hh : Differentiable ℂ h) :
    IsSubharmonic (fun z => ((Ufun p (h z) : ℝ) : EReal)) :=
  hLG _ (UComp.Ufun_comp_continuous hp1 hp2 hh) (UComp.Ufun_comp_local hp1 hp2 hh)

/-- `U` is subharmonic, given `LocGlobStmt` (replaces Demailly (4.12) in `ThmBIf.Ufun_subharmonic`). -/
theorem Ufun_subharmonic' (hLG : LocGlobStmt) (hp1 : 1 < p) (hp2 : p < 2) :
    IsSubharmonic (fun z => ((Ufun p z : ℝ) : EReal)) :=
  Ufun_comp_subharmonic hLG hp1 hp2 (h := id) differentiable_id

/-- **C16a** with no textbook axiom, given `LocGlobStmt`: `E` is plurisubharmonic on ℂ². -/
theorem E_psh' (hLG : LocGlobStmt) (hp1 : 1 < p) (hp2 : p < 2) :
    IsPSH (fun x : ℂ × ℂ => ((Efun p x.1 x.2 : ℝ) : EReal)) := by
  have hc : Continuous (fun x : ℂ × ℂ => Efun p x.1 x.2) := by
    simp only [Efun_eq_U]; exact (Ufun_continuous hp1 hp2).comp (continuous_fst.mul continuous_snd)
  refine ⟨fun x => EReal.coe_ne_top _, (continuous_coe_real_ereal.comp hc).upperSemicontinuous, fun a b => ?_⟩
  have hh : Differentiable ℂ (fun l : ℂ => (a.1 + l * b.1) * (a.2 + l * b.2)) := by fun_prop
  have := Ufun_comp_subharmonic hLG hp1 hp2 hh
  simpa [Efun_eq_U, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] using this

theorem integral_U_nonneg' (hLG : LocGlobStmt) (hp1 : 1 < p) (hp2 : p < 2) (g : Polynomial ℂ) (hg : g.eval 0 = 0) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π), Ufun p (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) := by
  have hq : 0 < p / 2 := by linarith
  have hUc := Ufun_continuous hp1 hp2
  have hsub := Ufun_comp_subharmonic hLG hp1 hp2 (h := fun l => g.eval l) g.differentiable
  have hcomp : Continuous (fun l : ℂ => Ufun p (g.eval l)) := hUc.comp g.continuous
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hcomp.continuousOn
  set n : ℕ := ⌈B⌉₊ with hn
  have hBn : B ≤ n := Nat.le_ceil B
  have h := hsub.2.2 n 0 1 one_pos
  simp only [hg, FailCole.trunc_coe] at h
  have hU0 : Ufun p 0 = 0 := by simp [Ufun, zero_rpow hq.ne']
  rw [hU0, max_eq_left (by simp : (0:ℝ) ≥ -(n : ℝ))] at h
  have heq : Set.EqOn (fun z => max (Ufun p (g.eval z)) (-(n : ℝ))) (fun z => Ufun p (g.eval z)) (sphere 0 |1|) := by
    intro z hz
    rw [abs_one] at hz
    have := hB z hz
    rw [Real.norm_eq_abs] at this
    exact max_eq_left (by linarith [neg_abs_le (Ufun p (g.eval z))])
  rw [circleAverage_congr_sphere heq, circleAverage_def, smul_eq_mul] at h
  simp only [circleMap_zero, Complex.ofReal_one, one_mul] at h
  have h2pi : 0 < (2 * π)⁻¹ := inv_pos.mpr two_pi_pos
  exact (mul_nonneg_iff_of_pos_left h2pi).mp h

/-- **C16, Theorem B "if"**, with no textbook axiom given `LocGlobStmt`. -/
theorem theoremB_if' {s : ℝ} (hLG : LocGlobStmt) (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (h2 : TwoVar p s) :
    HVIneq p s (hvConst p s) := by
  rw [discs_equiv hp1 hp2 hs]
  intro z w hw
  have hw0 : w.eval 0 = 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hw
  have hg : (z * w).eval 0 = 0 := by rw [Polynomial.eval_mul, hw0, mul_zero]
  have hU := integral_U_nonneg' hLG hp1 hp2 (z * w) hg
  have hp0 : 0 < p := by linarith
  have hcG : Continuous (fun θ : ℝ => G p s (z.eval (Complex.exp ((θ : ℂ) * Complex.I)))
      (w.eval (Complex.exp ((θ : ℂ) * Complex.I)))) := by
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by fun_prop
    exact (continuous_G p s hp0 hs).comp ((z.continuous.comp he).prodMk (w.continuous.comp he))
  have hcE : Continuous (fun θ : ℝ => Ufun p ((z * w).eval (Complex.exp ((θ : ℂ) * Complex.I)))) := by
    have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by fun_prop
    exact (Ufun_continuous hp1 hp2).comp ((z * w).continuous.comp he)
  refine le_trans hU (intervalIntegral.integral_mono_on two_pi_pos.le (hcE.intervalIntegrable _ _)
    (hcG.intervalIntegrable _ _) (fun θ _ => ?_))
  rw [Polynomial.eval_mul, ← Efun_eq_U]
  exact Efun_le_G hp1 hp2 hs h2 _ _

end ThmBIfLG

end P18
