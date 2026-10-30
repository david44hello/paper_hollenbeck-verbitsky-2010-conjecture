/-
  HVFalse/Proofs/R572Iff.lean - the equivalence in "Idea of the proof" (Sec. 1, l.137-140) as a chain: `∫_T |g|^q m(arg g)
  ≥ 0` for every polynomial `g` with `g(0) = 0` iff `|ζ|^q m(arg ζ)` has a subharmonic minorant `|ζ|^q φ(arg ζ)` iff the
  same inequality holds for every entire `g` with `g(0) = 0`; row C16i
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper composes two steps proved later; this file composes the two Lean steps (q = p/2, λ = 1):
  "⇒" (`minorant_of_integrals`): the Cole step of Prop. 4 (l.302-309), ColeHom.feasible_of_discs' (Cole's Thm 2.1
      [HKV2003] + Demailly (4.24) + homogeneity); it needs the integrals of polynomial `g` only.
  "⇐" (`integrals_of_minorant`): the step of Prop. 14, VComp.comp_submean (`V_φ∘g` is sub-mean on every circle, for
      every entire `g`), after making `φ` 2π-periodic (`φ` enters only through `arg ζ ∈ (-π, π]`).
-/
import HVFalse.Proofs.ColeHom
import HVFalse.Proofs.LamIf

open Real

namespace P18.R572Iff

variable {p s : ℝ}

/-- The integrand `|ζ|^q m(arg ζ)` is `M(ζ)` (paper l.299; `M_λ` at `λ = 1`). -/
theorem integrand_eq (ζ : ℂ) : ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ) = LamCole.Mlam p s 1 ζ := by
  rw [LamCole.Mlam_one]; rfl

/-- `φ` made `2π`-periodic: `φ(t)` with `t` reduced to `(-π, π]`. -/
noncomputable def per (φ : ℝ → ℝ) (t : ℝ) : ℝ := φ (toIocMod two_pi_pos (-π) t)

theorem per_periodic (φ : ℝ → ℝ) : Function.Periodic (per φ) (2 * π) := fun t => by
  simp only [per, toIocMod_add_right]

/-- `per φ` agrees with `φ` at every `arg ζ` (as `arg ζ ∈ (-π, π]`). -/
theorem per_arg (φ : ℝ → ℝ) (ζ : ℂ) : per φ (Complex.arg ζ) = φ (Complex.arg ζ) := by
  unfold per
  rw [(toIocMod_eq_self two_pi_pos).mpr ⟨Complex.neg_pi_lt_arg ζ, by linarith [Complex.arg_le_pi ζ]⟩]

/-- **"⇒"** (Prop. 4's Cole step): nonnegative integrals for every polynomial `g` with `g(0) = 0` give a subharmonic
minorant `|ζ|^q φ(arg ζ)` of `|ζ|^q m(arg ζ)`. -/
theorem minorant_of_integrals (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (h : ∀ g : Polynomial ℂ, g.eval 0 = 0 →
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖g.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
        mfun p s (Complex.arg (g.eval (Complex.exp ((θ : ℂ) * Complex.I))))) :
    ∃ φ : ℝ → ℝ, IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)) ∧
      ∀ ζ : ℂ, ‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) ≤ ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ) := by
  have hdisc : ∀ g : Polynomial ℂ, g.eval 0 = 0 →
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s 1 (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) := by
    intro g hg
    simpa only [integrand_eq] using h g hg
  obtain ⟨φ, hφ, hle⟩ := ColeHom.feasible_of_discs' hp1 hp2 hs hsS le_rfl hdisc
  refine ⟨φ, hφ.2, fun ζ => mul_le_mul_of_nonneg_left ?_ (rpow_nonneg (norm_nonneg ζ) _)⟩
  unfold mfun
  refine le_ciInf fun y => ?_
  simpa only [LamCole.gamLam_one] using hle y (Complex.arg ζ)

/-- **"⇐"** (Prop. 14's step): a subharmonic minorant `|ζ|^q φ(arg ζ)` of `|ζ|^q m(arg ζ)` gives
`∫₀^{2π} |g|^q m(arg g) dθ ≥ 0` for every entire `g` with `g(0) = 0`. -/
theorem integrals_of_minorant (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) {φ : ℝ → ℝ}
    (hsub : IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)))
    (hmin : ∀ ζ : ℂ, ‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) ≤ ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ))
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hg0 : g 0 = 0) :
    0 ≤ ∫ θ in (0 : ℝ)..(2 * π), ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
        mfun p s (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I)))) := by
  have hq0 : 1 / 2 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  have hq : 0 < p / 2 := by linarith
  have hφ : QSubtrig (p / 2) (per φ) := ⟨per_periodic φ, by simpa only [per_arg] using hsub⟩
  have hc : Continuous (per φ) := TrigCont.qsubtrig_continuous hq0 hq1 hφ
  -- the sub-mean value at 0 of `V_φ∘g` (V_φ(0) = 0)
  have h0 : 0 ≤ ∫ θ in (0 : ℝ)..(2 * π), VComp.Vfun (p / 2) (per φ) (g (Complex.exp ((θ : ℂ) * Complex.I))) := by
    have h := VComp.comp_submean hq0 hq1 hc hφ hg 0 one_pos
    simp only [hg0, VComp.Vfun_zero hq] at h
    rw [circleAverage_def, smul_eq_mul] at h
    simp only [circleMap_zero, Complex.ofReal_one, one_mul] at h
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr two_pi_pos)).mp h
  have he : Continuous (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) := by fun_prop
  have hcM : Continuous (fun θ : ℝ => ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
      mfun p s (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I))))) := by
    refine ((LamCole.Mlam_continuous hp1 hp2 hs hsS le_rfl).comp (hg.continuous.comp he)).congr fun θ => ?_
    exact (integrand_eq (g (Complex.exp ((θ : ℂ) * Complex.I)))).symm
  have hcV : Continuous (fun θ : ℝ => VComp.Vfun (p / 2) (per φ) (g (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    (VComp.Vfun_continuous hq hc hφ.1).comp (hg.continuous.comp he)
  refine le_trans h0 (intervalIntegral.integral_mono_on two_pi_pos.le (hcV.intervalIntegrable _ _)
    (hcM.intervalIntegrable _ _) (fun θ _ => ?_))
  simpa only [VComp.Vfun, per_arg] using hmin (g (Complex.exp ((θ : ℂ) * Complex.I)))

/-- **The equivalence of l.137-140** as a chain (`∫_T` with `dθ/2π`, l.178): (A) `∫_T |g|^q m(arg g) ≥ 0` for every
polynomial `g` with `g(0) = 0` ⇔ (B) `|ζ|^q m(arg ζ)` has a subharmonic minorant `|ζ|^q φ(arg ζ)` on `ℂ` ⇔ (C) the
inequality of (A) for every entire `g` with `g(0) = 0`. A ⇒ B: `minorant_of_integrals`; B ⇒ C: `integrals_of_minorant`;
C ⇒ A: a polynomial is entire. -/
theorem idea_chain (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ((∀ g : Polynomial ℂ, g.eval 0 = 0 →
        0 ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖g.eval (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
          mfun p s (Complex.arg (g.eval (Complex.exp ((θ : ℂ) * Complex.I))))) ↔
      ∃ φ : ℝ → ℝ, IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)) ∧
        ∀ ζ : ℂ, ‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) ≤ ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ)) ∧
    ((∃ φ : ℝ → ℝ, IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)) ∧
        ∀ ζ : ℂ, ‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) ≤ ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ)) ↔
      ∀ g : ℂ → ℂ, Differentiable ℂ g → g 0 = 0 →
        0 ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
          mfun p s (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I))))) := by
  have hpos : (0 : ℝ) < (2 * π)⁻¹ := inv_pos.mpr two_pi_pos
  have hBC : ∀ {φ : ℝ → ℝ}, IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)) →
      (∀ ζ : ℂ, ‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) ≤ ‖ζ‖ ^ (p / 2) * mfun p s (Complex.arg ζ)) →
      ∀ g : ℂ → ℂ, Differentiable ℂ g → g 0 = 0 →
        0 ≤ (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
          mfun p s (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I)))) :=
    fun hsub hmin g hg hg0 => mul_nonneg hpos.le (integrals_of_minorant hp1 hp2 hs hsS hsub hmin hg hg0)
  refine ⟨⟨fun hA => ?_, fun ⟨φ, hsub, hmin⟩ g hg => hBC hsub hmin (fun l => g.eval l) g.differentiable hg⟩,
    ⟨fun ⟨φ, hsub, hmin⟩ => hBC hsub hmin, fun hC => ?_⟩⟩
  · exact minorant_of_integrals hp1 hp2 hs hsS fun g hg => (mul_nonneg_iff_of_pos_left hpos).mp (hA g hg)
  · exact minorant_of_integrals hp1 hp2 hs hsS fun g hg =>
      (mul_nonneg_iff_of_pos_left hpos).mp (hC (fun l => g.eval l) g.differentiable hg)

end P18.R572Iff
