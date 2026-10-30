/-
  HVFalse/Proofs/ColeHom.lean - the paper's proof that the largest subharmonic minorant is q-homogeneous (S6)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  The paper, proof of Prop. 4 (l.300-309). Let F be continuous and q-homogeneous with ∫ F∘g ≥ 0 for every polynomial g, g(0) = 0.
  (a) S = {v subharmonic, v ≤ F}. Cole's Thm 2.1 (E = {0}) gives v₀ ∈ S with v₀(0) ≥ 0.
  (b) V = (sup S)⋆, the upper regularization. Demailly (4.24), PROVED in Envelope.lean: V is subharmonic (S is locally
      bounded above by F).
      V ≤ F as F is continuous; V ≥ every v ∈ S; so V(0) ≥ 0.
  (c) For r > 0, r^{-q} V(r·) ∈ S (`scale_subharmonic`, proved from the definition), so r^{-q} V(rζ) ≤ V(ζ). Using r and
      1/r, V is q-homogeneous (`cole_hom`). Finiteness off 0 and the profile: Sector E1c/E1d, as in LamCole.
  Then `cole_step'` (the λ-instance) and the Cole-only `feasible_of_discs'`, `truec_iff'` (C22a), `prop_fail'` (C09).
-/
import HVFalse.Defs.PotentialC
import HVFalse.Proofs.Envelope
import HVFalse.Cited.HKV21
import HVFalse.Proofs.LamIf

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace ColeHom

/-! ### Dilations and circle averages -/

theorem circleMap_mul (r : ℝ) (a : ℂ) (ρ θ : ℝ) :
    (r : ℂ) * circleMap a ρ θ = circleMap ((r : ℂ) * a) (r * ρ) θ := by
  simp only [circleMap, Complex.ofReal_mul]; ring

theorem circleAverage_dilate (f : ℂ → ℝ) (r : ℝ) (a : ℂ) (ρ : ℝ) :
    circleAverage (fun z => f ((r : ℂ) * z)) a ρ = circleAverage f ((r : ℂ) * a) (r * ρ) := by
  simp only [circleAverage_def, circleMap_mul]

theorem circleIntegrable_dilate {f : ℂ → ℝ} {r : ℝ} {a : ℂ} {ρ : ℝ}
    (h : CircleIntegrable f ((r : ℂ) * a) (r * ρ)) : CircleIntegrable (fun z => f ((r : ℂ) * z)) a ρ := by
  unfold CircleIntegrable at h ⊢
  simpa only [circleMap_mul] using h

theorem circleIntegrable_max_const {f : ℂ → ℝ} {a : ℂ} {ρ : ℝ} (h : CircleIntegrable f a ρ) (t : ℝ) :
    CircleIntegrable (fun z => max (f z) t) a ρ := by
  unfold CircleIntegrable at h ⊢
  have hc : IntervalIntegrable (fun _ : ℝ => t) volume 0 (2 * π) := intervalIntegrable_const
  exact ⟨Integrable.sup h.1 hc.1, Integrable.sup h.2 hc.2⟩

/-- A real-level truncation `max(w, -t)` of a sub-mean function is sub-mean. -/
theorem max_const_submean {w : ℂ → ℝ} {b : ℂ} {R t : ℝ} (hint : CircleIntegrable w b R)
    (hsub : w b ≤ circleAverage w b R) : max (w b) (-t) ≤ circleAverage (fun z => max (w z) (-t)) b R := by
  have hint' := circleIntegrable_max_const hint (-t)
  have h1 : circleAverage w b R ≤ circleAverage (fun z => max (w z) (-t)) b R :=
    circleAverage_mono hint hint' (fun z _ => le_max_left _ _)
  have h2 : -t ≤ circleAverage (fun z => max (w z) (-t)) b R := by
    have := circleAverage_mono (circleIntegrable_const (-t) b R) hint' (fun z _ => le_max_right _ _)
    rwa [circleAverage_const] at this
  exact max_le (hsub.trans h1) h2

/-! ### Scaling: `c · V(r ·)` is subharmonic (`c, r > 0`) -/

theorem ereal_cmul_ne_top {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) : (c : EReal) * x ≠ ⊤ := by
  induction x using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_ne_top
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
  | top => exact absurd rfl hx

theorem continuous_cmul {c : ℝ} (hc : 0 < c) : Continuous (fun x : EReal => (c : EReal) * x) := by
  have hc0 : (c : EReal) ≠ 0 := by exact_mod_cast hc.ne'
  rw [continuous_iff_continuousAt]
  intro x
  have h := EReal.continuousAt_mul (p := ((c : EReal), x)) (Or.inl hc0) (Or.inl hc0)
    (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))
  exact h.comp (continuous_const.prodMk continuous_id).continuousAt

theorem monotone_cmul {c : ℝ} (hc : 0 < c) : Monotone (fun x : EReal => (c : EReal) * x) :=
  fun _ _ h => mul_le_mul_of_nonneg_left h (by exact_mod_cast hc.le)

theorem trunc_bot (m : ℕ) : trunc m (⊥ : EReal) = -(m : ℝ) := by
  unfold trunc
  rw [max_eq_right bot_le, show (-(m : EReal)) = ((-(m : ℝ) : ℝ) : EReal) by simp, EReal.toReal_coe]

/-- `trunc n (c x) = c · max(trunc N x, -n/c)` when `N ≥ n/c`. -/
theorem trunc_cmul {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊤) (n N : ℕ) (hN : (n : ℝ) / c ≤ N) :
    trunc n ((c : EReal) * x) = c * max (trunc N x) (-((n : ℝ) / c)) := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.coe_mul_bot_of_pos hc, trunc_bot, trunc_bot, max_eq_right (by linarith)]
    field_simp
  | coe y =>
    rw [← EReal.coe_mul, FailCole.trunc_coe, FailCole.trunc_coe, max_assoc,
      max_eq_right (show -(N : ℝ) ≤ -((n : ℝ) / c) by linarith), mul_max_of_nonneg _ _ hc.le]
    congr 1
    field_simp
  | top => exact absurd rfl hx

theorem scale_subharmonic {V : ℂ → EReal} (hV : IsSubharmonic V) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IsSubharmonic (fun ζ => (c : EReal) * V ((r : ℂ) * ζ)) := by
  refine ⟨fun z => ereal_cmul_ne_top hc (hV.1 _), ?_, ?_⟩
  · have hu : UpperSemicontinuous (fun ζ => V ((r : ℂ) * ζ)) := fun ζ =>
      (hV.2.1 ((r : ℂ) * ζ)).comp (continuous_const.mul continuous_id).continuousAt
    exact (continuous_cmul hc).comp_upperSemicontinuous hu (monotone_cmul hc)
  · intro n a ρ hρ
    obtain ⟨N, hN⟩ := exists_nat_ge ((n : ℝ) / c)
    have hrep : ∀ z, trunc n ((c : EReal) * V ((r : ℂ) * z)) =
        c * max (trunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c)) :=
      fun z => trunc_cmul hc (hV.1 _) n N hN
    simp only [hrep]
    have hint : CircleIntegrable (fun z => trunc N (V z)) ((r : ℂ) * a) (r * ρ) := Sector.trunc_circleIntegrable hV N _ _
    have hsub : trunc N (V ((r : ℂ) * a)) ≤ circleAverage (fun z => trunc N (V z)) ((r : ℂ) * a) (r * ρ) :=
      hV.2.2 N _ _ (by positivity)
    have hint2 := circleIntegrable_dilate hint
    have hsub2 : trunc N (V ((r : ℂ) * a)) ≤ circleAverage (fun z => trunc N (V ((r : ℂ) * z))) a ρ := by
      rw [circleAverage_dilate (fun z => trunc N (V z))]; exact hsub
    have hm := max_const_submean (t := (n : ℝ) / c) hint2 hsub2
    have hsm : circleAverage (fun z => c * max (trunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c))) a ρ =
        c * circleAverage (fun z => max (trunc N (V ((r : ℂ) * z))) (-((n : ℝ) / c))) a ρ := by
      simp only [← smul_eq_mul]; exact circleAverage_fun_smul
    rw [hsm]
    exact mul_le_mul_of_nonneg_left hm hc.le

/-! ### Upper regularization -/

theorem le_uscRegC (u : ℂ → EReal) (z : ℂ) : u z ≤ uscRegC u z := by
  unfold uscRegC
  exact le_iInf fun ε => le_iSup₂_of_le z (mem_ball_self ε.2) le_rfl

theorem uscRegC_le {u : ℂ → EReal} {F : ℂ → ℝ} (hF : Continuous F) (hle : ∀ z, u z ≤ (F z : EReal)) (z : ℂ) :
    uscRegC u z ≤ (F z : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro b hb
  have hb' : F z < b := EReal.coe_lt_coe_iff.mp hb
  obtain ⟨ε, hε, hball⟩ := Metric.continuousAt_iff.mp hF.continuousAt (b - F z) (by linarith)
  unfold uscRegC
  refine (iInf_le _ ⟨ε, hε⟩).trans ?_
  refine iSup₂_le fun y hy => (hle y).trans ?_
  have h := hball (mem_ball.mp hy)
  rw [Real.dist_eq] at h
  exact EReal.coe_le_coe_iff.mpr (by linarith [le_abs_self (F y - F z)])

theorem locUnif_of_le {ι : Type} (u : ι → ℂ → EReal) {F : ℂ → ℝ} (hF : Continuous F)
    (hle : ∀ i z, u i z ≤ (F z : EReal)) : LocUnifBddAboveC u := by
  intro z
  obtain ⟨B, hB⟩ := (isCompact_closedBall z 1).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨1, one_pos, B, fun i y hy => (hle i y).trans (EReal.coe_le_coe_iff.mpr ?_)⟩
  have h := hB y (ball_subset_closedBall hy)
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans h

/-! ### The homogeneous minorant (paper l.294-309) -/

/-- **Cole's theorem + the paper's homogeneity proof**: for continuous `q`-homogeneous `F` with nonnegative disc integrals
(discs `g`, `g(0) = 0`), there is a `q`-homogeneous subharmonic `G ≤ F` with `G(0) ≥ 0`. -/
theorem cole_hom {F : ℂ → ℝ} (hFc : Continuous F) {q : ℝ}
    (hhom : ∀ (r : ℝ) (z : ℂ), 0 < r → F ((r : ℂ) * z) = r ^ q * F z)
    (hdisc : ∀ g : Polynomial ℂ, g.eval 0 = 0 →
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), F (g.eval (Complex.exp ((θ : ℂ) * Complex.I)))) :
    ∃ G : ℂ → EReal, IsSubharmonic G ∧ (∀ z, G z ≤ ((F z : ℝ) : EReal)) ∧ 0 ≤ G 0 ∧
      ∀ (t : ℝ) (z : ℂ), 0 < t → G ((t : ℂ) * z) = ((t ^ q : ℝ) : EReal) * G z := by
  set Fe : ℂ → EReal := fun z => ((F z : ℝ) : EReal) with hFe
  have hFusc : UpperSemicontinuous Fe := (continuous_coe_real_ereal.comp hFc).upperSemicontinuous
  have h21 : ∀ f : Polynomial ℂ, f.eval 0 ∈ ({0} : Set ℂ) →
      CircleIntNonneg (fun θ => Fe (f.eval (Complex.exp ((θ : ℂ) * Complex.I)))) := by
    intro f hf n
    have hcont : Continuous (fun θ : ℝ => F (f.eval (Complex.exp ((θ : ℂ) * Complex.I)))) :=
      hFc.comp (f.continuous.comp (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)))
    have hcont' : Continuous (fun θ : ℝ => trunc n (Fe (f.eval (Complex.exp ((θ : ℂ) * Complex.I))))) := by
      simp only [hFe, FailCole.trunc_coe]
      exact hcont.max continuous_const
    exact le_trans (hdisc f hf) (intervalIntegral.integral_mono_on two_pi_pos.le (hcont.intervalIntegrable _ _)
      (hcont'.intervalIntegrable _ _) (fun θ _ => FailCole.le_trunc_coe n _))
  obtain ⟨v0, hv0, hv0F, hv00⟩ :=
    Cited.hkv_thm21 Fe hFusc (fun z => EReal.coe_ne_top _) {0} (singleton_nonempty 0) h21
  -- the family of all subharmonic minorants of `F`, its upper envelope and the regularization `V`
  let S := {v : ℂ → EReal // IsSubharmonic v ∧ ∀ z, v z ≤ Fe z}
  set V : ℂ → EReal := uscRegC (fun z => ⨆ v : S, v.1 z) with hV
  have hVsh : IsSubharmonic V := Envelope.demailly_4_24 (fun v : S => v.1) (fun v => v.2.1)
    (locUnif_of_le _ hFc (fun v z => v.2.2 z))
  have hVF : ∀ z, V z ≤ Fe z := uscRegC_le hFc (fun z => iSup_le fun v => v.2.2 z)
  have hge : ∀ v : S, ∀ z, v.1 z ≤ V z := fun v z => (le_iSup (fun v : S => v.1 z) v).trans (le_uscRegC (fun z => ⨆ v : S, v.1 z) z)
  have hV0 : 0 ≤ V 0 := (hv00 0 rfl).trans (hge ⟨v0, hv0, hv0F⟩ 0)
  -- `r^{-q} V(r·)` is again a subharmonic minorant, hence `≤ V`
  have hscale : ∀ r : ℝ, 0 < r → ∀ ζ, ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * ζ) ≤ V ζ := by
    intro r hr ζ
    have hW : IsSubharmonic (fun ζ => ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * ζ)) :=
      scale_subharmonic hVsh (by positivity) hr
    have hWF : ∀ z, ((r ^ (-q) : ℝ) : EReal) * V ((r : ℂ) * z) ≤ Fe z := by
      intro z
      have h1 := Sector.ereal_mul_le (by positivity : 0 < r ^ (-q)) (hVF ((r : ℂ) * z))
      refine h1.trans (le_of_eq ?_)
      simp only [hFe]
      rw [hhom r z hr, ← mul_assoc, ← rpow_add hr, neg_add_cancel, rpow_zero, one_mul]
    exact hge ⟨_, hW, hWF⟩ ζ
  refine ⟨V, hVsh, hVF, hV0, fun t z ht => ?_⟩
  have h1 := hscale t ht z
  have h2 := hscale t⁻¹ (inv_pos.mpr ht) ((t : ℂ) * z)
  have e1 : ((t⁻¹ : ℝ) : ℂ) * ((t : ℂ) * z) = z := by
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
  have e2 : (t⁻¹) ^ (-q) = t ^ q := by rw [inv_rpow ht.le, rpow_neg ht.le, inv_inv]
  rw [e1, e2] at h2
  refine le_antisymm ?_ h2
  have h0 : (0 : EReal) ≤ ((t ^ q : ℝ) : EReal) := by exact_mod_cast rpow_nonneg ht.le q
  have h3 := mul_le_mul_of_nonneg_left h1 h0
  rwa [← mul_assoc, ← EReal.coe_mul, ← rpow_add ht, add_neg_cancel, rpow_zero, EReal.coe_one, one_mul] at h3

/-! ### Cole-only versions of the λ-chain -/

variable {p s lam : ℝ}

/-- The Cole step of LamCole, now from Cole's Thm 2.1 alone + Demailly (4.24) (no p.244 Remark). -/
theorem cole_step' (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam)
    (hdisc : ∀ g : Polynomial ℂ, g.eval 0 = 0 →
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (Complex.exp ((θ : ℂ) * Complex.I)))) :
    ∃ G : ℂ → EReal, IsSubharmonic G ∧ (∀ z, G z ≤ ((LamCole.Mlam p s lam z : ℝ) : EReal)) ∧ 0 ≤ G 0 ∧
      ∀ (t : ℝ) (z : ℂ), 0 < t → G ((t : ℂ) * z) = ((t ^ (p / 2) : ℝ) : EReal) * G z :=
  cole_hom (LamCole.Mlam_continuous hp1 hp2 hs hsS hlam) (fun r z hr => LamCole.Mlam_homog (by linarith) r z hr) hdisc

/-- λ-L2, Cole-only: nonnegative disc integrals of `M_λ` make `λ` feasible. -/
theorem feasible_of_discs' (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam)
    (hdisc : ∀ g : Polynomial ℂ, g.eval 0 = 0 →
      0 ≤ ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (Complex.exp ((θ : ℂ) * Complex.I)))) :
    LamFeasible p s lam := by
  have hq : 0 < p / 2 := by linarith
  have hq0 : 1 / 2 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  obtain ⟨G, hG, hGF, hG0, hGhom⟩ := cole_step' hp1 hp2 hs hsS hlam hdisc
  have hfin := Sector.homog_finite hq0 hq1 hG hGhom hG0
  obtain ⟨-, hper, hpolar⟩ := Sector.homog_profile hq0 hq1 hG hGhom hfin
  set φ : ℝ → ℝ := fun t => (G (Complex.exp ((t : ℂ) * Complex.I))).toReal with hφ
  have hGzero : G 0 = 0 := le_antisymm (Sector.homog_zero_le hq hG.1 hGhom) hG0
  have hVG : (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * φ (Complex.arg ζ) : ℝ) : EReal)) = G := by
    funext ζ
    by_cases hζ : ζ = 0
    · subst hζ; simp [hGzero, zero_rpow hq.ne']
    · exact (hpolar ζ hζ).symm
  refine ⟨φ, ⟨hper, ?_⟩, fun y t => ?_⟩
  · rw [hVG]; exact hG
  · have h1 := hGF (Complex.exp ((t : ℂ) * Complex.I))
    rw [← EReal.coe_toReal (hG.1 _) (hfin t), LamCole.Mlam_exp] at h1
    exact (EReal.coe_le_coe_iff.mp h1).trans (LamCole.mlam_le hp1 hp2 hs hsS hlam y t)

/-- Prop. 14 "only if", Cole-only: (HV) with `λ^{1/p} C` ⇒ `λ` feasible. -/
theorem feasible_of_hv' (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam)
    (hHV : HVIneq p s (lam ^ (1 / p) * hvConst p s)) : LamFeasible p s lam := by
  have hD := (LamLift.discs_lam hp1 hp2 hs (by linarith)).mp hHV
  by_contra hnf
  have hbad : ∃ g : Polynomial ℂ, g.eval 0 = 0 ∧
      ∫ θ in (0 : ℝ)..(2 * π), LamCole.Mlam p s lam (g.eval (Complex.exp ((θ : ℂ) * Complex.I))) < 0 := by
    by_contra hcon
    push Not at hcon
    exact hnf (feasible_of_discs' hp1 hp2 hs hsS hlam hcon)
  obtain ⟨g, hg0, hneg⟩ := hbad
  exact LamLift.not_discIneqLam_of_bad_disc hp1 hp2 hs hsS hlam g hg0 hneg hD

/-- **C22a, Cole-only** (Cole's Thm 2.1 + Demailly (4.24) + (5.11)). -/
theorem truec_iff' (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    HVIneq p s (lam ^ (1 / p) * hvConst p s) ↔ LamFeasible p s lam :=
  ⟨feasible_of_hv' hp1 hp2 hs hsS hlam,
    fun hf => (LamLift.discs_lam hp1 hp2 hs (by linarith)).mpr (LamIf.lam_if hp1 hp2 hs hf)⟩

/-- **C09 (Prop. fail), Cole-only, through λ = 1**: a failure point `Γ(y*,t*) < e(t*)`, `t* ∈ [-π, π]`, refutes (HV) with
the conjectured constant (forcing: a q-subtrigonometric `φ ≤ m` would have `φ ≥ e` on `[-π, π]`). -/
theorem prop_fail' (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p s y t < ee p t) : ¬ HVIneq p s (hvConst p s) := by
  intro hHV
  have hHV1 : HVIneq p s ((1 : ℝ) ^ (1 / p) * hvConst p s) := by rwa [one_rpow, one_mul]
  obtain ⟨φ, hφ, hle⟩ := feasible_of_hv' hp1 hp2 hs hsS le_rfl hHV1
  have hle' : ∀ y t : ℝ, φ t ≤ Gam p s y t := fun y t => by
    have := hle y t; rwa [LamCole.gamLam_one] at this
  have htc := Sector.qsubtrig_trigConvex (by linarith) (by linarith) hφ
  obtain ⟨y0, t0, ht0, hlt⟩ := hpt
  have hfor := (forcing_of_trigConvex hp1 hp2 hs hφ.1 htc hle').2 t0 ht0
  have := hle' y0 t0
  linarith

end ColeHom

end P18
