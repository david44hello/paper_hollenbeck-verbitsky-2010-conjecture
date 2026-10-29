/-
  HVFalse/Proofs/NewRows12.lean - claims of the paper first stated in Lean here (A1-A4)
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  A4 (after Prop. 13, l.611, "where Q₄(p) → 0 as p → 4/3"): Q₄ = Acoef is continuous at 4/3 (K(4/3, u) = 2√2/3 ≠ 0)
     and vanishes there (H(4/3, u(4/3)) = 0, C10a6).
  A1 (Sec. 2, l.202, "Γ(y,π/p) - e(π/p) = (p/8)(sec²ϑ - s)y² + O(y⁴)", every s > 0): the one-variable expansions of
     SaddleValley (term1_expand with c = 0, term2_expand) and e(π/p) = 0; the y² coefficients differ by (p/8)(S - s).
  A2 (Sec. 2, l.180-183): U = Re(tanϑ ζ^q) is harmonic on the slit plane; on {Re ζ < 0}, U = max(h₁, h₂) with h₁, h₂ the
     continuations of U from the upper and lower half-planes (Re(c(-ζ)^q), harmonic there).
  A3 (Sec. 3, l.235, "φ' has bounded variation"): on a window [c, c + π/(4q)],
     φ'₊ = R(tan θ)·q/cos θ - q sin θ·g(tan θ) (θ = q(t-c), g the convex transform TrigCont.convexOn_transform, R its
     right derivative, monotone); every factor is monotone or (monotone) + const·(monotone), so BV (Mathlib's
     BoundedVariationOn.mul; the sum lemma bv_add is proved here); windows are joined by eVariationOn.Icc_add_Icc.
-/
import HVFalse.Proofs.SmallB
import HVFalse.Proofs.UComp
import HVFalse.Proofs.TrigCont

open Real Asymptotics Filter Topology Set

namespace P18

namespace NewRows12

/-- **A4**, after Prop. 13 (l.611): `Q₄(p) → 0` as `p → 4/3`. -/
theorem Acoef_tendsto : Filter.Tendsto Acoef (nhds (4 / 3)) (nhds 0) := by
  have h38 : π / (2 * (4 / 3 : ℝ)) = 3 * π / 8 := by ring
  have hcos : cos (π / (2 * (4 / 3 : ℝ))) ≠ 0 := by
    rw [h38]; exact (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩).ne'
  have hu : uu (4 / 3) = 3 + 2 * √2 := by unfold uu; rw [h38]; exact tan_three_pi_div_eight_sq
  have hK : K (4 / 3) (uu (4 / 3)) ≠ 0 := by rw [hu, K_four_thirds]; positivity
  have hθ : ContinuousAt (fun p : ℝ => π / (2 * p)) (4 / 3) :=
    continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by norm_num)
  have htan : ContinuousAt (fun p : ℝ => tan (π / (2 * p))) (4 / 3) :=
    ContinuousAt.comp (g := tan) (continuousAt_tan.mpr hcos) hθ
  have hcosc : ContinuousAt (fun p : ℝ => cos (π / (2 * p))) (4 / 3) := continuous_cos.continuousAt.comp hθ
  have hS : ContinuousAt Ssec (4 / 3) := by
    unfold Ssec
    exact continuousAt_const.div (hcosc.pow 2) (pow_ne_zero 2 hcos)
  have huc : ContinuousAt uu (4 / 3) := by unfold uu; exact htan.pow 2
  have hHc : ContinuousAt (fun p => H p (uu p)) (4 / 3) := by unfold H; fun_prop
  have hKc : ContinuousAt (fun p => K p (uu p)) (4 / 3) := by unfold K; fun_prop
  have hcont : ContinuousAt Acoef (4 / 3) := by
    unfold Acoef
    exact ((((continuousAt_id.mul hS).mul huc).mul hHc).neg).div (continuousAt_const.mul hKc)
      (mul_ne_zero (by norm_num) hK)
  have h0 : Acoef (4 / 3) = 0 := by unfold Acoef; rw [H_at_four_thirds]; simp
  simpa [h0] using hcont.tendsto

/-- The `y²` coefficients of the two terms of `Γ(·, π/p)` differ by `(p/8)(S - s)`. -/
theorem coef_y2 {p s : ℝ} (hp1 : 1 < p) (hs : 0 < s) :
    p / 2 * ((1 / 2 + sin (π / p) * 0) / (1 + cos (2 * (π / (2 * p))))) - p / s * ((s / 2) ^ 2 / 2)
      = p / 8 * (Ssec p - s) := by
  obtain ⟨hS, hD, -, -⟩ := SaddleValley.trig_T hp1
  rw [hS, hD]
  field_simp
  ring

/-- **A1**, Sec. 2 (l.202): `Γ(y,π/p) - e(π/p) = (p/8)(sec²ϑ - s)y² + O(y⁴)` for every `s > 0`. -/
theorem gam_expansion_pi_p {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      |Gam p s y (π / p) - ee p (π / p) - p / 8 * (Ssec p - s) * y ^ 2| ≤ C * y ^ 4 := by
  have h1 := SaddleValley.term1_expand hp1 hp2 0
  have h2 := SaddleValley.term2_expand s (p / s)
  have h64 : (fun y : ℝ => y ^ 6) =O[𝓝 0] (fun y => y ^ 4) := SaddleValley.pow_isBigO_pow (by norm_num)
  have hee : ee p (π / p) = 0 := (ee_contact_zero (by linarith)).1
  have hcoef := coef_y2 hp1 hs
  have hO : (fun y => Gam p s y (π / p) - ee p (π / p) - p / 8 * (Ssec p - s) * y ^ 2) =O[𝓝 0]
      (fun y => y ^ 4) := by
    refine (((h1.sub h2).trans h64).add ((isBigO_refl (fun y : ℝ => y ^ 4) _).const_mul_left
      ((p / 2 * ((1 / 24 - cos (π / p) * 0 ^ 2 / 2) / (1 + cos (2 * (π / (2 * p)))))
          + p / 2 * (p / 2 - 1) / 2 * ((1 / 2 + sin (π / p) * 0) / (1 + cos (2 * (π / (2 * p))))) ^ 2)
        - (p / s * ((s / 2) ^ 4 / 24) + p / s * (p / s - 1) / 2 * ((s / 2) ^ 2 / 2) ^ 2)))).congr_left
      (fun y => ?_)
    have e1 : cos (π / p - 0 * y ^ 2) = cos (π / p) := by simp
    simp only [Gam, hee, e1]
    linear_combination (-y ^ 2) * hcoef
  obtain ⟨C, hC⟩ := hO.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hC
  refine ⟨C, δ, hδ, fun y hy => ?_⟩
  have h := hball (show dist y 0 < δ by rwa [Real.dist_eq, sub_zero])
  rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 4)] at h

/-! ### A2: `U` is harmonic off `(-∞, 0]` and has a convex corner there -/

/-- **A2a**, Sec. 2 (l.181): `U(ζ) = |ζ|^q e(arg ζ)` is harmonic on the slit plane (`U = Re(tanϑ ζ^q)`). -/
theorem U_harmonic_slit {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ)) Complex.slitPlane := by
  have hfun : (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ))
      = fun ζ => ((tan (π / (2 * p)) : ℂ) * ζ ^ ((p / 2 : ℝ) : ℂ)).re :=
    funext fun ζ => ThmBIf.Ufun_eq_re hp1 hp2 ζ
  rw [hfun]
  intro z hz
  exact (analyticAt_const.mul (analyticAt_id.cpow analyticAt_const hz)).harmonicAt_re

/-- The branch of `U` continued from the lower half-plane across `(-∞, 0)`. -/
noncomputable def hbranch2 (p : ℝ) (ζ : ℂ) : ℝ :=
  ((((tan (π / (2 * p)) * cos (p / 2 * π) : ℝ) : ℂ) - ((tan (π / (2 * p)) * sin (p / 2 * π) : ℝ) : ℂ) * Complex.I)
    * (-ζ) ^ ((p / 2 : ℝ) : ℂ)).re

theorem hbranch2_polar {p : ℝ} {ζ : ℂ} (hζ : ζ ≠ 0) :
    hbranch2 p ζ = tan (π / (2 * p)) * (‖ζ‖ ^ (p / 2) * cos (p / 2 * Complex.arg (-ζ) - p / 2 * π)) := by
  unfold hbranch2
  rw [Sector.re_coef_cpow (neg_ne_zero.mpr hζ), norm_neg, cos_sub]
  ring

/-- `cos b ≤ cos a` for `0 ≤ a ≤ b`, `a + b ≤ 2π`. -/
theorem cos_le_of_add_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hsum : a + b ≤ 2 * π) : cos b ≤ cos a := by
  by_cases hb : b ≤ π
  · exact cos_le_cos_of_nonneg_of_le_pi ha hb hab
  · push Not at hb
    have hw : cos b = cos (2 * π - b) := by rw [cos_sub, cos_two_pi, sin_two_pi]; ring
    rw [hw]
    exact cos_le_cos_of_nonneg_of_le_pi ha (by linarith) (by linarith)

/-- **A2b**, Sec. 2 (l.181-182): at a point of `(-∞, 0)`, `U` is locally the maximum of two harmonic functions
(the continuations of `U` from the upper and from the lower half-plane): a convex corner. -/
theorem U_convex_corner {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {ζ0 : ℂ} (hre : ζ0.re < 0) (him : ζ0.im = 0) :
    ∃ V ∈ nhds ζ0, ∃ h1 h2 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h1 V ∧ InnerProductSpace.HarmonicOnNhd h2 V ∧
      ∀ ζ ∈ V, ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ) = max (h1 ζ) (h2 ζ) := by
  have hq : 0 < p / 2 := by linarith
  have hq1 : p / 2 < 1 := by linarith
  have hT := ThmBIf.tan_th_pos hp1 hp2
  set V : Set ℂ := {ζ | ζ.re < 0} with hV
  have hVo : IsOpen V := isOpen_lt Complex.continuous_re continuous_const
  have hslit : ∀ ζ ∈ V, -ζ ∈ Complex.slitPlane := fun ζ hζ =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simp only [Complex.neg_re]; exact neg_pos.mpr hζ))
  refine ⟨V, hVo.mem_nhds hre, ThmBIf.hbranch p, hbranch2 p, ?_, ?_, ?_⟩
  · intro z hz
    unfold ThmBIf.hbranch
    exact (analyticAt_const.mul ((analyticAt_id.neg).cpow analyticAt_const (hslit z hz))).harmonicAt_re
  · intro z hz
    unfold hbranch2
    exact (analyticAt_const.mul ((analyticAt_id.neg).cpow analyticAt_const (hslit z hz))).harmonicAt_re
  intro ζ hζ
  have hζre : ζ.re < 0 := hζ
  have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0] at hζre; simp at hζre
  rw [ThmBIf.hbranch_polar hζ0, hbranch2_polar hζ0]
  unfold ee
  set β := Complex.arg (-ζ) with hβ
  set n := ‖ζ‖ ^ (p / 2) with hn
  have hn0 : 0 ≤ n := rpow_nonneg (norm_nonneg ζ) _
  have hβabs : |β| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by simpa using hζre))
  have hβ1 := (abs_lt.mp hβabs).1
  have hβ2 := (abs_lt.mp hβabs).2
  have hmono : ∀ {a b : ℝ}, cos b ≤ cos a →
      tan (π / (2 * p)) * (n * cos b) ≤ tan (π / (2 * p)) * (n * cos a) := fun h =>
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hn0) hT.le
  rcases lt_trichotomy ζ.im 0 with hi | hi | hi
  · -- lower half-plane: `arg ζ = β - π`, `U` is the second branch
    have hb : Complex.arg ζ = β - π := by
      have := Complex.arg_neg_eq_arg_sub_pi_of_im_pos (x := -ζ) (by simpa using hi); simpa using this
    have hβ0 : 0 ≤ β := Complex.arg_nonneg_iff.mpr (by simp; linarith)
    rw [hb, max_eq_right]
    · ring_nf
    · refine hmono ?_
      have h := cos_le_of_add_le (a := p / 2 * (π - β)) (b := p / 2 * β + p / 2 * π)
        (mul_nonneg hq.le (by linarith)) (by nlinarith) (by nlinarith)
      rw [show p / 2 * β - p / 2 * π = -(p / 2 * (π - β)) by ring, cos_neg]
      exact h
  · -- on the axis: both branches equal `U`
    have hζr : ζ = ((ζ.re : ℝ) : ℂ) := Complex.ext rfl (by simpa using hi)
    have hb0 : β = 0 := by
      rw [hβ, hζr, ← Complex.ofReal_neg, Complex.arg_ofReal_of_nonneg (by linarith)]
    have hpi : Complex.arg ζ = π := by rw [hζr, Complex.arg_ofReal_of_neg hζre]
    rw [hb0, hpi, max_eq_left]
    · ring_nf
    · refine hmono ?_
      rw [mul_zero, zero_sub, zero_add, cos_neg]
  · -- upper half-plane: `arg ζ = β + π`, `U` is the first branch
    have hb : Complex.arg ζ = β + π := by
      have := Complex.arg_neg_eq_arg_add_pi_of_im_neg (x := -ζ) (by simpa using hi); simpa using this
    have hβ0 : β ≤ 0 := by
      have : (-ζ).im < 0 := by simpa using hi
      exact (Complex.arg_neg_iff.mpr this).le
    rw [hb, max_eq_left]
    · ring_nf
    · refine hmono ?_
      have h := cos_le_of_add_le (a := p / 2 * β + p / 2 * π) (b := p / 2 * (π - β))
        (by nlinarith) (by nlinarith) (by nlinarith)
      rw [show p / 2 * β - p / 2 * π = -(p / 2 * (π - β)) by ring, cos_neg]
      exact h

/-! ### A3: `φ'` has bounded variation -/

/-- Variation of a sum (not in Mathlib v4.35). -/
theorem bv_add {f g : ℝ → ℝ} {s : Set ℝ} (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s := by
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) ?_
  unfold eVariationOn
  refine iSup_le fun ⟨n, u, hu, us⟩ => ?_
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le (f := f) (n := n) hu us) (eVariationOn.sum_le (f := g) (n := n) hu us)

theorem bv_const (c : ℝ) (s : Set ℝ) : BoundedVariationOn (fun _ : ℝ => c) s := by
  have h : ((fun _ : ℝ => c) '' s).Subsingleton :=
    Set.subsingleton_singleton.anti (by rintro _ ⟨x, -, rfl⟩; rfl)
  rw [BoundedVariationOn, eVariationOn.constant_on h]
  exact ENNReal.zero_ne_top

theorem bv_of_monotoneOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    BoundedVariationOn f (Icc a b) := by
  have h := hf.eVariationOn_eq (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  rw [Set.inter_self] at h
  rw [BoundedVariationOn, h]
  exact ENNReal.ofReal_ne_top

/-- On a window `[c, c + π/(4q)]` the map `t ↦ tan(q(t-c))` is monotone with values in `[0, 1]`. -/
theorem tan_window {q c t : ℝ} (hq : 0 < q) (ht : t ∈ Icc c (c + π / (4 * q))) :
    0 ≤ q * (t - c) ∧ q * (t - c) ≤ π / 4 := by
  have h4 : q * (π / (4 * q)) = π / 4 := by field_simp
  constructor
  · exact mul_nonneg hq.le (by linarith [ht.1])
  · have := mul_le_mul_of_nonneg_left (show t - c ≤ π / (4 * q) by linarith [ht.2]) hq.le
    linarith

/-- The projective transform at `c`, pointwise: `φ(t) = g(tan(q(t-c))) cos(q(t-c))` for `|q(t-c)| < π/2`. -/
theorem transform_eq {q : ℝ} (hq : 0 < q) (φ : ℝ → ℝ) (c t : ℝ) (h1 : -(π / 2) < q * (t - c))
    (h2 : q * (t - c) < π / 2) :
    φ t = φ (c + arctan (tan (q * (t - c))) / q) / cos (arctan (tan (q * (t - c)))) * cos (q * (t - c)) := by
  have hcos : 0 < cos (q * (t - c)) := cos_pos_of_mem_Ioo ⟨h1, h2⟩
  rw [arctan_tan h1 h2, show c + q * (t - c) / q = t by field_simp; ring, div_mul_cancel₀ _ hcos.ne']

/-- **A3 on one window**: `t ↦ φ'₊(t)` has bounded variation on `[c, c + π/(4q)]`. -/
theorem deriv_bv_window {q : ℝ} (hq : 0 < q) {φ : ℝ → ℝ} (htc : TrigConvex q φ) (c : ℝ) :
    BoundedVariationOn (fun t => derivWithin φ (Ici t) t) (Icc c (c + π / (4 * q))) := by
  set W := Icc c (c + π / (4 * q)) with hW
  have hcw : c ≤ c + π / (4 * q) := by have : 0 < π / (4 * q) := by positivity
                                       linarith
  set g : ℝ → ℝ := fun u => φ (c + arctan u / q) / cos (arctan u) with hg
  have hconv : ConvexOn ℝ univ g := TrigCont.convexOn_transform hq htc c
  set R : ℝ → ℝ := fun x => derivWithin g (Ioi x) x with hR
  have hRmono : MonotoneOn R univ := by simpa using hconv.monotoneOn_rightDeriv
  set th : ℝ → ℝ := fun t => q * (t - c) with hth
  have hthW : ∀ t ∈ W, 0 ≤ th t ∧ th t ≤ π / 4 := fun t ht => tan_window hq ht
  have hpi4 : π / 4 < π / 2 := by linarith [pi_pos]
  have htanmono : MonotoneOn (fun t => tan (th t)) W := by
    intro t1 h1 t2 h2 hle
    have a1 := hthW t1 h1; have a2 := hthW t2 h2
    exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos], by linarith⟩ ⟨by linarith [pi_pos], by linarith⟩
      (mul_le_mul_of_nonneg_left (by linarith) hq.le)
  have htan0 : ∀ t ∈ W, 0 ≤ tan (th t) := fun t ht =>
    tan_nonneg_of_nonneg_of_le_pi_div_two (hthW t ht).1 (by linarith [(hthW t ht).2])
  have hcosW : ∀ t ∈ W, 0 < cos (th t) := fun t ht =>
    cos_pos_of_mem_Ioo ⟨by linarith [(hthW t ht).1, pi_pos], by linarith [(hthW t ht).2]⟩
  -- the derivative formula on the window
  have hformula : ∀ t ∈ W, derivWithin φ (Ici t) t =
      R (tan (th t)) * (q / cos (th t)) + (-q) * (sin (th t) * g (tan (th t))) := by
    intro t ht
    have hc0 := hcosW t ht
    have hlin : HasDerivAt th q t := by simpa using ((hasDerivAt_id t).sub_const c).const_mul q
    have htan : HasDerivAt (fun t' => tan (th t')) (1 / cos (th t) ^ 2 * q) t :=
      (Real.hasDerivAt_tan hc0.ne').comp t hlin
    have hcos : HasDerivAt (fun t' => cos (th t')) (-sin (th t) * q) t := (Real.hasDerivAt_cos _).comp t hlin
    have hgr : HasDerivWithinAt g (R (tan (th t))) (Ici (tan (th t))) (tan (th t)) :=
      (hconv.hasDerivWithinAt_rightDeriv_of_mem_interior (by simp)).Ici_of_Ioi
    have hend : t < c + π / (2 * q) := by
      have : π / (4 * q) < π / (2 * q) := div_lt_div_of_pos_left pi_pos (by positivity) (by linarith)
      linarith [ht.2]
    have hmaps : MapsTo (fun t' => tan (th t')) (Ico t (c + π / (2 * q))) (Ici (tan (th t))) := by
      intro t' ht'
      have e1 := (hthW t ht).1
      have hlt : th t' < π / 2 := by
        have := mul_lt_mul_of_pos_left (show t' - c < π / (2 * q) by linarith [ht'.2]) hq
        rwa [show q * (π / (2 * q)) = π / 2 by field_simp] at this
      exact Real.strictMonoOn_tan.monotoneOn ⟨by linarith [pi_pos], by linarith [(hthW t ht).2]⟩
        ⟨by nlinarith [ht'.1, pi_pos], hlt⟩ (mul_le_mul_of_nonneg_left (by linarith [ht'.1]) hq.le)
    have hprod := (hgr.comp_of_eq t htan.hasDerivWithinAt hmaps rfl).mul hcos.hasDerivWithinAt
    have heq : φ =ᶠ[𝓝 t] fun t' => g (tan (th t')) * cos (th t') := by
      have hball : Metric.ball c (π / (2 * q)) ∈ 𝓝 t :=
        Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;>
          linarith [ht.1, ht.2, pi_pos])
      filter_upwards [hball] with t' ht'
      rw [Metric.mem_ball, Real.dist_eq] at ht'
      have hθ : |q * (t' - c)| < π / 2 := by
        rw [abs_mul, abs_of_pos hq]
        have := mul_lt_mul_of_pos_left ht' hq
        rwa [show q * (π / (2 * q)) = π / 2 by field_simp] at this
      exact transform_eq hq φ c t' (by linarith [neg_abs_le (q * (t' - c))]) (lt_of_le_of_lt (le_abs_self _) hθ)
    have hφ := (hprod.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds) heq.eq_of_nhds).mono_of_mem_nhdsWithin
      (s := Ici t) (Ico_mem_nhdsGE hend)
    rw [hφ.derivWithin (uniqueDiffWithinAt_Ici t)]
    simp only [Function.comp]
    field_simp
  refine (eVariationOn.eq_of_eqOn hformula).trans_ne ?_
  -- the pieces
  have hRW : BoundedVariationOn (fun t => R (tan (th t))) W :=
    bv_of_monotoneOn hcw (hRmono.comp htanmono (mapsTo_univ _ _))
  have hsecW : BoundedVariationOn (fun t => q / cos (th t)) W := by
    refine bv_of_monotoneOn hcw fun t1 h1 t2 h2 hle => ?_
    have hc : cos (th t2) ≤ cos (th t1) :=
      cos_le_cos_of_nonneg_of_le_pi (hthW t1 h1).1 (by linarith [(hthW t2 h2).2, pi_pos])
        (mul_le_mul_of_nonneg_left (by linarith) hq.le)
    exact div_le_div_of_nonneg_left hq.le (hcosW t2 h2) hc
  have hsinW : BoundedVariationOn (fun t => sin (th t)) W := by
    refine bv_of_monotoneOn hcw fun t1 h1 t2 h2 hle => ?_
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [(hthW t1 h1).1, pi_pos])
      (by linarith [(hthW t2 h2).2]) (mul_le_mul_of_nonneg_left (by linarith) hq.le)
  -- `g ∘ tan ∘ th` = (monotone) + m₀ · (monotone), with `m₀ = R 0`
  have hgW : BoundedVariationOn (fun t => g (tan (th t))) W := by
    have hmono0 : MonotoneOn (fun x => g x - R 0 * x) (Ici 0) := by
      intro x hx y hy hxy
      rcases eq_or_lt_of_le hxy with rfl | hlt
      · rfl
      have h1 : R 0 ≤ R x := hRmono (mem_univ _) (mem_univ _) hx
      have h2 : R x ≤ slope g x y := hconv.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ _) hlt
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h2
      nlinarith
    have hA : BoundedVariationOn (fun t => g (tan (th t)) - R 0 * tan (th t)) W :=
      bv_of_monotoneOn hcw (hmono0.comp htanmono fun t ht => htan0 t ht)
    have hB : BoundedVariationOn (fun t => R 0 * tan (th t)) W :=
      (bv_const (R 0) W).mul (bv_of_monotoneOn hcw htanmono)
    simpa using bv_add hA hB
  exact bv_add (hRW.mul hsecW) ((bv_const (-q) W).mul (hsinW.mul hgW))

/-- **A3**, Sec. 3 (l.235): "and `φ'` has bounded variation" (right derivative as the representative). -/
theorem deriv_bv {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (a b : ℝ) :
    BoundedVariationOn (fun t => derivWithin φ (Set.Ici t) t) (Set.Icc a b) := by
  have hq : 0 < q := by linarith
  have htc := Sector.qsubtrig_trigConvex hq0 hq1 hφ
  set f : ℝ → ℝ := fun t => derivWithin φ (Set.Ici t) t with hf
  set h : ℝ := π / (4 * q) with hh
  have hh0 : 0 < h := by positivity
  have hstep : ∀ n : ℕ, BoundedVariationOn f (Icc a (a + n * h)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hwin := deriv_bv_window hq htc (a + n * h)
      have hle1 : a ≤ a + n * h := by have : 0 ≤ (n : ℝ) * h := by positivity
                                      linarith
      have hle2 : a + n * h ≤ a + n * h + π / (4 * q) := by linarith
      have hsum := eVariationOn.Icc_add_Icc f (s := univ) hle1 hle2 (mem_univ _)
      simp only [univ_inter] at hsum
      rw [BoundedVariationOn, show a + ((n + 1 : ℕ) : ℝ) * h = a + n * h + π / (4 * q) by push_cast; ring,
        ← hsum]
      exact ENNReal.add_ne_top.mpr ⟨ih, hwin⟩
  obtain ⟨n, hn⟩ := exists_nat_ge ((b - a) / h)
  refine (hstep n).mono (Icc_subset_Icc le_rfl ?_)
  rw [div_le_iff₀ hh0] at hn
  linarith

end NewRows12

end P18
