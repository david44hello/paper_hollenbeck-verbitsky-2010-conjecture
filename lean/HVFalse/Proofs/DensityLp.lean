/-
  HVFalse/Proofs/DensityLp.lean - (eq:HV) on trigonometric polynomials ⇔ on all of L^p(T) (the paper, l.181 "by density")
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Route. Trigonometric polynomials f_k → f in L^p (density). By [HV2000] (cited, Cited/Riesz.lean)
  P₊f_k and P₋f_k are Cauchy in L^p; their limits have the Fourier coefficients of P₊f, P₋f (coefficients are continuous on
  L^p ⊂ L¹), so by D1 they are the g, h of `HVIneqLp`. (⇒): along a subsequence P₊f_k → g, P₋f_k → h a.e.; Fatou
  (`eLpNorm_lim_le_liminf_eLpNorm`) passes (eq:HV) to the limit, for every s > 0 (only continuity of (a,b) ↦ (|a|^s+|b|^s)^{1/s}
  is used). (⇐): (eq:HV) on all of L^p applied to the classes of trig c, P₊c, P₋c.
-/
import HVFalse.Proofs.DensityLpA

open Real MeasureTheory Filter Topology Set AddCircle
open scoped ENNReal NNReal

namespace P18

namespace DensityLp

theorem fact_one_le {p : ℝ} (hp : 1 ≤ p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp⟩

theorem norm_toLpT {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (φ : C(Circ, ℂ)) :
    ‖toLpT p φ‖ = (eLpNorm (⇑φ) (ENNReal.ofReal p) volume).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (coeFn_toLpT φ)]

theorem eLpNorm_cont_ne_top {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] (φ : C(Circ, ℂ)) :
    eLpNorm (⇑φ) (ENNReal.ofReal p) volume ≠ ⊤ := by
  rw [← eLpNorm_congr_ae (coeFn_toLpT (p := p) φ)]
  exact Lp.eLpNorm_ne_top _

/-- The Riesz bound as a Lipschitz bound between classes of trigonometric polynomials. -/
theorem dist_proj_le {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) [Fact (1 ≤ ENNReal.ofReal p)] (c d : ℤ →₀ ℂ) :
    dist (toLpT p (pC c)) (toLpT p (pC d)) ≤ 1 / sin (π / p) * dist (toLpT p (tC c)) (toLpT p (tC d)) ∧
      dist (toLpT p (mC c)) (toLpT p (mC d)) ≤ 1 / sin (π / p) * dist (toLpT p (tC c)) (toLpT p (tC d)) := by
  have hp : 0 < p := by linarith
  have hK : 0 ≤ 1 / sin (π / p) := by
    have : 0 < sin (π / p) := by
      apply sin_pos_of_pos_of_lt_pi (by positivity)
      rw [div_lt_iff₀ hp]; nlinarith [pi_pos]
    positivity
  have hR := riesz_lp hp1 hp2 (c - d)
  have key : ∀ {Q : C(Circ, ℂ)}, eLpNorm (⇑Q) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (1 / sin (π / p)) * eLpNorm (⇑(tC (c - d))) (ENNReal.ofReal p) volume →
      ‖toLpT p Q‖ ≤ 1 / sin (π / p) * ‖toLpT p (tC (c - d))‖ := by
    intro Q hQ
    rw [norm_toLpT, norm_toLpT, ← ENNReal.toReal_ofReal hK, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (eLpNorm_cont_ne_top _)) hQ
  simp only [dist_eq_norm, ← map_sub, ← tC_sub, ← pC_sub, ← mC_sub]
  exact ⟨key hR.1, key hR.2⟩

/-- From trigonometric polynomials `f_k → f`: `P₊f_k`, `P₋f_k` converge, to functions with the coefficients of `P₊f`, `P₋f`. -/
theorem exists_lim_proj {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) [Fact (1 ≤ ENNReal.ofReal p)] {f : LpT p}
    {c : ℕ → (ℤ →₀ ℂ)} (hc : Tendsto (fun k => toLpT p (tC (c k))) atTop (𝓝 f)) :
    ∃ g h : LpT p, Tendsto (fun k => toLpT p (pC (c k))) atTop (𝓝 g) ∧
      Tendsto (fun k => toLpT p (mC (c k))) atTop (𝓝 h) ∧
      (∀ n : ℤ, fourierCoeff (⇑g) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0) ∧
      (∀ n : ℤ, fourierCoeff (⇑h) n = if n < 0 then fourierCoeff (⇑f) n else 0) := by
  set K := 1 / sin (π / p) with hKdef
  have hK : 0 ≤ K := by
    have hp : 0 < p := by linarith
    have : 0 < sin (π / p) := by
      apply sin_pos_of_pos_of_lt_pi (by positivity)
      rw [div_lt_iff₀ hp]; nlinarith [pi_pos]
    positivity
  have hFc := hc.cauchySeq
  have hlip : ∀ (Pr : (ℤ →₀ ℂ) → C(Circ, ℂ)),
      (∀ a b, dist (toLpT p (Pr a)) (toLpT p (Pr b)) ≤ K * dist (toLpT p (tC a)) (toLpT p (tC b))) →
      CauchySeq fun k => toLpT p (Pr (c k)) := by
    intro Pr hPr
    rw [Metric.cauchySeq_iff] at hFc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hFc (ε / (K + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc dist (toLpT p (Pr (c m))) (toLpT p (Pr (c n))) ≤ K * dist (toLpT p (tC (c m))) (toLpT p (tC (c n))) :=
          hPr _ _
      _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left (hN m hm n hn).le hK
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (hlip pC fun a b => (dist_proj_le hp1 hp2 a b).1)
  obtain ⟨h, hh⟩ := cauchySeq_tendsto_of_complete (hlip mC fun a b => (dist_proj_le hp1 hp2 a b).2)
  have hF : ∀ n, Tendsto (fun k => c k n) atTop (𝓝 (fourierCoeff (⇑f) n)) := fun n => by
    have h1 := tendsto_coeff hc n
    simpa only [coeff_toLpT, coeff_tC] using h1
  refine ⟨g, h, hg, hh, fun n => ?_, fun n => ?_⟩
  · have h1 := tendsto_coeff hg n
    simp only [coeff_toLpT, coeff_pC] at h1
    refine tendsto_nhds_unique h1 ?_
    by_cases hn : 0 ≤ n
    · simp only [hn, if_true]; exact hF n
    · simp only [hn, if_false]; exact tendsto_const_nhds
  · have h1 := tendsto_coeff hh n
    simp only [coeff_toLpT, coeff_mC] at h1
    refine tendsto_nhds_unique h1 ?_
    by_cases hn : n < 0
    · simp only [hn, if_true]; exact hF n
    · simp only [hn, if_false]; exact tendsto_const_nhds

/-- **D2** (M. Riesz, from [HV2000] cited): for `1 < p ≤ 2` every `f ∈ L^p(T)` has `P₊f, P₋f ∈ L^p(T)`, i.e. functions
`g, h ∈ L^p` with `ĝ(n) = f̂(n)` (`n ≥ 0`), `0` (`n < 0`), and `ĥ(n) = f̂(n)` (`n < 0`), `0` (`n ≥ 0`). -/
theorem riesz_exists {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (f : LpT p) :
    ∃ g h : LpT p, (∀ n : ℤ, fourierCoeff (⇑g) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0) ∧
      (∀ n : ℤ, fourierCoeff (⇑h) n = if n < 0 then fourierCoeff (⇑f) n else 0) := by
  haveI := fact_one_le hp1.le
  obtain ⟨c, hc⟩ := exists_trig_tendsto f
  obtain ⟨g, h, -, -, hg, hh⟩ := exists_lim_proj hp1 hp2 hc
  exact ⟨g, h, hg, hh⟩

/-! ## D3 -/

theorem norm_hv (s : ℝ) (a b : ℂ) : ‖(‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s)‖ = (‖a‖ ^ s + ‖b‖ ^ s) ^ (1 / s) :=
  Real.norm_of_nonneg (by positivity)

/-! Helpers over opaque functions, built from combinators (composing at `⇑(toLpT p (pC c))` through `ℂ × ℂ` times out in
unification). -/

theorem continuous_hv' {s : ℝ} (hs : 0 < s) {G H : Circ → ℂ} (hG : Continuous G) (hH : Continuous H) :
    Continuous fun x => (‖G x‖ ^ s + ‖H x‖ ^ s) ^ (1 / s) :=
  ((hG.norm.rpow_const fun _ => Or.inr hs.le).add (hH.norm.rpow_const fun _ => Or.inr hs.le)).rpow_const
    fun _ => Or.inr (by positivity)

theorem aesm_hv {s : ℝ} (hs : 0 < s) {G H : Circ → ℂ} (hG : AEStronglyMeasurable G (volume : Measure Circ))
    (hH : AEStronglyMeasurable H (volume : Measure Circ)) :
    AEStronglyMeasurable (fun x => (‖G x‖ ^ s + ‖H x‖ ^ s) ^ (1 / s)) (volume : Measure Circ) := by
  have h1 : AEStronglyMeasurable (fun x => ‖G x‖ ^ s) (volume : Measure Circ) :=
    (Real.continuous_rpow_const hs.le).comp_aestronglyMeasurable hG.norm
  have h2 : AEStronglyMeasurable (fun x => ‖H x‖ ^ s) (volume : Measure Circ) :=
    (Real.continuous_rpow_const hs.le).comp_aestronglyMeasurable hH.norm
  exact (Real.continuous_rpow_const (by positivity : (0 : ℝ) ≤ 1 / s)).comp_aestronglyMeasurable (h1.add h2)

theorem tendsto_hv {s : ℝ} (hs : 0 < s) {a b : ℕ → ℂ} {a0 b0 : ℂ} (ha : Tendsto a atTop (𝓝 a0))
    (hb : Tendsto b atTop (𝓝 b0)) :
    Tendsto (fun j => (‖a j‖ ^ s + ‖b j‖ ^ s) ^ (1 / s)) atTop (𝓝 ((‖a0‖ ^ s + ‖b0‖ ^ s) ^ (1 / s))) :=
  ((ha.norm.rpow_const (Or.inr hs.le)).add (hb.norm.rpow_const (Or.inr hs.le))).rpow_const (Or.inr (by positivity))

/-- (eq:HV) for one trigonometric polynomial, as integrals over `[0, 2π]` ⇔ as `L^p(T)` norms. -/
theorem hv_trig_iff {p s C : ℝ} (hp : 0 < p) (hs : 0 < s) (hC : 0 < C) (c : ℤ →₀ ℂ) :
    (∫ θ in (0 : ℝ)..(2 * π), ((‖Pplus c θ‖ ^ s + ‖Pminus c θ‖ ^ s) ^ (1 / s)) ^ p
        ≤ C ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖trig c θ‖ ^ p) ↔
      eLpNorm (fun x => (‖pC c x‖ ^ s + ‖mC c x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal C * eLpNorm (⇑(tC c)) (ENNReal.ofReal p) volume := by
  have hcont : Continuous fun x : Circ => (‖pC c x‖ ^ s + ‖mC c x‖ ^ s) ^ (1 / s) :=
    continuous_hv' hs (map_continuous (pC c)) (map_continuous (mC c))
  rw [eLpNorm_circ hp hcont, eLpNorm_circ hp (map_continuous (tC c))]
  simp_rw [norm_hv, pC_coe, mC_coe, tC_coe]
  exact rpow_ineq_iff hp (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => by positivity)
    (intervalIntegral.integral_nonneg two_pi_pos.le fun θ _ => by positivity) hC.le

/-- **D3.** For `1 < p < 2`, `s > 0`, `C > 0`: (eq:HV) with constant `C` holds on trigonometric polynomials iff it holds on
all of `L^p(T)` (with `P₊f`, `P₋f` given by their Fourier coefficients). -/
theorem hvIneq_iff_lp {p s C : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hC : 0 < C) :
    HVIneq p s C ↔ HVIneqLp p s C := by
  have hp : 0 < p := by linarith
  haveI := fact_one_le hp1.le
  constructor
  · intro hHV f g h hg hh
    obtain ⟨c, hc⟩ := exists_trig_tendsto f
    obtain ⟨g', h', hG, hH, hg', hh'⟩ := exists_lim_proj hp1 hp2.le hc
    have hgg : g' = g := fourier_ext g' g fun n => by rw [hg', hg]
    have hhh : h' = h := fourier_ext h' h fun n => by rw [hh', hh]
    subst hgg hhh
    -- a.e. convergent subsequence for both projections
    have hp0 : ENNReal.ofReal p ≠ 0 := by rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hp
    obtain ⟨ns1, hns1, hae1⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hG)).exists_seq_tendsto_ae
    have hH1 : Tendsto (fun k => toLpT p (mC (c (ns1 k)))) atTop (𝓝 h') := hH.comp hns1.tendsto_atTop
    obtain ⟨ns2, hns2, hae2⟩ := (tendstoInMeasure_of_tendsto_eLpNorm hp0
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hH1)).exists_seq_tendsto_ae
    set N : ℕ → ℕ := fun j => ns1 (ns2 j) with hNdef
    have hN : StrictMono N := hns1.comp hns2
    have hlim_ae : ∀ᵐ x ∂(volume : Measure Circ), Tendsto (fun j => (‖toLpT p (pC (c (N j))) x‖ ^ s +
        ‖toLpT p (mC (c (N j))) x‖ ^ s) ^ (1 / s)) atTop (𝓝 ((‖g' x‖ ^ s + ‖h' x‖ ^ s) ^ (1 / s))) := by
      filter_upwards [hae1, hae2] with x hx1 hx2
      have hx1' : Tendsto (fun j => toLpT p (pC (c (N j))) x) atTop (𝓝 (g' x)) := hx1.comp hns2.tendsto_atTop
      exact tendsto_hv hs hx1' hx2
    have hmeas : ∀ j, AEStronglyMeasurable (fun x => (‖toLpT p (pC (c (N j))) x‖ ^ s +
        ‖toLpT p (mC (c (N j))) x‖ ^ s) ^ (1 / s)) (volume : Measure Circ) := fun j =>
      aesm_hv hs (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    have hmeas_lim : AEStronglyMeasurable (fun x => (‖g' x‖ ^ s + ‖h' x‖ ^ s) ^ (1 / s)) (volume : Measure Circ) :=
      aesm_hv hs (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
    have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p) hmeas _ hmeas_lim hlim_ae
    have hk : ∀ j, eLpNorm (fun x => (‖toLpT p (pC (c (N j))) x‖ ^ s + ‖toLpT p (mC (c (N j))) x‖ ^ s) ^ (1 / s))
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C * eLpNorm (⇑(toLpT p (tC (c (N j))))) (ENNReal.ofReal p) volume := by
      intro j
      have h1 := (hv_trig_iff hp hs hC (c (N j))).mp (hHV (c (N j)))
      have e1 : (fun x => (‖toLpT p (pC (c (N j))) x‖ ^ s + ‖toLpT p (mC (c (N j))) x‖ ^ s) ^ (1 / s)) =ᵐ[volume]
          fun x => (‖pC (c (N j)) x‖ ^ s + ‖mC (c (N j)) x‖ ^ s) ^ (1 / s) := by
        filter_upwards [coeFn_toLpT (p := p) (pC (c (N j))), coeFn_toLpT (p := p) (mC (c (N j)))] with x h1 h2
        rw [h1, h2]
      rw [eLpNorm_congr_ae e1, eLpNorm_congr_ae (coeFn_toLpT (tC (c (N j))))]
      exact h1
    have hlimF : Tendsto (fun j => ENNReal.ofReal C * eLpNorm (⇑(toLpT p (tC (c (N j))))) (ENNReal.ofReal p) volume)
        atTop (𝓝 (ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume)) := by
      have h1 : Tendsto (fun j => ‖toLpT p (tC (c (N j)))‖ₑ) atTop (𝓝 ‖f‖ₑ) :=
        (continuous_enorm.tendsto f).comp (hc.comp hN.tendsto_atTop)
      simp only [Lp.enorm_def] at h1
      exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    calc eLpNorm (fun x => (‖g' x‖ ^ s + ‖h' x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume
        ≤ atTop.liminf fun j => eLpNorm (fun x => (‖toLpT p (pC (c (N j))) x‖ ^ s +
            ‖toLpT p (mC (c (N j))) x‖ ^ s) ^ (1 / s)) (ENNReal.ofReal p) volume := hfatou
      _ ≤ atTop.liminf fun j => ENNReal.ofReal C * eLpNorm (⇑(toLpT p (tC (c (N j))))) (ENNReal.ofReal p) volume :=
          Filter.liminf_le_liminf (Eventually.of_forall hk)
      _ = ENNReal.ofReal C * eLpNorm (⇑f) (ENNReal.ofReal p) volume := hlimF.liminf_eq
  · intro hLp c
    refine (hv_trig_iff hp hs hC c).mpr ?_
    have h1 := hLp (toLpT p (tC c)) (toLpT p (pC c)) (toLpT p (mC c))
      (fun n => by rw [coeff_toLpT, coeff_toLpT, coeff_pC, coeff_tC])
      (fun n => by rw [coeff_toLpT, coeff_toLpT, coeff_mC, coeff_tC])
    have e1 : (fun x => (‖toLpT p (pC c) x‖ ^ s + ‖toLpT p (mC c) x‖ ^ s) ^ (1 / s)) =ᵐ[volume]
        fun x => (‖pC c x‖ ^ s + ‖mC c x‖ ^ s) ^ (1 / s) := by
      filter_upwards [coeFn_toLpT (p := p) (pC c), coeFn_toLpT (p := p) (mC c)] with x h1 h2
      rw [h1, h2]
    rwa [eLpNorm_congr_ae e1, eLpNorm_congr_ae (coeFn_toLpT (tC c))] at h1

end DensityLp

end P18
