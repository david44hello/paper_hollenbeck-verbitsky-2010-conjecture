/-
  HVFalse/Paper/Statements.lean - one theorem per claim of the paper "The Hollenbeck-Verbitsky (2010) conjecture is false"

  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Source: the paper, version 3.70 (28 October 2026); "l.N" = line N of the LaTeX source of the posted paper (version 3.70).
  Claim ids C01-C24 were assigned first; C25+ were added later.
  Proofs live in HVFalse/Proofs/*; bodies here only link them.
  Every (HV) row is stated on all of L^p(T) (`HVIneqLp`, HVFalse/Defs/HVLp.lean). Proved rows keep their
  trigonometric-polynomial form as a private `*_trig` lemma; C01b (density + [HV2000]) links the two.
-/
import HVFalse.Defs.Basic
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV
import HVFalse.Defs.Potential
import HVFalse.Defs.Extra
import HVFalse.Proofs.Bridges
import HVFalse.Proofs.SaddleSigns
import HVFalse.Proofs.Contact
import HVFalse.Proofs.Forcing
import HVFalse.Proofs.Coercive
import HVFalse.Proofs.Discs
import HVFalse.Proofs.Small
import HVFalse.Proofs.SaddleValley
import HVFalse.Proofs.Minorant
import HVFalse.Proofs.PointJag
import HVFalse.Proofs.FromFail
import HVFalse.Proofs.Threshold
import HVFalse.Proofs.Sector
import HVFalse.Proofs.SmallB
import HVFalse.Proofs.FailCole
import HVFalse.Proofs.FailLift
import HVFalse.Proofs.TheoremA
import HVFalse.Proofs.TrigCont
import HVFalse.Proofs.ThmBIf
import HVFalse.Proofs.ThresholdB
import HVFalse.Proofs.Relax
import HVFalse.Proofs.Bracket
import HVFalse.Proofs.SaddleTaylor
import HVFalse.Proofs.CellMono
import HVFalse.Proofs.Numeric2
import HVFalse.Defs.HVLp
import HVFalse.Proofs.DensityLp
import HVFalse.Proofs.Arcs
import HVFalse.Proofs.LamIf
import HVFalse.Proofs.Lift
import HVFalse.Proofs.ColeHom
import HVFalse.Proofs.IntervalH
import HVFalse.Proofs.Truec
import HVFalse.Proofs.LocGlob
import HVFalse.Proofs.BoxReductions
import HVFalse.Proofs.NewRows11
import HVFalse.Proofs.NewRows11b
import HVFalse.Proofs.NewRows12
import HVFalse.Proofs.NewRows11c
import HVFalse.Proofs.UMean
import HVFalse.Proofs.NewRows12b
import HVFalse.Proofs.RemarkH
import HVFalse.Paper.ComputerChecked
import HVFalse.Proofs.FinalRows
import HVFalse.Proofs.Prop8Steps
import HVFalse.Proofs.Prop8StepE
import HVFalse.Proofs.RemarkDelta
import HVFalse.Proofs.R2
import HVFalse.Proofs.R2Mine
import HVFalse.Proofs.R2b
import HVFalse.Proofs.R2c
import HVFalse.Proofs.R2d
import HVFalse.Proofs.R2e
import HVFalse.Defs.Explicit
import HVFalse.Defs.Cells
import HVFalse.Proofs.HandStep

open Real Set

namespace P18.Paper

-- Glue for the L^p rows (paper l.171 "by density"; not paper claims): the conjectured constant is positive, and
-- (HV) on all of L^p(T) is equivalent to (HV) on trigonometric polynomials (C01b below).
private theorem hvConst_pos {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 < hvConst p s := by
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

private theorem lp_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    HVIneqLp p s (hvConst p s) ↔ HVIneq p s (hvConst p s) :=
  (P18.DensityLp.hvIneq_iff_lp hp1 hp2 hs (hvConst_pos hp1 hp2)).symm

/-! ## Sec. 2 (set-up) and Lemma 1 (l.164-214) -/

-- Trigonometric-polynomial form of C01_discs_equiv (used by the proofs; the paper's L^p row follows).
private theorem C01_discs_equiv_trig {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    HVIneq p s (hvConst p s) ↔ DiscIneq p s :=
  P18.discs_equiv hp1 hp2 hs

/-- C01, l.166-174 (eq:discs): (HV) at `(p,s)` with the conjectured constant ⇔ `∫_T G∘h ≥ 0` for every polynomial disc
`h = (z, w)`, `w(0) = 0` (on trigonometric polynomials the correspondence `f = z + w̄` is exact). -/
theorem C01_discs_equiv {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    HVIneqLp p s (hvConst p s) ↔ DiscIneq p s :=
  by rw [lp_iff hp1 hp2 hs]; exact C01_discs_equiv_trig hp1 hp2 hs

/-- C01b, Sec. 2 (l.171, "by density"; the paper cites [HV2000] there): (HV) on all trigonometric polynomials ⇔ (HV) on all of `L^p(T)`, for any constant
`C > 0`; so every failure of (HV) is witnessed by a trigonometric polynomial. -/
theorem C01b_density {p s C : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hC : 0 < C) :
    HVIneq p s C ↔ HVIneqLp p s C :=
  P18.DensityLp.hvIneq_iff_lp hp1 hp2 hs hC

/-- C01c, Sec. 1 (l.61-66; M. Riesz's theorem, here through [HV2000]): for `f ∈ L^p(T)`, `1 < p ≤ 2`, the functions `P₊f`,
`P₋f` of (eq:HV) exist in `L^p(T)` (named by their Fourier coefficients, as in `HVIneqLp`). -/
theorem C01c_riesz_exists {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (f : LpT p) :
    ∃ g h : LpT p, (∀ n : ℤ, fourierCoeff (⇑g) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0) ∧
      (∀ n : ℤ, fourierCoeff (⇑h) n = if n < 0 then fourierCoeff (⇑f) n else 0) :=
  P18.DensityLp.riesz_exists hp1 hp2 f

/-- C01d, Sec. 1 (l.61-62, implicit in "P₊f = Σ_{n ≥ 0} f̂(n) e^{inθ}"): a function in `L^p(T)`, `p ≥ 1`, is determined by its Fourier
coefficients, so the `g`, `h` of `HVIneqLp` are exactly `P₊f`, `P₋f`. -/
theorem C01d_fourier_ext {p : ℝ} (hp : 1 ≤ p) (u v : LpT p) (h : ∀ n : ℤ, fourierCoeff (⇑u) n = fourierCoeff (⇑v) n) :
    u = v := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  exact P18.DensityLp.fourier_ext u v h


/-- C02a, l.175: `|z + w̄|² = 2|zw|(cosh y + cos t)` with `y = log(|z|/|w|)`, `t = arg(zw)`. -/
theorem C02a_norm_add_conj_sq (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖z + (starRingEnd ℂ) w‖ ^ 2 = 2 * ‖z * w‖ * (cosh (log (‖z‖ / ‖w‖)) + cos (Complex.arg (z * w))) :=
  P18.norm_add_conj_sq_cosh z w hz hw

/-- C02b, l.175-179: `G(z,w) = |zw|^q Γ(y,t)` on `{zw ≠ 0}`. -/
theorem C02b_G_eq_Gam {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    G p s z w = ‖z * w‖ ^ (p / 2) * Gam p s (log (‖z‖ / ‖w‖)) (Complex.arg (z * w)) := by
  unfold G; exact lift_pointwise p s hp1 hp2 hs z w hz hw

/-- C03a, l.205-208 (footnote): for `s ≤ sec²ϑ` the coefficient `(2cos ϑ)^{-p} - 2^{-p/s}` is positive (`x = 2cos ϑ < 2^{1/s}`). -/
theorem C03a_coeff_pos {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    0 < (2 * cos (π / (2 * p))) ^ (-p) - (2 : ℝ) ^ (-p / s) :=
  coeff_pos hp1 hp2 hs hsS

/-- C03b, l.204-205: for `s ≤ sec²ϑ`, `Γ(y,t) → +∞` as `|y| → ∞`, uniformly in `t`. -/
theorem C03b_gam_tendsto {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∀ M : ℝ, ∃ R : ℝ, ∀ y t : ℝ, R ≤ |y| → M ≤ Gam p s y t :=
  gam_tendsto hp1 hp2 hs hsS

/-- C03c, l.208: for `s ≤ sec²ϑ` the infimum `m(t) = inf_y Γ(y,t)` is attained. -/
theorem C03c_min_attained {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∀ t : ℝ, ∃ y0 : ℝ, ∀ y : ℝ, Gam p s y0 t ≤ Gam p s y t :=
  gam_min_attained hp1 hp2 hs hsS

/-- C03d, l.208: for `s ≤ sec²ϑ` all minimizers lie in a bounded set. -/
theorem C03d_minimizers_bounded {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∃ R : ℝ, ∀ t y0 : ℝ, (∀ y : ℝ, Gam p s y0 t ≤ Gam p s y t) → |y0| ≤ R :=
  gam_minimizers_bounded hp1 hp2 hs hsS

/-- C04a, l.195: `Γ` decreases in `s` (power means). -/
theorem C04a_gam_antitone_s {p r s : ℝ} (hp : 0 < p) (hr : 0 < r) (hrs : r ≤ s) (y t : ℝ) :
    Gam p s y t ≤ Gam p r y t :=
  gam_antitone_s p r s y t hp hr hrs

/-- C04b, l.195-197: (eq:two) holds exactly for `s ∈ (0, s₀(p)]`, for some `s₀(p) > 0`. -/
theorem C04b_twoVar_threshold {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0) :=
  P18.twoVar_threshold hp1 hp2

/-- C04d, l.197-204: `s₀(p) ≤ sec²ϑ` always (via `Γ(y,π/p) - e(π/p) = (p/8)(sec²ϑ - s)y² + O(y⁴)`), `s₀(p) ≥ p/(p-1)`
for `4/3 < p < 2` [Jag2026], and `s₀(p) = sec²ϑ` for `1 < p ≤ 4/3` [Mel2023, (37)]. -/
theorem C04d_threshold_bounds {p s0 : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 ≤ Ssec p ∧ (4 / 3 < p → p / (p - 1) ≤ s0) ∧ (p ≤ 4 / 3 → s0 = Ssec p) :=
  P18.threshold_bounds hp1 hp2 hs0

/-- C04c, l.208-209: `qπ/p = π/2`, so `e(±π/p) = 0`. -/
theorem C04c_ee_contact_zero {p : ℝ} (hp : 0 < p) : ee p (π / p) = 0 ∧ ee p (-(π / p)) = 0 :=
  P18.ee_contact_zero hp

/-- C05a, Lemma 1 contact (l.211-214): `ψ(±π/p) = 0` for `ψ(t) = Γ(0,t) - e(t)`, every `s`. -/
theorem C05a_contact_values {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    Gam p s 0 (π / p) - ee p (π / p) = 0 ∧ Gam p s 0 (-(π / p)) - ee p (-(π / p)) = 0 := by
  have hp0 : p ≠ 0 := by linarith
  refine ⟨?_, ?_⟩
  · rw [gam_contact p s hp1 hp2]
    simp only [ee]
    rw [show p / 2 * (π / p) = π / 2 by field_simp, cos_pi_div_two]
    ring
  · rw [gam_contact_neg p s hp1 hp2]
    simp only [ee]
    rw [show p / 2 * -(π / p) = -(π / 2) by field_simp, cos_neg, cos_pi_div_two]
    ring

/-- C05b, Lemma 1 (l.212): `ψ'(±π/p) = 0`. -/
theorem C05b_contact_deriv {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (fun t => Gam p s 0 t - ee p t) 0 (π / p) ∧
      HasDerivAt (fun t => Gam p s 0 t - ee p t) 0 (-(π / p)) :=
  ⟨psi_deriv_contact p s hp1 hp2, psi_deriv_contact_neg p s hp1 hp2⟩

/-- C05c, Lemma 1 (l.212): "Hence `m(±π/p) ≤ 0`" (`m(t) = inf_y Γ(y,t)`): some `y` has `Γ(y, ±π/p) ≤ 0`. -/
theorem C05c_m_contact_nonpos {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∃ y : ℝ, Gam p s y (π / p) ≤ 0) ∧ (∃ y : ℝ, Gam p s y (-(π / p)) ≤ 0) :=
  ⟨⟨0, (gam_contact p s hp1 hp2).le⟩, ⟨0, (gam_contact_neg p s hp1 hp2).le⟩⟩

/-- C05d, Lemma 1 (l.213): `m ≤ e + C(t ∓ π/p)²` near `±π/p` (via `m(t) ≤ Γ(0,t)`). -/
theorem C05d_contact_quadratic {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    (∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - π / p| < δ → Gam p s 0 t ≤ ee p t + C * (t - π / p) ^ 2) ∧
      (∃ C δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t + π / p| < δ → Gam p s 0 t ≤ ee p t + C * (t + π / p) ^ 2) :=
  ⟨contact_quadratic hp1 hp2 hs, contact_quadratic_neg hp1 hp2 hs⟩

/-! ## Sec. 3 — Subtrigonometric functions and a lifting lemma (l.220-281) -/

/-- C06a, Sec. 3 (l.222-236): a q-subtrigonometric `φ` is trigonometrically convex (`TrigConvex`, the three-point form of
HKV2003 (3.1) for `t ↦ φ(t/q)`). The paper derives `μ = φ'' + q²φ ≥ 0` (l.229-234); Lean proves the three-point inequality by a
Phragmén–Lindelöf sector comparison (HVFalse/Proofs/Sector.lean, no axiom) — a route difference. -/
theorem C06a_qsubtrig_trigConvex {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    TrigConvex q φ :=
  P18.Sector.qsubtrig_trigConvex hq0 hq1 hφ

/-- C06b, Sec. 3 (l.235-236): a q-subtrigonometric `φ` is continuous ("φ equals its continuous representative"). -/
theorem C06b_qsubtrig_continuous {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) :
    Continuous φ :=
  P18.TrigCont.qsubtrig_continuous hq0 hq1 hφ

/-- C06c, Sec. 3 (l.236): the continuous representative "has finite one-sided derivatives everywhere". -/
theorem C06c_qsubtrig_one_sided {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (x : ℝ) :
    ∃ dl dr : ℝ, HasDerivWithinAt φ dl (Iic x) x ∧ HasDerivWithinAt φ dr (Ici x) x :=
  P18.TrigCont.qsubtrig_one_sided hq0 hq1 hφ x

/-- C07a, Lemma 2 rigidity (l.238-241): if `φ` is q-subtrigonometric (`q = p/2`) and `φ ≤ m`, then `φ = e` on `I = [-π/p, π/p]`
and `φ ≥ e` on the circle (on `[-π, π]`, where `e` is the paper's formula). -/
theorem C07a_forcing {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {φ : ℝ → ℝ} (hφ : QSubtrig (p / 2) φ)
    (hle : ∀ y t : ℝ, φ t ≤ Gam p s y t) :
    (∀ t ∈ Icc (-(π / p)) (π / p), φ t = ee p t) ∧ (∀ t ∈ Icc (-π) π, ee p t ≤ φ t) :=
  forcing_of_trigConvex hp1 hp2 hs hφ.1 (C06a_qsubtrig_trigConvex (by linarith) (by linarith) hφ) hle

/-- C07b, Lemma 2 rigidity (l.239-241): "In particular `e ≤ m` everywhere" (when such a `φ` exists). -/
theorem C07b_forcing_e_le_m {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {φ : ℝ → ℝ} (hφ : QSubtrig (p / 2) φ)
    (hle : ∀ y t : ℝ, φ t ≤ Gam p s y t) : ∀ y : ℝ, ∀ t ∈ Icc (-π) π, ee p t ≤ Gam p s y t :=
  fun y t ht => le_trans ((C07a_forcing hp1 hp2 hs hφ hle).2 t ht) (hle y t)

/-- C08, Lemma 3 lift (l.267-273): for a polynomial `g ≢ 0` with `g(0) = 0`, `g = ζ^k B g₀` with `k ≥ 1`, `B` the Blaschke
product of the zeros of `g` in `0 < |ζ| < 1` and `g₀` (a polynomial) zero-free in the open disc, and a real trigonometric polynomial `y = Re(trig cy)` with
`Re Y = y` on `T`, `Im Y(0) = 0`: with a holomorphic square root `r = h^{1/2}`, `z = B r e^{Y/2}` and `w = ζ^k r e^{-Y/2}` are
analytic in the disc, continuous on its closure, `w(0) = 0`, `zw = g`, and on `T`, `G(z,w) = |g|^q Γ(y, arg g)`. -/
theorem C08_lift {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s)
    (gp g0p : Polynomial ℂ) (hgp : gp ≠ 0) (hg0 : gp.eval 0 = 0) (k : ℕ) (hk : 1 ≤ k) (zs : List ℂ)
    (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1) (hh_ne : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, g0p.eval ζ ≠ 0)
    (hfac : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, gp.eval ζ = ζ ^ k * blaschke zs ζ * g0p.eval ζ)
    (cy : ℤ →₀ ℂ) (Y : Polynomial ℂ)
    (hY : ∀ θ : ℝ, (Y.eval (Complex.exp ((θ : ℂ) * Complex.I))).re = (trig cy θ).re) (hY0 : (Y.eval 0).im = 0) :
    let g : ℂ → ℂ := fun ζ => gp.eval ζ
    ∃ r : ℂ → ℂ, (∀ ζ ∈ Metric.ball (0 : ℂ) 1, r ζ ^ 2 = g0p.eval ζ) ∧
      DifferentiableOn ℂ (fun ζ => blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (Metric.ball 0 1) ∧
      ContinuousOn (fun ζ => blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (Metric.closedBall 0 1) ∧
      DifferentiableOn ℂ (fun ζ => ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) (Metric.ball 0 1) ∧
      ContinuousOn (fun ζ => ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) (Metric.closedBall 0 1) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
        (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) * (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = g ζ) ∧
      (∀ θ : ℝ, G p s (blaschke zs (Complex.exp ((θ : ℂ) * Complex.I)) * r (Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (Y.eval (Complex.exp ((θ : ℂ) * Complex.I)) / 2))
          ((Complex.exp ((θ : ℂ) * Complex.I)) ^ k * r (Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-(Y.eval (Complex.exp ((θ : ℂ) * Complex.I))) / 2))
        = ‖g (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (p / 2) *
            Gam p s (trig cy θ).re (Complex.arg (g (Complex.exp ((θ : ℂ) * Complex.I))))) :=
  P18.Lift.lift hp1 hp2 hs gp g0p hgp hg0 k hk zs hzs hh_ne hfac cy Y hY hY0

/-! ## Secs. 4-5 — From a pointwise failure to a counterexample; the conjecture fails near s = sec² (l.283-504) -/

-- Trigonometric-polynomial form of C09_prop_fail (used by the proofs; the paper's L^p row follows).
private theorem C09_prop_fail_trig {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p s y t < ee p t) : ¬ HVIneq p s (hvConst p s) :=
  P18.ColeHom.prop_fail' hp1 hp2 hs hsS hpt

/-- C09, Prop. 4 (l.285-288): for `s ≤ sec²ϑ`, one failure point `Γ(y*,t*) < e(t*)` ANYWHERE (`t* ∈ [-π, π]`; `Γ` and the
periodic `e` are `2π`-periodic) makes (HV) fail with the conjectured constant. -/
theorem C09_prop_fail {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p s y t < ee p t) : ¬ HVIneqLp p s (hvConst p s) :=
  by rw [lp_iff hp1 hp2 hs]; exact C09_prop_fail_trig hp1 hp2 hs hsS hpt

/-- Glue (not a paper claim): Prop. 4 (failure point anywhere in `[-π, π]`) implies the interior form
(`t ∈ int I`) used by HVFalse/Proofs/FromFail.lean, since `π/p ≤ π`. -/
private theorem propFail_old : P18.PropFailStmt := fun {p s} hp1 hp2 hs hsS hpt => by
  obtain ⟨y, t, ⟨h1, h2⟩, hlt⟩ := hpt
  have hle : π / p ≤ π := div_le_self Real.pi_pos.le (by linarith)
  exact C09_prop_fail_trig hp1 hp2 hs hsS ⟨y, t, ⟨by linarith, by linarith⟩, hlt⟩

/-- C10a1, Prop. 5 saddle proof (l.360): `2K(S-2) - 3(2-p)²S = -H` with `S = u + 1`. -/
theorem C10a1_saddle_identity (p u : ℝ) : 2 * K p u * ((u + 1) - 2) - 3 * (2 - p) ^ 2 * (u + 1) = -H p u :=
  saddle_identity p u

/-- C10a2, Prop. 5 proof (l.344): `a₄₀ = pS(S-1)(S-2)/192`. -/
theorem C10a2_a40_identity (p S : ℝ) :
    p * S ^ 3 / 192 - p ^ 2 * S ^ 2 / 128 + p * S / 96 + p * (p - 2) * S ^ 2 / 128 = p * S * (S - 1) * (S - 2) / 192 :=
  a40_identity p S

/-- C10a3, Prop. 5 proof (l.358): `Q₄ = a₄₀ - a₂₁²/(4a₀₂) = -pSuH/(384K)`. -/
theorem C10a3_A_identity (p u : ℝ) (hp : p ≠ 0) (hK : K p u ≠ 0) :
    p * (u + 1) * u * ((u + 1) - 2) / 192 - (p ^ 2 * (2 - p) ^ 2 * u * (u + 1) ^ 2 / 256) / (4 * (p * K p u / 8))
      = -(p * (u + 1) * u * H p u) / (384 * K p u) :=
  A_identity p u hp hK

/-- C10a4, Prop. 5 proof (i) (l.364-365) and statement ("Moreover H(4/3) = 0"): `u(4/3) = tan²(3π/8) = 3 + 2√2`, a root of
`u² - 6u + 1`, and `H(4/3, u) = -(2/3)(u² - 6u + 1)`. -/
theorem C10a4_H_four_thirds :
    tan (3 * π / 8) ^ 2 = 3 + 2 * √2 ∧ (3 + 2 * √2) ^ 2 - 6 * (3 + 2 * √2) + 1 = 0 ∧
      ∀ u : ℝ, H (4 / 3) u = -(2 / 3) * (u ^ 2 - 6 * u + 1) :=
  ⟨tan_three_pi_div_eight_sq, u43_root, H_four_thirds⟩

/-- C10a5, LEAN-ONLY HELPER, not a claim of the paper (a true fact): `K(4/3) = 2√2/3`. -/
theorem C10a5_K_four_thirds : K (4 / 3) (3 + 2 * √2) = 2 * √2 / 3 :=
  K_four_thirds

/-- C10a6, Prop. 5 (l.327-328; proof l.364-365): "Moreover, `H`, as a function of `p ∈ (1,2)`, vanishes at `p = 4/3`", i.e. `H(4/3, u(4/3)) = 0`. -/
theorem C10a6_H_at_four_thirds : H (4 / 3) (uu (4 / 3)) = 0 :=
  P18.H_at_four_thirds

/-- C10a7, Prop. 5 proof (ii) (l.366-369): `u(2) = 1`, `H(2,1) = 0`, the two partial derivatives of `H` (as printed) vanish
at `(2,1)`, `u'(2) = -π/2`, and `d²/dp² H(p, u(p))` at `p = 2` equals `12 + 2π - π² > 0`. -/
theorem C10a7_H_at_two :
    uu 2 = 1 ∧ H 2 1 = 0 ∧ HasDerivAt (fun p => H p 1) 0 2 ∧ HasDerivAt (fun u => H 2 u) 0 1 ∧
      HasDerivAt uu (-(π / 2)) 2 ∧ HasDerivAt (deriv (fun p => H p (uu p))) (12 + 2 * π - π ^ 2) 2 ∧
      0 < 12 + 2 * π - π ^ 2 :=
  P18.ThresholdB.H_at_two

/-- C10e, Prop. 5 proof (l.373-378, Arb + mpmath): `d/dp H(p,u(p)) > 0` on `[4/3, 403/300]`, `H > 0` on `[403/300, 199/100]`,
`d²/dp² H(p,u(p)) > 0` on `[199/100, 2]` (the paper's route to `H > 0`; Lean proves `H > 0` by another route, C10c2). -/
theorem C10e_H_interval_steps :
    (∀ p ∈ Icc (4 / 3 : ℝ) (403 / 300), 0 < deriv (fun p => H p (uu p)) p) ∧
      (∀ p ∈ Icc (403 / 300 : ℝ) (199 / 100), 0 < H p (uu p)) ∧
      (∀ p ∈ Icc (199 / 100 : ℝ) 2, 0 < deriv (deriv (fun p => H p (uu p))) p) :=
  P18.IntervalH.H_interval_steps

/-- C10b1, Prop. 5 proof (l.333-335, eq:taylor) at `s = S`: the Taylor expansion of `Ψ = Γ - e` at `(0, π/p)`
(`a₂₀ = 0` at `s = S`; `a₄₀ = pS(S-1)(S-2)/192`). -/
theorem C10b1_taylor {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y τ : ℝ, |y| < δ → |τ| < δ →
      |Gam p (Ssec p) y (π / p + τ) - ee p (π / p + τ)
          - (a02 p * τ ^ 2 + a21 p * y ^ 2 * τ + p * Ssec p * (Ssec p - 1) * (Ssec p - 2) / 192 * y ^ 4)|
        ≤ C * (|τ| ^ 3 + y ^ 2 * τ ^ 2 + y ^ 4 * |τ| + |y| ^ 6) :=
  P18.SaddleTaylor.taylor_proved hp1 hp2

/-- C10b2, Prop. 5 (l.325-326): along the valley `t = π/p - (a₂₁/(2a₀₂)) y²`, `Γ - e = Q₄(p) y⁴ + O(y⁶)`. -/
theorem C10b2_valley {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      |Gam p (Ssec p) y (π / p - valleyC p * y ^ 2) - ee p (π / p - valleyC p * y ^ 2) - Acoef p * y ^ 4| ≤ C * y ^ 6 :=
  P18.SaddleValley.saddle_valley_proved hp1 hp2

/-- C10b3, Prop. 5 (l.326-327): "So `Γ < e` on this curve for small `y ≠ 0`". -/
theorem C10b3_valley_negative {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ 0 → |y| < δ →
      Gam p (Ssec p) y (π / p - valleyC p * y ^ 2) < ee p (π / p - valleyC p * y ^ 2) :=
  P18.valley_negative hp1 hp2

/-- C10c4, Prop. 5 proof (iii) (l.370-372): `K > 0` on all of `(1, 2)`. -/
theorem C10c4_K_pos_wide {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) : 0 < K p (uu p) :=
  P18.K_pos_wide hp1 hp2

/-- C10c1, Prop. 5 (l.324): `K > 0` on `(4/3, 2)` (Lean: Jordan's inequality). -/
theorem C10c1_K_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < K p (uu p) :=
  K_pos hp1 hp2

/-- C10c2, Prop. 5 (l.324): `H > 0` on `(4/3, 2)` (paper: Arb for p ≠ 3/2; Lean: Taylor bounds — route difference). -/
theorem C10c2_H_pos {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < H p (uu p) :=
  H_pos hp1 hp2

/-- C10c3, Prop. 5 (l.326): `a₂₁ > 0` and `Q₄(p) < 0` on `(4/3, 2)`. -/
theorem C10c3_a21_pos_A_neg {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < a21 p ∧ Acoef p < 0 :=
  P18.a21_pos_Acoef_neg hp1 hp2

/-- C10d, Prop. 5 proof (l.361): "The valley has `t < π/p`", i.e. `a₂₁/(2a₀₂) > 0`. -/
theorem C10d_valley_left {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : 0 < valleyC p :=
  P18.valleyC_pos hp1 hp2

/-- C24, Prop. 5 (l.327): at `p = 3/2`: `u = 3`, `K = 1/2`, `H = 1` and `Q₄ = -3/32`. -/
theorem C24_three_halves_values :
    uu (3 / 2) = 3 ∧ K (3 / 2) (uu (3 / 2)) = 1 / 2 ∧ H (3 / 2) (uu (3 / 2)) = 1 ∧ Acoef (3 / 2) = -3 / 32 :=
  P18.three_halves_values

-- Trigonometric-polynomial form of C11_theoremA (used by the proofs; the paper's L^p row follows).
private theorem C11_theoremA_trig {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 < Ssec p ∧ ∀ s ∈ Icc s1 (Ssec p), ¬ HVIneq p s (hvConst p s) :=
  P18.theoremA hp1 hp2

/-- C11, Theorem A (l.386-389): for every `p ∈ (4/3, 2)` there is `s₁(p) < sec²(π/2p)` such that (HV) fails with the
conjectured constant for every `s ∈ [s₁(p), sec²(π/2p)]`. (`s₁ > 0`: the conjectured range is `0 < s`.) -/
theorem C11_theoremA {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) :
    ∃ s1 : ℝ, 0 < s1 ∧ s1 < Ssec p ∧ ∀ s ∈ Icc s1 (Ssec p), ¬ HVIneqLp p s (hvConst p s) :=
  by
  obtain ⟨s1, h0, h1, h⟩ := C11_theoremA_trig hp1 hp2
  exact ⟨s1, h0, h1, fun s hs => by rw [lp_iff (by linarith) hp2 (by linarith [hs.1])]; exact h s hs⟩

/-- C12a, Prop. 7 (l.396-400): the closed form of `Γ - e` at `p = 3/2, s = 3.98, y = log(9/5), t = π/2`. -/
theorem C12a_point_closed_form :
    Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) =
      (106 / 45 : ℝ) ^ ((3 : ℝ) / 4)
        - (((9 / 5 : ℝ) ^ ((199 : ℝ) / 100) + (5 / 9 : ℝ) ^ ((199 : ℝ) / 100)) / 2) ^ ((75 : ℝ) / 199)
        - √3 * √(2 - √2) / 2 :=
  point_closed_form

/-- C12b, Prop. 7 (l.401): `Γ - e < -4.1·10⁻⁴` at that point (a consequence of the enclosure). -/
theorem C12b_point_fails : Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) < -41 / 100000 :=
  point_fails

/-- C12c, Prop. 7 (l.401): the enclosure `Γ - e ∈ -4.17314647396549·10⁻⁴ + [-10⁻¹⁸, 10⁻¹⁸]`. -/
theorem C12c_point_enclosure :
    |Gam (3 / 2) (398 / 100) (log (9 / 5)) (π / 2) - ee (3 / 2) (π / 2) - (-417314647396549 / 10 ^ 18)| ≤ 1 / 10 ^ 18 :=
  P18.point_enclosure

/-- C12d, Introduction (l.117: "s = 3.98 < sec²(π/3) = 4") and Cor. 9 (l.489-490) (+ `π/2 ∈ int I`, a Lean helper): `sec²(π/3) - s = 0.02`. -/
theorem C12d_point_location : π / 2 ∈ Ioo (-(π / (3 / 2))) (π / (3 / 2)) ∧ Ssec (3 / 2) - 398 / 100 = 2 / 100 :=
  P18.point_location

-- Trigonometric-polynomial form of C14_cor_false (used by the proofs; the paper's L^p row follows).
private theorem C14_cor_false_trig : ∀ s ∈ Icc (398 / 100 : ℝ) 4, ¬ HVIneq (3 / 2) s (hvConst (3 / 2) s) :=
  P18.cor_false_of_fail propFail_old

/-- C14, Corollary 9 (l.488-491): for `p = 3/2` the conjectured inequality fails for every `s ∈ [3.98, 4]`. -/
theorem C14_cor_false : ∀ s ∈ Icc (398 / 100 : ℝ) 4, ¬ HVIneqLp (3 / 2) s (hvConst (3 / 2) s) :=
  fun s hs => by rw [lp_iff (by norm_num) (by norm_num) (by linarith [hs.1])]; exact C14_cor_false_trig s hs

/-- C15a, l.499-500: Jaguzović's point `(y,t) = (log 2, π/2)` gives `Γ - e = -1.3102·10⁻³` at `(p,s) = (3/2, 4)`
(four significant digits: within `5·10⁻⁸`). -/
theorem C15a_jaguzovic_point : |Gam (3 / 2) 4 (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-13102 / 10 ^ 7)| ≤ 5 / 10 ^ 8 :=
  P18.jaguzovic_point

-- Trigonometric-polynomial form of C15b_fails_at_cutoff (used by the proofs; the paper's L^p row follows).
private theorem C15b_fails_at_cutoff_trig : ¬ HVIneq (3 / 2) 4 (hvConst (3 / 2) 4) :=
  P18.fails_at_cutoff_of_fail propFail_old

/-- C15b, l.499-502 (and Cor. 9, l.489): so (HV) fails at the end point `s = sec²(π/3) = 4`. -/
theorem C15b_fails_at_cutoff : ¬ HVIneqLp (3 / 2) 4 (hvConst (3 / 2) 4) :=
  by rw [lp_iff (by norm_num) (by norm_num) (by norm_num)]; exact C15b_fails_at_cutoff_trig

/-! ## Secs. 5-6 — Jaguzović's point; Theorem B and the threshold s₀(p) (l.499-532) -/

-- Trigonometric-polynomial form of C15c_jaguzovic_range (used by the proofs; the paper's L^p row follows).
private theorem C15c_jaguzovic_range_trig :
    (∀ s : ℝ, 39777 / 10000 < s → s ≤ 4 → Gam (3 / 2) s (log 2) (π / 2) < ee (3 / 2) (π / 2)) ∧
      |Gam (3 / 2) (398 / 100) (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-1398 / 10 ^ 7)| ≤ 5 / 10 ^ 8 ∧
      ∀ s ∈ Icc (3978 / 1000 : ℝ) 4, ¬ HVIneq (3 / 2) s (hvConst (3 / 2) s) :=
  P18.jaguzovic_range_of_fail (fun {p s} hp1 hp2 hs hsS hpt => C09_prop_fail_trig hp1 hp2 hs hsS hpt)

/-- C15c, l.500-502: at Jaguzović's point, `Γ - e < 0` for every `s > 3.9777` (up to `s = 4`), e.g. `-1.398·10⁻⁴` at
`s = 3.98` (4 digits); so `s₀(3/2) < 3.978`, i.e. (HV) fails for every `s ∈ [3.978, 4]`. -/
theorem C15c_jaguzovic_range :
    (∀ s : ℝ, 39777 / 10000 < s → s ≤ 4 → Gam (3 / 2) s (log 2) (π / 2) < ee (3 / 2) (π / 2)) ∧
      |Gam (3 / 2) (398 / 100) (log 2) (π / 2) - ee (3 / 2) (π / 2) - (-1398 / 10 ^ 7)| ≤ 5 / 10 ^ 8 ∧
      ∀ s ∈ Icc (3978 / 1000 : ℝ) 4, ¬ HVIneqLp (3 / 2) s (hvConst (3 / 2) s) :=
  by
  obtain ⟨h1, h2, h3⟩ := C15c_jaguzovic_range_trig
  exact ⟨h1, h2, fun s hs => by rw [lp_iff (by norm_num) (by norm_num) (by linarith [hs.1])]; exact h3 s hs⟩

/-- C16a, l.80 and l.180-184: `E = |zw|^q e(arg zw)` is plurisubharmonic. -/
theorem C16a_E_psh {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    IsPSH (fun x : ℂ × ℂ => ((Efun p x.1 x.2 : ℝ) : EReal)) :=
  P18.LocGlob.E_psh hp1 hp2

/-- C16b, l.180: `E = tan ϑ · Re (zw)^q` (principal power). -/
theorem C16b_E_eq_re {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (z w : ℂ) :
    Efun p z w = tan (π / (2 * p)) * ((z * w) ^ ((p / 2 : ℝ) : ℂ)).re :=
  P18.Efun_eq_re hp1 hp2 z w

/-- C16c, l.191: (eq:two) says `E ≤ G` on `{zw ≠ 0}`, hence everywhere by continuity. -/
theorem C16c_E_le_G {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (h2 : TwoVar p s) :
    ∀ z w : ℂ, Efun p z w ≤ G p s z w :=
  fun z w => P18.Efun_le_G hp1 hp2 hs h2 z w

-- Trigonometric-polynomial form of C16_theoremB_if (used by the proofs; the paper's L^p row follows).
private theorem C16_theoremB_if_trig {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (h2 : TwoVar p s) :
    HVIneq p s (hvConst p s) :=
  P18.LocGlob.theoremB_if hp1 hp2 hs h2

/-- C16, Theorem B "if" (l.508-516, method l.191-193): (eq:two) ⇒ (HV) with the conjectured constant. -/
theorem C16_theoremB_if {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (h2 : TwoVar p s) :
    HVIneqLp p s (hvConst p s) :=
  by rw [lp_iff hp1 hp2 hs]; exact C16_theoremB_if_trig hp1 hp2 hs hsS h2

-- Trigonometric-polynomial form of C17_theoremB_onlyif (used by the proofs; the paper's L^p row follows).
private theorem C17_theoremB_onlyif_trig {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hHV : HVIneq p s (hvConst p s)) : TwoVar p s := by
  by_contra h
  simp only [TwoVar, not_forall, not_le, exists_prop] at h
  obtain ⟨y, t, ht, hlt⟩ := h
  exact C09_prop_fail_trig hp1 hp2 hs hsS ⟨y, t, ht, hlt⟩ hHV

/-- C17, Theorem B "only if" (l.508-516): (HV) with the conjectured constant ⇒ (eq:two) (by Prop. 4). -/
theorem C17_theoremB_onlyif {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p)
    (hHV : HVIneqLp p s (hvConst p s)) : TwoVar p s :=
  C17_theoremB_onlyif_trig hp1 hp2 hs hsS ((lp_iff hp1 hp2 hs).mp hHV)

-- Trigonometric-polynomial form of C17c_HV_iff_threshold (used by the proofs; the paper's L^p row follows).
private theorem C17c_HV_iff_threshold_trig {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ Ssec p → (HVIneq p s (hvConst p s) ↔ s ≤ s0) :=
  P18.ThresholdB.hv_iff_threshold hp1 hp2

/-- C17c, Theorem B (l.509-510): "i.e. if and only if `s ≤ s₀(p)`". -/
theorem C17c_HV_iff_threshold {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ Ssec p → (HVIneqLp p s (hvConst p s) ↔ s ≤ s0) :=
  by
  obtain ⟨s0, h0, h⟩ := C17c_HV_iff_threshold_trig hp1 hp2
  exact ⟨s0, h0, fun s hs hsS => by rw [lp_iff hp1 hp2 hs]; exact h s hs hsS⟩

/-- C17d, Introduction (l.115-116): `s₀(p) = sec²(π/2p)` iff `p ≤ 4/3`. -/
theorem C17d_s0_eq_sec_iff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {s0 : ℝ} (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 = Ssec p ↔ p ≤ 4 / 3 :=
  P18.ThresholdB.s0_eq_sec_iff hp1 hp2 hs0

-- Trigonometric-polynomial form of C25_range_correct_iff (used by the proofs; the paper's L^p row follows).
private theorem C25_range_correct_iff_trig {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ s : ℝ, 0 < s → s < Ssec p → HVIneq p s (hvConst p s)) ↔ p ≤ 4 / 3 :=
  P18.ThresholdB.range_correct_iff hp1 hp2

/-- C25, Abstract (l.41-42) and Introduction (l.110-111; also l.57-59): the conjectured range is correct exactly for `p ≤ 4/3`
(the case `p ≤ 4/3` is Melentijević's theorem, a cited result). -/
theorem C25_range_correct_iff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ s : ℝ, 0 < s → s < Ssec p → HVIneqLp p s (hvConst p s)) ↔ p ≤ 4 / 3 :=
  by
  constructor
  · intro h
    exact (C25_range_correct_iff_trig hp1 hp2).mp fun s hs hsS => (lp_iff hp1 hp2 hs).mp (h s hs hsS)
  · intro h s hs hsS
    rw [lp_iff hp1 hp2 hs]
    exact (C25_range_correct_iff_trig hp1 hp2).mpr h s hs hsS

/-- C17f, Abstract (l.45-47: "this constant is the best one if and only if the two-variable inequality holds") and
Thm B: for `0 < s ≤ sec²(π/2p)`, `C_HV` is the LEAST constant in (HV) iff (eq:two) holds. "If": Thm B (C16) and the cited
lower bound [MM2022] (`mm2022_lower_bound`); "only if": C17. -/
theorem C17f_best_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    IsLeast {C : ℝ | 0 < C ∧ HVIneqLp p s C} (hvConst p s) ↔ TwoVar p s := by
  constructor
  · intro h
    exact C17_theoremB_onlyif hp1 hp2 hs hsS h.1.2
  · intro h2
    exact ⟨⟨hvConst_pos hp1 hp2, C16_theoremB_if hp1 hp2 hs hsS h2⟩,
      fun C hC => P18.Cited.mm2022_lower_bound p s hp1 hp2 hs C hC.1 hC.2⟩

/-- C25b, Abstract (l.42: "the conjecture holds on its whole range exactly when `p ≤ 4/3`"), in the conjecture's own
words: `C_HV` is the least constant in (HV) for every `s ∈ (0, sec²(π/2p))` iff `p ≤ 4/3` (C25 + [MM2022]). -/
theorem C25b_best_range_iff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ s : ℝ, 0 < s → s < Ssec p → IsLeast {C : ℝ | 0 < C ∧ HVIneqLp p s C} (hvConst p s)) ↔ p ≤ 4 / 3 := by
  constructor
  · intro h
    exact (C25_range_correct_iff hp1 hp2).mp fun s hs hsS => (h s hs hsS).1.2
  · intro hp s hs hsS
    exact ⟨⟨hvConst_pos hp1 hp2, (C25_range_correct_iff hp1 hp2).mpr hp s hs hsS⟩,
      fun C hC => P18.Cited.mm2022_lower_bound p s hp1 hp2 hs C hC.1 hC.2⟩

/-! ## Sec. 6 — A failure point is enough (l.520-532) -/

-- Trigonometric-polynomial form of C18_upper_by_point (used by the proofs; the paper's L^p row follows).
private theorem C18_upper_by_point_trig {p sp : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hsp : 0 < sp) (hspS : sp ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p sp y t < ee p t) :
    ∀ s ∈ Icc sp (Ssec p), ¬ HVIneq p s (hvConst p s) := by
  intro s hs
  obtain ⟨y, t, ht, hlt⟩ := hpt
  exact C09_prop_fail_trig hp1 hp2 (by linarith [hs.1]) hs.2
    ⟨y, t, ht, lt_of_le_of_lt (gam_antitone_s p sp s y t (by linarith) hsp hs.1) hlt⟩

/-- C18, l.520-522: an upper bound needs one point: a failure point at `s₊ ≤ sec²ϑ` gives failure of (HV)
for every `s ∈ [s₊, sec²ϑ]` (Prop. fail + monotonicity in `s`). -/
theorem C18_upper_by_point {p sp : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hsp : 0 < sp) (hspS : sp ≤ Ssec p)
    (hpt : ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p sp y t < ee p t) :
    ∀ s ∈ Icc sp (Ssec p), ¬ HVIneqLp p s (hvConst p s) :=
  fun s hs => by rw [lp_iff hp1 hp2 (by linarith [hs.1])]; exact C18_upper_by_point_trig hp1 hp2 hsp hspS hpt s hs

/-- C27, l.524-525: lower bounds need `Ψ ≥ 0` on the whole cylinder; by evenness `y ≥ 0`, `t ∈ [0, π]` suffice. -/
theorem C27_psi_abs (p s y t : ℝ) : Gam p s y t - ee p t = Gam p s |y| |t| - ee p |t| :=
  psi_abs p s y t

/-! ## Sec. 7 — The best constant, Prop. 14 (l.616-679) -/

/-- C22a, Prop. 14 (l.620-632): for `λ ≥ 1` and `s ≤ sec²ϑ`, (HV) holds with `λ^{1/p} C_{s,p}` iff a q-subtrigonometric `φ ≤ m_λ` exists. -/
theorem C22a_truec_iff {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) (hlam : 1 ≤ lam) :
    HVIneqLp p s (lam ^ (1 / p) * hvConst p s) ↔ LamFeasible p s lam :=
  (P18.DensityLp.hvIneq_iff_lp hp1 hp2 hs
      (mul_pos (Real.rpow_pos_of_pos (by linarith) _) (hvConst_pos hp1 hp2))).symm.trans
    (P18.ColeHom.truec_iff' hp1 hp2 hs hsS hlam)

/-- C22b, Prop. 14 proof (l.629-630): "Since `m_λ` increases with `λ`, the feasible `λ` form an interval" (an up-set). -/
theorem C22b_feasible_upset {p s lam lam' : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hlam : 0 < lam)
    (hll : lam ≤ lam') (hf : LamFeasible p s lam) : LamFeasible p s lam' :=
  P18.feasible_upset hp1 hp2 hs hlam hll hf

/-- C22c, Prop. 14 (l.620-623): the best constant is `C* = λ*^{1/p} C_{s,p}`, with `λ* ≥ 1` the infimum of the
`λ ≥ 1` for which a q-subtrigonometric `φ ≤ m_λ` exists. The proof uses the paper's two results on `L^p` from other
papers: "nonempty as C* < ∞" (from the cited [HV2000] bound, Truec.hv_finite) and `C* ≥ C_{s,p}` ([MM2022, §2] at t = 1,
the cited axiom mm2022_lower_bound). (Best constant = greatest lower bound of the valid constants `C > 0` on all of `L^p`.) -/
theorem C22c_truec_formula {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    ∃ lamStar : ℝ, 1 ≤ lamStar ∧ IsGLB {lam : ℝ | 1 ≤ lam ∧ LamFeasible p s lam} lamStar ∧
      IsGLB {C : ℝ | 0 < C ∧ HVIneqLp p s C} (lamStar ^ (1 / p) * hvConst p s) :=
  P18.Truec.truec_formula' hp1 hp2 hs hsS

/-- C23b, Sec. 7 (l.639-646): a q-subtrigonometric function satisfies the discrete inequality at every step `h`, `2qh < π`
(so the discrete values do not decrease along nested grids). The paper's q is p/2 ∈ (1/2, 1), as in C06a. -/
theorem C23b_qsubtrig_discrete {q h : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) (hh : 0 < h) (h2 : 2 * q * h < π) {φ : ℝ → ℝ}
    (hφ : QSubtrig q φ) (t : ℝ) : 2 * cos (q * h) * φ t ≤ φ (t + h) + φ (t - h) :=
  P18.Relax.qsubtrig_discrete hq0 hq1 hh h2 hφ t

/-- C23c, LEAN-ONLY HELPER, not a claim of the paper (the discrete inequality is exact for cos): "The inequality is exact for `cos(qt)`". -/
theorem C23c_ee_discrete_exact (p t h : ℝ) : ee p (t + h) + ee p (t - h) - 2 * cos (p / 2 * h) * ee p t = 0 :=
  ee_discrete_exact p t h

/-! ## Prop. 8 (l.411-460) — the explicit counterexample, `δ = e^{-2500}` unless a `δ` is quantified -/

/-- C13a, Prop. 8 (l.420): `w(0) = 0`. -/
theorem C13a_explicit_w0 (δ : ℝ) : Explicit.wf δ 0 = 0 :=
  P18.explicit_w0 δ

/-- C13d, Prop. 8 proof (l.427): `zw = e^{iγ} ζ Π²`. -/
theorem C13d_explicit_product (δ : ℝ) (ζ : ℂ) :
    Explicit.zf δ ζ * Explicit.wf δ ζ =
      Complex.exp (Complex.I * ((Explicit.gam δ : ℝ) : ℂ)) * ζ * Explicit.Pi δ ζ ^ 2 :=
  P18.explicit_product δ ζ

/-- C13e, Prop. 8 proof (l.428-439): on the arcs `(-π, -δ/2)`, `(-δ/2, δ/2)`, `(δ/2, π)` of `T`: `arg(zw) = -2π/3, t₂, t₃` and
`log|z/w| = 0, y₂, 0`. -/
theorem C13e_explicit_arcs :
    let δ := exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    (∀ θ ∈ Ioo (-π) (-(δ / 2)), Complex.arg (Z θ * W θ) = -(2 * π / 3) ∧ log (‖Z θ‖ / ‖W θ‖) = 0) ∧
    (∀ θ ∈ Ioo (-(δ / 2)) (δ / 2), Complex.arg (Z θ * W θ) = Explicit.tS ∧ log (‖Z θ‖ / ‖W θ‖) = Explicit.y2) ∧
    (∀ θ ∈ Ioo (δ / 2) π, Complex.arg (Z θ * W θ) = Explicit.bA ∧ log (‖Z θ‖ / ‖W θ‖) = 0) :=
  P18.explicit_arcs

/-- C13k, Prop. 8 proof (l.448-449, l.484): `Γ(y₁,t₁) = 0` at `(0, -2π/3)` (a contact point) and
`Γ(y₂,t₂) - e(t₂) = -7.7·10⁻⁴` (2 digits) at `(p, s) = (3/2, 3.98)`. -/
theorem C13k_explicit_arc_values :
    Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 ∧
      |Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS - (-77 / 10 ^ 5)| ≤ 5 / 10 ^ 6 :=
  P18.explicit_arc_values

/-- C13f, Prop. 8 proof (l.443): `qα₋, qα₊, qα_π < 1` (`q = 3/4`; Lean names aA, aB, aC). -/
theorem C13f_explicit_exponents : 3 / 4 * Explicit.aA < 1 ∧ 3 / 4 * Explicit.aB < 1 ∧ 3 / 4 * Explicit.aC < 1 :=
  P18.explicit_exponents

/-- C13g, remark after Prop. 8 (l.470): "`η = a₋ + a₊ - 1 = 0.0102/π ≈ 0.00325`" (`a_j = q α_j`): Lean proves `η > 0` and
`η = 0.0032468 ± 5·10⁻⁸`; the exact value `0.0102/π` is row C13s. -/
theorem C13g_explicit_e1 :
    0 < 3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 ∧
      |3 / 4 * Explicit.aA + 3 / 4 * Explicit.aB - 1 - 32468 / 10 ^ 7| ≤ 5 / 10 ^ 8 :=
  P18.explicit_e1

/-! ## Props 10, 11, 13 — brackets, cells, the false width (l.544-608) -/

-- Trigonometric-polynomial form of C19a_bracket_fails (used by the proofs; the paper's L^p row follows).
private theorem C19a_bracket_fails_trig :
    ∀ r ∈ ([(7 / 5, 52989 / 10000), (3 / 2, 39575 / 10000), (8 / 5, 31802 / 10000), (17 / 10, 26925 / 10000),
            (9 / 5, 23767 / 10000), (19 / 10, 21591 / 10000)] : List (ℝ × ℝ)),
      ∀ s ∈ Icc r.2 (Ssec r.1), ¬ HVIneq r.1 s (hvConst r.1 s) :=
  P18.bracket_fails

/-- C19a, Prop. 10 (l.544-547 and table l.555-560, the `s₊` side): (HV) fails for `s₊(p) ≤ s ≤ sec²(π/2p)` at the six `(p, s₊)` of the table. -/
theorem C19a_bracket_fails :
    ∀ r ∈ ([(7 / 5, 52989 / 10000), (3 / 2, 39575 / 10000), (8 / 5, 31802 / 10000), (17 / 10, 26925 / 10000),
            (9 / 5, 23767 / 10000), (19 / 10, 21591 / 10000)] : List (ℝ × ℝ)),
      ∀ s ∈ Icc r.2 (Ssec r.1), ¬ HVIneqLp r.1 s (hvConst r.1 s) :=
  by
  intro r hr s hs
  have hb : 1 < r.1 ∧ r.1 < 2 ∧ 0 < r.2 := by
    have hr' := hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [lp_iff hb.1 hb.2.1 (by linarith [hs.1, hb.2.2])]
  exact C19a_bracket_fails_trig r hr s hs

/-- C19c, Prop. 10 (l.564-567): at the six exact rational failure points `(y*, t*)` printed there (also in
logs/bracket_upper_arb.log, rows `(p, s₊, y*, t*)`), `Γ - e < -1.15·10⁻⁶` at `s = s₊`,
and `< -5.7·10⁻⁵` at `p = 9/5` ("the certified upper bounds for Γ - e there range from -1.15·10⁻⁶ (at p = 7/5) to
-5.7·10⁻⁵ (at p = 9/5)"). -/
theorem C19c_bracket_points :
    (∀ r ∈ ([(7 / 5, 52989 / 10000, 110877 / 500000, 2144519 / 1000000),
             (3 / 2, 1583 / 400, 49177 / 100000, 1768641 / 1000000),
             (8 / 5, 15901 / 5000, 837049 / 1000000, 613161 / 500000), (17 / 10, 1077 / 400, 298409 / 250000, 0),
             (9 / 5, 23767 / 10000, 613873 / 500000, 0), (19 / 10, 21591 / 10000, 625363 / 500000, 0)] :
             List (ℝ × ℝ × ℝ × ℝ)),
        r.2.2.2 ∈ Icc (-π) π ∧ Gam r.1 r.2.1 r.2.2.1 r.2.2.2 - ee r.1 r.2.2.2 < -(115 / 10 ^ 8)) ∧
      Gam (9 / 5) (23767 / 10000) (613873 / 500000) 0 - ee (9 / 5) 0 < -(57 / 10 ^ 6) :=
  P18.bracket_points

/-- C19b_reduction, Prop. 10 (the s₋ side): the box inequalities of the certificate (`C19b_boxes`, (eq:two) at the
six `(p, s₋)`) imply the paper's claim C19b on all of `L^p` (Theorem B "if" + monotonicity in `s`). So C19b rests on the
computer only through its box inequalities. CONDITIONAL: on `C19b_boxes` (checked by computer; NOT proved in Lean). -/
theorem C19b_reduction : C19b_boxes → C19b_bracket_holds := by
  intro hb
  unfold C19b_bracket_holds
  intro r hr s hs hsr
  have hp : 1 < r.1 ∧ r.1 < 2 := by
    have hr' := hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  rw [lp_iff hp.1 hp.2 hs]
  exact P18.LocGlob.theoremB_if hp.1 hp.2 hs (P18.twoVar_mono (by linarith [hp.1]) (hb r hr) hs hsr)

/-- C20a_reduction, Prop. 11: the box inequalities of the certificate (`C20a_boxes`, (eq:two) at each cell's
`s_cell`) imply the paper's claim C20a on all of `L^p` (Theorem B "if" + monotonicity in `s`). CONDITIONAL: on `C20a_boxes`
(checked by computer; NOT proved in Lean). -/
theorem C20a_reduction : C20a_boxes → C20a_cells := P18.BoxReductions.C20a_reduction

/-- C21_reduction, Prop. 13: the box inequalities of the certificate (`C21_boxes`, a failure point at
`sec²(π/2p) - Δ_cell` on each cell) imply the paper's claim C21 on all of `L^p` (Prop. 4 + `Γ` decreasing in `s`).
CONDITIONAL: on `C21_boxes` (checked by computer; NOT proved in Lean). -/
theorem C21_reduction : C21_boxes → C21_false_width := P18.BoxReductions.C21_reduction

/-- C20b, Introduction (l.120-122: "up to an explicit level above p/(p-1)") and Remark (l.590-592): every
cell's level (minus `2·10⁻⁶`) is at least `p/(p-1)` on the whole cell (largest at the left end). -/
theorem C20b_cells_contain_jag :
    ∀ i : ℕ, i < 140 → cellLeft i / (cellLeft i - 1) ≤ cellLevel i - 2 / 10 ^ 6 :=
  P18.cells_contain_jag

/-- C20c, Prop. 11 proof (l.583-584): both ends of the window decrease in `p`, so `L(p_b) ≤ L(p)` on the cell (with the cell's `κ`). -/
theorem C20c_level_antitone :
    ∀ i : ℕ, i < 140 → ∀ p ∈ Icc (cellLeft i) (cellRight i),
      cellLevel i ≤ p / (p - 1) + cellKappa i * (Ssec p - p / (p - 1)) :=
  fun i _ p hp => P18.CellMono.level_antitone i p hp

/-- C21b, Prop. 13 (l.600-601: "between 0.00147 and 0.0564 (about 0.021 at p = 3/2)"): every width lies in
`[0.00147, 0.0564]`, both ends are attained (cells 139 and 66, `j = 114` and `j = 41`), and the cell containing `3/2`
(cell 33, `j = 8`) has width `0.021 ± 0.0005`. -/
theorem C21b_false_width_range :
    (∀ j : Fin 115, (147 / 100000 : ℚ) ≤ falseWidth j ∧ falseWidth j ≤ 141 / 2500) ∧
      falseWidth 114 = 147 / 100000 ∧ falseWidth 41 = 141 / 2500 ∧ |falseWidth 8 - 21 / 1000| ≤ 5 / 10000 ∧
      (3 / 2 : ℝ) ∈ Icc (cellLeft 33) (cellRight 33) := by
  refine ⟨by decide +kernel, by norm_num [falseWidth], by norm_num [falseWidth], ?_, ?_⟩
  · rw [abs_le]; constructor <;> norm_num [falseWidth]
  · simp only [cellRight, cellLeft]; norm_num

/-! ## Sec. 7 — the discrete relaxation (l.634-679) -/

/-- C23a, Sec. 7 (l.646-650): node values with the discrete inequality give an interpolant (by solutions of `φ'' + q²φ = 0`) that is
q-subtrigonometric. -/
theorem C23a_interp_qsubtrig {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {N : ℕ} (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) (hdisc : ∀ i : ℤ, 2 * cos (q * (2 * π / N)) * v i ≤ v (i + 1) + v (i - 1)) :
    QSubtrig q (interp q N v) :=
  P18.Relax.interp_qsubtrig hq0 hq1 hN hper hdisc

/-- C23d, Sec. 7 (l.639-646): hence `λ_{*,N} ≤ λ_*`: a feasible `λ` of the continuous problem is feasible on `N` nodes. -/
theorem C23d_discrete_relaxation {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {N : ℕ} (hN : 4 ≤ N)
    (hf : LamFeasible p s lam) : DiscFeasible p s lam N :=
  P18.Relax.discrete_relaxation hp1 hp2 hs hN hf

/-- C23e, Sec. 7 (l.652-653): `λ_{*,N}` does not decrease along nested grids `N, 2N` (a feasible `2N`-node vector restricts). -/
theorem C23e_nested_grids {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {N : ℕ} (hN : 4 ≤ N)
    (hf : DiscFeasible p s lam (2 * N)) : DiscFeasible p s lam N :=
  P18.Relax.nested_grids hp1 hp2 hs hN hf

/-! ## Further claims of the paper -/

/-- C29a, Prop. 10 table (l.555-560), column "open window": the ends `p/(p-1)` and `sec²(π/2p)` to 4 decimals. -/
theorem C29a_window_ends : ∀ r ∈ ([(7/5, 35000/10000, 53119/10000), (3/2, 30000/10000, 40000/10000),
      (8/5, 26667/10000, 32398/10000), (17/10, 24286/10000, 27535/10000), (9/5, 22500/10000, 24203/10000),
      (19/10, 21111/10000, 21800/10000)] : List (ℝ × ℝ × ℝ)),
      |r.1 / (r.1 - 1) - r.2.1| ≤ 5 / 10 ^ 5 ∧ |Ssec r.1 - r.2.2| ≤ 5 / 10 ^ 5 :=
  P18.NewRows11.window_ends

/-- C29b, Prop. 10 table (l.555-560), column "failing fraction", defined at l.569-570 as
`(sec²ϑ - s̄)/(sec²ϑ - p/(p-1))` with `s̄ = (s₋ + s₊)/2`, rounded to 0.1%. -/
theorem C29b_failing_fractions : ∀ r ∈ ([(7/5, 52986/10000, 52989/10000, 7/1000), (3/2, 39572/10000, 39575/10000, 43/1000),
      (8/5, 31799/10000, 31802/10000, 104/1000), (17/10, 26921/10000, 26925/10000, 188/1000),
      (9/5, 23764/10000, 23767/10000, 257/1000), (19/10, 21588/10000, 21591/10000, 306/1000)] : List (ℝ × ℝ × ℝ × ℝ)),
      |(Ssec r.1 - (r.2.1 + r.2.2.1) / 2) / (Ssec r.1 - r.1 / (r.1 - 1)) - r.2.2.2| ≤ 5 / 10 ^ 4 :=
  P18.NewRows11.failing_fractions

/-- C29c_reduction, Introduction (l.119-120): the box part `C19b_boxes` (the lower bounds `s₋ ≤ s₀`) implies the
claim C29c ("under 1% ... at p=7/5 and about 31% at p=19/10"); its other side `s₀ < s₊` is proved. CONDITIONAL: on
`C19b_boxes` (checked by computer; NOT proved in Lean). -/
theorem C29c_reduction : C19b_boxes → C29c_window_fail_part := fun hb => P18.NewRows11.window_fail_part hb

/-- C30, Remark after Prop. 11 (l.590-592): "on the first cell, `[4/3, 4577/3420]`, Proposition 11 gives (HV) ... for all
`s ≤ 6.413`, while `p/(p-1) ≤ 4` there" (every rational
`s_cell` with `0 ≤ L(p_b) - s_cell < 2·10⁻⁶` is `≥ 6.413`). -/
theorem C30_first_cell : 6413 / 1000 ≤ cellLevel 0 - 2 / 10 ^ 6 ∧
    ∀ p ∈ Set.Icc (cellLeft 0) (cellRight 0), p / (p - 1) ≤ 4 :=
  P18.NewRows11.first_cell

/-- C31a, footnote of Sec. 2 (l.205-206): `Γ(y,t) ≥ ((2cosϑ)^{-p} - 2^{-p/s}) exp(q|y|) + o(exp(q|y|))` uniformly in `t`. -/
theorem C31a_gam_lower_asymp {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∀ ε > 0, ∃ R : ℝ, ∀ y t : ℝ, R ≤ |y| →
      ((2 * cos (π / (2 * p))) ^ (-p) - (2 : ℝ) ^ (-p / s) - ε) * exp (p / 2 * |y|) ≤ Gam p s y t :=
  P18.NewRows11.gam_lower_asymp hp1 hp2 hs

/-- C31b, footnote of Sec. 2 (l.206-207): "the bracket is positive if and only if `x := 2cosϑ < 2^{1/s}`". -/
theorem C31b_bracket_pos_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    0 < (2 * cos (π / (2 * p))) ^ (-p) - (2 : ℝ) ^ (-p / s) ↔ 2 * cos (π / (2 * p)) < (2 : ℝ) ^ (1 / s) :=
  P18.NewRows11.bracket_pos_iff hp1 hp2 hs

/-- C20d, Prop. 11 (l.573-577): the cells: 114 equal cells on `[4/3, 19/10]`, 16 on `[19/10, 99/50]`, 10 on
`[99/50, 199/100]`; `κ` changes at `cellLeft 52 = 1361/855 = 1.5918…` and `cellLeft 76 = 77/45 = 1.7111…`; Prop. 13's cells "contained in
`[997/684, 1.99]`" (l.600) start at `cellLeft 25 = 997/684`. -/
theorem C20d_cell_structure :
    cellLeft 0 = 4 / 3 ∧ cellLeft 114 = 19 / 10 ∧ cellLeft 130 = 99 / 50 ∧ cellLeft 140 = 199 / 100 ∧
      cellLeft 52 = 1361 / 855 ∧ cellLeft 76 = 77 / 45 ∧ cellLeft 25 = 997 / 684 ∧
      (15918 / 10000 : ℝ) ≤ 1361 / 855 ∧ (1361 / 855 : ℝ) < 15919 / 10000 ∧
      (17111 / 10000 : ℝ) ≤ 77 / 45 ∧ (77 / 45 : ℝ) < 17112 / 10000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [cellLeft]

/-- C16d, Sec. 1 (l.81: "since `E` vanishes when `w = 0`") and Sec. 2 (l.191: "since `E(·,0) = 0`"). -/
theorem C16d_E_zero {p : ℝ} (hp : 0 < p) (z : ℂ) : Efun p z 0 = 0 := by
  unfold Efun
  rw [mul_zero, norm_zero, Real.zero_rpow (by positivity : (0 : ℝ) < p / 2).ne', zero_mul]

/-- C17e, Theorem B (l.509-510) with the `s₀` of (eq:two) (l.115 names it): for the threshold `s₀(p)` of C04b,
(HV) holds on `L^p` for `0 < s ≤ sec²(π/2p)` exactly when `s ≤ s₀(p)` (C17c with its `s₀` tied to (eq:two)). -/
theorem C17e_HV_iff_s0 {p s0 : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    ∀ s : ℝ, 0 < s → s ≤ Ssec p → (HVIneqLp p s (hvConst p s) ↔ s ≤ s0) := by
  intro s hs hsS
  constructor
  · intro hHV
    exact (hs0 s hs).mp (C17_theoremB_onlyif hp1 hp2 hs hsS hHV)
  · intro hle
    rw [lp_iff hp1 hp2 hs]
    exact P18.LocGlob.theoremB_if hp1 hp2 hs ((hs0 s hs).mpr hle)

/-- C15d, Sec. 5 (l.499-500): at Jaguzović's point `(log 2, π/2)`, "`Γ - e < 0` there for every `s > 3.9777`" (C15c gives
`s ≤ 4`; beyond, `Γ` decreases in `s`). -/
theorem C15d_jag_point_all_s :
    ∀ s : ℝ, 39777 / 10000 < s → Gam (3 / 2) s (log 2) (π / 2) < ee (3 / 2) (π / 2) := by
  intro s hs
  rcases le_or_gt s 4 with h | h
  · exact C15c_jaguzovic_range.1 s hs h
  · exact lt_of_le_of_lt (C04a_gam_antitone_s (by norm_num) (by norm_num) h.le (log 2) (π / 2))
      (C15c_jaguzovic_range.1 4 (by norm_num) le_rfl)

/-- C08b, Lemma 3 (l.271): "`w(0) = 0`" for the `w = ξ^k r e^{-Y/2}` of C08 (`k ≥ 1`). -/
theorem C08b_lift_w_zero (k : ℕ) (hk : 1 ≤ k) (r : ℂ → ℂ) (Y : Polynomial ℂ) :
    (fun ζ : ℂ => ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) 0 = 0 := by
  simp [zero_pow (by omega : k ≠ 0)]

/-- C10a8, Prop. 5 proof (ii) (l.366-367): "this gives `d/dp H(2) = 0`" (`H` along `u = tan²(π/2p)`). -/
theorem C10a8_dH_two : HasDerivAt (fun p => H p (uu p)) 0 2 := by
  obtain ⟨hu2, -, -, -, huu, -⟩ := C10a7_H_at_two
  have hp : HasDerivAt (fun p : ℝ => p) 1 2 := hasDerivAt_id' 2
  have t1 := ((hp.sub_const 1).const_mul (-2)).mul (huu.pow 2)
  have t2 := ((((hp.const_sub 2).pow 2).const_mul 3).add (hp.const_mul 2)).mul huu
  have t3 := (((hp.const_sub 2).pow 2).const_mul 3).sub_const 2
  convert (t1.add t2).add t3 using 1
  · funext p
    simp only [H, Pi.mul_apply, Pi.add_apply, Pi.pow_apply]
    ring
  · simp only [Pi.add_apply, Pi.pow_apply, hu2]
    norm_num
    ring

/-- C04e, Sec. 2 (l.202): `Γ(y,π/p) - e(π/p) = (p/8)(sec²ϑ - s)y² + O(y⁴)`, for every `s > 0` (C10b1 is the case `s = S`). -/
theorem C04e_gam_expansion {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ y : ℝ, |y| < δ →
      |Gam p s y (π / p) - ee p (π / p) - p / 8 * (Ssec p - s) * y ^ 2| ≤ C * y ^ 4 :=
  P18.NewRows12.gam_expansion_pi_p hp1 hp2 hs

/-- C16e, Sec. 2 (l.180-181): `E`, "as a function of `ζ = zw`", is "harmonic off the half-line `(-∞,0]`". -/
theorem C16e_U_harmonic_slit {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    InnerProductSpace.HarmonicOnNhd (fun ζ : ℂ => ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ)) Complex.slitPlane :=
  P18.NewRows12.U_harmonic_slit hp1 hp2

/-- C16f, Sec. 2 (l.181-182): "near each point of `(-∞,0)` it is the maximum of two harmonic functions (a convex
corner)". -/
theorem C16f_U_convex_corner {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) {ζ0 : ℂ} (hre : ζ0.re < 0) (him : ζ0.im = 0) :
    ∃ V ∈ nhds ζ0, ∃ h1 h2 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h1 V ∧ InnerProductSpace.HarmonicOnNhd h2 V ∧
      ∀ ζ ∈ V, ‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ) = max (h1 ζ) (h2 ζ) :=
  P18.NewRows12.U_convex_corner hp1 hp2 hre him

/-- C06d, Sec. 3 (l.235): for q-subtrigonometric `φ`, "`φ'` has bounded variation" (the right derivative, on every
compact interval). -/
theorem C06d_deriv_bv {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (a b : ℝ) :
    BoundedVariationOn (fun t => derivWithin φ (Set.Ici t) t) (Set.Icc a b) :=
  P18.NewRows12.deriv_bv hq0 hq1 hφ a b

/-- C06e, Sec. 3 (l.229-234): for q-subtrigonometric `φ`, "`∫ φ (b'' + q²b) dt ≥ 0`" for every `0 ≤ b` on `T`;
"so `μ := φ'' + q²φ ≥ 0` as a measure". Lean takes every 2π-periodic `b ∈ C²` with `b ≥ 0` (the paper: `b ∈ C^∞(T)`;
C² includes these, so the Lean statement is at least as strong). -/
theorem C06e_mu_nonneg {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {φ : ℝ → ℝ} (hφ : QSubtrig q φ) (b : ℝ → ℝ)
    (hb : ContDiff ℝ 2 b) (hper : Function.Periodic b (2 * π)) (hpos : ∀ t, 0 ≤ b t) :
    0 ≤ ∫ t in (-π)..π, φ t * (deriv (deriv b) t + q ^ 2 * b t) :=
  P18.NewRows12b.mu_nonneg hq0 hq1 hφ b hb hper hpos

/-- C21c, after Prop. 13 (l.611-612): "Near `p = 4/3` the failure is weak: the coefficient `Q₄(p)` of Proposition 5
tends to `0` as `p → 4/3`" (`Q₄ = Acoef`). -/
theorem C21c_Q4_tendsto : Filter.Tendsto Acoef (nhds (4 / 3)) (nhds 0) :=
  P18.NewRows12.Acoef_tendsto

/-- C30b, Remark after Prop. 11 (l.592-593): "At the right end of a cell the certified part of the window,
`(s_cell - p/(p-1))/(sec²(π/2p) - p/(p-1))`, is about `κ`; inside the cell it is smaller". -/
theorem C30b_frac_le_right : ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i), ∀ sc : ℝ,
    cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i →
    (sc - p / (p - 1)) / (Ssec p - p / (p - 1))
      ≤ (sc - cellRight i / (cellRight i - 1)) / (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) :=
  P18.NewRows11b.frac_le_right

/-- C30c, Remark after Prop. 11 (l.593-594): "about 16% (at p = 1.975)" (`1.975 = cellLeft 129`). -/
theorem C30c_frac_at_1975 : ∀ sc : ℝ, cellLevel 129 - 2 / 10 ^ 6 < sc → sc ≤ cellLevel 129 →
    16 / 100 ≤ (sc - 1975 / 1000 / (1975 / 1000 - 1)) / (Ssec (1975 / 1000) - 1975 / 1000 / (1975 / 1000 - 1)) ∧
    (sc - 1975 / 1000 / (1975 / 1000 - 1)) / (Ssec (1975 / 1000) - 1975 / 1000 / (1975 / 1000 - 1)) ≤ 17 / 100 :=
  P18.NewRows11b.frac_at_1975

/-- C30d, Remark after Prop. 11 (l.593-594): "its minimum over `[4/3, 1.99]` is about 16% (at `p = 1.975`)": the certified part is at least 16% of the window on
every cell, for every certified `s_cell` (numerically, the minimum is about 0.1646, at `p = 1.975`; not proved). -/
theorem C30d_frac_ge : ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i), ∀ sc : ℝ,
    cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i → 16 / 100 ≤ (sc - p / (p - 1)) / (Ssec p - p / (p - 1)) :=
  P18.NewRows11b.frac_ge

/-- C04f, Sec. 5 (l.502-504, with Prop. 4): (eq:two) "fails at `s = sec²ϑ`" for every `p ∈ (4/3, 2)`; as the paper says
("Proposition 5 supplies a proof of that observation"), from Prop. 5 alone (the valley of C10b3), with no cited result
-/
theorem C04f_two_fails_at_sec {p : ℝ} (hp1 : 4 / 3 < p) (hp2 : p < 2) : ¬ TwoVar p (Ssec p) :=
  P18.R2.C04f_two_fails_at_sec hp1 hp2

/-- C30e, Remark after Prop. 11 (l.589-590): "The gain over the range `s ≤ p/(p-1)` of [Jag2026] ... is largest near
`p = 4/3`": on every other cell the level exceeds `p/(p-1)` by less than the first cell's certified gain over 4. -/
theorem C30e_gain_largest_first : ∀ i : ℕ, 1 ≤ i → i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i),
    cellLevel i - p / (p - 1) < cellLevel 0 - 2 / 10 ^ 6 - 4 :=
  P18.NewRows11c.gain_largest_first

/-- C30f_reduction, Remark after Prop. 11: the box part `C20a_boxes` implies C30f (eq:two beyond `p/(p-1)`).
CONDITIONAL: on `C20a_boxes` (checked by computer; NOT proved in Lean). -/
theorem C30f_reduction : C20a_boxes → C30f_beyond_jag := fun hb => P18.NewRows11c.beyond_jag hb

/-- C19d_reduction, Prop. 10: the box part `C19b_boxes` implies C19d (`s₋ ≤ s₀ < s₊`); the `s₀ < s₊` side
is proved outright (the six failure points). CONDITIONAL: on `C19b_boxes` (checked by computer; NOT proved in Lean). -/
theorem C19d_reduction : C19b_boxes → C19d_bracket_s0 := fun hb => P18.NewRows11c.bracket_s0 hb

/-- C16g, Sec. 2 (l.183): `E`, as a function of `ζ = zw`, "is subharmonic in `ζ`" (the paper cites [Dem, Ch. I, (4.12), (4.16)];
Lean proves it with no textbook fact: Proofs/LocGlob.lean). -/
theorem C16g_U_subharmonic {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    IsSubharmonic (fun ζ : ℂ => ((‖ζ‖ ^ (p / 2) * ee p (Complex.arg ζ) : ℝ) : EReal)) :=
  P18.LocGlob.Ufun_subharmonic hp1 hp2

/-- C16h, Sec. 2 (l.182-183): `E`, as a function of `ζ = zw`, has "mean over `|ζ| = r`" equal to
"`r^q tanϑ sin(qπ)/(qπ) > 0 = E(0)`" (polar form `ζ = r e^{it}`, `-π < t ≤ π`, so `E = r^q e(t)`; `q = p/2`, `ϑ = π/(2p)`). -/
theorem C16h_U_mean {p r : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hr : 0 < r) :
    (2 * π)⁻¹ * ∫ t in (-π)..π, r ^ (p / 2) * ee p t
        = r ^ (p / 2) * tan (π / (2 * p)) * sin (p / 2 * π) / (p / 2 * π) ∧
      0 < r ^ (p / 2) * tan (π / (2 * p)) * sin (p / 2 * π) / (p / 2 * π) ∧
      ‖(0 : ℂ)‖ ^ (p / 2) * ee p (Complex.arg 0) = 0 :=
  P18.UMean.U_mean hp1 hp2 hr

/-- C10a9, Remark 6 (l.382): "By the proof above, `H = 0` and `dH/dp > 0` at `p = 4/3`, so `H < 0` on an interval
`(4/3 - ε, 4/3)`" (`H` along `u = tan²(π/2p)`). With C10c2 (`H > 0` on `(4/3, 2)`) this is l.383: "Thus `H` changes sign
at `p = 4/3`". -/
theorem C10a9_H_sign_change :
    H (4 / 3) (uu (4 / 3)) = 0 ∧ 0 < deriv (fun p => H p (uu p)) (4 / 3) ∧
      ∃ ε > 0, ∀ p ∈ Ioo (4 / 3 - ε) (4 / 3), H p (uu p) < 0 :=
  P18.RemarkH.H_sign_change

/-- C20e, Prop. 11 (l.578: "`s_cell > p_a/(p_a-1)` (so `s_cell > p/(p-1)` on the whole cell)"): for every cell and EVERY
`s` with `0 ≤ L(p_b) - s < 2·10⁻⁶` (the certificate's `s_cell` is such an `s`), `p_a/(p_a-1) < s` and `p/(p-1) < s` on
the cell. So this conjunct of Prop. 11 is proved, not computer-checked. -/
theorem C20e_cell_beyond_jag : ∀ i : ℕ, i < 140 → ∀ sc : ℝ, cellLevel i - sc < 2 / 10 ^ 6 → sc ≤ cellLevel i →
    cellLeft i / (cellLeft i - 1) < sc ∧ ∀ p ∈ Icc (cellLeft i) (cellRight i), p / (p - 1) < sc :=
  P18.FinalRows.cell_beyond_jag

/-- C20a_full_given_cells, Prop. 11 (l.572-579): the statement as printed, GIVEN its computer part `C20a_cells` (a `def`,
NOT proved in Lean; so Prop. 11 itself is NOT proved in Lean, only this implication): for each of the 140 cells a
rational `s_cell` with `0 ≤ L(p_b) - s_cell < 2·10⁻⁶` and `s_cell > p_a/(p_a-1)` (so `s_cell > p/(p-1)` on the cell)
such that (HV) holds for every `p` of the cell and every `s ∈ (0, s_cell]`. CONDITIONAL: on `C20a_cells` (checked by
computer; NOT proved in Lean). -/
theorem C20a_full_given_cells (h : C20a_cells) : ∀ i : ℕ, i < 140 → ∃ sc : ℚ,
    0 ≤ cellLevel i - (sc : ℝ) ∧ cellLevel i - (sc : ℝ) < 2 / 10 ^ 6 ∧
      cellLeft i / (cellLeft i - 1) < (sc : ℝ) ∧ (∀ p ∈ Icc (cellLeft i) (cellRight i), p / (p - 1) < (sc : ℝ)) ∧
      ∀ p ∈ Icc (cellLeft i) (cellRight i), ∀ s : ℝ, 0 < s → s ≤ sc → HVIneqLp p s (hvConst p s) :=
  P18.FinalRows.prop11_full h

/-- C08c, Lemma 3 lift (l.272: "outside the finitely many zeros of `g`; at those zeros `z = w = 0` and `G(z,w) = 0`"):
for the `z = B r e^{Y/2}`, `w = ζ^k r e^{-Y/2}` of C08 (any `r` with `zw = g` on the closed disc, as C08 gives), at a zero
of `g` on `T`: `z = w = 0` and `G(z,w) = 0`. -/
theorem C08c_lift_zeros {p s : ℝ} (hp : 0 < p) (hs : 0 < s) {k : ℕ} {zs : List ℂ} (hzs : ∀ a ∈ zs, 0 < ‖a‖ ∧ ‖a‖ < 1)
    {g r : ℂ → ℂ} {Y : Polynomial ℂ}
    (hprod : ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
      (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) * (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = g ζ)
    (θ : ℝ) (hg : g (Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    let ζ := Complex.exp ((θ : ℂ) * Complex.I)
    blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2) = 0 ∧ ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2) = 0 ∧
      G p s (blaschke zs ζ * r ζ * Complex.exp (Y.eval ζ / 2)) (ζ ^ k * r ζ * Complex.exp (-(Y.eval ζ) / 2)) = 0 :=
  P18.FinalRows.lift_zeros hp hs hzs hprod θ hg

/-- C19e, Prop. 10 (l.545-547, the `s₊` side in `s₀` form): `s₀(p) < s₊(p)` at the six `p` of the table, for the
threshold `s₀` of (eq:two). Proved from the failure points; the `s₋` side (C19d) is the computer part. -/
theorem C19e_s0_lt_splus : ∀ r ∈ ([(7/5, 52989/10000), (3/2, 39575/10000), (8/5, 31802/10000), (17/10, 26925/10000),
    (9/5, 23767/10000), (19/10, 21591/10000)] : List (ℝ × ℝ)),
    ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar r.1 s ↔ s ≤ s0)) → s0 < r.2 :=
  P18.FinalRows.s0_lt_splus

/-- C13n, Prop. 8 (l.424): the stated claim C13m ("`f` violates (HV) with `C = C_HV` at `(p,s)`", NOT proved) implies
that (HV) with `C = C_HV` fails at `(p, s) = (3/2, 3.98)`. CONDITIONAL: on `C13m_explicit_violates` (NOT proved
in Lean by itself; PROVED GIVEN the computer check C13c: row C13m_given_C13c). -/
theorem C13n_violates_imp_fails (hm : C13m_explicit_violates) :
    ¬ HVIneqLp (3 / 2) (398 / 100) (hvConst (3 / 2) (398 / 100)) :=
  P18.FinalRows.violates_imp_fails hm

/-- C13b, Prop. 8 (proof l.442-444): "we have `z, w ∈ H^p` for every `δ ∈ (0, 2π)`" (`p = 3/2`; `InHardy`: holomorphic
in the disc with `sup_{r<1} ∫|f(re^{iθ})|^p dθ < ∞`). -/
theorem C13b_explicit_hardy_proved : C13b_explicit_hardy :=
  P18.HardyBound.C13b_proved

/-- C13m_hand_step, Prop. 8 proof (l.444-446): "So `f ∈ L^p(T)`; as `w(0) = 0`, the Fourier coefficients of `z` vanish
for `n < 0` and those of `w̄` vanish for `n ≥ 0`, so `P₊f = z` and `P₋f = w̄`, and ... `f` violates (HV) ... if ...
`∫_T G(z,w) dθ/2π < 0`": C13b and C13c imply C13m. -/
theorem C13m_hand_step_proved : C13m_hand_step :=
  P18.HandStep.C13m_hand_step_proved

/-- C13m, Prop. 8 (l.424, "so `f` violates (HV) with `C = C_HV` at `(p,s)`"): given the computer certificate C13c,
`f = z + w̄` (`δ = e^{-2500}`) is in `L^p`, `P₊f = z`, `P₋f = w̄`, and (HV) with `C = C_HV` fails for it at `(3/2, 3.98)`.
CONDITIONAL: on `C13c_explicit_integral` (checked by computer; NOT proved in Lean). -/
theorem C13m_given_C13c : C13c_explicit_integral → C13m_explicit_violates :=
  P18.HandStep.C13m_given_C13c

/-- C13p, Prop. 8 proof (l.450: "the integral is `Σ_j Γ(y_j,t_j) ∫_{arc_j} |zw|^q`"), pointwise: on each open arc,
`G(z,w) = |zw|^{3/4} Γ(y_j, t_j)` with `(y_j, t_j) = (0, -2π/3), (y₂, t₂), (0, t₃)` (integrability: C13v; the
integral form: C13w). -/
theorem C13p_arc_integrand :
    let δ := Real.exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    (∀ θ ∈ Set.Ioo (-π) (-(δ / 2)), G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3))) ∧
    (∀ θ ∈ Set.Ioo (-(δ / 2)) (δ / 2), G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS) ∧
    (∀ θ ∈ Set.Ioo (δ / 2) π, G (3 / 2) (398 / 100) (Z θ) (W θ) =
        ‖Z θ * W θ‖ ^ (3 / 4 : ℝ) * Gam (3 / 2) (398 / 100) 0 Explicit.bA) :=
  P18.Prop8Steps.arc_integrand

/-- C13q, Prop. 8 proof (l.451: "`|zw|^q = Π_k |2 sin((θ-θ_k)/2)|^{-qα_k}`", `θ_k = -δ/2, δ/2, π`, `α_k = α₋, α₊, α_π`). -/
theorem C13q_arc_modulus :
    let δ := Real.exp (-2500)
    ∀ θ ∈ Set.Ioo (-π) π, θ ≠ -(δ / 2) → θ ≠ δ / 2 →
      ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) * Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 4 : ℝ)
        = |2 * Real.sin ((θ + δ / 2) / 2)| ^ (-(3 / 4) * Explicit.aA) *
          |2 * Real.sin ((θ - δ / 2) / 2)| ^ (-(3 / 4) * Explicit.aB) *
          |2 * Real.sin ((θ - π) / 2)| ^ (-(3 / 4) * Explicit.aC) :=
  P18.Prop8Steps.arc_modulus

/-- C13r, Prop. 8 proof (l.455: "since `2 sin(x/2) ≥ 0.99 x` there", for `0 < x < x₀ ≤ e^{-1500}`): on `[0, 1/10]`. -/
theorem C13r_two_sin_half_ge : ∀ x ∈ Set.Icc (0 : ℝ) (1 / 10), 99 / 100 * x ≤ 2 * Real.sin (x / 2) :=
  P18.Prop8StepE.two_sin_half_ge

/-- C13s, remark "why `δ` is so small" after Prop. 8 (l.468-485), its EXACT claims (its numbers are numerical and not in
Lean): `η = a₋ + a₊ - 1 = 0.0102/π`; `q t₂ = π a₋ - π/2`, `q t₃ = π/2 + π η`; `e(t₂) = tan ϑ sin(π a₋)`,
`e(t₃) = -tan ϑ sin(π η)`; "the reflection formula ... gives `e(t₂) B(1-a₋, 1-a₊) + e(t₃) B(1-a₊, η) = 0`. Hence
`W₁ = (Γ - e)(y₂,t₂) B(1-a₋, 1-a₊) + (Γ - e)(0,t₃) B(1-a₊, η)`"; "on the third arc `Γ(0,t₁) = e(t₁) = 0`". -/
theorem C13s_remark_delta :
    let am : ℝ := 3 / 4 * Explicit.aA
    let ap : ℝ := 3 / 4 * Explicit.aB
    let η : ℝ := am + ap - 1
    η = 102 / 10000 / π ∧ 3 / 4 * Explicit.tS = π * am - π / 2 ∧ 3 / 4 * Explicit.bA = π / 2 + π * η ∧
    ee (3 / 2) Explicit.tS = Real.tan (π / 3) * Real.sin (π * am) ∧
    ee (3 / 2) Explicit.bA = -(Real.tan (π / 3) * Real.sin (π * η)) ∧
    ee (3 / 2) Explicit.tS * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re +
      ee (3 / 2) Explicit.bA * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re = 0
    ∧ (Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re
        + Gam (3 / 2) (398 / 100) 0 Explicit.bA * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re
      = (Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS - ee (3 / 2) Explicit.tS) * (Complex.betaIntegral ((1 - am : ℝ) : ℂ) ((1 - ap : ℝ) : ℂ)).re
        + (Gam (3 / 2) (398 / 100) 0 Explicit.bA - ee (3 / 2) Explicit.bA) * (Complex.betaIntegral ((1 - ap : ℝ) : ℂ) ((η : ℝ) : ℂ)).re)
    ∧ (Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) = 0 ∧ ee (3 / 2) (-(2 * π / 3)) = 0) :=
  P18.RemarkDelta.remark_delta_exact

/-- C21d, after Prop. 13 (l.610-611): "The first of them contains `p = 4/3`, where (eq:two) holds for every
`s ≤ sec²(π/2p)` [Mel], so no `Δ_cell > 0` exists there" (the first cell; same shape as C21). -/
theorem C21d_no_width_first_cell :
    (4 / 3 : ℝ) ∈ Set.Icc (cellLeft 0) (cellRight 0) ∧
      ∀ Δ > 0, ¬ ∀ p ∈ Set.Icc (cellLeft 0) (cellRight 0), ∀ s ∈ Set.Icc (Ssec p - Δ) (Ssec p),
        ¬ HVIneqLp p s (hvConst p s) :=
  P18.R2.C21d_no_width_first_cell

/-- C30g, Remark after Prop. 11 (l.592-593): "At the right end of a cell the certified part of the window ... is
about `κ`": within `4·10⁻⁴`, for every certified `s_cell`. -/
theorem C30g_right_end_kappa : ∀ i : ℕ, i < 140 → ∀ sc : ℝ, cellLevel i - 2 / 10 ^ 6 < sc → sc ≤ cellLevel i →
    |(sc - cellRight i / (cellRight i - 1)) / (Ssec (cellRight i) - cellRight i / (cellRight i - 1)) - cellKappa i|
      ≤ 4 / 10 ^ 4 :=
  P18.R2.C30f_right_end_kappa

/-- C17g, Abstract and Thm B (l.45-47): C17f with the paper's own definition of "the best constant" (the greatest
lower bound `C*` of the valid constants, as in C22c): `C* = C_HV` iff (eq:two). -/
theorem C17g_best_glb_iff {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (hsS : s ≤ Ssec p) :
    IsGLB {C : ℝ | 0 < C ∧ HVIneqLp p s C} (hvConst p s) ↔ TwoVar p s :=
  ⟨fun h => C17_theoremB_onlyif hp1 hp2 hs hsS (P18.R2.isGLB_valid_mem h),
   fun h => ((C17f_best_iff hp1 hp2 hs hsS).mpr h).isGLB⟩

/-- C25c, Abstract (l.41-42): C25b with "best" read as the greatest lower bound of the valid constants (as in C22c):
`C* = C_HV` for every `s ∈ (0, sec²(π/2p))` iff `p ≤ 4/3`. -/
theorem C25c_best_range_glb_iff {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    (∀ s : ℝ, 0 < s → s < Ssec p → IsGLB {C : ℝ | 0 < C ∧ HVIneqLp p s C} (hvConst p s)) ↔ p ≤ 4 / 3 :=
  ⟨fun h => (C25_range_correct_iff hp1 hp2).mp fun s hs hsS => P18.R2.isGLB_valid_mem (h s hs hsS),
   fun h s hs hsS => ((C25b_best_range_iff hp1 hp2).mpr h s hs hsS).isGLB⟩

/-- C04g, Sec. 2 (l.200-203): `e(π/p) = 0`, `cos(π/p) = cos 2ϑ`, `1 + cos 2ϑ = 2/sec²ϑ`, so for every `1 < p < 2`
and `s`: `Γ(y,π/p) - e(π/p) = (1 + (sec²ϑ/2)(cosh y - 1))^q - cosh(sy/2)^{p/s}`. -/
theorem C04g_gam_closed_pi_p {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (y : ℝ) :
    Gam p s y (π / p) - ee p (π / p) = (1 + Ssec p / 2 * (Real.cosh y - 1)) ^ (p / 2) - Real.cosh (s * y / 2) ^ (p / s) :=
  P18.R2Mine.gam_closed_pi_p hp1 hp2 y

/-- C04h, Sec. 2 (l.204): `Γ(y,π/p) - e(π/p)` "is negative for small `y ≠ 0` when `s > sec²ϑ`". -/
theorem C04h_gam_neg_above_sec {p s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : Ssec p < s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ 0 → |y| < δ → Gam p s y (π / p) < ee p (π / p) :=
  P18.R2Mine.gam_neg_pi_p hp1 hp2 hs

/-- C04i, Sec. 2 (l.199): "always `s₀(p) ≤ sec²ϑ`", for every `1 < p < 2`, from C04h alone (no cited result; the
paper's own claim, split off the cited conjuncts of C04d). -/
theorem C04i_s0_le_sec {p s0 : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs0 : ∀ s : ℝ, 0 < s → (TwoVar p s ↔ s ≤ s0)) :
    s0 ≤ Ssec p :=
  P18.R2Mine.s0_le_sec hp1 hp2 hs0

/-- C10f, proof of Prop. 5 (l.374-375): `u'(p) = -(π/p²) √u (1 + u)` for `u = u(p) = tan²(π/2p)`, `1 < p < 2`. -/
theorem C10f_u_deriv {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt uu (-(π / p ^ 2) * √(uu p) * (1 + uu p)) p :=
  P18.R2Mine.uu_hasDerivAt hp1 hp2

/-- C10g, proof of Prop. 5 (l.375): `u''(p) = (2π/p³) √u (1+u) + (π²/(2p⁴)) (1+u)(1+3u)`, the derivative of the
`u'` of C10f, `1 < p < 2`. -/
theorem C10g_u_deriv2 {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    HasDerivAt (fun x => -(π / x ^ 2) * √(uu x) * (1 + uu x))
      (2 * π / p ^ 3 * √(uu p) * (1 + uu p) + π ^ 2 / (2 * p ^ 4) * (1 + uu p) * (1 + 3 * uu p)) p :=
  P18.R2Mine.uu_hasDerivAt2 hp1 hp2

/-- C13t, after the proof of Prop. 8 (l.462-464): with `g = zw`, "`Re(ξg'/g) = 1 + Σ_k α_k Re(ω_k/(1-ω_k)) >
1 - ½Σ_k α_k = 0` ... so `g` is starlike", for every `δ` and every `ζ ≠ 0` in the disc. ("hence univalent" and the
slit image, l.464-466, are NOT formalized: AUDIT_NOTES (P3).) -/
theorem C13t_starlike (δ : ℝ) : ∀ ζ ∈ Metric.ball (0 : ℂ) 1, ζ ≠ 0 →
    0 < (ζ * deriv (fun ξ => Explicit.zf δ ξ * Explicit.wf δ ξ) ζ / (Explicit.zf δ ζ * Explicit.wf δ ζ)).re :=
  P18.R2b.C13t_starlike δ

/-- C13u, proof of Prop. 8, Step 1 (l.430-433): "`Re Y` is `y₂` times the harmonic measure of the arc `(-δ/2, δ/2)` ...
So `0 ≤ Re Y ≤ y₂` in the disc", for every `δ ∈ (0, 2π)`. -/
theorem C13u_ReY_bounds {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 2 * π) :
    ∀ ζ ∈ Metric.ball (0 : ℂ) 1, 0 ≤ (Explicit.Yf δ ζ).re ∧ (Explicit.Yf δ ζ).re ≤ Explicit.y2 :=
  P18.R2c.C13u_ReY_bounds hδ0 hδ1

/-- C23f, Sec. 7, "Two inequalities" (l.640-645), the ω step: if `ρ'' + q²ρ ≥ 0` on an interval of length `< π/q` and
`ρ` vanishes at both ends, then `ρ ≤ 0` there (via `ω = cρ' - c'ρ` nondecreasing, `(ρ/c)' = ω/c²`). The paper applies it
to `ρ` with `ρ'' + q²ρ = μ` a measure; this row is the `C²` case (Lean proves C23b, which the step serves, by another
route: q-subtrigonometric ⇒ trigonometrically convex ⇒ the discrete inequality). -/
theorem C23f_omega_step {q a b : ℝ} (hq : 0 < q) (hab : a < b) (hlen : q * (b - a) < π) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hμ : ∀ t ∈ Set.Icc a b, 0 ≤ deriv (deriv ρ) t + q ^ 2 * ρ t)
    (ha : ρ a = 0) (hb : ρ b = 0) : ∀ t ∈ Set.Icc a b, ρ t ≤ 0 :=
  P18.R2c.omega_step hq hab hlen hρ hμ ha hb

/-- C06f, Sec. 3 (l.226-228): "For continuous `φ`, the q-subtrigonometric functions are therefore the 2π-periodic
q-trigonometrically convex functions of Levin's theory": the converse of C06a; with C06a, the iff. -/
theorem C06f_trigConvex_qsubtrig {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hper : Function.Periodic φ (2 * π)) (htc : TrigConvex q φ) : QSubtrig q φ :=
  P18.R2d.C06f_trigConvex_qsubtrig hq0 hq1 hc hper htc

/-- C13v, proof of Prop. 8, Step 3 (l.451-452): "Each arc integral is therefore the integral of an explicit positive
function with integrable power singularities at the two end points of the arc": `|zw|^q` (`q = 3/4`, `δ = e^{-2500}`) is
integrable on each of the three arcs. -/
theorem C13v_arc_integrable :
    let δ := Real.exp (-2500)
    let F := fun θ : ℝ => ‖Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I)) *
      Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))‖ ^ (3 / 4 : ℝ)
    IntervalIntegrable F MeasureTheory.volume (-π) (-(δ / 2)) ∧ IntervalIntegrable F MeasureTheory.volume (-(δ / 2)) (δ / 2) ∧
      IntervalIntegrable F MeasureTheory.volume (δ / 2) π :=
  P18.R2e.C13v_arc_integrable

/-- C13w, proof of Prop. 8, Step 3 (l.449-450): "the integral is `Σ_j Γ(y_j,t_j) ∫_{arc_j} |zw|^q dθ/2π`" (on
`(-π, π)`; the common factor `1/2π` is dropped on both sides). -/
theorem C13w_arc_integral :
    let δ := Real.exp (-2500)
    let Z := fun θ : ℝ => Explicit.zf δ (Complex.exp ((θ : ℂ) * Complex.I))
    let W := fun θ : ℝ => Explicit.wf δ (Complex.exp ((θ : ℂ) * Complex.I))
    ∫ θ in (-π)..π, G (3 / 2) (398 / 100) (Z θ) (W θ) =
      Gam (3 / 2) (398 / 100) 0 (-(2 * π / 3)) * (∫ θ in (-π)..(-(δ / 2)), ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) +
      Gam (3 / 2) (398 / 100) Explicit.y2 Explicit.tS * (∫ θ in (-(δ / 2))..(δ / 2), ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) +
      Gam (3 / 2) (398 / 100) 0 Explicit.bA * (∫ θ in (δ / 2)..π, ‖Z θ * W θ‖ ^ (3 / 4 : ℝ)) :=
  P18.R2e.C13w_arc_integral

end P18.Paper
