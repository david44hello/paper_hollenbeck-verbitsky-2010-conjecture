/-
  HVFalse/Proofs/Relax.lean - Sec. 7, the discrete relaxation (the paper): C23a, C23b, C23d, C23e
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Routes.
  C23b: Sector.qsubtrig_trigConvex + discrete_of_trigConvex. Needs 1/2 < q (paper: q = p/2, 1 < p < 2).
  C23d: restrict a feasible φ to the nodes.
  C23e: two fine steps give one coarse step: v₊₂ + v₋₂ ≥ (4c² - 2) v₀ = 2cos(2qh') v₀, c = cos(qh') ≥ 0. (Route difference:
        the paper restricts via the interpolant; the direct three-line algebra needs no interpolant.)
  C23a: the interpolant is φ(t) = Σ_{i<N} c_i K(t - i h), c_i = (v_{i+1} + v_{i-1} - 2cos(qh) v_i) / (2 sin(qh) sin(qπ)) ≥ 0,
        K(t) = cos(qt) on [-π, π], extended 2π-periodically (a single convex kink at ±π). Both sides are q-sinusoids on each
        cell, so it suffices to match the node values; at the nodes this is the circulant identity Σ_i (Δv)_i K(ν_j - ih) =
        2 sin(qh) sin(qπ) v_j (summation by parts; the second difference of K vanishes off the kink). Then
        |ζ|^q K(arg ζ - μ) = U(ζ e^{-iμ}) / tanϑ with U = ThmBIf.Ufun (2q) subharmonic (LocGlob.Ufun_subharmonic, no textbook fact), a
        rotation keeps the sub-mean-value inequality (circle averages are rotation invariant: `circleAverage_rotate`), and
        a nonnegative sum of continuous functions with the sub-mean-value inequality has it too. (The paper: "derivative
        jump ≥ 0, so q-subtrigonometric".)
-/
import HVFalse.Proofs.Bridges
import HVFalse.Proofs.Sector
import HVFalse.Proofs.ThmBIf
import HVFalse.Proofs.LocGlob
import HVFalse.Defs.Cells
import HVFalse.Defs.Extra

open Real Set Metric

namespace P18

namespace Relax

/-! ## Nodes -/

theorem N_mul_h {N : ℕ} (hN : 0 < N) : (N : ℝ) * (2 * π / N) = 2 * π := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [mul_div_assoc', mul_div_cancel_left₀ _ hN']

theorem node_succ (N : ℕ) (i : ℤ) :
    -π + ((i + 1 : ℤ) : ℝ) * (2 * π / N) = (-π + (i : ℝ) * (2 * π / N)) + 2 * π / N := by
  push_cast; ring

theorem node_pred (N : ℕ) (i : ℤ) :
    -π + ((i - 1 : ℤ) : ℝ) * (2 * π / N) = (-π + (i : ℝ) * (2 * π / N)) - 2 * π / N := by
  push_cast; ring

theorem node_addN {N : ℕ} (hN : N ≠ 0) (i : ℤ) :
    -π + ((i + N : ℤ) : ℝ) * (2 * π / N) = (-π + (i : ℝ) * (2 * π / N)) + 2 * π := by
  have h := N_mul_h (Nat.pos_of_ne_zero hN)
  push_cast; linear_combination h

theorem node_mem {N : ℕ} (hN : 0 < N) {m : ℤ} (hm0 : 0 ≤ m) (hmN : m ≤ N) :
    -π + (m : ℝ) * (2 * π / N) ∈ Icc (-π) π := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNr
  have hNh := N_mul_h hN
  have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
  have a1 := mul_nonneg hm0' hh.le
  have a2 := mul_le_mul_of_nonneg_right hmN' hh.le
  constructor <;> linarith

theorem sin_qh_pos {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) : 0 < sin (q * (2 * π / N)) := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNp
  have hhπ : 2 * π / N ≤ π := by rw [div_le_iff₀ hNp]; nlinarith [pi_pos]
  exact sin_pos_of_pos_of_lt_pi (mul_pos hq0 hh) (by nlinarith [mul_lt_mul_of_pos_right hq1 hh])

theorem den_pos {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) :
    0 < 2 * sin (q * (2 * π / N)) * sin (q * π) := by
  have h2 : 0 < sin (q * π) := sin_pos_of_pos_of_lt_pi (mul_pos hq0 pi_pos) (by nlinarith [pi_pos])
  exact mul_pos (mul_pos two_pos (sin_qh_pos hq0 hq1 hN)) h2

/-! ## C23b, C23d, C23e -/

/-- **C23b** (paper l.639-646), for `q = p/2 ∈ (1/2, 1)`: a q-subtrigonometric `φ` satisfies the discrete inequality at every
step `h` with `2qh < π`. -/
theorem qsubtrig_discrete {q h : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) (hh : 0 < h) (h2 : 2 * q * h < π) {φ : ℝ → ℝ}
    (hφ : QSubtrig q φ) (t : ℝ) : 2 * cos (q * h) * φ t ≤ φ (t + h) + φ (t - h) :=
  discrete_of_trigConvex (by linarith) hh h2 (Sector.qsubtrig_trigConvex hq0 hq1 hφ) t

/-- **C23d** (paper l.645-646): a feasible `λ` of the continuous problem is feasible on `N ≥ 4` nodes (`λ_{*,N} ≤ λ_*`). -/
theorem discrete_relaxation {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {N : ℕ} (hN : 4 ≤ N)
    (hf : LamFeasible p s lam) : DiscFeasible p s lam N := by
  obtain ⟨φ, hφ, hle⟩ := hf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNpos
  have h2 : 2 * (p / 2) * (2 * π / N) < π := by
    rw [show 2 * (p / 2) * (2 * π / N) = 2 * p * π / N by ring, div_lt_iff₀ hNpos]
    nlinarith [mul_pos pi_pos (show (0 : ℝ) < N - 2 * p by linarith)]
  refine ⟨fun i => φ (-π + (i : ℝ) * (2 * π / N)), fun i => ?_, fun i => ?_, fun i y => hle y _⟩
  · show φ (-π + ((i + N : ℤ) : ℝ) * (2 * π / N)) = φ (-π + (i : ℝ) * (2 * π / N))
    rw [node_addN (by omega) i]
    exact hφ.1 _
  · show 2 * cos (p / 2 * (2 * π / N)) * φ (-π + (i : ℝ) * (2 * π / N)) ≤
      φ (-π + ((i + 1 : ℤ) : ℝ) * (2 * π / N)) + φ (-π + ((i - 1 : ℤ) : ℝ) * (2 * π / N))
    rw [node_succ, node_pred]
    exact qsubtrig_discrete (by linarith) (by linarith) hh h2 hφ _

/-- **C23e** (paper l.652-653): a feasible `2N`-node vector restricts to a feasible `N`-node vector (`λ_{*,N} ≤ λ_{*,2N}`). -/
theorem nested_grids {p s lam : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) {N : ℕ} (hN : 4 ≤ N)
    (hf : DiscFeasible p s lam (2 * N)) : DiscFeasible p s lam N := by
  obtain ⟨v, hper, hdisc, hob⟩ := hf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  have hc : 0 ≤ cos (p / 2 * (2 * π / ((2 * N : ℕ) : ℝ))) := by
    apply cos_nonneg_of_mem_Icc
    rw [hcast, show p / 2 * (2 * π / (2 * (N : ℝ))) = p * π / (2 * N) by ring]
    have h0 : 0 ≤ p * π / (2 * N) := div_nonneg (by nlinarith [pi_pos]) (by linarith)
    constructor
    · linarith [pi_pos]
    · rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith [mul_pos pi_pos (show (0 : ℝ) < N - p by linarith)]
  have hcos2 : cos (p / 2 * (2 * π / N)) = 2 * cos (p / 2 * (2 * π / ((2 * N : ℕ) : ℝ))) ^ 2 - 1 := by
    rw [← cos_two_mul, hcast]
    congr 1
    field_simp
  refine ⟨fun i => v (2 * i), fun i => ?_, fun i => ?_, fun i y => ?_⟩
  · show v (2 * (i + N)) = v (2 * i)
    have h := hper (2 * i)
    rw [show 2 * i + ((2 * N : ℕ) : ℤ) = 2 * (i + N) by push_cast; ring] at h
    exact h
  · show 2 * cos (p / 2 * (2 * π / N)) * v (2 * i) ≤ v (2 * (i + 1)) + v (2 * (i - 1))
    have h0 := hdisc (2 * i)
    have h1 := hdisc (2 * i + 1)
    have h2 := hdisc (2 * i - 1)
    rw [show 2 * i + 1 + 1 = 2 * (i + 1) by ring, show 2 * i + 1 - 1 = 2 * i by ring] at h1
    rw [show 2 * i - 1 - 1 = 2 * (i - 1) by ring, show 2 * i - 1 + 1 = 2 * i by ring] at h2
    rw [hcos2]
    nlinarith [mul_le_mul_of_nonneg_left h0 hc]
  · have e : -π + ((2 * i : ℤ) : ℝ) * (2 * π / ((2 * N : ℕ) : ℝ)) = -π + (i : ℝ) * (2 * π / N) := by
      rw [hcast]; push_cast; field_simp
    have h := hob (2 * i) y
    rw [e] at h
    exact h

/-! ## C23a: the kernel `K` and the node identity -/

/-- `K(x) = cos(q x)` on `[-π, π]`, extended `2π`-periodically (`toIocMod` = the representative in `(-π, π]`). -/
noncomputable def kern (q x : ℝ) : ℝ := cos (q * toIocMod two_pi_pos (-π) x)

theorem kern_eq {q x : ℝ} (hx : x ∈ Icc (-π) π) : kern q x = cos (q * x) := by
  unfold kern
  rcases eq_or_lt_of_le hx.1 with h | h
  · subst h
    rw [toIocMod_apply_left, show q * (-π + 2 * π) = -(q * -π) by ring, cos_neg]
  · rw [(toIocMod_eq_self two_pi_pos).2 ⟨h, by linarith [hx.2]⟩]

theorem kern_periodic (q : ℝ) : Function.Periodic (kern q) (2 * π) := fun x => by
  unfold kern; rw [toIocMod_add_right]

/-- The kernel at the nodes: `G(m) = K(-π + m h)`. -/
noncomputable def kG (q : ℝ) (N : ℕ) (m : ℤ) : ℝ := kern q (-π + (m : ℝ) * (2 * π / N))

/-- Its discrete second difference `L(m) = G(m+1) + G(m-1) - 2 cos(qh) G(m)`. -/
noncomputable def kL (q : ℝ) (N : ℕ) (m : ℤ) : ℝ :=
  kG q N (m + 1) + kG q N (m - 1) - 2 * cos (q * (2 * π / N)) * kG q N m

theorem kG_periodic {q : ℝ} {N : ℕ} (hN : N ≠ 0) (m : ℤ) : kG q N (m + N) = kG q N m := by
  unfold kG; rw [node_addN hN m]; exact kern_periodic q _

theorem kL_periodic {q : ℝ} {N : ℕ} (hN : N ≠ 0) (m : ℤ) : kL q N (m + N) = kL q N m := by
  unfold kL
  rw [show m + (N : ℤ) + 1 = (m + 1) + N by ring, show m + (N : ℤ) - 1 = (m - 1) + N by ring,
    kG_periodic hN, kG_periodic hN, kG_periodic hN]

/-- Off the kink, `K` is a q-sinusoid, so its second difference vanishes. -/
theorem kL_eq_zero_of_pos {q : ℝ} {N : ℕ} (hN : 0 < N) {m : ℤ} (h1 : 1 ≤ m) (h2 : m + 1 ≤ N) : kL q N m = 0 := by
  unfold kL kG
  rw [kern_eq (node_mem hN (m := m + 1) (by omega) h2), kern_eq (node_mem hN (m := m - 1) (by omega) (by omega)),
    kern_eq (node_mem hN (m := m) (by omega) (by omega)),
    show q * (-π + ((m + 1 : ℤ) : ℝ) * (2 * π / N)) = q * (-π + (m : ℝ) * (2 * π / N)) + q * (2 * π / N) by
      push_cast; ring,
    show q * (-π + ((m - 1 : ℤ) : ℝ) * (2 * π / N)) = q * (-π + (m : ℝ) * (2 * π / N)) - q * (2 * π / N) by
      push_cast; ring,
    cos_add, cos_sub]
  ring

theorem kL_eq_zero {q : ℝ} {N : ℕ} (hN : 0 < N) {m : ℤ} (hm : m ≠ 0) (h1 : -(N : ℤ) < m) (h2 : m < N) :
    kL q N m = 0 := by
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · rw [← kL_periodic (q := q) (N := N) (by omega) m]
    exact kL_eq_zero_of_pos hN (by omega) (by omega)
  · exact kL_eq_zero_of_pos hN (by omega) (by omega)

/-- At the kink: `L(0) = 2 sin(qh) sin(qπ)`. -/
theorem kL_zero {q : ℝ} {N : ℕ} (hN : 2 ≤ N) : kL q N 0 = 2 * sin (q * (2 * π / N)) * sin (q * π) := by
  have hN0 : 0 < N := by omega
  have hNh := N_mul_h hN0
  have hm1 : kG q N (0 - 1) = kG q N ((N : ℤ) - 1) := by
    rw [← kG_periodic (q := q) (N := N) (by omega) (0 - 1)]; congr 1
  unfold kL; rw [hm1]; unfold kG
  rw [kern_eq (node_mem hN0 (m := 0 + 1) (by omega) (by omega)),
    kern_eq (node_mem hN0 (m := (N : ℤ) - 1) (by omega) (by omega)),
    kern_eq (node_mem hN0 (m := 0) (by omega) (by omega)),
    show q * (-π + ((0 + 1 : ℤ) : ℝ) * (2 * π / N)) = -(q * π - q * (2 * π / N)) by push_cast; ring,
    show q * (-π + (((N : ℤ) - 1 : ℤ) : ℝ) * (2 * π / N)) = q * π - q * (2 * π / N) by
      push_cast; linear_combination q * hNh,
    show q * (-π + ((0 : ℤ) : ℝ) * (2 * π / N)) = -(q * π) by push_cast; ring,
    cos_neg, cos_neg, cos_sub]
  ring

/-- Summation over one period does not see a shift of the index. -/
theorem sum_shift {N : ℕ} {F : ℤ → ℝ} (hF : ∀ i : ℤ, F (i + N) = F i) :
    ∑ i ∈ Finset.range N, F ((i : ℤ) + 1) = ∑ i ∈ Finset.range N, F (i : ℤ) := by
  have h1 := Finset.sum_range_succ (fun i : ℕ => F (i : ℤ)) N
  have h2 := Finset.sum_range_succ' (fun i : ℕ => F (i : ℤ)) N
  have h3 : F (N : ℤ) = F 0 := by simpa using hF 0
  push_cast at h1 h2
  linarith

theorem sum_shift_pred {N : ℕ} {F : ℤ → ℝ} (hF : ∀ i : ℤ, F (i + N) = F i) :
    ∑ i ∈ Finset.range N, F ((i : ℤ) - 1) = ∑ i ∈ Finset.range N, F (i : ℤ) := by
  have h := sum_shift (N := N) (F := fun k => F (k - 1)) (fun i => by
    show F (i + N - 1) = F (i - 1)
    rw [show i + (N : ℤ) - 1 = (i - 1) + N by ring]
    exact hF _)
  simp only [add_sub_cancel_right] at h
  exact h.symm

/-- The coefficient `c_i = (v_{i+1} + v_{i-1} - 2cos(qh) v_i) / (2 sin(qh) sin(qπ))` (`≥ 0` by the discrete inequality). -/
noncomputable def coef (q : ℝ) (N : ℕ) (v : ℤ → ℝ) (i : ℤ) : ℝ :=
  (v (i + 1) + v (i - 1) - 2 * cos (q * (2 * π / N)) * v i) / (2 * sin (q * (2 * π / N)) * sin (q * π))

/-- The node identity `Σ_i c_i K(ν_j - i h) = v_j` (summation by parts). -/
theorem node_identity {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) {j : ℕ} (hj : j < N) :
    ∑ i ∈ Finset.range N, coef q N v i * kG q N ((j : ℤ) - i) = v j := by
  have hN0 : N ≠ 0 := by omega
  have hden := den_pos hq0 hq1 hN
  have hA : ∑ i ∈ Finset.range N, v ((i : ℤ) + 1) * kG q N ((j : ℤ) - i) =
      ∑ i ∈ Finset.range N, v (i : ℤ) * kG q N ((j : ℤ) - i + 1) := by
    have h := sum_shift (N := N) (F := fun k => v k * kG q N ((j : ℤ) - k + 1)) (fun k => by
      show v (k + N) * kG q N ((j : ℤ) - (k + N) + 1) = v k * kG q N ((j : ℤ) - k + 1)
      rw [hper, ← kG_periodic hN0 ((j : ℤ) - (k + N) + 1)]
      congr 2; ring)
    beta_reduce at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; ring
  have hB : ∑ i ∈ Finset.range N, v ((i : ℤ) - 1) * kG q N ((j : ℤ) - i) =
      ∑ i ∈ Finset.range N, v (i : ℤ) * kG q N ((j : ℤ) - i - 1) := by
    have h := sum_shift_pred (N := N) (F := fun k => v k * kG q N ((j : ℤ) - k - 1)) (fun k => by
      show v (k + N) * kG q N ((j : ℤ) - (k + N) - 1) = v k * kG q N ((j : ℤ) - k - 1)
      rw [hper, ← kG_periodic hN0 ((j : ℤ) - (k + N) - 1)]
      congr 2; ring)
    beta_reduce at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2; ring
  have hsum : ∑ i ∈ Finset.range N, (v ((i : ℤ) + 1) + v ((i : ℤ) - 1) - 2 * cos (q * (2 * π / N)) * v i) *
      kG q N ((j : ℤ) - i) = ∑ i ∈ Finset.range N, v (i : ℤ) * kL q N ((j : ℤ) - i) := by
    have e1 : ∀ i ∈ Finset.range N, (v ((i : ℤ) + 1) + v ((i : ℤ) - 1) - 2 * cos (q * (2 * π / N)) * v i) *
        kG q N ((j : ℤ) - i) = v ((i : ℤ) + 1) * kG q N ((j : ℤ) - i) + v ((i : ℤ) - 1) * kG q N ((j : ℤ) - i)
          - 2 * cos (q * (2 * π / N)) * (v i * kG q N ((j : ℤ) - i)) := fun i _ => by ring
    have e2 : ∀ i ∈ Finset.range N, v (i : ℤ) * kL q N ((j : ℤ) - i) = v (i : ℤ) * kG q N ((j : ℤ) - i + 1)
        + v (i : ℤ) * kG q N ((j : ℤ) - i - 1) - 2 * cos (q * (2 * π / N)) * (v i * kG q N ((j : ℤ) - i)) :=
      fun i _ => by unfold kL; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB]
  have hsingle : ∑ i ∈ Finset.range N, v (i : ℤ) * kL q N ((j : ℤ) - i) = v j * kL q N 0 := by
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.2 hj)]
    · rw [sub_self]
    · intro i hi hij
      have hi' := Finset.mem_range.1 hi
      rw [kL_eq_zero (q := q) (N := N) (m := (j : ℤ) - i) (by omega) (by omega) (by omega) (by omega), mul_zero]
  have hcoef : ∀ i ∈ Finset.range N, coef q N v i * kG q N ((j : ℤ) - i) =
      (v ((i : ℤ) + 1) + v ((i : ℤ) - 1) - 2 * cos (q * (2 * π / N)) * v i) * kG q N ((j : ℤ) - i) /
        (2 * sin (q * (2 * π / N)) * sin (q * π)) := fun i _ => by unfold coef; ring
  rw [Finset.sum_congr rfl hcoef, ← Finset.sum_div, hsum, hsingle, kL_zero hN, mul_div_assoc, div_self hden.ne',
    mul_one]

theorem node_identity_le {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) {j : ℕ} (hj : j ≤ N) :
    ∑ i ∈ Finset.range N, coef q N v i * kG q N ((j : ℤ) - i) = v j := by
  rcases lt_or_eq_of_le hj with hlt | heq
  · exact node_identity hq0 hq1 hN hper hlt
  · rw [heq]
    have h0 := node_identity hq0 hq1 hN hper (j := 0) (by omega)
    simp only [Nat.cast_zero] at h0
    have hvN : v (N : ℤ) = v 0 := by simpa using hper 0
    rw [hvN, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← kG_periodic (q := q) (N := N) (by omega) (0 - (i : ℤ))]
    congr 2; ring

/-! ## C23a: the interpolant on a cell -/

theorem trig_interp (D H u : ℝ) : cos D * sin (H - u) + cos (D + H) * sin u = sin H * cos (D + u) := by
  rw [sin_sub, cos_add, cos_add]; ring

/-- On a cell where `K(· - c) = cos(q(· - c + s))`, `K(θ - c)` is the q-sinusoid through its end values. -/
theorem kern_cell_interp {q a hh c s θ : ℝ} (hcos : ∀ y ∈ Icc a (a + hh), kern q (y - c) = cos (q * (y - c + s)))
    (hθ : θ ∈ Icc a (a + hh)) (hh0 : 0 ≤ hh) :
    sin (q * hh) * kern q (θ - c) = kern q (a - c) * sin (q * (a + hh - θ)) + kern q (a + hh - c) * sin (q * (θ - a)) := by
  rw [hcos θ hθ, hcos a ⟨le_rfl, by linarith⟩, hcos (a + hh) ⟨by linarith, le_rfl⟩]
  have h := trig_interp (q * (a - c + s)) (q * hh) (q * (θ - a))
  rw [show q * (a + hh - θ) = q * hh - q * (θ - a) by ring, show q * (a + hh - c + s) = q * (a - c + s) + q * hh by ring,
    show q * (θ - c + s) = q * (a - c + s) + q * (θ - a) by ring]
  linarith

/-- On cell `j`, each kernel `K(· - i h)` (`0 ≤ i < N`) is one q-sinusoid (shift `s = 0` if `i ≤ j`, else `2π`). -/
theorem kern_cell_cos (q : ℝ) {N : ℕ} (hN : 0 < N) {i j : ℕ} (hi : i < N) (hj : j < N) :
    ∃ s : ℝ, ∀ y ∈ Icc (-π + (j : ℝ) * (2 * π / N)) (-π + (j : ℝ) * (2 * π / N) + 2 * π / N),
      kern q (y - (i : ℝ) * (2 * π / N)) = cos (q * (y - (i : ℝ) * (2 * π / N) + s)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNr
  have hNh := N_mul_h hN
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hi
  have hj' : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hj
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  by_cases hij : i ≤ j
  · have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    refine ⟨0, fun y hy => ?_⟩
    rw [add_zero]
    apply kern_eq
    have a1 := mul_le_mul_of_nonneg_right hij' hh.le
    have a2 := mul_le_mul_of_nonneg_right hj' hh.le
    have a3 := mul_nonneg hi0 hh.le
    constructor <;> linarith [hy.1, hy.2]
  · have hji : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    refine ⟨2 * π, fun y hy => ?_⟩
    rw [← kern_periodic q (y - (i : ℝ) * (2 * π / N))]
    apply kern_eq
    have a1 := mul_le_mul_of_nonneg_right hji hh.le
    have a2 := mul_le_mul_of_nonneg_right hi' hh.le
    have a3 := mul_nonneg hj0 hh.le
    constructor <;> linarith [hy.1, hy.2]

theorem exists_cell {N : ℕ} (hN : 0 < N) {θ : ℝ} (hθ : θ ∈ Ico (-π) π) :
    ∃ j : ℕ, j < N ∧ -π + (j : ℝ) * (2 * π / N) ≤ θ ∧ θ < -π + (j : ℝ) * (2 * π / N) + 2 * π / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNr
  have hNh := N_mul_h hN
  have hx0 : 0 ≤ (θ + π) / (2 * π / N) := div_nonneg (by linarith [hθ.1]) hh.le
  have hxN : (θ + π) / (2 * π / N) < N := by rw [div_lt_iff₀ hh]; linarith [hθ.2]
  refine ⟨⌊(θ + π) / (2 * π / N)⌋₊, (Nat.floor_lt hx0).2 hxN, ?_, ?_⟩
  · have h := (le_div_iff₀ hh).1 (Nat.floor_le hx0); linarith
  · have h := (div_lt_iff₀ hh).1 (Nat.lt_floor_add_one ((θ + π) / (2 * π / N))); linarith

theorem interp_cell {q : ℝ} {N : ℕ} (v : ℤ → ℝ) {j : ℕ} {θ : ℝ} (hN : 0 < N)
    (h1 : -π + (j : ℝ) * (2 * π / N) ≤ θ) (h2 : θ < -π + (j : ℝ) * (2 * π / N) + 2 * π / N) :
    interp q N v θ = (v j * sin (q * (-π + (j : ℝ) * (2 * π / N) + 2 * π / N - θ)) +
      v (j + 1) * sin (q * (θ - (-π + (j : ℝ) * (2 * π / N))))) / sin (q * (2 * π / N)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 2 * π / N := div_pos two_pi_pos hNr
  have hfl : ⌊(θ + π) / (2 * π / N)⌋ = (j : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; constructor
    · rw [le_div_iff₀ hh]; linarith
    · rw [div_lt_iff₀ hh]; linarith
  simp only [interp, hfl, Int.cast_natCast]

theorem interp_periodic {q : ℝ} {N : ℕ} (hN : 0 < N) {v : ℤ → ℝ} (hper : ∀ i : ℤ, v (i + N) = v i) :
    Function.Periodic (interp q N v) (2 * π) := by
  intro t
  have hNh := N_mul_h hN
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hfl : ⌊(t + 2 * π + π) / (2 * π / N)⌋ = ⌊(t + π) / (2 * π / N)⌋ + N := by
    rw [← Int.floor_add_intCast]
    congr 1
    push_cast
    field_simp
    ring
  simp only [interp, hfl]
  generalize ⌊(t + π) / (2 * π / N)⌋ = J
  have e : ((J + N : ℤ) : ℝ) * (2 * π / N) = (J : ℝ) * (2 * π / N) + 2 * π := by
    push_cast; linear_combination hNh
  rw [e, show J + (N : ℤ) + 1 = (J + 1) + N by ring, hper, hper]
  ring_nf

theorem interp_eq_sum_Ico {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) {θ : ℝ} (hθ : θ ∈ Ico (-π) π) :
    interp q N v θ = ∑ i ∈ Finset.range N, coef q N v i * kern q (θ - (i : ℝ) * (2 * π / N)) := by
  have hN0 : 0 < N := by omega
  obtain ⟨j, hj, h1, h2⟩ := exists_cell hN0 hθ
  have hS := sin_qh_pos hq0 hq1 hN
  rw [interp_cell v hN0 h1 h2, div_eq_iff hS.ne', Finset.sum_mul]
  have hterm : ∀ i ∈ Finset.range N, coef q N v i * kern q (θ - (i : ℝ) * (2 * π / N)) * sin (q * (2 * π / N)) =
      coef q N v i * kG q N ((j : ℤ) - i) * sin (q * (-π + (j : ℝ) * (2 * π / N) + 2 * π / N - θ)) +
      coef q N v i * kG q N ((j : ℤ) + 1 - i) * sin (q * (θ - (-π + (j : ℝ) * (2 * π / N)))) := by
    intro i hi
    obtain ⟨s, hs⟩ := kern_cell_cos q hN0 (Finset.mem_range.1 hi) hj
    have key := kern_cell_interp hs ⟨h1, h2.le⟩ (div_pos two_pi_pos (by exact_mod_cast hN0)).le
    have e1 : kern q (-π + (j : ℝ) * (2 * π / N) - (i : ℝ) * (2 * π / N)) = kG q N ((j : ℤ) - i) := by
      unfold kG; congr 1; push_cast; ring
    have e2 : kern q (-π + (j : ℝ) * (2 * π / N) + 2 * π / N - (i : ℝ) * (2 * π / N)) = kG q N ((j : ℤ) + 1 - i) := by
      unfold kG; congr 1; push_cast; ring
    rw [e1, e2] at key
    linear_combination coef q N v i * key
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    node_identity_le hq0 hq1 hN hper hj.le]
  have h := node_identity_le hq0 hq1 hN hper (j := j + 1) (by omega)
  push_cast at h
  rw [h]

theorem interp_eq_sum {q : ℝ} {N : ℕ} (hq0 : 0 < q) (hq1 : q < 1) (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
    interp q N v θ = ∑ i ∈ Finset.range N, coef q N v i * kern q (θ - (i : ℝ) * (2 * π / N)) := by
  rcases lt_or_eq_of_le hθ.2 with hlt | heq
  · exact interp_eq_sum_Ico hq0 hq1 hN hper ⟨hθ.1.le, hlt⟩
  · subst heq
    have h := interp_eq_sum_Ico hq0 hq1 hN hper (θ := -π) ⟨le_rfl, by linarith [pi_pos]⟩
    have hp : interp q N v π = interp q N v (-π) := by
      have h' := interp_periodic (q := q) (by omega) hper (-π)
      rwa [show -π + 2 * π = π by ring] at h'
    rw [hp, h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hk := kern_periodic q (-π - (i : ℝ) * (2 * π / N))
    rw [show -π - (i : ℝ) * (2 * π / N) + 2 * π = π - (i : ℝ) * (2 * π / N) by ring] at hk
    rw [hk]

/-! ## C23a: subharmonicity -/

/-- For a continuous real `f`, the (truncated) `IsSubharmonic` gives the plain sub-mean-value inequality. -/
theorem submean_of_subharmonic {f : ℂ → ℝ} (hf : Continuous f) (hs : IsSubharmonic (fun z => ((f z : ℝ) : EReal)))
    (c : ℂ) {r : ℝ} (hr : 0 < r) : f c ≤ circleAverage f c r := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hf.continuousOn
  have hlow : ∀ z ∈ closedBall c r, -(⌈M⌉₊ : ℝ) ≤ f z := fun z hz => by
    have h1 := hM z hz
    rw [Real.norm_eq_abs] at h1
    linarith [neg_abs_le (f z), Nat.le_ceil M]
  have hsph : sphere c |r| ⊆ closedBall c r := by rw [abs_of_pos hr]; exact sphere_subset_closedBall
  have h := hs.2.2 ⌈M⌉₊ c r hr
  rw [FailCole.trunc_coe, max_eq_left (hlow c (mem_closedBall_self hr.le))] at h
  rwa [circleAverage_congr_sphere (f₂ := f) (fun z hz => by
    show trunc ⌈M⌉₊ ((f z : ℝ) : EReal) = f z
    rw [FailCole.trunc_coe]
    exact max_eq_left (hlow z (hsph hz)))] at h

/-- A continuous real `f` with the sub-mean-value inequality on every circle is subharmonic. -/
theorem subharmonic_of_submean {f : ℂ → ℝ} (hf : Continuous f)
    (hs : ∀ (c : ℂ) (r : ℝ), 0 < r → f c ≤ circleAverage f c r) : IsSubharmonic (fun z => ((f z : ℝ) : EReal)) := by
  refine ⟨fun _ => EReal.coe_ne_top _, (continuous_coe_real_ereal.comp hf).upperSemicontinuous, fun n c r hr => ?_⟩
  simp only [FailCole.trunc_coe]
  have hmint : CircleIntegrable (fun z => max (f z) (-(n : ℝ))) c r :=
    (hf.max continuous_const).continuousOn.circleIntegrable'
  have hfint : CircleIntegrable f c r := hf.continuousOn.circleIntegrable'
  refine max_le ((hs c r hr).trans (circleAverage_mono hfint hmint fun z _ => le_max_left _ _)) ?_
  have h := circleAverage_mono (circleIntegrable_const (-(n : ℝ)) c r) hmint (fun z _ => le_max_right (f z) _)
  rwa [circleAverage_const] at h

/-- A nonnegative combination of continuous functions with the sub-mean-value inequality has it too. -/
theorem submean_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (K : ι → ℂ → ℝ)
    (hc : ∀ i, Continuous (K i)) (hs : ∀ i (c : ℂ) (r : ℝ), 0 < r → K i c ≤ circleAverage (K i) c r)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∑ i ∈ s, a i * K i c ≤ circleAverage (fun z => ∑ i ∈ s, a i * K i z) c r := by
  have hint : ∀ i ∈ s, CircleIntegrable (fun z => a i * K i z) c r := fun i _ =>
    (continuous_const.mul (hc i)).continuousOn.circleIntegrable'
  rw [circleAverage_fun_sum hint]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : circleAverage (fun z => a i * K i z) c r = a i * circleAverage (K i) c r := by
    simpa only [smul_eq_mul] using
      (circleAverage_fun_smul : circleAverage (fun z => a i • K i z) c r = a i • circleAverage (K i) c r)
  rw [h1]
  exact mul_le_mul_of_nonneg_left (hs i c r hr) (ha i hi)

/-- Circle averages are invariant under rotation: `avg_{c,r} f(· e^{ix}) = avg_{c e^{ix}, r} f`. -/
theorem circleAverage_rotate (f : ℂ → ℝ) (x : ℝ) (c : ℂ) (r : ℝ) :
    circleAverage (fun z => f (z * Complex.exp ((x : ℂ) * Complex.I))) c r =
      circleAverage f (c * Complex.exp ((x : ℂ) * Complex.I)) r := by
  rw [circleAverage_def, circleAverage_eq_integral_add x]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show f (circleMap c r θ * Complex.exp ((x : ℂ) * Complex.I)) =
    f (circleMap (c * Complex.exp ((x : ℂ) * Complex.I)) r (θ + x))
  congr 1
  simp only [circleMap]
  rw [show (((θ + x : ℝ) : ℂ)) * Complex.I = (θ : ℂ) * Complex.I + (x : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add]
  ring

theorem arg_mul_exp {ζ : ℂ} (hζ : ζ ≠ 0) (x : ℝ) :
    Complex.arg (ζ * Complex.exp ((x : ℂ) * Complex.I)) = toIocMod two_pi_pos (-π) (Complex.arg ζ + x) := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
  rw [mul_assoc, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, Complex.arg_real_mul _ hn,
    Complex.arg_exp_mul_I]

/-- The rotated kernel on ℂ: `U(ζ e^{-i·ih})` with `U = ThmBIf.Ufun (2q) = |ζ|^q tanϑ cos(q arg ζ)`. -/
noncomputable def kernC (q : ℝ) (N : ℕ) (i : ℕ) (ζ : ℂ) : ℝ :=
  ThmBIf.Ufun (2 * q) (ζ * Complex.exp (((-((i : ℝ) * (2 * π / N)) : ℝ) : ℂ) * Complex.I))

theorem kernC_eq {q : ℝ} {N : ℕ} (hq : 0 < q) (i : ℕ) (ζ : ℂ) :
    kernC q N i ζ = tan (π / (2 * (2 * q))) * (‖ζ‖ ^ q * kern q (Complex.arg ζ - (i : ℝ) * (2 * π / N))) := by
  unfold kernC ThmBIf.Ufun ee kern
  rw [show 2 * q / 2 = q by ring]
  by_cases hζ : ζ = 0
  · subst hζ; simp [zero_rpow hq.ne']
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, arg_mul_exp hζ, ← sub_eq_add_neg]
    ring

/-- **C23a** (paper l.646-650): the interpolant of `N`-periodic node values with the discrete inequality, by solutions of
`φ'' + q²φ = 0` on each cell, is q-subtrigonometric. -/
theorem interp_qsubtrig {q : ℝ} (hq0 : 1 / 2 < q) (hq1 : q < 1) {N : ℕ} (hN : 2 ≤ N) {v : ℤ → ℝ}
    (hper : ∀ i : ℤ, v (i + N) = v i) (hdisc : ∀ i : ℤ, 2 * cos (q * (2 * π / N)) * v i ≤ v (i + 1) + v (i - 1)) :
    QSubtrig q (interp q N v) := by
  have hq : 0 < q := by linarith
  have hp1 : 1 < 2 * q := by linarith
  have hp2 : 2 * q < 2 := by linarith
  have hT : 0 < tan (π / (2 * (2 * q))) := ThmBIf.tan_th_pos hp1 hp2
  refine ⟨interp_periodic (by omega) hper, ?_⟩
  have hsum : ∀ ζ : ℂ, ‖ζ‖ ^ q * interp q N v (Complex.arg ζ) =
      ∑ i ∈ Finset.range N, coef q N v i / tan (π / (2 * (2 * q))) * kernC q N i ζ := fun ζ => by
    rw [interp_eq_sum hq hq1 hN hper (Complex.arg_mem_Ioc ζ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [kernC_eq hq i ζ, div_mul_eq_mul_div, eq_div_iff hT.ne']
    ring
  have hKc : ∀ i : ℕ, Continuous (kernC q N i) := fun i => by
    unfold kernC
    exact (ThmBIf.Ufun_continuous hp1 hp2).comp (continuous_id.mul continuous_const)
  have hU : ∀ (c : ℂ) (r : ℝ), 0 < r → ThmBIf.Ufun (2 * q) c ≤ circleAverage (ThmBIf.Ufun (2 * q)) c r :=
    fun c r hr => submean_of_subharmonic (ThmBIf.Ufun_continuous hp1 hp2) (LocGlob.Ufun_subharmonic hp1 hp2) c hr
  have hKs : ∀ (i : ℕ) (c : ℂ) (r : ℝ), 0 < r → kernC q N i c ≤ circleAverage (kernC q N i) c r := by
    intro i c r hr
    have h1 := hU (c * Complex.exp (((-((i : ℝ) * (2 * π / N)) : ℝ) : ℂ) * Complex.I)) r hr
    rw [← circleAverage_rotate] at h1
    exact h1
  have ha : ∀ i ∈ Finset.range N, 0 ≤ coef q N v i / tan (π / (2 * (2 * q))) := fun i _ =>
    div_nonneg (div_nonneg (by linarith [hdisc i]) (den_pos hq hq1 hN).le) hT.le
  have hfun : (fun ζ : ℂ => ‖ζ‖ ^ q * interp q N v (Complex.arg ζ)) =
      fun ζ => ∑ i ∈ Finset.range N, coef q N v i / tan (π / (2 * (2 * q))) * kernC q N i ζ := funext hsum
  show IsSubharmonic (fun ζ : ℂ => (((fun ζ : ℂ => ‖ζ‖ ^ q * interp q N v (Complex.arg ζ)) ζ : ℝ) : EReal))
  rw [hfun]
  exact subharmonic_of_submean (continuous_finsetSum _ fun i _ => continuous_const.mul (hKc i))
    (fun c r hr => submean_sum (Finset.range N) _ ha _ hKc hKs c hr)

end Relax

end P18
