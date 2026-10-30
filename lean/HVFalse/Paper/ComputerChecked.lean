/-
  HVFalse/Paper/ComputerChecked.lean - the claims of the paper that rest on large computer certificates, STATED, NOT PROVED
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Each `def` below is the EXACT Lean statement of one paper claim (type-checked by Lean), kept as a proposition instead of a
  theorem with a proof hole, so that the proved part of the project has no proof hole at all. scripts/audit.py lists every `def` here
  as NOT PROVED (computer-checked), except C13b and C13m_hand_step, which are now PROVED (rows `X_proved : X` in
  Statements.lean). Groups: (c1) Prop. 8 explicit counterexample: C13b (`z, w ∈ H^p`; PROVED), C13c (the integral;
  computer), C13m (f violates (HV); PROVED GIVEN C13c) and C13m_hand_step (C13b, C13c -> C13m; PROVED); (c2) C19b (holds side of Prop. 10, 6 values of p);
  (c3) C20a (Prop. 11, 140 cells); (c4) C21 (Prop. 13, 115 cells); (c5) C29c (Introduction, rests on the box part of (c2)). Logs: logs/ of the release folder.
  To prove one later: `theorem X_proved : X := ...` in a proof file, and move the row back to Statements.lean.
-/
import HVFalse.Defs.Basic
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV
import HVFalse.Defs.HVLp
import HVFalse.Defs.Explicit
import HVFalse.Defs.Cells

open Real Set

namespace P18.Paper

/-- The boundary value `θ ↦ F(e^{iθ})` of a function on the disc, as a function on `T = ℝ/2πℤ`. -/
noncomputable def onT (F : ℂ → ℂ) : Circ → ℂ := fun x => F (AddCircle.toCircle x)

/-- C13b, Prop. 8 (l.449-450; proof l.471-473, "we have `z, w ∈ H^p` for every `δ ∈ (0, 2π)`"): `z, w ∈ H^p`
(`p = 3/2`). A hand proof in the paper; PROVED in Lean for every `δ ∈ (0, 2π)`: row C13b_explicit_hardy_proved
(HVFalse/Proofs/HardyBound.lean). -/
def C13b_explicit_hardy : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 2 * π →
    Explicit.InHardy (3 / 2) (Explicit.zf δ) ∧ Explicit.InHardy (3 / 2) (Explicit.wf δ)

/-- C13c, Prop. 8 (l.451-454): `∫_T G(z,w) dθ/2π ∈ -1.391990813 + [-2.6·10⁻¹⁰, 2.6·10⁻¹⁰]` (boundary values = the
formulas at `ζ = e^{iθ}`; they are the radial limits off three points). -/
def C13c_explicit_integral : Prop :=
    |1 / (2 * π) * (∫ θ in (0 : ℝ)..(2 * π), G (3 / 2) (398 / 100)
        (Explicit.zf (exp (-2500)) (Complex.exp ((θ : ℂ) * Complex.I)))
        (Explicit.wf (exp (-2500)) (Complex.exp ((θ : ℂ) * Complex.I)))) - (-1391990813 / 10 ^ 9)| ≤ 26 / 10 ^ 11

/-- C13m, Prop. 8 (l.454, "so `f` violates (HV) with `C = C_HV` at `(p,s)`"; Introduction l.114-115): `f = z + w̄`
(boundary values on `T`, `δ = e^{-2500}`) is in `L^p`, `P₊f = z`, `P₋f = w̄` (Fourier coefficients), and (HV) with
`C = C_HV` FAILS for it at `(p, s) = (3/2, 3.98)`. NOT proved in Lean by itself; PROVED GIVEN C13c, a computer
certificate (row C13m_given_C13c: C13b and the hand step are proved); the step to "(HV) fails" is the PROVED row C13n. -/
def C13m_explicit_violates : Prop :=
  ∃ f g h : LpT (3 / 2),
    (f : Circ → ℂ) =ᵐ[MeasureTheory.volume]
        onT (fun ζ => Explicit.zf (exp (-2500)) ζ + (starRingEnd ℂ) (Explicit.wf (exp (-2500)) ζ)) ∧
    (g : Circ → ℂ) =ᵐ[MeasureTheory.volume] onT (Explicit.zf (exp (-2500))) ∧
    (h : Circ → ℂ) =ᵐ[MeasureTheory.volume] onT (fun ζ => (starRingEnd ℂ) (Explicit.wf (exp (-2500)) ζ)) ∧
    (∀ n : ℤ, fourierCoeff (⇑g) n = if 0 ≤ n then fourierCoeff (⇑f) n else 0) ∧
    (∀ n : ℤ, fourierCoeff (⇑h) n = if n < 0 then fourierCoeff (⇑f) n else 0) ∧
    ¬ (MeasureTheory.eLpNorm (fun x => (‖g x‖ ^ (398 / 100 : ℝ) + ‖h x‖ ^ (398 / 100 : ℝ)) ^ (1 / (398 / 100 : ℝ)))
          (ENNReal.ofReal (3 / 2)) MeasureTheory.volume
        ≤ ENNReal.ofReal (hvConst (3 / 2) (398 / 100)) * MeasureTheory.eLpNorm f (ENNReal.ofReal (3 / 2)) MeasureTheory.volume)

/-- C13m_hand_step, Prop. 8 proof (l.473-474): "Thus `f ∈ L^p(T)`. Since `w(0) = 0`, the Fourier coefficients of `z`
vanish for `n < 0` and those of `w̄` for `n ≥ 0`, so that `P₊f = z`, `P₋f = w̄` and, as in Section 2, `f` violates (HV)
... if and only if `∫_T G(z,w) dθ/2π < 0`": the hand step from C13b and C13c to C13m. A hand step in the paper; PROVED in Lean:
row C13m_hand_step_proved (HVFalse/Proofs/HandStep.lean). -/
def C13m_hand_step : Prop := C13b_explicit_hardy → C13c_explicit_integral → C13m_explicit_violates

/-- C19b, Prop. 10 (l.546-548, the `s₋` side): (HV) holds for `0 < s ≤ s₋(p)` at the six `(p, s₋)` of the table. -/
def C19b_bracket_holds : Prop :=
    ∀ r ∈ ([(7 / 5, 52986 / 10000), (3 / 2, 39572 / 10000), (8 / 5, 31799 / 10000), (17 / 10, 26921 / 10000),
            (9 / 5, 23764 / 10000), (19 / 10, 21588 / 10000)] : List (ℝ × ℝ)),
      ∀ s : ℝ, 0 < s → s ≤ r.2 → HVIneqLp r.1 s (hvConst r.1 s)

/-- C20a, Prop. 11 (l.576-581): for each of the 140 cells there is a rational `s_cell` with `s_cell ≤ L(p_b) < s_cell + 2·10⁻⁶`
such that (HV) holds for every `p` of the cell and every `s ∈ (0, s_cell]` (the part `s_cell > p_a/(p_a-1)` is the
proved row C20e; the whole statement: row C20a_full_given_cells). -/
def C20a_cells : Prop :=
    ∀ i : ℕ, i < 140 → ∃ sc : ℚ, cellLevel i - (sc : ℝ) < 2 / 10 ^ 6 ∧ (sc : ℝ) ≤ cellLevel i ∧
      ∀ p ∈ Icc (cellLeft i) (cellRight i), ∀ s : ℝ, 0 < s → s ≤ sc → HVIneqLp p s (hvConst p s)

/-- C21, Prop. 13 (l.600-604): on each of the 115 cells inside `[997/684, 1.99]` (cell `j + 25`, `j = 0..114`) (HV) fails for
every `p` of the cell and every `s ∈ [sec²(π/2p) - Δ_cell, sec²(π/2p)]`, with the certified `Δ_cell = falseWidth j` (exact
rationals of the Arb log; one `δ` for all cells would say much less). -/
def C21_false_width : Prop :=
    ∀ j : Fin 115, ∀ p ∈ Icc (cellLeft ((j : ℕ) + 25)) (cellRight ((j : ℕ) + 25)),
      ∀ s ∈ Icc (Ssec p - (falseWidth j : ℝ)) (Ssec p), ¬ HVIneqLp p s (hvConst p s)


/-! ## The box parts: the instances of (eq:two), or of its failure, that the computer certificates establish
(these are (eq:two) ITSELF at the certified values, not the certificates' box bounds; the box bounds, the short
arguments (i)-(iii) of the certificate (paper l.527-543) and `L(p) < sec²` on each cell (l.586) are not in Lean). The step from each box
statement to the paper's claim is PROVED in Statements.lean (C19b_reduction, C20a_reduction, C21_reduction). -/

/-- (c2) box part of C19b: the two-variable inequality (eq:two) at the six `(p, s₋)` of the table of Prop. 10 (established by the Arb
and mpmath certificates of logs/bracket_lower_arb.log). -/
def C19b_boxes : Prop :=
  ∀ r ∈ ([(7 / 5, 52986 / 10000), (3 / 2, 39572 / 10000), (8 / 5, 31799 / 10000), (17 / 10, 26921 / 10000),
          (9 / 5, 23764 / 10000), (19 / 10, 21588 / 10000)] : List (ℝ × ℝ)), TwoVar r.1 r.2

/-- (c3) box part of C20a: for each of the 140 cells a rational `s_cell` with the level conditions and (eq:two) at
`s = s_cell` for every `p` of the cell (logs/cells_arb.log). -/
def C20a_boxes : Prop :=
  ∀ i : ℕ, i < 140 → ∃ sc : ℚ, cellLevel i - (sc : ℝ) < 2 / 10 ^ 6 ∧ (sc : ℝ) ≤ cellLevel i ∧
    ∀ p ∈ Icc (cellLeft i) (cellRight i), TwoVar p sc

/-- (c4) box part of C21: for each of the 115 cells and every `p` of the cell, a failure point of (eq:two) at
`s = sec²(π/2p) - Δ_cell` (logs/false_cells_arb.log: one rational point per sub-cell). -/
def C21_boxes : Prop :=
  ∀ j : Fin 115, ∀ p ∈ Icc (cellLeft ((j : ℕ) + 25)) (cellRight ((j : ℕ) + 25)),
    ∃ y t : ℝ, t ∈ Icc (-π) π ∧ Gam p (Ssec p - (falseWidth j : ℝ)) y t < ee p t

/-- C29c, Introduction (l.110-111): "The part of the open window where the conjecture fails is under 1% of its length at
`p=7/5` and about 31% at `p=19/10`" (the part is `(s₀, sec²ϑ)`; it needs `s₀ ≥ s₋`, i.e. the computer side of Prop. 10;
its reduction to `C19b_boxes` is the PROVED row C29c_reduction). -/
def C29c_window_fail_part : Prop :=
  (∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar (7 / 5) s ↔ s ≤ s0)) →
      (Ssec (7 / 5) - s0) / (Ssec (7 / 5) - (7 / 5) / (7 / 5 - 1)) < 1 / 100) ∧
    (∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar (19 / 10) s ↔ s ≤ s0)) →
      |(Ssec (19 / 10) - s0) / (Ssec (19 / 10) - (19 / 10) / (19 / 10 - 1)) - 31 / 100| ≤ 1 / 100)

/-- C19d, Prop. 10 (l.545-546): "For the six values of `p` below, `s₋(p) ≤ s₀(p) < s₊(p)`" (`s₀` the threshold of (eq:two);
the `s₋` side is the computer side; reduction to `C19b_boxes`: the PROVED row C19d_reduction). -/
def C19d_bracket_s0 : Prop :=
  ∀ r ∈ ([(7/5, 52986/10000, 52989/10000), (3/2, 39572/10000, 39575/10000),
      (8/5, 31799/10000, 31802/10000), (17/10, 26921/10000, 26925/10000), (9/5, 23764/10000, 23767/10000),
      (19/10, 21588/10000, 21591/10000)] : List (ℝ × ℝ × ℝ)),
    ∀ s0 : ℝ, (∀ s : ℝ, 0 < s → (TwoVar r.1 s ↔ s ≤ s0)) → r.2.1 ≤ s0 ∧ s0 < r.2.2

/-- C30f, Prop. 11 (statement l.577, `s_cell > p/(p-1)` on the whole cell; proof l.586: "Therefore (eq:two) holds at
`s = s_cell` for every `p` of the cell"): on every cell (eq:two) holds for some `s > p/(p-1)` (reduction to `C20a_boxes`:
the PROVED row C30f_reduction). -/
def C30f_beyond_jag : Prop :=
  ∀ i : ℕ, i < 140 → ∀ p ∈ Set.Icc (cellLeft i) (cellRight i), ∃ s : ℝ, p / (p - 1) < s ∧ TwoVar p s

end P18.Paper
