/-
  HVFalse/Defs/Cells.lean - the 140 cells of Prop. cells and the discrete relaxation of Sec. 7
  Copyright (C) Dave Goel 2026--now. All rights reserved.
-/
import Mathlib
import HVFalse.Defs.Basic
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV

open Real

namespace P18

/-- l.573-574: left end of cell `i` (0-based): 114 equal cells on `[4/3, 19/10]` (width 17/3420), 16 on `[19/10, 99/50]`
(width 1/200), 10 on `[99/50, 199/100]` (width 1/1000). -/
noncomputable def cellLeft (i : ℕ) : ℝ :=
  if i < 114 then 4 / 3 + (i : ℝ) * (17 / 3420)
  else if i < 130 then 19 / 10 + ((i - 114 : ℕ) : ℝ) * (1 / 200)
  else 99 / 50 + ((i - 130 : ℕ) : ℝ) * (1 / 1000)

/-- Right end of cell `i` = left end of cell `i + 1` (`cellLeft 140 = 199/100`). -/
noncomputable def cellRight (i : ℕ) : ℝ := cellLeft (i + 1)

/-- l.575-577: `κ = 9/10` on the first 52 cells (`[4/3, 1361/855]`), `4/5` on the next 24 (to `77/45`), `13/20` on the last 64. -/
noncomputable def cellKappa (i : ℕ) : ℝ := if i < 52 then 9 / 10 else if i < 76 then 4 / 5 else 13 / 20

/-- l.575: the target level of cell `i`: `p_b/(p_b-1) + κ (sec²(π/2p_b) - p_b/(p_b-1))` with `p_b = cellRight i`. -/
noncomputable def cellLevel (i : ℕ) : ℝ :=
  cellRight i / (cellRight i - 1) + cellKappa i * (Ssec (cellRight i) - cellRight i / (cellRight i - 1))

/-- Sec. 7, l.635 and l.646-650: the interpolant of `N`-periodic node values `v` (nodes `ν_j = -π + j Δt`, `Δt = 2π/N`; written `h` here) by solutions of
`φ'' + q²φ = 0` on each cell `[t_i, t_{i+1}]`. -/
noncomputable def interp (q : ℝ) (N : ℕ) (v : ℤ → ℝ) (t : ℝ) : ℝ :=
  let h := 2 * π / N
  let i := ⌊(t + π) / h⌋
  let ti := -π + (i : ℝ) * h
  (v i * sin (q * (ti + h - t)) + v (i + 1) * sin (q * (t - ti))) / sin (q * h)

/-- Sec. 7, l.634-637: the discrete problem on `N` nodes is feasible at `λ`: `N`-periodic node values with the discrete
inequality `v_{i+1} + v_{i-1} - 2 cos(qh) v_i ≥ 0` and `v_i ≤ m_λ(t_i)` (i.e. `≤ Γ_λ(y, t_i)` for every `y`). -/
def DiscFeasible (p s lam : ℝ) (N : ℕ) : Prop :=
  ∃ v : ℤ → ℝ, (∀ i : ℤ, v (i + N) = v i) ∧
    (∀ i : ℤ, 2 * cos (p / 2 * (2 * π / N)) * v i ≤ v (i + 1) + v (i - 1)) ∧
    ∀ (i : ℤ) (y : ℝ), v i ≤ GamLam p s lam y (-π + (i : ℝ) * (2 * π / N))

/-- l.599-602, Prop. 13: the certified false width `Δ_cell` of cell `j + 25` (`j = 0..114`), exact
rationals from the Arb log logs/false_cells_arb.log (lines "(2) FAILS at
s = sec^2(pi/2p) - Δ ... PROVED"), extracted by a script (not shipped). -/
def falseWidth : Fin 115 → ℚ := ![
    31 / 4000, 203 / 25000, 53 / 6250, 221 / 25000, 1837 / 100000, 381 / 20000, 1971 / 100000, 509 / 25000,
    2099 / 100000, 2161 / 100000, 111 / 5000, 1139 / 50000, 1167 / 50000, 597 / 25000, 3661 / 100000, 3737 / 100000,
    381 / 10000, 97 / 2500, 3947 / 100000, 4011 / 100000, 509 / 12500, 4131 / 100000, 2093 / 50000, 4239 / 100000,
    4289 / 100000, 867 / 20000, 4379 / 100000, 221 / 5000, 2229 / 50000, 2247 / 50000, 2263 / 50000, 1139 / 25000,
    2291 / 50000, 2303 / 50000, 5553 / 100000, 697 / 12500, 2797 / 50000, 561 / 10000, 2811 / 50000, 176 / 3125,
    2819 / 50000, 141 / 2500, 5637 / 100000, 563 / 10000, 5619 / 100000, 7 / 125, 2787 / 50000, 5541 / 100000,
    5501 / 100000, 341 / 6250, 1081 / 20000, 107 / 2000, 5289 / 100000, 209 / 4000, 1289 / 25000, 1271 / 25000,
    5009 / 100000, 493 / 10000, 4849 / 100000, 953 / 20000, 4679 / 100000, 4591 / 100000, 9 / 200, 551 / 12500,
    863 / 20000, 211 / 5000, 4123 / 100000, 2013 / 50000, 491 / 12500, 957 / 25000, 233 / 6250, 907 / 25000,
    1763 / 50000, 137 / 4000, 3323 / 100000, 161 / 5000, 1559 / 50000, 603 / 20000, 2913 / 100000, 281 / 10000,
    2707 / 100000, 521 / 20000, 1251 / 50000, 3 / 125, 1149 / 50000, 2197 / 100000, 131 / 6250, 399 / 20000,
    379 / 20000, 897 / 50000, 847 / 50000, 319 / 20000, 187 / 12500, 291 / 25000, 1083 / 100000, 501 / 50000,
    921 / 100000, 841 / 100000, 381 / 50000, 683 / 100000, 121 / 20000, 527 / 100000, 9 / 2000, 249 / 100000,
    99 / 50000, 339 / 100000, 321 / 100000, 151 / 50000, 71 / 25000, 133 / 50000, 31 / 12500, 23 / 10000,
    177 / 100000, 81 / 50000, 147 / 100000]

end P18
