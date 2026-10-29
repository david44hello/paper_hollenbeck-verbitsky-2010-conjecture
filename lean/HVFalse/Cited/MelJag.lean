/-
  HVFalse/Cited/MelJag.lean - results of Melentijević [Mel2023] and Jaguzović [Jag2026], as axioms
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Sources (open, arXiv v2 = latest): Melentijević arXiv:2203.14364v2 (= Math. Ann. 388 (2024) 4405-4448); Jaguzović
  arXiv:2408.17093v2 (= Izv. Math. 90 (2026), no. 4, 796-812, DOI 10.4213/im9742e). STATUS: both REFEREED (journals
  2024 and 2026; journal records checked 20261027 on Springer and mathnet.ru). Each axiom's docstring quotes its source verbatim.
  The L^p inequalities are stated here only for trigonometric polynomials (`HVIneq`): a special case, so weaker than the source.
-/
import Mathlib
import HVFalse.Defs.Basic
import HVFalse.Defs.Saddle
import HVFalse.Defs.HV

open Real

namespace P18.Cited

/-- [Mel2023, Section 8 "Proof of the Lemma 1 for s = sec²(π/2p) and 1 < p ≤ 4/3", (37), arXiv pp. 22-23], VERBATIM: "Our main
inequality is Φ(y,t) = −cosh^{p/s}(sy/2) + (cosh y + cos t)^{p/2}/(1 + cos(π/p))^{p/2} − tan(π/2p) cos(tp/2) ≥ 0, (37) for y ≥ 0
and t ∈ [0, π]", with s = sec²(π/2p). -/
axiom mel_eq37 (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 4 / 3) (y t : ℝ) (hy : 0 ≤ y) (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    0 ≤ -(cosh (Ssec p * y / 2) ^ (p / Ssec p)) + (cosh y + cos t) ^ (p / 2) / (1 + cos (π / p)) ^ (p / 2)
      - tan (π / (2 * p)) * cos (t * p / 2)

/-- [Jag2026, Section 2 "Proof of the Theorem 1", (2), arXiv pp. 3-4], at s = p/(p−1), VERBATIM: "it is enough to prove
Φ(r,t) = −((1 + r^s)/2)^{p/s} + (1 + r² + 2r cos t)^{p/2}/(2^p cos^p(π/2p)) − r^{p/2} tan(π/2p) cos(tp/2) ≥ 0, (2) for
0 ≤ r ≤ 1, −π ≤ t ≤ π." — proved there (the edge t = 0 by Jaguzović, the rest cited from [10, Subsection 4.1] =
Melentijević–Marković 2023), "z ∈ C, w ∈ C, p ∈ (4/3, 2), s = p/(p−1)". -/
axiom jag_eq2 (p : ℝ) (hp1 : 4 / 3 < p) (hp2 : p < 2) (r t : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ht0 : -π ≤ t) (ht1 : t ≤ π) :
    0 ≤ -(((1 + r ^ (p / (p - 1))) / 2) ^ (p / (p / (p - 1))))
      + (1 + r ^ 2 + 2 * r * cos t) ^ (p / 2) / (2 ^ p * cos (π / (2 * p)) ^ p)
      - r ^ (p / 2) * tan (π / (2 * p)) * cos (t * p / 2)

end P18.Cited
