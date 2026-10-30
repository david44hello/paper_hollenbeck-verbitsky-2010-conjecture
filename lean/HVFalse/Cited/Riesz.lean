/-
  HVFalse/Cited/Riesz.lean - the Hollenbeck-Verbitsky (2000) bound for the Riesz projections, as an axiom
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Used for the step from trigonometric polynomials to all of L^p(T) (paper l.181, "by density and M. Riesz's theorem"): it
  makes P₊, P₋ continuous on the dense class, so (eq:HV) passes to the limit; and for C* < ∞ in Prop. 14 (l.631, "by
  M. Riesz's theorem"). The paper cites [HV2000] for this bound (l.58); for 1 < p ≤ 2 it implies M. Riesz's theorem. STATUS: REFEREED ([HV2000] J. Funct. Anal. 175 (2000), no. 2,
  370-392; [Mel2023] Math. Ann. 388 (2024), DOI 10.1007/s00208-023-02639-1).
-/
import Mathlib
import HVFalse.Defs.HV

open Real

namespace P18.Cited

/-- [Mel2023, p. 2, (1)-(2)] (arXiv:2203.14364v2; cited by the paper), quoting [HV2000] (B. Hollenbeck and I. E. Verbitsky,
Best constants for the Riesz projection, J. Funct. Anal. 175 (2000), 370-392; cited by the paper, l.58), VERBATIM: "The Riesz
projection operator P+ : Lp(T) → Hp(T), and the co-analytic projection operator P− = I − P+ [...] are defined as
(1) P+ f(ζ) = Σ_{n=0}^{+∞} f̂(n)ζ^n and P− f(ζ) = Σ_{n=−∞}^{−1} f̂(n)ζ^n." and "In [16], Hollenbeck and Verbitsky proved
slightly stronger result than that stated in Gohberg - Krupnik conjecture: (2) ‖max{|P+(f)|, |P−(f)|}‖_{Lp(T)} ≤
(1/sin(π/p)) ‖f‖_{Lp(T)}, f ∈ Lp(T)." ([16] = [HV2000]; the same page: "This implies the result on the norm of the Riesz
projection on the circle for 1 < p ≤ 2".) Instance: f a trigonometric polynomial (`trig c`, with `Pplus`, `Pminus` the exact
finite sums), `1 < p ≤ 2`, both sides to the power `p`, the normalization dθ/2π dropped (it cancels). Restricted to
trigonometric polynomials, this is weaker than the source. -/
axiom hv2000_riesz (p : ℝ) (hp1 : 1 < p) (hp2 : p ≤ 2) (c : ℤ →₀ ℂ) :
    ∫ θ in (0 : ℝ)..(2 * π), (max ‖Pplus c θ‖ ‖Pminus c θ‖) ^ p
      ≤ (1 / sin (π / p)) ^ p * ∫ θ in (0 : ℝ)..(2 * π), ‖trig c θ‖ ^ p

end P18.Cited
