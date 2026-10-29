/-
  HVFalse/Cited/MM2022.lean - the lower bound C_{s,p} ≥ C_HV of Melentijević-Marković [MM2022], as an axiom
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Source: P. Melentijević and M. Marković, Best constants in inequalities involving analytic and co-analytic projections and
  Riesz's theorem in various function spaces, Potential Anal. 59 (2023), no. 4, 1599-1620, DOI 10.1007/s11118-022-10021-0;
  STATUS: REFEREED (journal, 2023) (cited by the paper, l.71:
  "The lower bound C* ≥ C^HV is proved in [MM2022]"). Open version read: arXiv:1912.08944v4 (same title; the published PDF
  is paywalled and was not read). The quote below was read from the arXiv v4 page images.
-/
import Mathlib
import HVFalse.Defs.HV
import HVFalse.Defs.HVLp

open Real

namespace P18.Cited

/-- [MM2022, arXiv:1912.08944v4, p.2], VERBATIM: "Hollenbeck and Verbitsky [4] posed a problem to find the optimal constant
C_{s,p} for the inequality ‖(|P₊f|^s+|P₋f|^s)^{1/s}‖_{L^p(T)} ≤ C_{s,p}‖f‖_{L^p(T)}, f ∈ L^p(T), 1<p<∞, 0<s<∞." and
[ibid., §2 "Lower estimates of the constants C_{s,p}", p.4], VERBATIM: "In this section we estimate from below for constants
C_{s,p} for 0<s<∞ and 1<p<∞. [...] Since, for 1<p≤2 we have √(1+t²−2t cos(π/p)) ≥ √(1+t²+2t cos(π/p)), we may conclude
C_{s,p} ≥ sup_{t∈[0,1]} (1+t^s)^{1/s} / √(1+t²+2t cos(π/p))." (P₊ = Σ_{n≥0}, P₋ = I − P₊, complex scalars: p.1-2.)
Instance: t = 1, where the bound is 2^{1/s}/√(2+2cos(π/p)) = 2^{1/s}/(2cos(π/2p)) = `hvConst p s`; 1 < p < 2, every s > 0.
Any constant `C` for which the inequality holds on all of L^p (`HVIneqLp p s C`) is ≥ the optimal C_{s,p} ≥ that bound. -/
axiom mm2022_lower_bound (p s : ℝ) (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (C : ℝ) (hC : 0 < C)
    (hHV : HVIneqLp p s C) : hvConst p s ≤ C

end P18.Cited
