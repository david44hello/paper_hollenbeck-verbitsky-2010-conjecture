/-
  HVFalse/Cited/HKV21.lean - Cole's theorem [HKV2003, Thm 2.1] alone (no p.244 Remark), as an axiom
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Source: B. Hollenbeck, N. J. Kalton and I. E. Verbitsky, Best constants for some operators associated with the Fourier
  and Hilbert transforms, Studia Math. 157 (2003), no. 3, 237-278. STATUS: REFEREED (journal, 2003). Open access journal
  version: https://kaltonmemorial.missouri.edu/assets/docs/sm2003a.pdf. RULES: the axiom is TRUE and NO
  STRONGER than its source (the "necessary" half of Thm 2.1, E = {0}). HKV do not define "subharmonic" or "upper
  semicontinuous"; we use the textbook notions of HVFalse/Defs/Potential.lean; values in [-∞, ∞) are `EReal` with `≠ ⊤`;
  HKV's measure dθ/2π: see `CircleIntNonneg`. The paper's own proof that the minorant is q-homogeneous is PROVED in
  Proofs/ColeHom.lean (with Demailly (4.24), itself PROVED in Proofs/Envelope.lean).
-/
import Mathlib
import HVFalse.Defs.Potential
import HVFalse.Defs.CitedDefs

namespace P18.Cited

/-- [HKV2003, Theorem 2.1 (Cole), p. 242], VERBATIM: "Suppose F : C → [−∞, ∞) is an upper semicontinuous function and E is a
nonempty subset of C. Then in order that we have the inequality ∫₀^{2π} F∘f(e^{iθ}) dθ/2π ≥ 0 (2.1) whenever f is a polynomial
with f(0) ∈ E, it is necessary and sufficient that there exists a subharmonic function G with G(z) ≤ F(z) for z ∈ C and
G(z) ≥ 0 for z ∈ E." The paper quotes it with E = {0} ("for polynomials vanishing at 0").
This axiom is the direction "(2.1) for every such f ⇒ such a G exists"; nothing about homogeneity. -/
axiom hkv_thm21 (F : ℂ → EReal) (hF : UpperSemicontinuous F) (hFtop : ∀ z, F z ≠ ⊤) (E : Set ℂ) (hE : E.Nonempty)
    (h21 : ∀ f : Polynomial ℂ, f.eval 0 ∈ E →
      CircleIntNonneg (fun θ => F (f.eval (Complex.exp ((θ : ℂ) * Complex.I))))) :
    ∃ G : ℂ → EReal, IsSubharmonic G ∧ (∀ z, G z ≤ F z) ∧ (∀ z ∈ E, 0 ≤ G z)

end P18.Cited
