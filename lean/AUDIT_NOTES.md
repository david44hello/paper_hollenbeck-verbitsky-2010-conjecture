## Route differences (where the Lean proof does not follow the paper word for word)
<!-- AUDIT_NOTES.md - hand-written; scripts/audit.py appends it to AUDIT.md. Copyright (C) Dave Goel 2026--now. All rights reserved. -->

(R1) **(HV) on L^p via trigonometric polynomials** (C01b-d). The analysis is done on trigonometric polynomials (Defs/HV.lean), then
transported to all of L^p(T) (Proofs/DensityLp*.lean): density of trigonometric polynomials, uniqueness of Fourier
coefficients, Fatou, and the cited [HV2000] bound for P₊, P₋ (quoted verbatim from Mel2023 (2); paper l.63). This is the paper's
"by density" (l.171).

(R2) **q-subtrigonometric ⇒ trigonometrically convex, and continuity** (C06a, C06b, C07). The paper (l.224-228) says
"Compare" HKV2003 (3.1) and Prop. 3.3, which assume a continuous φ (continuity is what C06b proves). Lean proves a sector Phragmén–Lindelöf
comparison instead (Proofs/Sector.lean, no axiom) and continuity by a tan substitution that makes φ/cos convex
(Proofs/TrigCont.lean, no axiom). HKV Prop. 3.3 and Lemma 3.1 are not used.

(R3) **Signs in Prop. 5 (the saddle)** (C10c, C10e). The paper certifies the sign of H by interval arithmetic (Arb + mpmath).
Lean proves H > 0 on (4/3, 2) by hand (C10c2), and also the paper's three interval steps (C10e) by hand, with Taylor
bounds for tan and crude box bounds; no interval arithmetic.

(R4) **From a bad disc to a failure of (HV)** (Prop. 4, C09). The paper uses Fejér means, a Blaschke product and a square
root. Lean uses g = ζg₁, z = g₁e^{Y/2}, w = ζe^{−Y/2} with Y a polynomial, exponential partial sums, and Stone–Weierstrass
(Proofs/FailLift.lean, Proofs/Select.lean; no axiom). Lemma 3 (C08) is not used by this proof.

(R5) **Cole's theorem and the homogeneous minorant** (C09 and everything after it). Lean uses Cole's theorem exactly as the paper
quotes it (HKV2003 Thm 2.1, E = {0}; axiom hkv_thm21) and then the paper's OWN proof that the largest subharmonic minorant V
is q-homogeneous (l.297-306; Proofs/ColeHom.lean). That proof uses Demailly (4.24) (the regularized upper envelope of
subharmonic functions is subharmonic), cited by the paper at l.301; Lean PROVES it (Proofs/Envelope.lean, no axiom).
So Theorem A and Prop. 4 rest on Cole's Thm 2.1 alone (+ [HV2000] for L^p). HKV's p.244 Remark is no longer used.

(R6) **Theorem B "if"** (C16, C16a). The paper says U(z,w) = v(zw) is plurisubharmonic. Lean proves it with NO textbook fact:
U∘h is locally sub-mean for every entire h (Proofs/UComp.lean), and a continuous locally sub-mean function is subharmonic
(Proofs/LocGlob.lean: maximum principle + trigonometric approximation). Demailly (4.12) and (5.11) are not used here.

(R7) **Prop. 14, the best constant** (C22a, C22c). The paper uses Demailly (5.11) (U = v(zw) is plurisubharmonic). Lean
proves the one-variable fact it needs with NO textbook fact (Proofs/VComp.lean: V_φ∘h is sub-mean for entire h,
via supporting q-sinusoids of the trigonometrically convex φ and the local-to-global principle of Proofs/LocGlob*). C22c needs
[HV2000] (C* < ∞) and the lower bound C* ≥ C_HV of [MM2022, §2] (instance t = 1; axiom mm2022_lower_bound; REFEREED (journal, 2023); open version read: arXiv v4).

(R8) **The ω step of Sec. 7** (C23f, l.640-645). The paper applies it to ρ with ρ'' + q²ρ = μ, a measure; the row C23f is
the C² case. The conclusion it serves (the discrete inequality, C23b, C23d) is proved by another route:
q-subtrigonometric ⇒ trigonometrically convex ⇒ the discrete inequality.

## Prop. 8 (the explicit counterexample): what Lean proves, what it only states, what it leaves out

(P1) **PROVED in Lean**: the arc structure and its values (C13d `zw = e^{iγ} ξ Π²`, C13e `arg zw`, `log|z/w|` on the
three arcs, C13f `qα_k < 1`, C13k the arc values of `Γ - e`); the integrand on each arc (C13p, l.450) and
`|zw|^q = Π_k |2 sin((θ-θ_k)/2)|^{-qα_k}` (C13q, l.451); `2 sin(x/2) ≥ 0.99x` on `[0, 1/10]` (C13r, l.455); "C13m implies
that (HV) fails" (C13n); and the exact claims of the remark "why δ is so small" (C13s: `η = 0.0102/π`, `q t₂ = π a₋ - π/2`,
`q t₃ = π/2 + π η`, the values `e(t₂)`, `e(t₃)`, `W₁ = Σ (Γ - e) B` by the reflection formula, `Γ(0,t₁) = e(t₁) = 0`);
`0 ≤ Re Y ≤ y₂` in the disc (C13u, l.430-433); `|zw|^q` integrable on each arc (C13v, l.451-452) and the integral
form `∫ G = Σ_j Γ_j ∫_{arc_j} |zw|^q` (C13w, l.449-450); from the paragraph after the proof, `Re(ξg'/g) > 0` in
the disc, "so g is starlike" (C13t, l.462-464); `z, w ∈ H^p` for every `δ ∈ (0, 2π)` (C13b_explicit_hardy_proved,
l.442-444; Proofs/HardyBound.lean: `|1 - e^{iφ}| ≤ 2|1 - re^{iφ}|`, all `α_k > 0` with sum 2, and C13u give
`|z|, |w| ≤ 2e^{y₂/2}|Π|` on the circles `|ζ| = r`); and the hand step from C13b and C13c to C13m
(C13m_hand_step_proved, l.444-446; Proofs/HandStep.lean: `f = z + w̄ ∈ L^p`, `P₊f = z` and `P₋f = w̄` by Cauchy's theorem
on `|ζ| = r` and dominated convergence as `r → 1`, and (HV) with `C = C_HV` would force `∫_T G ≥ 0`).

(P2) **STATED in Lean, NOT proved** (each a `def … : Prop` in HVFalse/Paper/ComputerChecked.lean; a proof may use one
only as an explicit hypothesis of its statement, and such rows have the status "PROVED GIVEN …", e.g. C13n):
C13c (the enclosure of `∫_T G`, l.421-423): a computer certificate. C13m (l.424, "so f violates (HV) with C = C_HV"):
PROVED GIVEN C13c (row C13m_given_C13c), since C13b and the hand step are proved (P1); so the explicit counterexample
rests on the computer certificate C13c alone. (C13b_explicit_hardy and C13m_hand_step are also `def … : Prop` there;
their rows `…_proved` in Statements.lean prove them.) The box parts of Props. 10, 11 and 13 (C19b_boxes, C20a_boxes,
C21_boxes) are stated, not proved: COMPUTER CERTIFICATE ONLY ((eq:two) at the certified values: the box checks plus the certificate's short hand arguments (i)-(iii), l.524-541, and L(p) < sec² on each cell, l.584; NOT proved in Lean).

(P3) **Not formalized** (geometric function theory is not in Mathlib): the rest of the paragraph after the proof of
Prop. 8 (paper l.464-466), which the paper says the proof does not use: "[g is starlike,] hence univalent. As arg g is constant
on each of the three arcs and |g| → ∞ at the three singular points, g maps the disc onto ℂ minus three radial slits"
(also the Introduction, l.123-124). Mathlib has neither "starlike ⇒ univalent" nor the boundary correspondence
needed for the slit image.

## Numerical only (the paper says so: numerical, not certified) — not in Lean

- The remark "why δ is so small" (l.468-485; "its numbers are numerical, not certified"): `W₁ ≈ -0.0053` (terms `+5.4330`
  and `-5.4383`), `W₀ ≈ 3.82`, `η ≈ 0.00325`, "`log(1/δ) > 2133` approximately", `(Γ - e)(y₂,t₂) ≈ -7.7·10⁻⁴` and
  `(Γ - e)(0,t₃) ≈ 1.7·10⁻⁵`; the clause "the weight `|zw|^q` behaves like `2^{-a_π}|θ+δ/2|^{-a₋}|θ-δ/2|^{-a₊}`"
  (l.471) and its asymptotic display (l.474), which the paper offers as a heuristic. (The earlier
  certified-sign runs at `δ = e^{-2133}, e^{-2134}` are logs only; the paper no longer uses them.)
- Sec. 7 (after Prop. 14): the values of `λ_{*,N}` (l.660-667) and `C*/C_HV ≥ 1 + 3.82·10⁻⁵` at `(3/2, 4)` and
  `1 + 1.08·10⁻⁵` at `(3/2, 3.98)` (l.679), also quoted in the Introduction (l.129-131: "A discretization of this problem, solved by linear programming (numerical, not certified), gives
  `C*/C_HV - 1 ≥ 1.0·10⁻⁵` at `(3/2, 3.98)` ... and `≥ 3.8·10⁻⁵` at the end point `s = 4`").
- The Remark after Prop. 11 (l.593-594): the minimum of the certified fraction, "about 16% (at `p = 1.975`)": Lean
  proves the minimum lies in `[16%, 17%]` (C30c, C30d), not its value (numerically about 0.1646) or where it is.
- Sec. 7, Computation (l.656-658): "this can only overestimate `m_λ`, which enlarges the feasible set and so can only
  lower the computed `λ_{*,N}`" (a remark about the numerical method).

## Further sentences of the paper and where Lean has them

- Sec. 2 (l.199-204): "always s₀(p) ≤ sec²ϑ", now derived for every 1 < p < 2: the closed form of Γ(y,π/p) - e(π/p)
  (C04g), "negative for small y ≠ 0 when s > sec²ϑ" (C04h), and s₀ ≤ sec²ϑ itself (C04i). All PROVED, no cited result.
- Proof of Prop. 5 (l.374-375): u'(p) = -(π/p²)√u(1+u) (C10f) and the u''(p) formula (C10g). PROVED. (The paper uses
  them in its interval check of the signs of H and K; Lean proves Prop. 5 in its own rows, C10a-C10e.)
- After Prop. 13 (l.612-613): "the failing fraction falls from 30.6% at p = 19/10 to 0.7% at p = 7/5": the two ends of the
  table's column "failing fraction", PROVED as defined in the paper (C29b).
- After Prop. 8 (l.462-464): Re(ξg'/g) > 0, "so g is starlike": PROVED (C13t). "hence univalent" and the slit image: (P3).
- Sec. 7, after the definition of λ_{*,N} (l.675-677): the floating-point error sentence is numerical only.
