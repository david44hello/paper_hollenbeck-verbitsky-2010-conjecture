## Route differences (where the Lean proof does not follow the paper word for word)
<!-- AUDIT_NOTES.md - hand-written; scripts/audit.py appends it to AUDIT.md. Copyright (C) Dave Goel 2026--now. All rights reserved. -->

(R1) **(HV) on L^p via trigonometric polynomials** (C01b-d). The analysis is done on trigonometric polynomials (Defs/HV.lean), then
transported to all of L^p(T) (Proofs/DensityLp*.lean): density of trigonometric polynomials, uniqueness of Fourier
coefficients, Fatou, and the cited [HV2000] bound for P₊, P₋ (quoted verbatim from Mel2023 (2); paper l.58). This is the paper's
"by density and M. Riesz's theorem" (l.181); see (R9).

(R2) **q-subtrigonometric ⇒ trigonometrically convex, and continuity** (C06a, C06b). The paper (l.244-245) cites
[HKV2003, Prop. 3.3], which assumes a continuous φ (continuity is shown just before, l.242-243). Lean proves a sector
Phragmén–Lindelöf comparison instead (Proofs/Sector.lean, no axiom) and continuity by a tan substitution that makes φ/cos
convex (Proofs/TrigCont.lean, no axiom). HKV Prop. 3.3, (3.1) and Lemmas 3.1, 3.2 are not used.

(R3) **Signs in Prop. 5 (the saddle)** (C10c, C10e). The paper certifies the sign of H by interval arithmetic (Arb, l.391-396;
a second, independently written program, l.166-168). Lean proves H > 0 on (4/3, 2) by hand (C10c2), and also the paper's
three interval steps (C10e) by hand, with Taylor bounds for tan and crude box bounds; no interval arithmetic.

(R4) **From a bad disc to a failure of (HV)** (Prop. 4, C09). The paper uses Fejér means and Lemma 3 (a Blaschke product
and square roots). Lean uses g = ζg₁, z = g₁e^{Y/2}, w = ζe^{−Y/2} with Y a polynomial, exponential partial sums, and
Stone–Weierstrass (Proofs/FailLift.lean, Proofs/Select.lean; no axiom). Lemma 3 (C08) is not used by this proof.

(R5) **Cole's theorem and the homogeneous minorant** (C09 and everything after it). Lean uses Cole's theorem exactly as the paper
quotes it (l.300-302: HKV2003 Thm 2.1, E = {0}; axiom hkv_thm21) and then the paper's OWN proof that the largest
subharmonic minorant V is q-homogeneous (l.300-309; Proofs/ColeHom.lean). That proof uses Demailly (4.24) (the regularized
upper envelope of subharmonic functions is subharmonic), cited by the paper at l.304; Lean PROVES it (Proofs/Envelope.lean,
no axiom). So Theorem A and Prop. 4 rest on Cole's Thm 2.1 alone (+ [HV2000] for L^p, R9).

(R6) **Theorem B "if"** (C16, C16a). The paper cites [Dem, Ch. I, (4.12), (4.16), (5.11)] for "E is plurisubharmonic"
(l.191-192). Lean proves it with NO textbook fact: U∘h is locally sub-mean for every entire h (Proofs/UComp.lean), and a
continuous locally sub-mean function is subharmonic (Proofs/LocGlob.lean: maximum principle + trigonometric approximation).

(R7) **Prop. 14, the best constant** (C22a, C22c). The paper uses Demailly (5.11) (U = v(zw) is plurisubharmonic, l.628).
Lean proves the one-variable fact it needs with NO textbook fact (Proofs/VComp.lean: V_φ∘h is sub-mean for entire h,
via supporting q-sinusoids of the trigonometrically convex φ and the local-to-global principle of Proofs/LocGlob*). C22c
needs C* < ∞ (the paper: M. Riesz's theorem, l.631; see R9) and C* ≥ C_HV [MM, Sec. 2] (l.633; the lemma
mm2022_lower_bound_one, the case t = 1 of the axiom mm2022_lower_bound).

(R8) **Sec. 7, λ_{*,N} ≤ λ_*** (C23b, C23d). The paper (l.641-643) uses the trigonometric convexity of Sec. 3 and the
defining inequality [HKV2003, (3.1)] at the midpoint. Lean derives the discrete inequality from C06a (R2), with no axiom.
The row C23f (an ω-step argument for the same inequality) is proved but RETIRED: the paper does not state it.

(R9) **M. Riesz's theorem** (C01b, C01c, C22c). The paper invokes M. Riesz's theorem at l.181 and l.631; Lean derives the
bound it needs from the cited [HV2000] result (the norm of P_+, cited by the paper at l.58).

(R10) **Lemma 2, rigidity** (C07a, C07b). The paper's proof (l.251-269) works with the measure μ = φ'' + q²φ: Step 1
integrates c dμ by parts on I, Step 2 integrates by parts beyond ±π/p (ρ = φ - β cos(qt) ≥ 0), Step 3 squeezes β at π/p
with Lemma 1. Lean proves the same statement from the three-point (trigonometric convexity) inequality alone
(Proofs/Forcing.lean: a discrete Green formula and comparisons inside and outside I), with no measure, no one-sided
derivatives and no axiom.

## Cited results (the only axioms; HVFalse/Cited/, each with its source quoted verbatim)

- `hkv_thm21`: Cole's theorem, [HKV2003, Thm 2.1] (Studia Math. 157 (2003), REFEREED), the direction from (2.1) for every
  polynomial with f(0) ∈ E to a subharmonic minorant, as the paper quotes it (l.300-302, E = {0}).
- `hv2000_riesz`: the bound ‖max(|P₊f|, |P₋f|)‖_p ≤ (1/sin(π/p))‖f‖_p of [HV2000] (J. Funct. Anal. 175 (2000), REFEREED),
  quoted from [Mel2023, (2)]; 1 < p ≤ 2, trigonometric polynomials. The paper cites [HV2000] at l.58; see (R9).
- `mel_eq37`: (eq:two) at s = sec²ϑ for 1 < p ≤ 4/3, [Mel2023, Sec. 8, (37)] (Math. Ann. 388 (2024), REFEREED); paper
  l.206-207 and l.131.
- `jag_eq2`: (eq:two) at s = p/(p-1) for 4/3 < p < 2, [Jag2026, (2)] (Izv. Math. 90 (2026), REFEREED); paper l.205-206
  and l.131.
- `mm2022_lower_bound`: [MM2022, Sec. 2] (Potential Anal. 59 (2023), REFEREED; open version read: arXiv:1912.08944v4):
  for 1 < p < 2, s > 0 and every t in MM's own range [0, 1], every constant C for which (HV) holds on L^p satisfies
  C ≥ (1 + t^s)^{1/s}/√(1 + t² + 2t cos(π/p)). At t = 0 Lean's value is 1 (0^s = 0 for s > 0, √1 = 1), as in MM; at
  t = 1 it is C_HV (lemma mm2022_lower_bound_one); on [0, 1] the radicand is ≥ (1 - t)² + 2t(1 + cos(π/p)) > 0. The paper
  cites it at l.66, l.212-213 (at t = e^{-y}) and l.633. Rows that use it: C17f, C25b, C22c, C17g, C25c, C04k, C04m (C04k, C04m at t = e^{-y}; the others at t = 1).

## Prop. 8 (the explicit counterexample): what Lean proves, what it only states, what it leaves out

(P1) **PROVED in Lean**: the arc structure and its values (C13d `zw = e^{iγ} ξ Π²`, C13e `arg zw`, `log|z/w|` on the
three arcs, C13f `qα_k < 1` and C13f2 their values `≈ 0.927, 0.076, 0.497`, C13k the arc values of `Γ - e`); the integrand
on each arc (C13p, l.477) and `|zw|^q = Π_k |2 sin((θ-θ_k)/2)|^{-qα_k}` (C13q, l.478); `2 sin(x/2) ≥ 0.99x` on
`[0, 1/10]` (C13r, l.482); "C13m implies that (HV) fails" (C13n); the exact claims of the remark "the size of δ" (C13s:
`η = 0.0102/π`, `q t₂ = π a₋ - π/2`, `q t₃ = π/2 + π η`, the values `e(t₂)`, `e(t₃)`, `W₁ = Σ (Γ - e) B` by the reflection
formula, and `Γ = e = 0` at the contact point `(0, -π/p)`, l.434-435; C13g2: `η = q(t₃ - π/p)/π`);
`0 ≤ Re Y ≤ y₂` in the disc (C13u, l.460-463); `|zw|^q` integrable on each arc (C13v, l.478-479) and the integral
form `∫ G = Σ_j Γ_j ∫_{arc_j} |zw|^q` (C13w, l.476-477); from the paragraph after the proof, `Re(ξg'/g) > 0` in
the disc, "Hence g is starlike" (C13t, l.490-492); `z, w ∈ H^p` for every `δ ∈ (0, 2π)` (C13b_explicit_hardy_proved,
l.471-473; Proofs/HardyBound.lean: `|1 - e^{iφ}| ≤ 2|1 - re^{iφ}|`, all `α_k > 0` with sum 2, and C13u give
`|z|, |w| ≤ 2e^{y₂/2}|Π|` on the circles `|ζ| = r`); and the hand step from C13b and C13c to C13m
(C13m_hand_step_proved, l.473-474; Proofs/HandStep.lean: `f = z + w̄ ∈ L^p`, `P₊f = z` and `P₋f = w̄` by Cauchy's theorem
on `|ζ| = r` and dominated convergence as `r → 1`, and (HV) with `C = C_HV` would force `∫_T G ≥ 0`).

(P2) **STATED in Lean, NOT proved** (each a `def … : Prop` in HVFalse/Paper/ComputerChecked.lean; a proof may use one
only as an explicit hypothesis of its statement, and such rows have the status "PROVED GIVEN …", e.g. C13n):
C13c (the enclosure of `∫_T G`, l.451-453): a computer certificate. C13m (l.454, "so f violates (HV) with C = C_HV"):
PROVED GIVEN C13c (row C13m_given_C13c), since C13b and the hand step are proved (P1); so the explicit counterexample
rests on the computer certificate C13c alone. (C13b_explicit_hardy and C13m_hand_step are also `def … : Prop` there;
their rows `…_proved` in Statements.lean prove them.) The box parts of Props. 10, 11 and 13 (C19b_boxes, C20a_boxes,
C21_boxes) are stated, not proved: COMPUTER CERTIFICATE ONLY ((eq:two) at the certified values: the box checks plus the certificate's short hand arguments (i)-(iii), l.527-543, and L(p) < sec² on each cell, l.586; NOT proved in Lean).

(P3) **Not formalized** (geometric function theory is not in Mathlib): the rest of the paragraph after the proof of
Prop. 8 (paper l.492-494), which the paper says the proof does not use: "Hence g is starlike, and therefore univalent. As
arg g is constant on each of the three arcs and |g| → ∞ at the three singular points, g maps the disc onto ℂ minus three
radial slits" (also before Prop. 8, l.436, and the Introduction, l.114-115). Mathlib has neither "starlike ⇒ univalent"
nor the boundary correspondence needed for the slit image.

## Numerical or heuristic only (the paper says so) — not in Lean

- The remark "the size of δ" (l.496-507; "This remark is heuristic, and its numbers are not certified"): `W₁ ≈ -0.0053`,
  `W₀ ≈ 3.82`, `η ≈ 0.00325`, "`log(1/δ) > 2133` approximately", `(Γ - e)(0,t₃) ≈ 1.7·10⁻⁵` (Lean proves
  `(Γ - e)(y₂,t₂) = -7.7·10⁻⁴` to two digits, C13k, and `η` to five, C13g); the clause "the weight `|zw|^q` behaves like
  `2^{-a_π}|θ+δ/2|^{-a₋}|θ-δ/2|^{-a₊}`" (l.498-499) and the display (l.500), which the paper offers as a heuristic.
- Before Prop. 8 (l.430-439): the heuristic paragraph ("Heuristically, the weight |zw|^q has a power singularity at each end
  point of an arc ..."). Its exact parts are rows: the exponents at the short arc add up to more than 1 (η > 0, C13g),
  `Γ - e < 0` on the short arc (C13k), and the long arc at `-π/p` is the contact point, where `Γ = e = 0` (C13k, C13s).
- Sec. 7 (after Prop. 14): the values of `λ_{*,N}` (l.660-670) and `C*/C_HV ≥ 1 + 3.82·10⁻⁵` at `(3/2, 4)` and
  `1 + 1.08·10⁻⁵` at `(3/2, 3.98)` (l.677), also quoted in the Introduction (l.117-120: "A discretization, solved by linear
  programming (numerical, not certified), gives `C*/C_HV - 1 ≥ 1.08·10⁻⁵` at `(p,s) = (3/2, 3.98)` and `≥ 3.82·10⁻⁵` at
  `(3/2, 4)`").
- The Remark after Prop. 11 (l.594-595): the minimum of the certified fraction, "about 16% (at `p = 1.975`)": Lean
  proves the minimum lies in `[16%, 17%]` (C30c, C30d), not its value (numerically about 0.1646) or where it is.
- Sec. 7, computation (l.654-656): "This can only overestimate `m_λ`, which enlarges the feasible set and so can only
  lower the computed `λ_{*,N}`" (a remark about the numerical method); the floating-point sentence (l.674-676).

## Further sentences of the paper and where Lean has them

- Sec. 2 (l.198-202): `Γ - e = exp(q|y|) Φ(exp(-|y|), t)`: PROVED (C04j).
- Sec. 2 (l.207-211): "Moreover s₀(p) ≤ sec²ϑ": the closed form of Γ(y,π/p) - e(π/p) (C04g), "negative for small y ≠ 0
  when s > sec²ϑ" (C04h), and s₀ ≤ sec²ϑ itself (C04i). All PROVED, no cited result.
- Sec. 2 (l.211-215), the end point of the conjectured range: the bound of [MM, Sec. 2] for every y ≥ 0 (C04k, from the
  cited result), "equals C^HV at y = 0 and ... exceeds it exactly when Γ(y,π/p) < 0" (C04l, PROVED), and "Hence C* > C^HV
  for s > sec²ϑ" (C04m, from C04h, C04l and the cited result).
- Proof of Prop. 5 (l.384-385): u'(p) = -(π/p²)√u(1+u) (C10f) and the u''(p) formula (C10g). PROVED. (The paper uses
  them in its interval check of the sign of H; Lean proves Prop. 5 in its own rows, C10a-C10e.)
- Sec. 5 (l.410-414): Jaguzović's point (C15a-C15d) and "about three times as large in absolute value": the ratio of the
  two certified values at s = 3.98 lies in (2.98, 2.99) (C15e, PROVED from C12c and C15c).
- After Prop. 8 (l.490-492): Re(ξg'/g) > 0, "Hence g is starlike": PROVED (C13t). "and therefore univalent" and the slit
  image: (P3).
- After Prop. 13 (l.610-613): "the failure is slight near p = 4/3 (see the table after Proposition 10)" refers to the
  table's failing fractions, PROVED as defined (C29b); the first cell (C21d) and Theorem A (C11) cover the rest.
- Introduction, the method paragraph and "Idea of the proof" (l.123-154), summaries of results proved later: (HV) ⇔
  ∫ G ≥ 0 (C01); G = |zw|^q Γ, E = |zw|^q e (C02b, C16a, C16b); "E ≤ G becomes Γ ≥ e" (C16c); the sub-mean-value step
  (C16, C16d); g = zw and |z/w| prescribed independently (Lemma 3, C08); Γ = e = 0 at the contact points and
  m ≤ e + O((t∓π/p)²) (C05a-C05d); every minorant φ equals e on |t| ≤ π/p and lies above e (C07a, C07b); (eq:two) necessary
  and sufficient (C16, C17); one failure point gives a counterexample (C09); the degenerate saddle and its quartic term
  (C10b2, C10b3, C10c3), whose sign changes at p = 4/3 (C10a9 with C10a3, C10c4); persistence for slightly smaller s
  (C11); Jaguzović's point at p = 3/2 (C15b, C15c). The equivalence of `∫|g|^q m(arg g) ≥ 0` for every g with the existence
  of a subharmonic minorant `|ζ|^q φ(arg ζ)` (l.137-140) is row C16i (Proofs/R572Iff.lean), a chain: inequality for every
  polynomial g ⇔ minorant ⇔ inequality for every entire g. "Polynomial ⇒ minorant" is the Cole step of the proof of Prop. 4
  (Proofs/ColeHom.lean, R5; it uses the cited Cole theorem), "minorant ⇒ entire" the sub-mean step of the proof of Prop. 14
  (Proofs/VComp.lean, R7; no cited result). For the paper's "analytic g", Lean states the iff for polynomials and for
  entire g (not for g holomorphic only near the closed disc).

## Rows that are not claims of the paper (counted apart in the summary)

- LEAN-ONLY HELPER: C10a5 (K(4/3) = 2√2/3), C10d (the curve of Prop. 5 has t < π/p), C23c (the discrete inequality is
  exact for cos(qt)).
- RETIRED (proved; the paper does not state them): C21c (Q₄(p) → 0 as p → 4/3), C23f (the ω step), C06f (the converse
  of C06a).
