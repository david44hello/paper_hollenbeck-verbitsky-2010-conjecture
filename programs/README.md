# The Hollenbeck–Verbitsky (2010) conjecture is false: programs and logs

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

Run from this folder. Numbering as in the paper.

| Statement | Kind | Program | Command | Log |
|---|---|---|---|---|
| Prop. 5 (sign of H) | interval (Arb) | `code/saddle_sign_arb.py` | `python3 code/saddle_sign_arb.py --test; python3 code/saddle_sign_arb.py` | `logs/saddle_sign_arb.log` |
| Prop. 5 (sign of H) | interval (mpmath) | `code/saddle_sign_mpmath.py` | `python3 code/saddle_sign_mpmath.py` | `logs/saddle_sign_mpmath.log` |
| Prop. 7; Jaguzović's point (Section 5) | interval (Arb) | `code/point_arb.py` | `python3 code/point_arb.py --test; python3 code/point_arb.py --run` | `logs/point_arb.log` |
| Prop. 7; Prop. 10, s₊ | interval (mpmath) | `code/point_check_mpmath.py` | `python3 code/point_check_mpmath.py --test; python3 code/point_check_mpmath.py --run` | `logs/point_check_mpmath.log` |
| Prop. 8 | interval (Arb), quadrature | `code/counterexample_quadrature_arb.py` | `python3 code/counterexample_quadrature_arb.py --test; for L in 2000 2200 2500 3000; do python3 code/counterexample_quadrature_arb.py --verify 3 2 398 100 1.79 0.0102 0.4865 $L 128; done` | `logs/counterexample_quadrature_arb.log` |
| Prop. 8 | interval (Arb), Beta function | `code/counterexample_beta_arb.py` | `python3 code/counterexample_beta_arb.py --test; python3 code/counterexample_beta_arb.py --necks 2000 2133 2134 2200 2500 3000 --v-cut 120` | `logs/counterexample_beta_arb.log` |
| Prop. 8 (W₁, W₀, threshold) | numerical | `code/counterexample_closed_form.py` | `python3 code/counterexample_closed_form.py` | `logs/counterexample_closed_form.log` |
| Prop. 10, s₊ | interval (Arb) | `code/badcells_arb.py` | `python3 code/badcells_arb.py --test; python3 code/badcells_arb.py --points 7/5 3/2 8/5 17/10 9/5 19/10 --digits 4` | `logs/bracket_upper_arb.log` |
| Prop. 10, s₋ | interval (Arb) | `code/truepoints_arb.py` | `python3 code/truepoints_arb.py 7/5:52986/10000 3/2:39572/10000 8/5:31799/10000 17/10:26921/10000 9/5:23764/10000 19/10:21588/10000 --radius 1/5 --ymax 3 --max-boxes 3000000` | `logs/bracket_lower_arb.log` |
| Prop. 10, s₋ | interval (mpmath) | `code/truepoints_mpmath.py` | `python3 code/truepoints_mpmath.py --test; python3 code/truepoints_mpmath.py --run` | `logs/bracket_lower_mpmath.log` |
| Prop. 11 | interval (Arb) | `code/certify_arb.py` | `bash code/run_cells.sh` | `logs/cells_arb.log` |
| Prop. 13 | interval (Arb) | `code/badcells_arb.py` | `bash code/run_false_cells.sh` | `logs/false_cells_arb.log` |
| Section 7 | numerical (LP) | `code/best_constant_lp.py` | `bash code/run_best_constant.sh` | `logs/best_constant.log` |
| Section 7 | numerical (LP) | `code/best_constant_second.py` | `python3 code/best_constant_second.py --test; python3 code/best_constant_second.py --run` | `logs/best_constant_second.log` |
| Section 7 (checks) | numerical (LP) | `code/best_constant_lp.py` | `python3 code/best_constant_lp.py --test` | `logs/best_constant_controls.log` |

Notes on the logs:

- In `logs/saddle_sign_mpmath.log` the three `FAIL at` lines at the top come from the three negative controls listed at its end.
- `code/truepoints_arb.py` has no test of its own: it runs `certify_cell` of `code/certify_arb.py`, whose `--test` (with its negative controls) is at the top of `logs/cells_arb.log`.
- In `logs/counterexample_quadrature_arb.log` the `--verify` lines print the midpoints of the Arb input balls; each ball contains the exact decimal input, so these enclosures (±2.5·10⁻¹⁰) are wider than those of the `--test` run (±3·10⁻¹⁵).

All logs were made in the same environment: Python 3.12.3, python-flint 0.9.0 (Arb), mpmath 1.4.1, NumPy 2.5.4, SciPy 1.18.1 (`requirements.txt`), with `bash code/run_logged.sh logs/NAME.log COMMAND`, which writes the date, these versions and the md5 of every program at the top of the log.

### The remainder factors in `counterexample_beta_arb.py`

Notation as in the program header: s = a + bb, e1 = s - 1, sinc(u) = sin(u)/u, H0 = 2^(-c), and
H(theta) = sinc(theta/2)^(-s) (2 cos(theta/2))^(-c), so that theta^(-s) H(theta) = (2 sin(theta/2))^(-s) (2 cos(theta/2))^(-c).
Write d for the exponent of the near endpoint of a long arc and e = s - d for the other one; theta = t + delta/2.

1. Short arc, factor 1 + [0, 3 delta^2]. With x = theta + delta/2 in (0, delta), the integrand is
   x^(-a) (delta - x)^(-bb) H0 times sinc(x/2)^(-a) sinc((delta - x)/2)^(-bb) cos(theta/2)^(-c). Each factor lies in
   [1, 1 + delta^2/8] (sinc(u) >= 1 - u^2/6, cos(u) >= 1 - u^2/2, exponents in (0, 1)), so their product lies in
   [1, 1 + delta^2/2]; and the integral of x^(-a) (delta - x)^(-bb) over (0, delta) is delta^(-e1) B(1 - a, 1 - bb).

2. Long arcs, tail factor 1 - [0, 2 delta]. The integral of t^(-d) (t + delta)^(-e) over (0, 1 - delta/2) equals
   delta^(-e1) (B(1 - d, e1) - T), where T is the integral of u^(-d) (1 + u)^(-e) over (X, infinity), X = (1 - delta/2)/delta.
   From 1 - e/u <= (1 + 1/u)^(-e) <= 1: delta^(-e1) T = (1 - delta/2)^(-e1) e1^(-1) (1 - r) with 0 <= r <= e e1 /(s X) <= 2 delta.

3. Long arcs, factor 1 +- 40 (C2 + 1) delta. Exactly, 2pi J_far = int_0^(pi - delta/2) t^(-d) (t + delta)^(-e) H(theta) rho(t) dt,
   with rho = (sinc(t/2)/sinc(theta/2))^(-d) (sinc((t + delta)/2)/sinc(theta/2))^(-e). Since |(log sinc)'| <= 2/pi + delta
   on (0, pi/2 + delta/4], |log rho| <= s delta/(2 pi) + delta^2, so rho = 1 +- 0.34 delta. Put f(theta) = (theta - delta/2)^(-d)
   (theta + delta/2)^(-e); for theta >= delta, |f(theta) - theta^(-s)| <= delta theta^(-s-1). With |H - H0| <= C2 theta^2 on
   [0, 1] (C2 is computed by the program), this gives |int_(delta/2)^1 f (H - H0) - I1| <= 3 C2 delta and
   |int_1^pi f H - I2| <= delta I2. Hence |2pi J_far - core| <= (3 C2 + I2 + 0.35 core) delta, where core = H0 delta^(-e1)
   B(1 - d, e1) - H0 (1 - delta/2)^(-e1) e1^(-1) (1 - r) + I1 + I2. The program prints these values but does not test
   core > max(1, I2) itself. The inequality holds by a wide margin at every delta used: 2pi J_b = 24.2 at ln(1/delta) = 30
   (the --test value) and 1.4 * 10^5 at ln(1/delta) = 2000, growing like delta^(-e1), against I2 = 1.734. So the error is
   at most (3 C2 + 2) delta core <= 40 (C2 + 1) delta core, the factor used. At delta <= e^(-2000) every one of these constants could be multiplied by 10^800 without changing a printed digit.
