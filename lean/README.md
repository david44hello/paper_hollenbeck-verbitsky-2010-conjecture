# The Hollenbeck–Verbitsky (2010) conjecture is false: the Lean proof

Dave Goel. Copyright (C) Dave Goel 2026--now. All rights reserved.

This folder is the Lean 4 proof. It proves all results of the paper, Theorems A and B included, except the statements that rest on the programs in `../programs/`: the enclosure of the integral in Proposition 8, and the instances of inequality (3) and of its failure behind Propositions 10 (lower bounds), 11 and 13. Lean states these and proves the rest from them; the instances also use the short hand arguments of Section 6 of the paper and the bound L(p) < sec²(π/2p) on each cell, which Lean does not prove either. It also leaves out a side remark after Proposition 8, which the proof does not use: that the map g is univalent and maps the disc onto the plane minus three slits (Lean proves that g is starlike). It assumes only the published results cited in the paper; `AUDIT.md` lists them, and `HVFalse/Cited/` quotes each one from its source. `AUDIT.md` gives each of the 146 claims of the paper with its status in Lean: 103 proved, 26 proved from the cited results, 9 proved given a computer check, and 8 statements not proved in Lean by themselves. `AUDIT_NOTES.md` lists what is not formalized and the values the paper calls numerical, not certified.

The log files named in this folder (logs/...) are in ../programs/logs/.

Build, from this folder: `lake exe cache get && lake build` (Lean 4 v4.35.0, Mathlib commit 56a005855ea1).
