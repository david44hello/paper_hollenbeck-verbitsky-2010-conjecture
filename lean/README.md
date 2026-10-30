# The Hollenbeck–Verbitsky (2010) conjecture is false — Lean 4 proof

The paper: its link will be added here when it is posted.

This folder is a Lean 4 proof of the paper's results.

## Directions to Reproduce

Install Git, Lean (https://lean-lang.org/install/), Python 3 and ripgrep, then run:

```bash
git clone https://github.com/david44hello/paper_hollenbeck-verbitsky-2010-conjecture.git
cd paper_hollenbeck-verbitsky-2010-conjecture/lean
./check.sh
```

Its last line looks like:

```
AUDIT: 150 paper claims (+ 3 Lean-only helpers, 3 retired rows). PROVED: 104, PROVED (LEAN-ONLY HELPER): 3, PROVED (RETIRED): 3, PROVED GIVEN A COMPUTER CHECK: 6, PROVED-FROM-CITED: 29, PROVED-FROM-CITED GIVEN A COMPUTER CHECK: 3, NOT PROVED (computer-checked): 7, NOT PROVED by itself; PROVED GIVEN C13c (row C13m_given_C13c; C13c is checked by computer): 1 (+ 3 box parts). Table: .../AUDIT.md
```

29 claims are proved from results that the paper cites. 17 rest on the computer checks in
[../programs/](../programs/): 9 are proved given them, and 8 are stated in Lean but not proved by themselves.
[AUDIT.md](AUDIT.md) names them, claim by claim. The logs that the Lean files name (`logs/...`) are in
[../programs/logs/](../programs/logs/).

Copyright (C) Dave Goel 2026--now. All rights reserved.
