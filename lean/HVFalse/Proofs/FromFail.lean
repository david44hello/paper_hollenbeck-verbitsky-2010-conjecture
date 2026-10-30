/-
  HVFalse/Proofs/FromFail.lean - claims that follow from Prop. fail (C09) in a few lines: C18, C14, C15b
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  Statements.lean instantiates `h9` with the proof of C09 once it exists; until then these are "proved from C09".
-/
import HVFalse.Proofs.Small
import HVFalse.Defs.HV

open Real Set

namespace P18

/-- The statement of C09 (Prop. fail, l.289-292), as a hypothesis. -/
def PropFailStmt : Prop :=
  ∀ {p s : ℝ}, 1 < p → p < 2 → 0 < s → s ≤ Ssec p →
    (∃ y t : ℝ, t ∈ Ioo (-(π / p)) (π / p) ∧ Gam p s y t < ee p t) → ¬ HVIneq p s (hvConst p s)

/-- C18, l.523-524: one failure point at `s₊ ≤ sec²ϑ` with `|t*| < π/p` gives failure for every `s ∈ [s₊, sec²ϑ]`
(Prop. fail + monotonicity in `s`). -/
theorem upper_by_point_of_fail (h9 : PropFailStmt) {p sp : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hsp : 0 < sp)
    (hspS : sp ≤ Ssec p) (hpt : ∃ y t : ℝ, t ∈ Ioo (-(π / p)) (π / p) ∧ Gam p sp y t < ee p t) :
    ∀ s ∈ Icc sp (Ssec p), ¬ HVIneq p s (hvConst p s) := by
  intro s ⟨hs1, hs2⟩
  obtain ⟨y, t, ht, hlt⟩ := hpt
  exact h9 hp1 hp2 (lt_of_lt_of_le hsp hs1) hs2
    ⟨y, t, ht, lt_of_le_of_lt (gam_antitone_s p sp s y t (by linarith) hsp hs1) hlt⟩

/-- C14, Corollary false (l.509-511): for `p = 3/2` (HV) fails for every `s ∈ [3.98, 4]`. -/
theorem cor_false_of_fail (h9 : PropFailStmt) :
    ∀ s ∈ Icc (398 / 100 : ℝ) 4, ¬ HVIneq (3 / 2) s (hvConst (3 / 2) s) := by
  have hS : Ssec (3 / 2) = 4 := by linarith [point_location.2]
  intro s hs
  refine upper_by_point_of_fail h9 (by norm_num) (by norm_num) (by norm_num) (by rw [hS]; norm_num)
    ⟨log (9 / 5), π / 2, point_location.1, by linarith [point_fails]⟩ s ⟨hs.1, ?_⟩
  rw [hS]
  exact hs.2

/-- C15b, l.410-412: (HV) fails at the end point `s = sec²(π/3) = 4` (here via C14 at `s = 4`). -/
theorem fails_at_cutoff_of_fail (h9 : PropFailStmt) : ¬ HVIneq (3 / 2) 4 (hvConst (3 / 2) 4) :=
  cor_false_of_fail h9 4 ⟨by norm_num, le_refl _⟩

end P18
