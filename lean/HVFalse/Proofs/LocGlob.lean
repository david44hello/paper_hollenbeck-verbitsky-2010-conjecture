/-
  HVFalse/Proofs/LocGlob.lean - continuous + locally sub-mean ⇒ subharmonic, axiom-free (replaces Demailly (4.12) e)⇒b))
  Copyright (C) Dave Goel 2026--now. All rights reserved.

  `LocGlob.submean_of_local` (LocGlobCore.lean): continuous + locally sub-mean ⇒ sub-mean on every circle.
  Here: `subharmonic_of_continuous_local` and `locGlob : ThmBIfLG.LocGlobStmt`, so that U∘h is subharmonic, E is psh
  (C16a), and Theorem B "if" (C16) holds, all with NO textbook axiom.
-/
import HVFalse.Proofs.LocGlobCore
import HVFalse.Proofs.ThmBIfLG

open Real Metric Set Filter Topology MeasureTheory

namespace P18

namespace LocGlob

/-- **Continuous + locally sub-mean ⇒ subharmonic** (no textbook axiom). -/
theorem subharmonic_of_continuous_local {u : ℂ → ℝ} (hu : Continuous u)
    (hloc : ∀ a, ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ → u a ≤ circleAverage u a r) :
    IsSubharmonic (fun z => ((u z : ℝ) : EReal)) :=
  ⟨fun _ => EReal.coe_ne_top _, (continuous_coe_real_ereal.comp hu).upperSemicontinuous,
    fun n _ _ hr => UComp.trunc_of_submean hu (submean_of_local hu hloc hr) n⟩

theorem locGlob : ThmBIfLG.LocGlobStmt := fun _ hu hloc => subharmonic_of_continuous_local hu hloc

variable {p : ℝ}

/-- `U` is subharmonic, with no textbook axiom (replaces `ThmBIf.Ufun_subharmonic`, which used Demailly (4.12)). -/
theorem Ufun_subharmonic (hp1 : 1 < p) (hp2 : p < 2) : IsSubharmonic (fun z => ((ThmBIf.Ufun p z : ℝ) : EReal)) :=
  ThmBIfLG.Ufun_subharmonic' locGlob hp1 hp2

/-- **C16a**, no textbook axiom. -/
theorem E_psh (hp1 : 1 < p) (hp2 : p < 2) : IsPSH (fun x : ℂ × ℂ => ((Efun p x.1 x.2 : ℝ) : EReal)) :=
  ThmBIfLG.E_psh' locGlob hp1 hp2

/-- **C16, Theorem B "if"** (trigonometric-polynomial form), no textbook axiom. -/
theorem theoremB_if {s : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hs : 0 < s) (h2 : TwoVar p s) :
    HVIneq p s (hvConst p s) :=
  ThmBIfLG.theoremB_if' locGlob hp1 hp2 hs h2

end LocGlob

end P18
