/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2

/-!
# Scalar-entry consequences of marginal J2

This module reads the mutual shell independence through a measurable
scalar entry at one fixed spatial point.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2

open Homogenization ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}
variable {P : MeasureTheory.ProbabilityMeasure (ℕ → ShellField d)}

/-- At any fixed point and matrix entry, the scalar values of the natural
shell sequence are mutually independent. -/
theorem iIndepFun_entry_coordinate (hJ2 : ShellLawJ2 d P)
    (x : Vec d) (i k : Fin d) :
    iIndepFun (fun (n : ℕ) (F : ℕ → ShellField d) ↦ (F n) x i k)
      P.toMeasure :=
  hJ2.independent.comp
    (fun _ : ℕ ↦ fun j : ShellField d ↦ j x i k)
    (fun _ ↦ ShellField.measurable_eval_entry x i k)

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
