/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- Marginal J2: the canonical coordinate maps of
the natural-number-indexed shell sequence are mutually independent. The
literal disjoint-subcollection statement is a derived consumer theorem. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  independent :
    iIndepFun
      (fun n : ℕ ↦
        fun F : ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d ↦ F n)
      P.toMeasure
