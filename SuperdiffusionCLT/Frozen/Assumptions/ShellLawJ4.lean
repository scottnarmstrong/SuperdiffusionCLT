/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw

@[expose] public section

open Homogenization MeasureTheory

/-- Marginal J4: the joint law of the entire
natural-number-indexed shell sequence is invariant under every signed-
permutation conjugation and, separately, under whole-sequence negation. -/
structure SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
    (d : ℕ)
    (P : ProbabilityMeasure
      (ℕ → SuperdiffusionCLT.Frozen.Assumptions.ShellField d)) : Prop where
  hyperoctahedral : ∀ (R : Mat d)
      (hR : Homogenization.IsSignedPermutationMatrix R),
    P.map
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.rotateSequence
          (d := d) R hR) = P
  negation :
    P.map
        (SuperdiffusionCLT.Frozen.Assumptions.ShellField.negateSequence
          (d := d)) = P
