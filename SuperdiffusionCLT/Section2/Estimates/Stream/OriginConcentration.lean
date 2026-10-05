/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.EntryConsequences
public import SuperdiffusionCLT.Assumptions.ShellLaw.J2EntryConsequences
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Cutoff.Finite

/-!
# Marginal finite-shell concentration at the origin

This module proves the scalar and matrix forms of the first finite-shell
concentration estimate. Shell amplitudes are exactly one; no positive-gamma
scaling or geometric-sum argument is present.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)}

/-- The exact Euclidean operator norm is bounded by the sum of the absolute
values of all matrix entries. -/
theorem matrixOperatorNorm_le_sum_univ_abs_entry (A : Mat d) :
    matrixOperatorNorm A ≤ ∑ p : Fin d × Fin d, |A p.1 p.2| := by
  have hsum : ∑ p : Fin d × Fin d, |A p.1 p.2| =
      ∑ i : Fin d, ∑ k : Fin d, |A i k| :=
    Fintype.sum_prod_type (fun p : Fin d × Fin d ↦ |A p.1 p.2|)
  rw [hsum]
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    (matrixFrobeniusNorm_le_sum_abs_entries A)

end

end SuperdiffusionCLT.Section2.Estimates.Stream
