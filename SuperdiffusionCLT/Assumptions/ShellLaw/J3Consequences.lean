/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
public import SuperdiffusionCLT.Assumptions.ShellField.SequenceLaw
public import SuperdiffusionCLT.Probability.GaussianTail

/-!
# Basic consequences of the marginal J3 tail

This module records the first ordinary probabilistic consequences of the
J3 assumption. At every natural shell index, the direct regularity
observable is measurable, has the CoarseGraining library's unit-scale `Gamma₂`
weak-Orlicz bound, and belongs to `L²` under the canonical sequence law.

No centering, independence, or further integrability premise is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3

open Homogenization IndependentSums MeasureTheory

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-- The J3 observable of a fixed natural shell coordinate is measurable. This
fact depends only on the canonical coordinate and observable APIs. -/
theorem measurable_j3Observable_coordinate (n : ℕ) :
    Measurable
      (fun F : ℕ → ShellField d ↦ ShellField.j3Observable d n (F n)) :=
  (ShellField.j3Observable_measurable d n).comp
    (ShellField.measurable_shellCoordinate n)

/-- The strict Gaussian tail gives the CoarseGraining library's unit-scale `Gamma₂`
weak-Orlicz estimate for the shell-`n` J3 observable. -/
theorem isBigOWith_gammaSigma_j3Observable_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) :
    IsBigOWith P.toMeasure (gammaSigma 2)
      (fun F : ℕ → ShellField d ↦ ShellField.j3Observable d n (F n)) 1 :=
  SuperdiffusionCLT.Probability.isBigOWith_gammaSigma_two_of_gaussian_tail
    (by
      intro t ht
      have h := hJ3.gaussian_tail n t ht
      simpa using h)

/-- The strict Gaussian tail also places the shell-`n` J3 observable in
`L²` under the canonical sequence law. -/
theorem memLp_two_j3Observable_coordinate
    (hJ3 : ShellLawJ3 d P) (n : ℕ) :
    MemLp
      (fun F : ℕ → ShellField d ↦ ShellField.j3Observable d n (F n))
      2 P.toMeasure :=
  SuperdiffusionCLT.Probability.memLp_two_of_gaussian_tail
    (measurable_j3Observable_coordinate n)
    (fun F ↦ ShellField.j3Observable_nonneg d n (F n))
    (hJ3.gaussian_tail n)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3
