/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction

/-!
# J1 version 2 for the Dirac zero law

Under a Dirac measure any two sub-sigma-fields are independent, so the
restriction-lane range of dependence holds at every separation. Together with
the other certificates this shows the prefix, J1 version 2, J2, J3 and J4 are
jointly satisfiable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-- Under a Dirac measure the pointwise-restriction sigma-fields of any two sets
are independent. -/
theorem shellLawJ1Restriction_diracZeroLaw : ShellLawJ1Restriction d (diracZeroLaw d) where
  restriction_range_dependence n U V hU hV _ := by
    rw [shellMarginalLaw_diracZeroLaw]
    exact SuperdiffusionCLT.Probability.indep_dirac
      (ShellField.shellRestrictionSigma_le U hU)
      (ShellField.shellRestrictionSigma_le V hV) (ShellField.zero d)

end

end SuperdiffusionCLT.Assumptions.ShellLaw
