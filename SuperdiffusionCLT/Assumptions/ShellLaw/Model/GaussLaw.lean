/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3H
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedIndepF
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedShellLawC
public import SuperdiffusionCLT.Assumptions.ShellLaw.Nonvacuity

/-!
# The Gaussian shell law

`nv_gaussLaw d` is the product over shells of the dilated seed shell laws, where the seed is the
Gaussian field of amplitude `nv_epsJ3 d`.  For `2 ≤ d` this law satisfies the shell-law prefix,
J1 version 2, J2, J3 and J4, and it is not the Dirac law at zero.

Certified here: every shell-law condition except J5, for a nonzero Gaussian law.
Not yet certified here: J5 (handled separately).

## Main results

* `nv_j3_seedShellLaw_eq`
* `nv_gaussLaw`
* `nv_gaussLaw_prefix`, `nv_gaussLaw_J1Restriction`, `nv_gaussLaw_J2`, `nv_gaussLaw_J3`, `nv_gaussLaw_J4`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

theorem nv_j3_seedShellLaw_eq (d : ℕ) (ε : ℝ) : nv_j3_seedShellLaw d ε = nv_seedShellLaw d ε :=
  ProbabilityMeasure.toMeasure_injective (by rw [nv_seedShellLaw_toMeasure]; rfl)

/-- The Gaussian shell law. -/
def nv_gaussLaw (d : ℕ) : ProbabilityMeasure (ℕ → ShellField d) :=
  nv_productLaw (nv_seedShellLaw d (nv_epsJ3 d))

theorem nv_gaussLaw_prefix (hd : 2 ≤ d) : ShellLawPrefix d (nv_gaussLaw d) :=
  nv_shellLawPrefix_productLaw hd _ (nv_seedShellLaw_map_translate d _)

theorem nv_gaussLaw_J1Restriction : ShellLawJ1Restriction d (nv_gaussLaw d) :=
  nv_shellLawJ1Restriction_seedProduct _

theorem nv_gaussLaw_J2 : ShellLawJ2 d (nv_gaussLaw d) :=
  nv_shellLawJ2_productLaw _

theorem nv_gaussLaw_J3 (hd : 0 < d) : ShellLawJ3 d (nv_gaussLaw d) :=
  nv_shellLawJ3_epsJ3 hd _ fun n ↦ by
    rw [nv_j3_seedShellLaw_eq]
    exact congrArg ProbabilityMeasure.toMeasure
      (nv_shellMarginalLaw_productLaw (nv_seedShellLaw d (nv_epsJ3 d)) n)

theorem nv_gaussLaw_J4 : ShellLawJ4 d (nv_gaussLaw d) :=
  nv_shellLawJ4_productLaw _ (fun R hR ↦ nv_seedShellLaw_map_rotate d _ R hR)
    (nv_seedShellLaw_map_negate d _)

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
