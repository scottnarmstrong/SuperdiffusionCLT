/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Section3.HighContrast.RangeDependence

/-!
# The restriction-lane form of (J1)

`SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction` is the restriction-lane
form of (J1): the shell `j_n` has range of dependence `3^n sqrt d` for the
pointwise-restriction sigma-fields. This module records the two bridges that place
it in the existing lane API:

* it is definitionally the predicate `ShellRestrictionRangeDependence` of
  `SuperdiffusionCLT.Section3.HighContrast.RangeDependence`, so every consequence
  proved from that predicate is a consequence of this assumption; and
* it implies the integral-lane assumption `ShellLawJ1`, so it is the stronger of the two.

Together with `cutoffRangeDependence_of_shellRestrictionRangeDependence` the
first bridge gives the obligation `CutoffRangeDependence` of `StructuralLaw`
directly from the restriction-lane assumption.

## Main results

* `shellLawJ1Restriction_iff_shellRestrictionRangeDependence`: the two-way bridge.
* `shellLawJ1_of_shellLawJ1Restriction`: the restriction-lane form implies `ShellLawJ1`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff

variable {d : ℕ}

/-- **The two-way bridge.** The restriction-lane (J1) is the predicate
`ShellRestrictionRangeDependence`; the structure carries exactly that one
field. -/
theorem shellLawJ1Restriction_iff_shellRestrictionRangeDependence
    (P : ProbabilityMeasure (ShellSeq d)) :
    ShellLawJ1Restriction d P ↔ ShellRestrictionRangeDependence d P :=
  ⟨fun h => h.restriction_range_dependence, fun h => ⟨h⟩⟩

/-- **The restriction-lane form implies `ShellLawJ1`.** The integral lane is below the
restriction lane, so independence of the restriction lanes of two separated
sets gives independence of their integral lanes. -/
theorem shellLawJ1_of_shellLawJ1Restriction {P : ProbabilityMeasure (ShellSeq d)}
    (h : ShellLawJ1Restriction d P) : ShellLawJ1 d P :=
  shellLawJ1_of_shellRestrictionRangeDependence
    ((shellLawJ1Restriction_iff_shellRestrictionRangeDependence P).1 h)

end SuperdiffusionCLT.Section3.HighContrast
