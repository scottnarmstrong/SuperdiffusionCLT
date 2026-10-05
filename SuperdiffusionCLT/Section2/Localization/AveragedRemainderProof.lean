/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3AveragedClose
public import SuperdiffusionCLT.Section2.Localization.Conj3BridgeIdentity
public import SuperdiffusionCLT.Section2.Localization.SkewRemainderVariational

/-!
# The route's doubled fields at the cutoff pair

This module records the two doubled fields of the averaged conjunct-3 route: the level-`m`
doubled field at the forward maximizer `v`, and the centered-pair doubled field at the
forward maximizer `u`. Both are the forward doubled field of a coefficient bundle at the
loading `(p, q)`.

## Main definitions

* `routeDoubledFieldM`: the route's level-`m` doubled field.
* `routeDoubledFieldL`: the route's centered-pair doubled field.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- The route's level-`m` doubled field, at the forward maximizer `v`. -/
abbrev routeDoubledFieldM (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m : ℕ) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d))) :
    Book.Ch02.DoubledField d :=
  forwardDoubledField U (levelMCoeffOn U nu hnu omega m) p q v

/-- The route's centered-pair doubled field, at the forward maximizer `u`. -/
abbrev routeDoubledFieldL (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu)
    (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d))) (U : Set (Vec d))) :
    Book.Ch02.DoubledField d :=
  forwardDoubledField U (centeredPairCoeffOn U nu hnu omega m L hmL) p q u

end

end SuperdiffusionCLT.Section2.Localization
