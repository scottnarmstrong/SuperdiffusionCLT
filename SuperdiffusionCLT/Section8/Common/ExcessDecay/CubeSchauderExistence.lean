/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.ScalarMatrix
public import Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
public import Homogenization.Sobolev.PotentialSolenoidalL2Realization
public import SuperdiffusionCLT.Section8.Common.Support.Dirichlet

/-!
# Cube Schauder, existence leg: the constant scalar background

The existence leg of the cube Schauder construction solves
```text
  -sigma Δ v = ∇ · g   in □_m ,      v = h   on ∂□_m
```
with CoarseGraining's Lax--Milgram Dirichlet existence theorem at the constant scalar background
`sigma • I`.  This module records the spelling lemmas for that background.

## Main results

* `matVecMul_smul_one`, `matVecMul_one` — `(c • I) x = c • x` and `I x = x`.
* `isEllipticFieldOn_smul_one` — the constant scalar background `sigma • I` is a
  `(sigma, sigma)`-elliptic field on any measurable set.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Estimates.Schauder

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section8.Common.Support
open Homogenization.PotentialSolenoidalL2Data

variable {d : ℕ}

/-! ## 1. The constant scalar background -/

/-- `(c • I) x = c • x`, at the exact spelling `c • (1 : Mat d)` used in the statement. -/
theorem matVecMul_smul_one (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x :=
  matVecMul_scalarMatrix c x

/-- `(1 : Mat d) x = x`. -/
theorem matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  have h := matVecMul_smul_one (1 : ℝ) x
  simpa using h

/-- The constant scalar background `sigma • I` is a `(sigma, sigma)`-elliptic
field on any measurable set. -/
theorem isEllipticFieldOn_smul_one {sigma : ℝ} (hsigma : 0 < sigma) {U : Set (Vec d)}
    (hU : MeasurableSet U) :
    IsEllipticFieldOn sigma sigma U (fun _ => sigma • (1 : Mat d)) :=
  isEllipticFieldOn_constantCoeffField hU (isEllipticMatrix_scalarMatrix hsigma)

section Pairing

variable {U : Set (Vec d)}

end Pairing

end SuperdiffusionCLT.Section8.Common.Estimates.Schauder
