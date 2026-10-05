/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.CompactOpen

/-!
# Marginal shell field

This file contains the carrier for one shell of the marginal
multiscale stream matrix.
-/

@[expose] public section

open scoped Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Frozen.Assumptions

/-- The smooth skew-matrix representative used for each marginal shell.

A shell stores a continuous value, first derivative,
and second derivative, with exact derivative compatibility and pointwise
skew-symmetry. -/
noncomputable def ShellField (d : ℕ) :=
  { p :
      ContinuousMap (Homogenization.Vec d) (Homogenization.Mat d) ×
        (ContinuousMap (Homogenization.Vec d)
            (Homogenization.Vec d →L[ℝ] Homogenization.Mat d) ×
          ContinuousMap (Homogenization.Vec d)
            (Homogenization.Vec d →L[ℝ]
              (Homogenization.Vec d →L[ℝ] Homogenization.Mat d))) //
    (∀ x, HasFDerivAt p.1 (p.2.1 x) x) ∧
      (∀ x, HasFDerivAt p.2.1 (p.2.2 x) x) ∧
      ∀ x i j, p.1 x i j = -p.1 x j i }

end SuperdiffusionCLT.Frozen.Assumptions
