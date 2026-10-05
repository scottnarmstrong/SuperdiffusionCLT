/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.MinimalScale.GridMaxEnlarge
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputs
public import SuperdiffusionCLT.Section7.MinimalScale.TranslatedInputsB

/-!
# Constants of the anchor shapes of the translated sharp-scale inputs

This file records the nonnegativity of the constant `b2c_C1`, which enters the logarithmic
enlargement `b2c_enl` of the scale used to bring the translated sharp-scale inputs of
`Frozen.Section6.sharp_scale_inputs` to their anchor shapes.
-/

@[expose] public section

open scoped ENNReal
open scoped Matrix.Norms.L2Operator

namespace SuperdiffusionCLT.Section7

open MeasureTheory

theorem b2c_C1_nonneg (N : ℝ) (hN : 0 ≤ N) (b : ℕ) : 0 ≤ b2c_C1 N b := by
  unfold b2c_C1
  have : 0 ≤ Real.log (1 + (b : ℝ)) :=
    Real.log_nonneg (by linarith only [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])
  nlinarith only [this, hN]

end SuperdiffusionCLT.Section7
