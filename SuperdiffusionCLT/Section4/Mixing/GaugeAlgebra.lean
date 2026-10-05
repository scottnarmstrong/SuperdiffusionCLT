/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.BlockGauge

/-!
# Gauge algebra for mixing below the cutoff

This file records the block-matrix conjugation identity used for the second
term in the proof of `p.mixing.P.three.prime`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02

variable {d : ℕ}

/-- Conjugating a scalar block diagonal matrix by `G_{-h}` adds the quadratic
`t hᵀh` term to the upper-left block and the two linear off-diagonal terms.
This is the exact algebraic display used in the second-term estimate. -/
theorem mixBelow_gaugeBlockConjugation (h : Mat d) (s t : ℝ) :
    blockMatMul (blockMatTranspose (blockG (-h)))
      (blockMatMul (blockDiag (s • (1 : Mat d)) (t • (1 : Mat d)))
        (blockG (-h))) =
      { upperLeft := s • (1 : Mat d) + t • (matTranspose h * h)
        upperRight := -(t • matTranspose h)
        lowerLeft := -(t • h)
        lowerRight := t • (1 : Mat d) } := by
  refine blockMat_ext ?_ ?_ ?_ ?_
  all_goals
    ext i j
    simp [blockMatMul, blockMatTranspose, blockG, blockDiag, matTranspose,
      Matrix.mul_apply]

end SuperdiffusionCLT.Section4.Mixing
