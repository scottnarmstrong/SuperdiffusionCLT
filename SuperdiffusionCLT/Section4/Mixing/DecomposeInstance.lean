/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.GaugeAlgebra
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff

/-!
# The add-and-subtract decomposition `e.decompose.AL.minus.Aell`

This is the decomposition in the proof of
Proposition `p.mixing.P.three.prime`. This file records the algebraic
add-and-subtract identity in the block bilinear-form carrier used throughout
`Frozen.Section4.mixing_below_cutoff`, then instantiates it with the random
block coarse field at cutoff `L`, the descendant triadic cubes of `cu_m` at
depth `m - n` (realizing `z ∈ 3^n ℤ^d ∩ cu_m`), and the gauge-conjugated
`ℓ`-cutoff annealed matrix.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02

variable {d : ℕ}

/-- The bilinear value of a block-matrix difference, at a fixed pair `(p, q)`,
splits as the difference of the two bilinear values. Bilinear (two-vector)
form of `Homogenization.blockVecDot_blockMatVecMul_ofFullBlockMat_sub`. -/
theorem mixTerms_blockVecDot_ofFullBlockMat_sub_bilinear
    (A B : BlockMat d) (p q : BlockVec d) :
    blockVecDot p (blockMatVecMul (ofFullBlockMat (toFullBlockMat A - toFullBlockMat B)) q) =
      blockVecDot p (blockMatVecMul A q) - blockVecDot p (blockMatVecMul B q) := by
  rw [blockMatVecMul_ofFullBlockMat_sub, blockVecDot_sub_right]

end SuperdiffusionCLT.Section4.Mixing
