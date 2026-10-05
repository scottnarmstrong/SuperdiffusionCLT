/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.BlockGauge

/-!
# The group law of the block gauge

The manuscript defines the block gauge matrix `G_h` of `e.G`

`G_h = (Id 0 ; h Id)`,   `G_h : 2d x 2d`,

and records at `e.G.group` the multiplication law

`G_{h_1} G_{h_2} = G_{h_1 + h_2}`,

from which it reads off `G_0 = I` and the two-sided inverse `G_{-h}`. These are the
properties of `G_h` used by the localization argument of subsection
`ss.localization`: the factorization `e.bfG.factoring` of
`bfA_j` in the gauge of `κ_j` is what makes adding a constant
anti-symmetric matrix to the coefficient field a mere conjugation by `G_{-k_0}`,
as in display `e.commute.coarse.grained.k0`.

The gauge type is `Homogenization.Book.Ch02.blockG : Mat d -> BlockMat d`
on block matrices over `Homogenization.Vec d`. The multiplication law is already
proved in `SuperdiffusionCLT.Section2.Localization.BlockGauge` as
`blockG_mul_blockG`; this module records the full package `e.G.group` on that
type, forwarding the multiplication law to the existing lemma and deriving the
two-sided inverse and the identity by block multiplication.

## Main results

* the multiplication law `e.G.group` itself is `blockG_mul_blockG` of
  `Section2/Localization/BlockGauge.lean`; this module adds the identity and
  inverse laws.
* `blockG_mul_neg`, `blockG_neg_mul`: `G_h G_{-h} = G_{-h} G_h = I` in the
  block multiplication `blockMatMul`.
* `blockG_zero`: `G_0 = I`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The inverse laws in multiplication form -/

/-- The gauge with parameter `-h` is a right inverse of the gauge with
parameter `h`: `G_h G_{-h} = I_{2d}`, proved by block multiplication. -/
theorem blockG_mul_neg (h : Mat d) :
    blockMatMul (blockG h) (blockG (-h)) = blockIdentity d := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp [blockMatMul, blockG, blockIdentity, blockDiag]

/-- The gauge with parameter `-h` is a left inverse of the gauge with
parameter `h`: `G_{-h} G_h = I_{2d}`, proved by block multiplication. -/
theorem blockG_neg_mul (h : Mat d) :
    blockMatMul (blockG (-h)) (blockG h) = blockIdentity d := by
  refine blockMat_ext ?_ ?_ ?_ ?_ <;>
    simp [blockMatMul, blockG, blockIdentity, blockDiag]

/-- The gauge of the zero matrix is the block identity: `G_0 = I_{2d}`. -/
theorem blockG_zero : blockG (0 : Mat d) = blockIdentity d := by
  rfl

/-! ## The inverse through the public block inverse -/

end

end SuperdiffusionCLT.Section2.Localization