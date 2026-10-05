/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Cutoff.StreamCutoffAPI

/-!
# The drift of the marginal infrared cutoff

This module defines the cutoff drift `f_L = ∇ · k_L`.

## Divergence convention

Throughout, the divergence of a matrix field `A` is the vector field with
`j`-th coordinate

`(∇ · A)_j = ∑_{i = 1}^{d} ∂_{x_i} A_{ij}`,

the convention printed in a footnote of the paper and used for the drift
`f = ∇ · k`. The summed index is the row index and the free index is the
column index.

No differentiability hypothesis is needed: each shell of the carrier stores its
own derivative, and `streamCutoffDeriv` is the sum of these stored derivatives.

## Main definitions

* `driftCutoff`: the cutoff drift `f_L = ∇ · k_L`.

-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Cutoff

open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The cutoff drift `f_L = ∇ · k_L` of the infrared cutoff, in the convention
`(∇ · A)_j = ∑_i ∂_{x_i} A_{ij}`. It is defined at every point of `Vec d`. -/
def driftCutoff (omega : ShellSeq d) (L : ℕ) : Vec d → Vec d :=
  fun x k ↦ ∑ i : Fin d, streamCutoffDeriv omega L x (Pi.single i 1) i k

end

end SuperdiffusionCLT.Section2.Cutoff
