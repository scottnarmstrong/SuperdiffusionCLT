/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.HarmonicityTransferFace

/-!
# The odd reflection on the §4.3 windows: the one-met-face transfer

The abstract single-face transfer of `HarmonicityTransferFace.lean` is stated
for an arbitrary reflection-symmetric open bounded convex domain.

## Main results

* `h1FunctionOfSetEq` — transport of an `H¹` function along an equality of its domain, with
  `h1FunctionOfSetEq_grad` recording that the gradient is unchanged.

The geometry of the reflected window and the single-face transfer itself are not part of this
module.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization SuperdiffusionCLT.Section8.Common.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Transporting an `H¹` datum along an equality of domains -/

/-- Transport of an `H¹` function along an equality of its domain. -/
def h1FunctionOfSetEq {U V : Set (Vec d)} (h : U = V) (u : H1Function U) : H1Function V :=
  h ▸ u

@[simp] theorem h1FunctionOfSetEq_grad {U V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (h1FunctionOfSetEq h u).grad = u.grad := by
  subst h
  rfl

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
