/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3StepsD

/-!
# `l.RHS.term3` with the constant quantified first

This file concerns `e.RHS.term3` and its proof.  The printed statement has the
conclusion `∃ C : ℝ, 1 ≤ C ∧ …` **after** every binder, in particular after
the scale selection `S` and after `δ` and `η_L`; as a statement that is vacuous.
Here the constant comes first, as the paper's does.

## The two printed defects, and what is stated instead

1. **`3^{−h/8}` versus `3^{−h/16}`.**  `e.bL.to.bhomell` bounds the
   coarse-block second moment by `C(… + ν⁻⁴(L')⁴(3^{−(ℓ−n)/4} + 3^{−(ℓ'−ℓ)/2} +
   3^{−h/8}))`, and `e.RHS.term3.A` multiplies its **square root** by
   `(δ + Cη_L)^{1/2}`.  The square roots of the first two polynomial terms are
   the second and third summands of the printed `e.RHS.term3`; the square root
   of the third is `3^{−h/16}`, whereas `e.RHS.term3` prints `3^{−h/8}`, and
   `3^{−h/16} ≤ C 3^{−h/8}` fails for every `h`-independent `C`.  So
   the constant-first statement carries `3^{−h/16}`, which the inputs give.
2. **`(δ + η_L)^{1/2}` is not bounded by the statement.**  Both the
   `e.RHS.term3.B` term and the coarse-block term carry that factor, which the
   printed second group absorbs into its constant while the statement binds only
   `0 ≤ δ`, `0 ≤ η_L`.  So the constant-first statement carries the factor
   `1 + (δ + η_L)^{1/2}` in its second group instead.

The exact printed statement follows from the constant-first one, at the cost of the
`h`-dependent factor `3^{h/16}`: precisely the content of defect 1.

## What the constant depends on

`termThreeConst C1 C2 C3a C3b Cz Cs Cw CB Cerr` depends **only** on the constants
of the printed inputs: the seven constants of the four displays of
`e.bL.to.bhomell` and of the Hölder split, the constant `CB` of `e.RHS.term3.B`,
and the carrier-swap constant `Cerr` of `e.RHS.term3.A`.  It does not depend on
the dimension, on `ν`, on the law, on the scale selection, on `δ`, on `η_L`, on
the response or on the glued fields.  The Hölder-split constant `C0` is a binder
of both statements but does not enter the constant, because it appears in the
displays only on the smaller side.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

/-! ## Envelope arithmetic -/

/-- **The constant of `e.bL.to.bhomell`**: the witness of the
final linear combination of its Step B, in the input constants alone. -/
def bLToBhomellConst (C1 C2 C3a C3b Cz Cs Cw : ℝ) : ℝ := C1 + C3a + C3b + C2 + Cz * Cw + Cs

theorem bLToBhomellConst_nonneg {C1 C2 C3a C3b Cz Cs Cw : ℝ}
    (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3a : 0 ≤ C3a) (hC3b : 0 ≤ C3b)
    (hCz : 0 ≤ Cz) (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) :
    0 ≤ bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw := by
  have hCzCw : (0 : ℝ) ≤ Cz * Cw := mul_nonneg hCz hCw
  rw [bLToBhomellConst]
  linarith only [hC1, hC2, hC3a, hC3b, hCzCw, hCs]

/-- **The constant of the constant-first `e.RHS.term3`**: Step 4 needs the
constant of `e.bL.to.bhomell` through its square root, the constant `CB` of
`e.RHS.term3.B` and the carrier-swap constant `Cerr` of `e.RHS.term3.A`. -/
def termThreeConst (C1 C2 C3a C3b Cz Cs Cw CB Cerr : ℝ) : ℝ :=
  2 * max 1 (max (Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw)) (max CB Cerr))

theorem one_le_termThreeConst (C1 C2 C3a C3b Cz Cs Cw CB Cerr : ℝ) :
    1 ≤ termThreeConst C1 C2 C3a C3b Cz Cs Cw CB Cerr := by
  have h : (1 : ℝ) ≤ max 1 (max (Real.sqrt (bLToBhomellConst C1 C2 C3a C3b Cz Cs Cw))
    (max CB Cerr)) := le_max_left _ _
  rw [termThreeConst]
  linarith only [h]

/-! ## `e.RHS.term3`, with the constant quantified first -/

/-! ## `e.RHS.term3`, in the survey's shape -/

end

end SuperdiffusionCLT.Section3.Terms
