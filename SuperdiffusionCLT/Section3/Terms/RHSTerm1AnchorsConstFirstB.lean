/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1AnchorsConstFirst

/-!
# `l.RHS.term1` from the anchors, with the constant quantified first

The statement is `e.RHS.term1` of the paper.
The anchors form of the statement takes the section data as top-level
binders and only then concludes `∃ C, 1 ≤ C ∧ …`; with the data fixed that says
nothing about uniformity.  Here the constant comes
first, as in `RegboundsWindowB.l_RHS_term4_of_window`.

Here: the `Ĥ̲^{-1}` display of Step 2 and the closing coarsening of Step 3, as explicit
constants.  Every constant depends only on `d`, on the
localization constant `Cloc`, on the concentration constant `Cc` and on the
constant of `e.nablaw.Lt`.  The window factor `√(1 + 2h)` is
not absorbed into a constant: it is carried through Step 2 and paid for in the
closing coarsening, where `h ≤ 2ℓ` makes it free.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

/-! ## The `Ĥ̲^{-1}` display of Step 2, at a named constant -/

/-- **The constant of the third display of Step 2**: the multiscale constant of
the order-one carrier, the concentration constant `Cc` and the `L̲²` constant. -/
def hminusSecondMomentConstFirst (d : ℕ) (Cc : ℝ) : ℝ :=
  max 1 (12 * multiscaleOrderOneConst d ^ (2 : ℕ) * Cc * hminusL2Const d)

theorem one_le_hminusSecondMomentConstFirst (d : ℕ) (Cc : ℝ) :
    1 ≤ hminusSecondMomentConstFirst d Cc := le_max_left _ _

/-! ## `e.decompose.flux.u.n.second` at a named constant -/

/-! ## The closing coarsening of Step 3 -/

/-! ## `e.RHS.term1` from the anchors, with the constant quantified first -/

/-- The constant of `e.decompose.flux.u.n.first`. -/
def stepOneConstFirst (d : ℕ) (Cloc Creg : ℝ) : ℝ :=
  Real.sqrt (8 * (gradWL2ConstFirst Creg * fluxL2ConstFirst d Cloc))

theorem one_le_stepOneConstFirst (d : ℕ) (Cloc Creg : ℝ) :
    1 ≤ stepOneConstFirst d Cloc Creg := by
  have h3 : (1 : ℝ) ≤ gradWL2ConstFirst Creg := one_le_gradWL2ConstFirst Creg
  have h0 : (1 : ℝ) ≤ fluxL2ConstFirst d Cloc := one_le_fluxL2ConstFirst d Cloc
  have h30 : (0 : ℝ) ≤ gradWL2ConstFirst Creg := le_trans zero_le_one h3
  have h8 : (1 : ℝ) ≤ 8 * (gradWL2ConstFirst Creg * fluxL2ConstFirst d Cloc) := by
    nlinarith only [h3, h0, h30]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (8 * (gradWL2ConstFirst Creg * fluxL2ConstFirst d Cloc)) :=
        Real.sqrt_le_sqrt h8

/-- The constant of `e.decompose.flux.u.n.second`. -/
def stepTwoConstFirst (d : ℕ) (Cc Creg : ℝ) : ℝ :=
  Real.sqrt (h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg *
    hminusSecondMomentConstFirst d Cc)

theorem one_le_stepTwoConstFirst (d : ℕ) (Cc Creg : ℝ) :
    1 ≤ stepTwoConstFirst d Cc Creg := by
  have h4 : (1 : ℝ) ≤ h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg :=
    one_le_h1SecondMomentConstFirst _ _
  have h5 : (1 : ℝ) ≤ hminusSecondMomentConstFirst d Cc :=
    one_le_hminusSecondMomentConstFirst d Cc
  have h40 : (0 : ℝ) ≤ h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg :=
    le_trans zero_le_one h4
  have hprod : (1 : ℝ) ≤ h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg *
      hminusSecondMomentConstFirst d Cc := by nlinarith only [h4, h5, h40]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (h1SecondMomentConstFirst (gradWL2ConstFirst Creg) Creg *
          hminusSecondMomentConstFirst d Cc) := Real.sqrt_le_sqrt hprod

/-- **The constant of `e.RHS.term1`** read off the anchors: it depends on the
dimension, on the localization constant `Cloc`, on the concentration constant
`Cc` and on the constant `Creg` of `e.nablaw.Lt`, and on nothing else. -/
def termOneAnchorsConst (d : ℕ) (Cloc Cc Creg : ℝ) : ℝ :=
  max 1 (max (stepOneConstFirst d Cloc Creg) (16 * stepTwoConstFirst d Cc Creg))

end

end SuperdiffusionCLT.Section3.Terms
