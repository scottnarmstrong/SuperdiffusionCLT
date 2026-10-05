/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02.Theorems.DoubledMu
public import Homogenization.CoarseGraining.AdjointSymmetry.BasicAdjoint

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Public Chapter 1 zero normal trace is closed under negation. -/
theorem solenoidalZeroNormalTraceFieldOn_neg
    {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : Book.Ch01.SolenoidalZeroNormalTraceFieldOn U g) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn U (-g) := by
  refine ⟨?_, ?_⟩
  · exact hg.1.neg
  · intro φ
    have hfun :
        (fun x => vecDot ((-g) x) (φ.grad x)) =
          (fun x => -vecDot (g x) (φ.grad x)) := by
      funext x
      simp [vecDot]
    rw [hfun, integral_neg, hg.2 φ]
    simp

/-- Flip the flux component of a public doubled field. -/
def doubledFieldFlipFlux (X : Book.Ch02.DoubledField d) :
    Book.Ch02.DoubledField d :=
  { potential := X.potential
    flux := -X.flux }

@[simp] theorem doubledFieldFlipFlux_eval
    (X : Book.Ch02.DoubledField d) (x : Vec d) :
    (doubledFieldFlipFlux X).eval x = blockVecFlipFlux (X.eval x) :=
  rfl

@[simp] theorem doubledFieldFlipFlux_flipFlux
    (X : Book.Ch02.DoubledField d) :
    doubledFieldFlipFlux (doubledFieldFlipFlux X) = X := by
  cases X
  simp [doubledFieldFlipFlux]

/-- Flipping the flux carries public doubled admissibility to the adjoint loading. -/
theorem isDoubledMuAdmissible_flipFlux
    {U : Book.Ch02.Domain d} {P : BlockVec d}
    {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuAdmissible U P X) :
    Book.Ch02.IsDoubledMuAdmissible U (blockVecFlipFlux P)
      (doubledFieldFlipFlux X) := by
  refine ⟨?_, ?_⟩
  · simpa [doubledFieldFlipFlux, blockVecFlipFlux] using hX.1
  · have hneg := solenoidalZeroNormalTraceFieldOn_neg hX.2
    convert hneg using 1
    funext x
    simp [doubledFieldFlipFlux, blockVecFlipFlux, sub_eq_add_neg, add_comm]

/-- The public doubled energy is invariant under coefficient transposition and the
flux flip. -/
theorem doubledMuValue_transpose_flipFlux
    {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (X : Book.Ch02.DoubledField d) :
    Book.Ch02.doubledMuValue U a.transpose (doubledFieldFlipFlux X) =
      Book.Ch02.doubledMuValue U a X := by
  unfold Book.Ch02.doubledMuValue Book.Ch02.average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [Book.Ch02.blockEnergyDensityAt, doubledFieldFlipFlux_eval,
    Homogenization.Internal.Ch02.BookCh02.book_blockMatrixField_eq_blockCoeffField,
    Book.Ch02.CoeffOn.transpose_apply, Homogenization.blockCoeffField]
  exact
    (Homogenization.blockEnergyDensity_matTranspose_flipFlux
      (a := a.toCoeffField) (X :=
        Homogenization.Internal.Ch02.BookCh02.blockStateOfDoubled X) (x := x))

/-- A public doubled-`mu` minimizer is carried to the adjoint loading by the
flux flip. -/
theorem isDoubledMuMinimizer_flipFlux
    {U : Book.Ch02.Domain d} {a : Book.Ch02.CoeffOn U}
    {P : BlockVec d} {X : Book.Ch02.DoubledField d}
    (hX : Book.Ch02.IsDoubledMuMinimizer U a P X) :
    Book.Ch02.IsDoubledMuMinimizer U a.transpose (blockVecFlipFlux P)
      (doubledFieldFlipFlux X) := by
  refine ⟨isDoubledMuAdmissible_flipFlux hX.1, ?_⟩
  intro Y hY
  have hYunflip := isDoubledMuAdmissible_flipFlux (U := U)
    (P := blockVecFlipFlux P) (X := Y) hY
  have hmin := hX.2 (doubledFieldFlipFlux Y) (by
    simpa [doubledFieldFlipFlux_flipFlux] using hYunflip)
  calc
    Book.Ch02.doubledMuValue U a.transpose (doubledFieldFlipFlux X) =
        Book.Ch02.doubledMuValue U a X := doubledMuValue_transpose_flipFlux a X
    _ ≤ Book.Ch02.doubledMuValue U a (doubledFieldFlipFlux Y) := hmin
    _ = Book.Ch02.doubledMuValue U a.transpose Y :=
      by
        simpa only [doubledFieldFlipFlux_flipFlux] using
          (doubledMuValue_transpose_flipFlux a (doubledFieldFlipFlux Y)).symm

end
end SuperdiffusionCLT.Section2.Localization
