/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.AntisymmetricShift
public import SuperdiffusionCLT.Section8.DivergenceForm.PotentialWeakSolution
public import SuperdiffusionCLT.Section8.DivergenceForm.ScalarWeakSolution
public import SuperdiffusionCLT.Section8.Common.Regularity.Ported.ZerothOrderCarrier

/-!
# Freezing a constant skew part

A constant skew matrix has zero weak pairing against an `H¹` gradient and an
`H¹₀` test gradient. Consequently it may be subtracted from each weak
coefficient carrier used by the interior regularity argument.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.Regularity.Freezing

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section8.Common.ExcessDecay
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.ZeroTraceSobolev

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Subtracting a constant skew matrix preserves the scalar-plus-divergence
matrix weak equation. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_sub_skew_const_iff
    {a : CoeffField d} {k₀ : Mat d} (hk₀ : matTranspose k₀ = -k₀)
    {u : H1Function U} {g : Vec d → ℝ} {f : Vec d → Vec d} :
    IsMatrixDivFormWeakSolutionZerothOrderOn (fun x ↦ a x - k₀) U u g f ↔
      IsMatrixDivFormWeakSolutionZerothOrderOn a U u g f := by
  constructor
  · intro h φ
    rw [← integral_vecDot_matVecMul_sub_const_eq_of_skew a hk₀ u φ]
    exact h φ
  · intro h φ
    rw [integral_vecDot_matVecMul_sub_const_eq_of_skew a hk₀ u φ]
    exact h φ

/-- A scalar-forced weak solution for `a` is equivalently one for `a - k₀`
when `k₀` is constant and skew. -/
theorem isScalarForcedWeakSolution_sub_skew_const
    {a : CoeffField d} {k₀ : Mat d} (hk₀ : matTranspose k₀ = -k₀)
    {g : Vec d → ℝ} {u : H1Function U} :
    IsScalarForcedWeakSolution (fun x ↦ a x - k₀) U g u ↔
      IsScalarForcedWeakSolution a U g u := by
  constructor
  · rintro ⟨hg, h⟩
    refine ⟨hg, fun φ ↦ ?_⟩
    rw [← integral_vecDot_matVecMul_sub_const_eq_of_skew a hk₀ u φ]
    exact h φ
  · rintro ⟨hg, h⟩
    refine ⟨hg, fun φ ↦ ?_⟩
    rw [integral_vecDot_matVecMul_sub_const_eq_of_skew a hk₀ u φ]
    exact h φ

end

end SuperdiffusionCLT.Section8.Common.Regularity.Freezing
