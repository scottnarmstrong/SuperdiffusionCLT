/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatioE
public import SuperdiffusionCLT.Section5.Coupled.EstimateF

/-!
# `cor.lower.ratio`: the test field `e' = 0`

With `e' = 0` the flux `shom^{-1} hshell e'` vanishes, the Neumann response is `0`, and the slope of
the principal term is the slope of `lem.coupled.input`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)

variable {d : ℕ}

theorem lowerRatio_hshellFlux_zero [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (ω : ShellSeq d) (y : Vec d) :
    hshellFlux nu P m h ω 0 y = 0 := by
  funext i
  simp [hshellFlux, matVecMul]

theorem lowerRatio_neumann_zero [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (ω : ShellSeq d)
    (Q : TriadicCube d) :
    SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse Q
      (hshellFlux nu P m h ω 0) (0 : H1MeanZeroFunction (openCubeSet Q)) := by
  intro φ
  simp [lowerRatio_hshellFlux_zero, vecDot]

theorem lowerRatio_unit_vector [NeZero d] : ∃ e : Vec d, vecNormSq e = 1 := by
  refine ⟨Pi.single 0 1, ?_⟩
  simp [vecNormSq, vecDot, Pi.single_apply]

/-- The slope of the principal term at `e' = 0` is that of `lem.coupled.input`. -/
theorem lowerRatio_len_eq [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)) (m h : ℕ) (Q : TriadicCube d)
    (ω : ShellSeq d) (e : Vec d) (gD gN : Vec d → Vec d) (hgN : ∀ y, gN y = 0) :
    blockLenSq (ahomSqrtApply nu (m - h) P
      (principalPhat m h Q ω (blockSlope nu (m - h) P Q e 0 gD gN))) =
    blockVecDot (coupledVec nu P m h Q ω e gD) (coupledVec nu P m h Q ω e gD) := by
  have : gN = fun _ => 0 := funext hgN
  subst this
  rfl

end SuperdiffusionCLT.Section5
