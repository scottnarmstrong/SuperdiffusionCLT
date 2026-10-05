/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyApriori
public import SuperdiffusionCLT.Section2.Estimates.Stream.CenteredShellFluxBounds
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellValueLargeCube
public import SuperdiffusionCLT.Section3.ResponseFields.LpEstimates

/-!
# A pointwise bound on a vector field gives an `L̲^q` bound

`vecCubeLpENorm_le_ofReal_of_forall_le` is the deterministic pointwise-to-`L̲^q` step: a vector
field whose Euclidean magnitude is at most `c` at every point of the half-open cube has `L̲^q`
norm at most `c`, because the normalized cube measure is supported on the cube.  It is the
step used by the Poincare route of `ShellFluxWitnessesB.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ} {P : ProbabilityMeasure (ShellSeq d)}

/-- A vector field whose Euclidean magnitude is bounded by `c` at every point
of the half-open cube has `L̲^q` norm at most `c`, because the normalized cube
measure is supported on the cube. -/
theorem vecCubeLpENorm_le_ofReal_of_forall_le {Q : TriadicCube d} {q : ℝ≥0∞}
    {F : Vec d → Vec d} {c : ℝ} (_hc : 0 ≤ c)
    (hF : MeasureTheory.AEStronglyMeasurable (hilbertifyVecField F) (normalizedCubeMeasure Q))
    (h : ∀ x ∈ cubeSet Q, vecNorm (F x) ≤ c) :
    vecCubeLpENorm Q q F ≤ ENNReal.ofReal c := by
  have hae : ∀ᵐ x ∂normalizedCubeMeasure Q,
      ‖hilbertifyVecField F x‖ₑ ≤ ENNReal.ofReal c := by
    have hmem : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q :=
      MeasureTheory.Measure.ae_smul_measure
        (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet Q)) _
    refine hmem.mono fun x hx => ?_
    rw [← ofReal_norm, norm_hilbertifyVecField_apply]
    exact ENNReal.ofReal_le_ofReal (h x hx)
  have hbnd := MeasureTheory.eLpNorm_le_of_ae_enorm_bound
    (μ := normalizedCubeMeasure Q) (p := q) (f := hilbertifyVecField F) hF hae
  rw [normalizedCubeMeasure_apply_univ Q, ENNReal.one_rpow, smul_eq_mul, mul_one] at hbnd
  exact hbnd

end

end SuperdiffusionCLT.Section3.Setup