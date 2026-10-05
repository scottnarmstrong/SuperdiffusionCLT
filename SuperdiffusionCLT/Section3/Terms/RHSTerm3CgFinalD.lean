/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm3CgFinalC
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3Energy

/-!
# Coarse-block bound with unrestricted error summands

The conclusion is `e.RHS.term3.A`. The separate
error-sign assumptions are unnecessary because the pigeon estimate controls
their sum. The fourth-moment observable in the Poincaré step of its proof
is measurable and integrable; its quantitative bound remains the
constant comparison in the final theorem.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The fourth-power cube-mean difference in the coarse Poincaré carrier is
integrable. Its defining expectation therefore has its ordinary finite meaning. -/
theorem cgFinalD_integrable_fourth_difference {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) {e : Homogenization.Vec d} (he : Homogenization.vecNormSq e = 1)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega))
    (q : (_ : Homogenization.TriadicCube d) × Homogenization.TriadicCube d)
    (hq : q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m) :
    MeasureTheory.Integrable (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      Homogenization.vecNormSq (Homogenization.volumeAverageVec (Homogenization.openCubeSet q.2) ((w omega).toH1Function.grad) -
        Homogenization.volumeAverageVec (Homogenization.openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ))
      P.toMeasure := by
  have hmem : MeasureTheory.MemLp (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      Homogenization.vecNormSq (Homogenization.volumeAverageVec (Homogenization.openCubeSet q.2) ((w omega).toH1Function.grad) -
        Homogenization.volumeAverageVec (Homogenization.openCubeSet q.1) ((w omega).toH1Function.grad))) 2 P.toMeasure := by
    convert memLp_two_vecNormSq_cubeMeanDiff_coarsePairs_discharged
      hd hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder he w hw q hq using 1
    norm_num
  have h := hmem.integrable_mul hmem
  simp only [Real.rpow_two, pow_two]
  exact h

/-- The finite coarse-pair average commutes with the expectation without an
extra integrability assumption. -/
theorem cgFinalD_poincareCarrier_eq_integral {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    {nu : ℝ} (hnu : 0 < nu) (hnu1 : nu ≤ 1) {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P) (hJ1V2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P) (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P) (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection)
    (hSorder : SuperdiffusionCLT.Section3.Setup.ScalesOrdering S) {e : Homogenization.Vec d} (he : Homogenization.vecNormSq e = 1)
    (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (S.m : ℤ))))
    (hw : ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      SuperdiffusionCLT.Section3.Setup.IsDirichletResponse omega S.LPrime S.ellPrime S.m
        (SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e) (w omega)) :
    cgPoincareCarrier d P S w = ∫ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
      ((coarsePairs d S.n (coarseBlockScale d S) S.m).card : ℝ)⁻¹ *
        ∑ q ∈ coarsePairs d S.n (coarseBlockScale d S) S.m,
          Homogenization.vecNormSq (Homogenization.volumeAverageVec (Homogenization.openCubeSet q.2) ((w omega).toH1Function.grad) -
            Homogenization.volumeAverageVec (Homogenization.openCubeSet q.1) ((w omega).toH1Function.grad)) ^ (2 : ℝ)
        ∂P.toMeasure := by
  rw [cgPoincareCarrier, MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _
    (fun q hq => cgFinalD_integrable_fourth_difference hd hnu hnu1 hPrefix hJ1V2 hJ2
      hJ3 hJ4 S hSorder he w hw q hq)]

end

end SuperdiffusionCLT.Section3.Terms
