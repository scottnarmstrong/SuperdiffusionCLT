/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayC
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT2Centring
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import Homogenization.Book.Ch04.Theorems.StationaryExpectations

/-!
# Signed centring of the localization perturbation

The mean in the proof of `l.localization.average` concerns the signed quadratic form,
not the operator norm. Stationarity identifies the expected coarse matrix on
any cube of scale `n ≥ 0` with the annealed matrix on the origin cube.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory

variable {d : ℕ} {nu : ℝ}

/-- Stationarity identifies the expectation on a cube with the origin-cube mean. -/
theorem displayL_integral_coarse_entry [NeZero d] (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (a b : Homogenization.BlockCoord d) :
    (∫ omega, Homogenization.toFullBlockMat
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField)
      a b ∂P.toMeasure) =
    Homogenization.toFullBlockMat
      (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) a b := by
  have htransfer (Q : Homogenization.TriadicCube d) :=
    SuperdiffusionCLT.Section2.Annealed.integral_cutoffLaw (nu := nu) l P
      (fun c => Homogenization.blockMatEntry
        (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q) c.toFun) a b)
      (SuperdiffusionCLT.Section2.Annealed.aemeasurable_blockMatEntry_cutoffLaw
        hnu l P Q a b).aestronglyMeasurable
  have hs := Homogenization.Book.Ch04.RestrictionLawCarrier.integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_stationary
      (SuperdiffusionCLT.Section2.Annealed.restrictionLawCarrier_cutoffLaw hnu l P)
      (SuperdiffusionCLT.Section2.Annealed.restrictionStationaryLaw_cutoffLaw
        hPrefix hJ2 nu l) R (by rw [hR]; exact Int.natCast_nonneg n) a b
  rw [htransfer R, htransfer (Homogenization.originCube d R.scale), hR] at hs
  have hmean : Homogenization.toFullBlockMat
      (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) a b =
      ∫ omega, Homogenization.toFullBlockMat
        (Homogenization.coarseBlockMatrix
          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField)
        a b ∂P.toMeasure := by
    cases a <;> cases b <;> rfl
  rw [hmean]
  exact hs

/-- Integrability of each signed perturbation entry, without a centring premise. -/
theorem displayL_integrable_perturbation_entry [NeZero d] (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (a b : Homogenization.BlockCoord d) :
    Integrable (fun omega => Homogenization.toFullBlockMat
      (localizationPerturbationMatrix nu l P n R omega) a b) P.toMeasure := by
  have hi := SuperdiffusionCLT.Section2.Annealed.integrable_blockMatEntry_coarseBlockMatrix
    hnu l R hPrefix hJ2 hJ3 hJ4 a b
  simp only [localizationPerturbationMatrix, Homogenization.toFullBlockMat_ofFullBlockMat,
    Matrix.sub_apply]
  exact MeasureTheory.Integrable.sub' hi (integrable_const
      (Homogenization.toFullBlockMat
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) a b))

/-- The correct unconditional centring: every signed perturbation entry has mean zero. -/
theorem displayL_integral_perturbation_entry_zero [NeZero d] (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
    (l n : ℕ) (R : Homogenization.TriadicCube d) (hR : R.scale = (n : ℤ))
    (a b : Homogenization.BlockCoord d) :
    ∫ omega, Homogenization.toFullBlockMat
      (localizationPerturbationMatrix nu l P n R omega) a b ∂P.toMeasure = 0 := by
  simp only [localizationPerturbationMatrix, Homogenization.toFullBlockMat_ofFullBlockMat,
    Matrix.sub_apply]
  have hi : Integrable (fun omega => Homogenization.toFullBlockMat
      (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField)
      a b) P.toMeasure :=
    SuperdiffusionCLT.Section2.Annealed.integrable_blockMatEntry_coarseBlockMatrix
      hnu l R hPrefix hJ2 hJ3 hJ4 a b
  rw [MeasureTheory.integral_sub hi (integrable_const _)]
  rw [displayL_integral_coarse_entry hnu P hPrefix hJ2 l n R hR a b]
  simp only [MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul, sub_self]

/-- The gauge entries read only upper shells, including when the increment is empty. -/
theorem displayL_stronglyMeasurable_gauge_entry (l L : ℕ)
    (R : Homogenization.TriadicCube d) (v : Homogenization.BlockVec d)
    (a : Homogenization.BlockCoord d) :
    StronglyMeasurable[SuperdiffusionCLT.Probability.shellSigma
      (localizationUpperShells l)]
      (fun omega => Homogenization.toFullBlockVec (localizationGaugeVector l L R v omega) a) := by
  let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
    SuperdiffusionCLT.Probability.shellSigma (localizationUpperShells l)
  have hi : Measurable (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L) := by
    unfold SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
    refine Finset.measurable_sum _ fun k hk => ?_
    exact SuperdiffusionCLT.Frozen.Assumptions.ShellField.measurable_forgetShell.comp
      (shellSigma_coordinate_measurable (S := localizationUpperShells l)
        (Finset.mem_Ioc.mp hk).1)
  have havg := SuperdiffusionCLT.Section2.Cutoff.measurable_volumeAverageMat_of_isBounded
    (Homogenization.isBounded_cubeSet R) (Homogenization.measurableSet_cubeSet R) hi
  have hm (i j : Fin d) : Measurable (fun omega =>
      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
        (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x)) i j) :=
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp havg)).neg
  cases a with
  | inl i =>
    change StronglyMeasurable (fun _ : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      Homogenization.matVecMul (1 : Homogenization.Mat d) v.1 i +
        Homogenization.matVecMul (0 : Homogenization.Mat d) v.2 i)
    exact stronglyMeasurable_const
  | inr i =>
    change StronglyMeasurable (fun omega =>
      Homogenization.matVecMul
        (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
          (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x))
        v.1 i + Homogenization.matVecMul (1 : Homogenization.Mat d) v.2 i)
    apply Measurable.stronglyMeasurable
    apply Measurable.add _ measurable_const
    exact Finset.measurable_sum _ fun j _ => (hm i j).mul measurable_const

end SuperdiffusionCLT.Section2.Localization
