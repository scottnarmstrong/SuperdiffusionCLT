/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingStepEAmplitudeB
public import SuperdiffusionCLT.Section3.Terms.CoarseBlockLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Localization.LocalizationDisplayC

/-!
# Spatial independence of the normalized localization perturbations

The proof of `l.localization.average` applies concentration separately on separated
sublattices. The family over all cubes in LocalizationAverageClose is not the
family asserted to be independent by that argument. Here locality is proved
for the actual perturbation, and J1V2 together with J2 gives independence on
any separated family. No independence of overlapping cubes is asserted.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory

variable {d : ℕ}

private theorem displayJ_full_mul (A B : Homogenization.BlockMat d) :
    Homogenization.toFullBlockMat (Homogenization.Book.Ch02.blockMatMul A B) =
      Homogenization.toFullBlockMat A * Homogenization.toFullBlockMat B := by
  ext i j
  cases i <;> cases j <;>
    simp only [Homogenization.toFullBlockMat, Homogenization.Book.Ch02.blockMatMul,
      Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type]

private theorem displayJ_measurable_mul {Ω : Type*} [MeasurableSpace Ω]
    {A B : Ω → Homogenization.FullBlockMat d} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun omega => A omega * B omega) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

/-- The entire coarse matrix is measurable in the spatial restriction lane. -/
theorem displayJ_measurable_coarse {nu : ℝ} (hnu : 0 < nu) (l : ℕ)
    (R : Homogenization.TriadicCube d) :
    Measurable[SuperdiffusionCLT.Section3.HighContrast.blockLane l
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
        (Homogenization.cubeSet R) (Homogenization.measurableSet_cubeSet R))]
      (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
        Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix
          (Homogenization.cubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField)) := by
  let hU := Homogenization.measurableSet_cubeSet R
  let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
    SuperdiffusionCLT.Section3.HighContrast.blockLane l
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
        (Homogenization.cubeSet R) hU)
  have hA := SuperdiffusionCLT.Section3.Terms.measurable_blockLane_restrictedCoefficientCutoff
    nu hU (le_refl l)
  have hEll := fun omega =>
    SuperdiffusionCLT.Section3.Terms.aeLocallyUniformlyEllipticField_restrictedCoefficientCutoff
      hnu hU omega l
  have hfull : Measurable (fun omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
      Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix
        (Homogenization.cubeSet R)
        (SuperdiffusionCLT.Section3.Terms.restrictedCoefficientCutoff nu hU omega l).toFun)) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    cases i <;> cases j
    · exact SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperLeft_apply
        hA hEll R _ _
    · exact SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_upperRight_apply
        hA hEll R _ _
    · exact SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerLeft_apply
        hA hEll R _ _
    · exact SuperdiffusionCLT.Section2.Annealed.measurable_coarseBlockMatrix_lowerRight_apply
        hA hEll R _ _
  simp only [SuperdiffusionCLT.Section3.Terms.coarseBlockMatrix_restrictedCoefficientCutoff_eq
    nu hU hU (Set.Subset.refl _) ] at hfull
  exact hfull

/-- The normalized matrix perturbation reads only lower shells on its own cube. -/
theorem displayJ_measurable_V {nu : ℝ} (hnu : 0 < nu) (l : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (n : ℕ) (R : Homogenization.TriadicCube d) :
    Measurable[SuperdiffusionCLT.Section3.HighContrast.blockLane l
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
        (Homogenization.cubeSet R) (Homogenization.measurableSet_cubeSet R))]
      (fun omega => Homogenization.toFullBlockMat (localizationV nu l P n R omega)) := by
  let : MeasurableSpace (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :=
    SuperdiffusionCLT.Section3.HighContrast.blockLane l
      (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma
        (Homogenization.cubeSet R) (Homogenization.measurableSet_cubeSet R))
  have hcoarse := displayJ_measurable_coarse hnu l R
  have hsub : Measurable (fun omega =>
      Homogenization.toFullBlockMat (Homogenization.coarseBlockMatrix
        (Homogenization.cubeSet R)
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega l).toCoeffField) -
      Homogenization.toFullBlockMat
        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu l P
          (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))))) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hcoarse)).sub
      measurable_const
  have hmul := displayJ_measurable_mul
    (measurable_const (a := Homogenization.toFullBlockMat
      (SuperdiffusionCLT.Section2.Annealed.envelopeInvSqrt d nu l)))
    (displayJ_measurable_mul hsub (measurable_const (a := Homogenization.toFullBlockMat
      (SuperdiffusionCLT.Section2.Annealed.envelopeInvSqrt d nu l))))
  simpa only [localizationV, SuperdiffusionCLT.Section2.Annealed.envelopeRescale,
    localizationPerturbationMatrix, displayJ_full_mul,
    Homogenization.toFullBlockMat_ofFullBlockMat] using hmul

/-- J1V2 and J2 give independence of the full perturbation matrices on separated cubes. -/
theorem displayJ_iIndepFun_V {ι : Type*} {nu : ℝ} (hnu : 0 < nu) (l : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    (n : ℕ) (R : ι → Homogenization.TriadicCube d)
    (hsep : Pairwise fun i j =>
      SuperdiffusionCLT.Frozen.Assumptions.ShellField.AreShellSeparated l
        (Homogenization.cubeSet (R i)) (Homogenization.cubeSet (R j))) :
    ProbabilityTheory.iIndepFun (fun i omega =>
      Homogenization.toFullBlockMat (localizationV nu l P n (R i) omega)) P.toMeasure :=
  SuperdiffusionCLT.Section2.Estimates.Stream.iIndepFun_of_blockLane_shellRestrictionSigma
    hJ1 hJ2 l (fun i => Homogenization.measurableSet_cubeSet (R i))
    (fun i => displayJ_measurable_V hnu l P n (R i)) hsep

/-- The actual colour classes at spacing `3^l` give independent perturbations.
The modulus is `3^(l-n) * d + 1`, so there are at most its d-th power classes. -/
theorem displayJ_colorClass_independent {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (hJ1 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
    {n l m : ℕ} (hnl : n ≤ l) (hlm : l ≤ m)
    (c : Fin d → Fin (SuperdiffusionCLT.Section2.Annealed.descendantColorModulus d (l - n))) :
    ProbabilityTheory.iIndepFun
      (fun (R : {R : Homogenization.TriadicCube d //
        R ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorClass d (l - n) m n c})
        omega => Homogenization.toFullBlockMat (localizationV nu l P n R.val omega))
      P.toMeasure := by
  apply displayJ_iIndepFun_V hnu l P hJ1 hJ2 n
    (fun R : {R : Homogenization.TriadicCube d //
      R ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorClass d (l - n) m n c} => R.val)
  intro R S hne
  obtain ⟨hR, hcR⟩ := SuperdiffusionCLT.Section2.Annealed.mem_descendantColorClass_iff.mp R.property
  obtain ⟨hS, hcS⟩ := SuperdiffusionCLT.Section2.Annealed.mem_descendantColorClass_iff.mp S.property
  exact SuperdiffusionCLT.Section2.Annealed.areShellSeparated_of_stepEColor_eq hnl
    (SuperdiffusionCLT.Section2.Annealed.scale_eq_of_mem_descendantsAtDepth_originCube
      (hnl.trans hlm) hR)
    (SuperdiffusionCLT.Section2.Annealed.scale_eq_of_mem_descendantsAtDepth_originCube
      (hnl.trans hlm) hS)
    (fun h => hne (Subtype.ext h)) (hcR.trans hcS.symm)

/-- Spatial locality also gives measurability in the lower shell coordinates. -/
theorem displayJ_measurable_V_lower {nu : ℝ} (hnu : 0 < nu) (l : ℕ)
    (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (n : ℕ) (R : Homogenization.TriadicCube d) :
    Measurable[SuperdiffusionCLT.Probability.shellSigma (localizationLowerShells l)]
      (fun omega => Homogenization.toFullBlockMat (localizationV nu l P n R omega)) := by
  apply (displayJ_measurable_V hnu l P n R).mono _ le_rfl
  apply iSup₂_le
  intro k hk
  exact le_trans (MeasurableSpace.comap_mono
    (SuperdiffusionCLT.Frozen.Assumptions.ShellField.shellRestrictionSigma_le
      (Homogenization.cubeSet R) (Homogenization.measurableSet_cubeSet R)))
    (le_iSup₂_of_le k hk le_rfl)

/-- The square-root cardinality input to colour-class Gamma aggregation is automatic. -/
theorem displayJ_color_sqrt_bound (d l m n : ℕ) :
    (∑ c ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorSet d (l - n) m n,
      Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
        d (l - n) m n c).card : ℝ)) ≤
    Real.sqrt ((SuperdiffusionCLT.Section2.Annealed.descendantColorSet
      d (l - n) m n).card : ℝ) *
      Real.sqrt ((localizationAverageGrid d m n).card : ℝ) := by
  classical
  have hcardsum :
      (∑ c ∈ SuperdiffusionCLT.Section2.Annealed.descendantColorSet d (l - n) m n,
        ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
          d (l - n) m n c).card : ℝ)) = ((localizationAverageGrid d m n).card : ℝ) := by
    have hcard := Finset.card_biUnion
      (SuperdiffusionCLT.Section2.Annealed.pairwiseDisjoint_descendantColorClass
        d (l - n) m n)
    rw [SuperdiffusionCLT.Section2.Annealed.biUnion_descendantColorClass] at hcard
    exact_mod_cast hcard.symm
  have hsch := Real.sum_sqrt_mul_sqrt_le
    (s := SuperdiffusionCLT.Section2.Annealed.descendantColorSet d (l - n) m n)
    (f := fun _ => (1 : ℝ))
    (g := fun c => ((SuperdiffusionCLT.Section2.Annealed.descendantColorClass
      d (l - n) m n c).card : ℝ))
    (hf := fun _ => zero_le_one) (hg := fun _ => Nat.cast_nonneg _)
  simpa only [Real.sqrt_one, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    hcardsum] using hsch

end SuperdiffusionCLT.Section2.Localization
