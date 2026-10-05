/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.LocAvgUniformWitness
public import SuperdiffusionCLT.Section4.NewMixing.Splitting

/-!
# The splitting step with the witness constant fixed first

The splitting step of `Splitting.lean` binds its amplitude constant after the scales
`L, m, ell, n`. The constant comes from `locAvg_uniform`, which fixes it before every
parameter; this file states the splitting with the constant bound first, so that the final
assembly can use one constant for all parameters.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Localization

noncomputable section

theorem newMixAsm_splitting_uniform (d : ℕ) [NeZero d] :
    ∃ C : ℝ, ∀
    {nu : ℝ} {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    (hnu : 0 < nu), nu ≤ 1 →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
    ∀ {L m ell n : ℕ}, n ≤ ell → ell ≤ m → ell ≤ L →
    ∃ X0 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X0 ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure
        (Homogenization.IndependentSums.gammaSigma ((1:ℝ)/3)) X0
        (C * nu ^ (-(3:ℝ)) *
          ((if ell < L then (L:ℝ) * (3:ℝ) ^ (-((ell - n : ℕ):ℝ)) else 0) +
            max 1 (ell:ℝ) * max 1 (L:ℝ) * max 1 ((m-n:ℕ):ℝ) *
              (3:ℝ) ^ (-((d:ℝ)/2 * ((m-ell:ℕ):ℝ))))) ∧
      ∀ (h0 : Mat d) (hh0 : matTranspose h0 = -h0) (Pvec : BlockVec d)
        (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
        blockVecDot Pvec
            (blockMatVecMul
              (Homogenization.Book.Ch02.coarseBlockMatrix
                (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m:ℤ)))
                (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
              Pvec) ≤
          Homogenization.blockVecDot (blockMatVecMul (blockG (-h0)) Pvec)
              (blockMatVecMul (blockG (-h0)) Pvec) * X0 omega +
          Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
            (fun R => blockVecDot
              (blockMatVecMul
                (Homogenization.Book.Ch02.blockG
                  (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                          omega ell L y) + h0)))
                Pvec)
              (blockMatVecMul
                (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                  (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                (blockMatVecMul
                  (Homogenization.Book.Ch02.blockG
                    (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y) + h0)))
                  Pvec))) := by
  obtain ⟨C, hC⟩ := locAvg_uniform d
  refine ⟨C, ?_⟩
  intro nu P hnu hnu1 hPrefix hJ1V2 hJ2 hJ3 hJ4 L m ell n hn_ell hell_m hell_L
  obtain ⟨X0, hX0meas, hX0BigO, hX0bound⟩ :=
    hC nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 m n ell L hn_ell hell_m hell_L
  refine ⟨X0, hX0meas, hX0BigO, ?_⟩
  intro h0 hh0 Pvec omega
  set Q0 : BlockVec d := blockMatVecMul (blockG (-h0)) Pvec with hQ0def
  -- Step 1: the gauge shift, then the raw/Book.Ch02 bridge.
  have hstep1 :
      blockVecDot Pvec
          (blockMatVecMul
            (Homogenization.Book.Ch02.coarseBlockMatrix
              (Homogenization.Book.Ch02.cubeDomain (Homogenization.originCube d (m:ℤ)))
              (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
            Pvec) =
        blockVecDot Q0
          (blockMatVecMul
            (Homogenization.coarseBlockMatrix
              (Homogenization.openCubeSet (Homogenization.originCube d (m:ℤ)))
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            Q0) := by
    rw [newMixParam_splitting_gaugeShift hnu omega L m h0 hh0 Pvec, hQ0def]
    congr 2
    rw [← SuperdiffusionCLT.Section2.Localization.coarseBlockMatrix_toCoeffField]
    rw [SuperdiffusionCLT.Section2.CoarseGraining.coefficientCutoffCoeffOn_toCoeffField]
    rw [Homogenization.Book.Ch02.cubeDomain_coe]
  rw [hstep1]
  -- Step 2: subadditivity.
  have hstep2 := newMixParam_subadditivity hnu omega L m n Q0
  refine le_trans hstep2 ?_
  -- Step 3: `openCubeSet` to `cubeSet` (localization_average's own convention).
  have hstep3 :
      Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
          (fun R => blockVecDot Q0
            (blockMatVecMul
              (Homogenization.coarseBlockMatrix (Homogenization.openCubeSet R)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              Q0)) =
        Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
          (fun R => blockVecDot Q0
            (blockMatVecMul
              (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              Q0)) := by
    unfold Homogenization.descendantsAverage
    refine congrArg (fun t => ((Homogenization.descendantsAtDepth
      (Homogenization.originCube d (m:ℤ)) (m - n)).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [SuperdiffusionCLT.Section2.Localization.localizationCubePassage_coarseBlockMatrix R
      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField]
  rw [hstep3]
  -- Step 4: the one-shot bound, converted from `|diff| ≤ X` to `≤ B + X`.
  have habs := hX0bound Q0 omega
  change |Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
      (fun R => blockVecDot Q0
        (blockMatVecMul
          (Homogenization.ofFullBlockMat
            (Homogenization.toFullBlockMat
                (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
              Homogenization.toFullBlockMat
                (Homogenization.Book.Ch02.blockMatMul
                  (Homogenization.Book.Ch02.blockMatTranspose
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y))))
                  (Homogenization.Book.Ch02.blockMatMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                      (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y)))))))
          Q0))| ≤ Homogenization.blockVecDot Q0 Q0 * X0 omega at habs
  rw [abs_le] at habs
  have hdiffEq :
      Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
          (fun R => blockVecDot Q0
            (blockMatVecMul
              (Homogenization.ofFullBlockMat
                (Homogenization.toFullBlockMat
                    (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                      (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
                  Homogenization.toFullBlockMat
                    (Homogenization.Book.Ch02.blockMatMul
                      (Homogenization.Book.Ch02.blockMatTranspose
                        (Homogenization.Book.Ch02.blockG
                          (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                              (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega ell L y))))
                      (Homogenization.Book.Ch02.blockMatMul
                        (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                          (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                        (Homogenization.Book.Ch02.blockG
                          (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                              (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega ell L y)))))))
              Q0)) =
        Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
            (fun R => blockVecDot Q0
              (blockMatVecMul
                (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
                Q0)) -
          Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
            (fun R => blockVecDot Q0
              (blockMatVecMul
                (Homogenization.Book.Ch02.blockMatMul
                  (Homogenization.Book.Ch02.blockMatTranspose
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y))))
                  (Homogenization.Book.Ch02.blockMatMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                      (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y)))))
                Q0)) := by
    have hptwise : (fun R : Homogenization.TriadicCube d => blockVecDot Q0
          (blockMatVecMul
            (Homogenization.ofFullBlockMat
              (Homogenization.toFullBlockMat
                  (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                    (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) -
                Homogenization.toFullBlockMat
                  (Homogenization.Book.Ch02.blockMatMul
                    (Homogenization.Book.Ch02.blockMatTranspose
                      (Homogenization.Book.Ch02.blockG
                        (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                            (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                              omega ell L y))))
                    (Homogenization.Book.Ch02.blockMatMul
                      (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                        (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                      (Homogenization.Book.Ch02.blockG
                        (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                            (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                              omega ell L y)))))))
            Q0)) =
        (fun R : Homogenization.TriadicCube d => blockVecDot Q0
              (blockMatVecMul
                (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
                  (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
                Q0) -
            blockVecDot Q0
              (blockMatVecMul
                (Homogenization.Book.Ch02.blockMatMul
                  (Homogenization.Book.Ch02.blockMatTranspose
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y))))
                  (Homogenization.Book.Ch02.blockMatMul
                    (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                      (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                    (Homogenization.Book.Ch02.blockG
                      (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                          (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                            omega ell L y)))))
                Q0)) := by
      funext R
      exact Homogenization.blockVecDot_blockMatVecMul_ofFullBlockMat_sub _ _ Q0
    rw [hptwise]
    have hneg : (fun R : Homogenization.TriadicCube d =>
        blockVecDot Q0 (blockMatVecMul (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) Q0) -
        blockVecDot Q0
          (blockMatVecMul
            (Homogenization.Book.Ch02.blockMatMul
              (Homogenization.Book.Ch02.blockMatTranspose
                (Homogenization.Book.Ch02.blockG
                  (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega ell L y))))
              (Homogenization.Book.Ch02.blockMatMul
                (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                  (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                (Homogenization.Book.Ch02.blockG
                  (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega ell L y)))))
            Q0)) =
      (fun R : Homogenization.TriadicCube d =>
        blockVecDot Q0 (blockMatVecMul (Homogenization.coarseBlockMatrix (Homogenization.cubeSet R)
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) Q0) +
        (-1 : ℝ) * blockVecDot Q0
          (blockMatVecMul
            (Homogenization.Book.Ch02.blockMatMul
              (Homogenization.Book.Ch02.blockMatTranspose
                (Homogenization.Book.Ch02.blockG
                  (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega ell L y))))
              (Homogenization.Book.Ch02.blockMatMul
                (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                  (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                (Homogenization.Book.Ch02.blockG
                  (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega ell L y)))))
            Q0)) := by funext R; ring
    rw [hneg, Homogenization.descendantsAverage_add, Homogenization.descendantsAverage_smul]
    ring
  rw [hdiffEq] at habs
  -- Step 5: `Q0`-tested, `blockG(-h_z)`-conjugated average of the annealed block matrix equals the
  -- `Pvec`-tested, `blockG(-(h_z+h0))`-conjugated form, via the group law.
  have hstep5 :
      Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
          (fun R => blockVecDot Q0
            (blockMatVecMul
              (Homogenization.Book.Ch02.blockMatMul
                (Homogenization.Book.Ch02.blockMatTranspose
                  (Homogenization.Book.Ch02.blockG
                    (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                          omega ell L y))))
                (Homogenization.Book.Ch02.blockMatMul
                  (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                    (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
                  (Homogenization.Book.Ch02.blockG
                    (-Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                          omega ell L y)))))
              Q0)) =
        Homogenization.descendantsAverage (Homogenization.originCube d (m:ℤ)) (m - n)
          (fun R => blockVecDot
            (blockMatVecMul
              (Homogenization.Book.Ch02.blockG
                (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                      (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                        omega ell L y) + h0)))
              Pvec)
            (blockMatVecMul
              (SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu ell P
                (Homogenization.cubeSet (Homogenization.originCube d (n:ℤ))))
              (blockMatVecMul
                (Homogenization.Book.Ch02.blockG
                  (-(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                        (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                          omega ell L y) + h0)))
                Pvec))) := by
    unfold Homogenization.descendantsAverage
    refine congrArg (fun t => ((Homogenization.descendantsAtDepth
      (Homogenization.originCube d (m:ℤ)) (m - n)).card : ℝ)⁻¹ * t) ?_
    refine Finset.sum_congr rfl (fun R _ => ?_)
    rw [SuperdiffusionCLT.Section2.Localization.blockVecDot_conj_blockMatMul, hQ0def,
      ← Homogenization.blockMatVecMul_blockMatMul,
      SuperdiffusionCLT.Section2.Localization.blockG_mul_blockG]
    have harg :
        -(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
              (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                omega ell L y)) + -h0 =
          -(Homogenization.volumeAverageMat (Homogenization.cubeSet R)
                (fun y => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                  omega ell L y) + h0) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.neg_apply]
      ring
    rw [harg]
  rw [hstep5] at habs
  linarith only [habs.2]


end

end SuperdiffusionCLT.Section4.NewMixing
