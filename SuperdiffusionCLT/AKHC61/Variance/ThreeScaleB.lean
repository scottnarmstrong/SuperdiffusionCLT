/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ThreeScale
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import Homogenization.Book.Ch04.Theorems.AnnealedSubadditivity.BlockLoewner

/-!
# The three-scale variance comparison `e.variance.HC`: the cutoff field

The expectation step of `e.variance.HC` for the cutoff field
`a_L = ν Id + k_L` under the shell law `P`, at scales `k ≤ n`, with the
normalizing matrix a positive diagonal `W = diag w` (in the applications
`w α = (bfAhom(cu_m))_{αα}`).

Inputs: `0 < ν`, `ShellLawPrefix`, `ShellLawJ2` (stationarity of the cutoff
law), entrywise integrability of the coarse block matrices (supplied from
(P2') by `SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`),
and integrability of the squared linear average, which is the quantity the
(P3') clause controls.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-- An entry of a descendant-averaged block matrix is the descendant average
of the entries. -/
theorem akhc_blockMatEntry_descendantsAverageBlockMat (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → BlockMat d) (α β : BlockCoord d) :
    blockMatEntry (descendantsAverageBlockMat Q j F) α β =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, blockMatEntry (F R) α β := by
  cases α <;> cases β <;> rfl

/-- An entry of the annealed block matrix is the expectation of the entry. -/
theorem akhc_blockMatEntry_annealedBlockMatrix (nu : ℝ) (L : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (U : Set (Vec d)) (α β : BlockCoord d) :
    blockMatEntry (annealedBlockMatrix nu L P U) α β =
      ∫ omega, blockMatEntry
        (coarseBlockMatrix U (coefficientCutoff nu omega L).toCoeffField) α β ∂P.toMeasure := by
  cases α <;> cases β <;> rfl

/-- The entrywise identity `avsum_R (A_R - B) = avsum_R A_R - B`. -/
theorem akhc_avg_sub_const (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → BlockMat d)
    (B : BlockMat d) (α β : BlockCoord d) :
    ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, (blockMatEntry (F R) α β - blockMatEntry B α β) =
      blockMatEntry (descendantsAverageBlockMat Q j F) α β - blockMatEntry B α β := by
  rw [akhc_blockMatEntry_descendantsAverageBlockMat, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul, mul_sub]
  have hne : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **Stationarity**: every depth-`(n - k)` descendant of `cu_n` has the same
expected coarse block matrix as `cu_k`. -/
theorem akhc_integral_blockMatEntry_descendant [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (L : ℕ)
    {k n : ℕ} (hkn : k ≤ n) {R : TriadicCube d}
    (hR : R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k)) (α β : BlockCoord d) :
    ∫ omega, blockMatEntry
        (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField) α β
          ∂P.toMeasure =
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β := by
  have hkn' : (k : ℤ) ≤ (originCube d (n : ℤ)).scale := by
    show (k : ℤ) ≤ (n : ℤ)
    exact_mod_cast hkn
  have hRs : R ∈ descendantsAtScale (originCube d (n : ℤ)) (k : ℤ) := by
    rw [descendantsAtScale_eq_descendantsAtDepth _ hkn']
    have hdepth : Int.toNat ((originCube d (n : ℤ)).scale - (k : ℤ)) = n - k := by
      show Int.toNat ((n : ℤ) - (k : ℤ)) = n - k
      omega
    rw [hdepth]
    exact hR
  have hstat := restrictionStationaryLaw_cutoffLaw hPrefix hJ2 nu L
  have hmain :=
    (restrictionLawCarrier_cutoffLaw hnu L P).integral_coarseBlockMatrix_entry_cubeSet_eq_originCube_of_mem_descendantsAtScale_originCube
      hstat (Int.natCast_nonneg k) (by exact_mod_cast hkn) hRs α β
  rw [akhc_blockMatEntry_annealedBlockMatrix]
  rw [integral_cutoffLaw L P _ (aemeasurable_blockMatEntry_cutoffLaw hnu L P R α β).aestronglyMeasurable,
    integral_cutoffLaw L P _
      (aemeasurable_blockMatEntry_cutoffLaw hnu L P _ α β).aestronglyMeasurable] at hmain
  exact hmain

/-- **Samplewise three-scale inequality for the cutoff field.** -/
theorem akhc_threeScale_cutoff_pointwise [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ) {k n : ℕ} (hkn : k ≤ n)
    {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α) (omega : ShellSeq d) :
    akhcRelFrobSq w (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w) ≤
      (3 + 6 * d) * akhcRelFrobSq w (fun α β =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) +
        3 * akhcRelFrobSq w (akhcSubDiag
          (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w) +
        6 * akhcRelTrace w (blockMatEntry
            (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) *
          akhcRelTrace w (fun α β =>
            blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
                (fun R => coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField)) α β -
              blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
                (coefficientCutoff nu omega L).toCoeffField) α β) := by
  set a := coefficientCutoff nu omega L with ha_def
  set Avg := descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
    (fun R => coarseBlockMatrix (cubeSet R) a.toCoeffField) with hAvg
  have hsub : BlockMatLoewnerLE (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toCoeffField)
      Avg := by
    have h := Book.Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_of_aelocallyUniformlyEllipticField
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)
      (show ((k : ℤ)) ≤ (n : ℤ) by exact_mod_cast hkn)
    have hdepth : Int.toNat ((n : ℤ) - (k : ℤ)) = n - k := by omega
    rw [hdepth] at h
    exact h
  have hsymR : ∀ Q : TriadicCube d,
      IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toCoeffField) :=
    fun Q => isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L Q
  have hsymAvg : IsSymmetricBlockMat Avg := by
    intro α β
    rw [hAvg, akhc_blockMatEntry_descendantsAverageBlockMat,
      akhc_blockMatEntry_descendantsAverageBlockMat]
    congr 1
    exact Finset.sum_congr rfl fun R _ => hsymR R α β
  have hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X
      (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) a.toCoeffField) X) :=
    fun X => zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff hnu omega L _ X
  have hmain := akhc_threeScale_pointwise hw (hsymR _) hsymAvg hpos hsub
    (Ak := annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))
  have hlin : (fun α β =>
      ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
          (blockMatEntry (coarseBlockMatrix (cubeSet R) a.toCoeffField) α β -
            blockMatEntry (annealedBlockMatrix nu L P
              (cubeSet (originCube d (k : ℤ)))) α β)) =
      fun α β => blockMatEntry Avg α β -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β := by
    funext α β
    rw [hAvg]
    exact akhc_avg_sub_const _ _ _ _ α β
  rw [hlin]
  exact hmain

end

end SuperdiffusionCLT.AKHC61.Variance
