/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Corollary.LowerRatioB
public import SuperdiffusionCLT.Section5.Localization.FluctB

/-!
# `cor.lower.ratio`: `shom_{m-h} shom_m^{-1}` as a lower bound for the cube energies

`shom_m^{-1}` is the infimum of the nonincreasing sequence `shom_{m,*}^{-1}(cu_K)`, so for every `K`
`|v|² shom_m^{-1} ≤ E[(0,v) · bfA_m(cu_K) (0,v)]`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2 SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}

theorem lowerRatio_vecNormSq_nonneg (v : Vec d) : 0 ≤ vecNormSq v :=
  by unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- **The left side of `e.lower.ratio.product`.** -/
theorem lowerRatio_ratio_le [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (Kc : ℕ) (v : Vec d) :
    ENNReal.ofReal (vecNormSq v * (sigmaBarInfinite nu m P)⁻¹) ≤
      ∫⁻ ω, ENNReal.ofReal (blockVecDot ((0 : Vec d), v) (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField) ((0 : Vec d), v))) ∂P.toMeasure := by
  have hint : Integrable (fun ω : ShellSeq d => blockVecDot ((0 : Vec d), v) (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField) ((0 : Vec d), v))) P.toMeasure := by
    have h1 : (fun ω : ShellSeq d => blockVecDot ((0 : Vec d), v) (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField) ((0 : Vec d), v))) = fun ω =>
        ∑ i, ∑ j, v i * v j * (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toFun).lowerRight i j := by
      funext ω
      exact lowerRatio_quad_eq _ v
    rw [h1]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (integrable_coarseBlockMatrix_lowerRight_apply hnu m (originCube d (Kc : ℤ)) hPrefix hJ2 hJ3
        hJ4 i j).const_mul _
  refine le_trans ?_ (loc_ofReal_integral_le_lintegral hint)
  rw [lowerRatio_expect_quad hnu m hPrefix hJ2 hJ3 hJ4 Kc v]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle := sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 Kc
  have hinv : (sigmaBarInfinite nu m P)⁻¹ = sigmaBarStarInvLimit nu m P := by
    rw [sigmaBarInfinite, inv_inv]
  rw [hinv, mul_comm]
  exact mul_le_mul_of_nonneg_right hle (lowerRatio_vecNormSq_nonneg v)

end SuperdiffusionCLT.Section5
