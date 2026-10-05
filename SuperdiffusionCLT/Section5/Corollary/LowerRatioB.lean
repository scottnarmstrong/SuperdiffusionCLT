/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section5.Corollary.LowerRatio

/-!
# `cor.lower.ratio`: the left side as an annealed quadratic form

For `P₀ = (0, v)` the expectation of `P₀ · bfA_m(cu_K) P₀` is
`shom_{m,*}^{-1}(cu_K) |v|²` (`e.homs.defs.U`, the lower block).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2 SuperdiffusionCLT.Frozen.Assumptions

variable {d : ℕ}

/-- The quadratic form of a block vector `(0, v)` only sees the lower right block. -/
theorem lowerRatio_quad_eq (A : BlockMat d) (v : Vec d) :
    blockVecDot ((0 : Vec d), v) (blockMatVecMul A ((0 : Vec d), v)) =
      ∑ i, ∑ j, v i * v j * A.lowerRight i j := by
  simp [blockVecDot, blockMatVecMul, vecDot, matVecMul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **The annealed lower block as an expectation of the quadratic form.** -/
theorem lowerRatio_expect_quad [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : MeasureTheory.ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (Kc : ℕ) (v : Vec d) :
    ∫ ω, blockVecDot ((0 : Vec d), v) (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField) ((0 : Vec d), v)) ∂P.toMeasure =
      sigmaBarStarInvSeq nu m P Kc * vecNormSq v := by
  have hint : ∀ i j : Fin d, Integrable (fun ω : ShellSeq d => v i * v j *
      (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
        (coefficientCutoff nu ω m).toFun).lowerRight i j) P.toMeasure := fun i j =>
    (integrable_coarseBlockMatrix_lowerRight_apply hnu m (originCube d (Kc : ℤ)) hPrefix hJ2 hJ3
      hJ4 i j).const_mul _
  have h1 : (fun ω : ShellSeq d => blockVecDot ((0 : Vec d), v) (blockMatVecMul
        (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
          (coefficientCutoff nu ω m).toCoeffField) ((0 : Vec d), v))) = fun ω =>
      ∑ i, ∑ j, v i * v j * (coarseBlockMatrix (cubeSet (originCube d (Kc : ℤ)))
        (coefficientCutoff nu ω m).toFun).lowerRight i j := by
    funext ω
    exact lowerRatio_quad_eq _ v
  rw [h1, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  have h2 : ∀ i : Fin d, ∫ ω, ∑ j, v i * v j * (coarseBlockMatrix
      (cubeSet (originCube d (Kc : ℤ))) (coefficientCutoff nu ω m).toFun).lowerRight i j
        ∂P.toMeasure = ∑ j, v i * v j * (sigmaBarStarInv nu m P
          (cubeSet (originCube d (Kc : ℤ)))) i j := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  rw [sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 (Kc : ℤ)]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, vecNormSq, vecDot, sigmaBarStarInvSeq,
    sigmaBarStarInvScalar]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end SuperdiffusionCLT.Section5
