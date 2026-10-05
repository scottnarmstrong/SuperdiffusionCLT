/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Norms.NegativeHatFullGradient
public import Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualBesovBound

/-!
# The multiscale Poincaré bridge for the amended hatted negative norm

display `e.apply.multiscale.Poincare`, applies the multiscale Poincaré inequality
(`\cite[Lemma A.2]{AK.HC}` with `q = 1`) in the form

> `3^{-sl} ‖j_k‖_{Ŵ̲^{-s,p}(cu_l)} ≤ C ∑_{h ≤ l} 3^{s(h-l)}
>   ( ⨍_{y ∈ 3^h ℤ^d ∩ cu_l} |(j_k)_{y+cu_h}|^p )^{1/p}`.

This module proves that inequality for the amended carrier
`matHatNegENorm` of `Section2/Norms/NegativeHatFullGradient.lean`, with an explicit
constant, for continuous matrix fields.

## The route

1. `matHatNegENorm_le_iSup_cubeEuclideanNegativeWspSmoothDualENorm`
   (`Section2/Norms/NegativeHatFullGradient.lean`) hands the amended norm to the
   upstream smooth-dual norm of the row fields `x ↦ v ᵥ* M x`, with
   constant `1`.
2. `Homogenization.cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm`
   is the upstream realization of Lemma A.2, with constant
   `Homogenization.cubeEuclideanNegativeWspSmoothDualBesovConstant d`.
3. `cubeEuclideanNegativeBesovESeminorm_rowLpField_le` (proved here) rewrites
   the upstream depth sum of the row field as the marginal depth sum of the
   matrix field, at the cost of the dimension factor `d` coming from
   `vecNorm (v ᵥ* A) ≤ d ‖A‖ vecNorm v`.
4. `cubeNegativeBesovDepthENorm_le_cubeMultiscaleDepthSum`
   (`Section2/Norms/MultiscalePoincare.lean`) converts the upstream `ℓ^p`
   depth sum into the printed `ℓ¹` depth sum at the cost of the manuscript's
   own prefactor `3^{s l}`.

## The constant

`matHatNegBridgeConstant d = cubeEuclideanNegativeWspSmoothDualBesovConstant d * d`,
a finite quantity depending only on the dimension
(`matHatNegBridgeConstant_lt_top`). The remaining factor
`3 ^ (s * Q.scale)` of the conclusion is the manuscript's own prefactor
`3^{-sl}`, moved to the other side of the display.

## The real depth sum, and subadditivity

Two further blocks sit here because they are statements about the carriers of
this directory and not about shells.

* `cubeMultiscaleDepthSumReal` is the printed depth sum as a real number, and
  `summable_cubeMultiscaleDepthTerm` shows that its defining series converges
  for every continuous matrix field: the sub-cube averages of a continuous
  field on a fixed cube are bounded uniformly in the depth
  (`exists_bound_norm_volumeAverageMat`), so the geometric weight `3^{-sj}`
  already gives convergence. Hence `ofReal_cubeMultiscaleDepthSumReal`, which
  identifies the `ℝ≥0∞` depth sum with the `ENNReal.ofReal` of the real one.
* `matHatNegENorm_finset_sum_le` is the subadditivity of the amended norm on
  a finite sum of continuous matrix fields; the pairing density
  is linear in the field, and a supremum of sums is at most the sum of the
  suprema.

## Main definitions

* `matHatNegBridgeConstant`: the dimension-only constant of the bridge.
* `cubeMultiscaleDepthSumReal`: the printed depth sum as a real number.

## Main results

* `norm_vecMul_le_dim_mul`: `‖v ᵥ* A‖ ≤ d ‖A‖ vecNorm v` for the ambient
  norm of `Vec d` and the `L²` operator norm of `Mat d`.
* `cubeAverageVec_vecMul_eq`: the cube average of a row field of a continuous
  matrix field is the row of the cube average of the matrix field.
* `cubeEuclideanNegativeBesovESeminorm_rowLpField_le`: the upstream negative
  Besov seminorm of a row field is at most `d` times the marginal `ℓ^p` depth
  sum of the matrix field.
* `matHatNegENorm_le_cubeMultiscaleDepthSum`: the bridge, in the plain-real
  exponent form used by the shell-increment clause.
* `exists_bound_norm_volumeAverageMat`, `summable_cubeMultiscaleDepthTerm`,
  `ofReal_cubeMultiscaleDepthSumReal`: the real form of the depth sum.
* `matHatNegENorm_finset_sum_le`: subadditivity of the amended norm.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Norms

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.Book.Ch03.ABK26
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The row field of a matrix -/

/-- The row vector `v ᵥ* A` is the matrix-vector product of the transpose. -/
theorem vecMul_eq_matVecMul_transpose (v : Vec d) (A : Mat d) :
    Matrix.vecMul v A = matVecMul A.transpose v := by
  funext i
  simp only [Matrix.vecMul, matVecMul, dotProduct, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm (v j) (A j i)

/-- The Frobenius square is invariant under transposition. -/
theorem matrixFrobeniusNormSq_transpose (A : Mat d) :
    matrixFrobeniusNormSq A.transpose = matrixFrobeniusNormSq A := by
  simp only [matrixFrobeniusNormSq, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- The Euclidean length of a row field is controlled by the `L²` operator
norm of the matrix, with the dimension factor of
`matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm`. -/
theorem vecNorm_vecMul_le_dim_mul (v : Vec d) (A : Mat d) :
    vecNorm (Matrix.vecMul v A) ≤ (d : ℝ) * ‖A‖ * vecNorm v := by
  have hfrob : vecNormSq (matVecMul A.transpose v) ≤
      matrixFrobeniusNormSq A * vecNormSq v := by
    have h := vecNormSq_matVecMul_le_matrixFrobeniusNormSq_mul_vecNormSq
      A.transpose v
    rwa [matrixFrobeniusNormSq_transpose] at h
  have hsq : vecNorm (Matrix.vecMul v A) ^ 2 ≤
      (matrixFrobeniusNorm A * vecNorm v) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, mul_pow, vecNorm_sq_eq_vecNormSq,
      matrixFrobeniusNorm, Real.sq_sqrt (matrixFrobeniusNormSq_nonneg A),
      vecMul_eq_matVecMul_transpose]
    exact hfrob
  have hstep : vecNorm (Matrix.vecMul v A) ≤ matrixFrobeniusNorm A * vecNorm v := by
    have h0 : 0 ≤ vecNorm (Matrix.vecMul v A) := vecNorm_nonneg _
    have h1 : 0 ≤ matrixFrobeniusNorm A * vecNorm v :=
      mul_nonneg (matrixFrobeniusNorm_nonneg A) (vecNorm_nonneg v)
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq h0, Real.sqrt_sq h1] at hroot
  refine le_trans hstep ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNorm_nonneg v)
  exact matrixFrobeniusNorm_le_dim_mul_matrixOperatorNorm A

/-- The ambient norm of a row field is controlled by the `L²` operator norm of
the matrix. -/
theorem norm_vecMul_le_dim_mul (v : Vec d) (A : Mat d) :
    ‖Matrix.vecMul v A‖ ≤ (d : ℝ) * ‖A‖ * vecNorm v := by
  refine le_trans ?_ (vecNorm_vecMul_le_dim_mul v A)
  rw [vecNorm]
  exact HilbertVec.norm_le_norm_ofVec _

/-! ## Cube averages of row fields -/

/-- The cube average of the row field `x ↦ v ᵥ* M x` of a continuous matrix
field is the row `v ᵥ* (M)_R` of its cube average. -/
theorem cubeAverageVec_vecMul_eq (R : TriadicCube d) {M : Vec d → Mat d}
    (hM : Continuous M) (v : Vec d) :
    cubeAverageVec R (fun x => Matrix.vecMul v (M x)) =
      Matrix.vecMul v (volumeAverageMat (cubeSet R) M) := by
  funext i
  have hint : ∀ l : Fin d,
      IntegrableOn (fun x : Vec d => v l * M x l i) (cubeSet R) volume := by
    intro l
    have hcont : Continuous (fun x : Vec d => v l * M x l i) :=
      continuous_const.mul (((continuous_apply i).comp
        ((continuous_apply l).comp hM)))
    exact (hcont.locallyIntegrable.integrableOn_isCompact
      (isBounded_cubeSet R).isCompact_closure).mono_set subset_closure
  have hsum : ∫ x in cubeSet R, (∑ l : Fin d, v l * M x l i) ∂volume =
      ∑ l : Fin d, v l * ∫ x in cubeSet R, M x l i ∂volume := by
    rw [integral_finsetSum _ fun l _ => hint l]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  simp only [cubeAverageVec, cubeAverage, Matrix.vecMul, dotProduct,
    volumeAverageMat, volumeAverage]
  rw [hsum, volume_cubeSet_toReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

/-! ## The upstream depth sum of a row field -/

private theorem card_descendantsAtDepth_ne_zero (Q : TriadicCube d) (j : ℕ) :
    ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
  have hne : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
  exact_mod_cast Finset.card_ne_zero_of_mem hne.choose_spec

/-- **The upstream negative Besov seminorm of a row field.** For a continuous
matrix field `M` and a vector `v` in the Euclidean unit ball, the upstream
depth sum of the row field `x ↦ v ᵥ* M x` is at most `d` times the marginal
`ℓ^p` depth sum of `M`. -/
theorem cubeEuclideanNegativeBesovESeminorm_rowLpField_le (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {M : Vec d → Mat d}
    (hM : Continuous M) {v : Vec d} (hv : vecNorm v ≤ 1) :
    cubeEuclideanNegativeBesovESeminorm Q s p (rowLpField Q hM v) ≤
      ENNReal.ofReal (d : ℝ) *
        cubeNegativeBesovDepthENorm Q s.1 p.exponent.toReal M := by
  classical
  have hpt1 : (1 : ℝ) < p.exponent.toReal := by
    have h1 : (1 : ℝ≥0∞).toReal < p.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) (ne_of_lt p.lt_top)).2 p.one_lt
    simpa using h1
  have hpt0 : (0 : ℝ) < p.exponent.toReal := lt_trans zero_lt_one hpt1
  have hinv0 : (0 : ℝ) ≤ (p.exponent.toReal)⁻¹ := le_of_lt (inv_pos.2 hpt0)
  have hdepth : ∀ j : ℕ,
      cubeEuclideanNegativeBesovDepthEnergy Q s p (rowLpField Q hM v) j ≤
        ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
          cubeDepthEnergy Q s.1 p.exponent.toReal M j := by
    intro j
    have hscale : descendantsAtScale Q (Q.scale - (j : ℤ)) =
        descendantsAtDepth Q j := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q (by omega)]
      congr 1
      omega
    have hcard : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 :=
      card_descendantsAtDepth_ne_zero Q j
    have hcardpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm hcard)
    have hterm : ∀ R ∈ descendantsAtDepth Q j,
        (ENNReal.ofReal ‖cubeAverageVec R (rowLpField Q hM v).toField‖) ^
            p.exponent.toReal ≤
          ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
            ENNReal.ofReal (‖volumeAverageMat (cubeSet R) M‖ ^ p.exponent.toReal) := by
      intro R _
      have hle : ‖cubeAverageVec R (rowLpField Q hM v).toField‖ ≤
          (d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖ := by
        have hEq : cubeAverageVec R (rowLpField Q hM v).toField =
            Matrix.vecMul v (volumeAverageMat (cubeSet R) M) := by
          exact cubeAverageVec_vecMul_eq R hM v
        rw [hEq]
        refine le_trans (norm_vecMul_le_dim_mul v _) ?_
        have hnn : (0 : ℝ) ≤ (d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖ := by
          positivity
        calc (d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖ * vecNorm v
            ≤ (d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖ * 1 :=
              mul_le_mul_of_nonneg_left hv hnn
          _ = (d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖ := mul_one _
      calc (ENNReal.ofReal ‖cubeAverageVec R (rowLpField Q hM v).toField‖) ^
              p.exponent.toReal
          ≤ (ENNReal.ofReal ((d : ℝ) * ‖volumeAverageMat (cubeSet R) M‖)) ^
              p.exponent.toReal :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hle) hpt0.le
        _ = ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
              ENNReal.ofReal (‖volumeAverageMat (cubeSet R) M‖ ^ p.exponent.toReal) := by
            rw [← ENNReal.ofReal_mul (by positivity),
              ← Real.mul_rpow (by positivity) (norm_nonneg _),
              ENNReal.ofReal_rpow_of_nonneg (by positivity) hpt0.le]
    have hsum : (descendantsAtDepth Q j).sum (fun R =>
          (ENNReal.ofReal ‖cubeAverageVec R (rowLpField Q hM v).toField‖) ^
            p.exponent.toReal) ≤
        ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
          ENNReal.ofReal ((descendantsAtDepth Q j).sum fun R =>
            ‖volumeAverageMat (cubeSet R) M‖ ^ p.exponent.toReal) := by
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun R _ => Real.rpow_nonneg (norm_nonneg _) p.exponent.toReal),
        Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hcardE : (((descendantsAtDepth Q j).card : ℝ≥0∞))⁻¹ =
        ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos hcardpos, ENNReal.ofReal_natCast]
    unfold cubeEuclideanNegativeBesovDepthEnergy
    rw [hscale, Finset.sum_attach (descendantsAtDepth Q j)
      (fun R => (ENNReal.ofReal
        ‖cubeAverageVec R (rowLpField Q hM v).toField‖) ^ p.exponent.toReal),
      hcardE, cubeDepthEnergy, cubeDepthPthMoment,
      ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hcardpos))]
    calc ENNReal.ofReal (Real.rpow 3 (s.1 * p.exponent.toReal *
              (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
            ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
            (descendantsAtDepth Q j).sum (fun R =>
              (ENNReal.ofReal
                ‖cubeAverageVec R (rowLpField Q hM v).toField‖) ^ p.exponent.toReal)
        ≤ ENNReal.ofReal (Real.rpow 3 (s.1 * p.exponent.toReal *
              (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
            ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
            (ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
              ENNReal.ofReal ((descendantsAtDepth Q j).sum fun R =>
                ‖volumeAverageMat (cubeSet R) M‖ ^ p.exponent.toReal)) :=
          mul_le_mul_right hsum _
      _ = ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) *
            (ENNReal.ofReal (Real.rpow 3 (s.1 * p.exponent.toReal *
                (((Q.scale - (j : ℤ) : ℤ) : ℝ)))) *
              (ENNReal.ofReal (((descendantsAtDepth Q j).card : ℝ)⁻¹) *
                ENNReal.ofReal ((descendantsAtDepth Q j).sum fun R =>
                  ‖volumeAverageMat (cubeSet R) M‖ ^ p.exponent.toReal))) := by
          ring
  have hd : ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) ^
      (p.exponent.toReal)⁻¹ = ENNReal.ofReal (d : ℝ) := by
    have h1 : ENNReal.ofReal ((d : ℝ) ^ p.exponent.toReal) =
        ENNReal.ofReal (d : ℝ) ^ p.exponent.toReal :=
      (ENNReal.ofReal_rpow_of_nonneg (x := (d : ℝ)) (p := p.exponent.toReal)
        (by positivity) hpt0.le).symm
    rw [h1, ENNReal.rpow_rpow_inv (ne_of_gt hpt0)]
  have hmain := ENNReal.tsum_le_tsum hdepth
  rw [ENNReal.tsum_mul_left] at hmain
  have hroot := ENNReal.rpow_le_rpow hmain hinv0
  rw [cubeEuclideanNegativeBesovESeminorm_eq_tsum_depthEnergy,
    cubeNegativeBesovDepthENorm]
  refine le_trans hroot (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ hinv0, hd]

/-! ## The bridge -/

/-- The dimension-only constant of the multiscale Poincaré bridge: the upstream
smooth-dual Besov constant times the dimension factor of
`norm_vecMul_le_dim_mul`. -/
def matHatNegBridgeConstant (d : ℕ) : ℝ≥0∞ :=
  cubeEuclideanNegativeWspSmoothDualBesovConstant d * (d : ℝ≥0∞)

theorem matHatNegBridgeConstant_lt_top (d : ℕ) :
    matHatNegBridgeConstant d < ∞ :=
  ENNReal.mul_lt_top (cubeEuclideanNegativeWspSmoothDualBesovConstant_lt_top d)
    (ENNReal.natCast_lt_top d)

/-- **The multiscale Poincaré bridge, bundled exponents.** For a continuous
matrix field the amended hatted negative norm on a triadic cube is bounded by
the printed `ℓ¹` depth sum of the sub-cube averages, with the dimension-only
constant `matHatNegBridgeConstant d` and the manuscript's own scale prefactor
`3 ^ (s * Q.scale)`. -/
theorem matHatNegENorm_le_cubeMultiscaleDepthSum_bundled (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) {M : Vec d → Mat d}
    (hM : Continuous M) :
    matHatNegENorm Q s.1 p.exponent M ≤
      matHatNegBridgeConstant d *
        ENNReal.ofReal ((3 : ℝ) ^ (s.1 * ((Q.scale : ℤ) : ℝ))) *
          cubeMultiscaleDepthSum Q s.1 p.exponent.toReal M := by
  have hpt1 : (1 : ℝ) ≤ p.exponent.toReal := by
    have h1 : (1 : ℝ≥0∞).toReal < p.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) (ne_of_lt p.lt_top)).2 p.one_lt
    have h2 : (1 : ℝ) < p.exponent.toReal := by simpa using h1
    exact h2.le
  refine le_trans
    (matHatNegENorm_le_iSup_cubeEuclideanNegativeWspSmoothDualENorm Q s p hM)
    ?_
  refine iSup_le fun v => iSup_le fun hv => ?_
  calc cubeEuclideanNegativeWspSmoothDualENorm Q s p (rowLpField Q hM v)
      ≤ cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          cubeEuclideanNegativeBesovESeminorm Q s p (rowLpField Q hM v) :=
        cubeEuclideanNegativeWspSmoothDualENorm_le_cubeEuclideanNegativeBesovESeminorm
          d Q s p (rowLpField Q hM v)
    _ ≤ cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          (ENNReal.ofReal (d : ℝ) *
            cubeNegativeBesovDepthENorm Q s.1 p.exponent.toReal M) :=
        mul_le_mul_right
          (cubeEuclideanNegativeBesovESeminorm_rowLpField_le Q s p hM hv) _
    _ ≤ cubeEuclideanNegativeWspSmoothDualBesovConstant d *
          (ENNReal.ofReal (d : ℝ) *
            (ENNReal.ofReal ((3 : ℝ) ^ (s.1 * ((Q.scale : ℤ) : ℝ))) *
              cubeMultiscaleDepthSum Q s.1 p.exponent.toReal M)) := by
        exact mul_le_mul_right (mul_le_mul_right
          (cubeNegativeBesovDepthENorm_le_cubeMultiscaleDepthSum Q hpt1 M) _) _
    _ = matHatNegBridgeConstant d *
          ENNReal.ofReal ((3 : ℝ) ^ (s.1 * ((Q.scale : ℤ) : ℝ))) *
            cubeMultiscaleDepthSum Q s.1 p.exponent.toReal M := by
        rw [matHatNegBridgeConstant, ENNReal.ofReal_natCast]
        ring

/-- **The multiscale Poincaré bridge**, in the plain-real exponent form of the
shell-increment clause: for `0 < s < 1`, `1 < p < ∞` and a continuous matrix
field `M`,

`‖M‖_{Ŵ̲^{-s,p}(Q)} ≤ C(d) · 3^{s · Q.scale} · ∑_j 3^{-sj} ((M)_j)^{1/p}`,

where the depth sum is `cubeMultiscaleDepthSum` and `C(d)` is
`matHatNegBridgeConstant d`. -/
theorem matHatNegENorm_le_cubeMultiscaleDepthSum (Q : TriadicCube d)
    {s p : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hp : 1 < p) {M : Vec d → Mat d}
    (hM : Continuous M) :
    matHatNegENorm Q s (ENNReal.ofReal p) M ≤
      matHatNegBridgeConstant d *
        ENNReal.ofReal ((3 : ℝ) ^ (s * ((Q.scale : ℤ) : ℝ))) *
          cubeMultiscaleDepthSum Q s p M := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  let sOrd : FractionalOrder := ⟨s, ⟨hs0, hs1⟩⟩
  let pExp : FiniteLpExponent :=
    { exponent := ENNReal.ofReal p
      one_lt := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by simp]
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one |>.2 hp
      lt_top := ENNReal.ofReal_lt_top }
  have htoReal : pExp.exponent.toReal = p := ENNReal.toReal_ofReal hp0.le
  have h := matHatNegENorm_le_cubeMultiscaleDepthSum_bundled Q sOrd pExp hM
  rwa [htoReal] at h

/-! ## The printed depth sum as a real number -/

/-- A real power of `3` with a natural exponent factor is the natural power
of the corresponding real power. -/
theorem rpow_three_mul_natCast (a : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (a * (n : ℝ)) = ((3 : ℝ) ^ a) ^ n := by
  rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_natCast]


private theorem volume_cubeSet_ne_zero (Q : TriadicCube d) :
    volume (cubeSet Q) ≠ 0 := by
  intro h
  have h2 : (volume (cubeSet Q)).toReal = cubeVolume Q := volume_cubeSet_toReal Q
  rw [h, ENNReal.toReal_zero] at h2
  exact (ne_of_gt (cubeVolume_pos Q)) h2.symm

private theorem abs_volumeAverage_le {U : Set (Vec d)}
    (hUb : Bornology.IsBounded U) (hUpos : volume U ≠ 0) {f : Vec d → ℝ}
    {C : ℝ} (hC : ∀ y ∈ U, |f y| ≤ C) : |volumeAverage U f| ≤ C := by
  have hfin : volume U ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono subset_closure)
      hUb.isCompact_closure.measure_lt_top)
  have hVpos : 0 < (volume U).toReal := ENNReal.toReal_pos hUpos hfin
  have hbound : ‖∫ y in U, f y ∂volume‖ ≤ C * (volume U).toReal := by
    have h := norm_setIntegral_le_of_norm_le_const
      (lt_of_le_of_ne le_top hfin) (f := fun y => f y) (C := C)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hC y hy)
    simpa only [MeasureTheory.Measure.real] using h
  have habs : |volumeAverage U f| =
      (volume U).toReal⁻¹ * |∫ y in U, f y ∂volume| := by
    rw [volumeAverage, abs_mul, abs_of_nonneg (inv_nonneg.2 hVpos.le)]
  rw [habs]
  have hstep : (volume U).toReal⁻¹ * |∫ y in U, f y ∂volume| ≤
      (volume U).toReal⁻¹ * (C * (volume U).toReal) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hVpos.le)
    simpa only [Real.norm_eq_abs] using hbound
  calc (volume U).toReal⁻¹ * |∫ y in U, f y ∂volume|
      ≤ (volume U).toReal⁻¹ * (C * (volume U).toReal) := hstep
    _ = C := by field_simp

/-- A continuous matrix field has a uniform bound on the averages over all
sub-cubes of a fixed triadic cube. -/
theorem exists_bound_norm_volumeAverageMat (Q : TriadicCube d)
    {M : Vec d → Mat d} (hM : Continuous M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : TriadicCube d, cubeSet R ⊆ cubeSet Q →
      ‖volumeAverageMat (cubeSet R) M‖ ≤ C := by
  classical
  have hcompact : IsCompact (closure (cubeSet Q)) :=
    (isBounded_cubeSet Q).isCompact_closure
  have hg : Continuous (fun x : Vec d => ∑ i : Fin d, ∑ l : Fin d, |M x i l|) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun l _ =>
      ((continuous_apply l).comp ((continuous_apply i).comp hM)).abs
  obtain ⟨C1, hC1⟩ := hcompact.exists_bound_of_continuousOn hg.continuousOn
  set C0 : ℝ := max C1 0 with hC0def
  have hC0nonneg : 0 ≤ C0 := le_max_right _ _
  have hentry : ∀ x ∈ cubeSet Q, ∀ i l : Fin d, |M x i l| ≤ C0 := by
    intro x hx i l
    have hxK : x ∈ closure (cubeSet Q) := subset_closure hx
    have hsum : ∑ i : Fin d, ∑ l : Fin d, |M x i l| ≤ C0 :=
      le_trans (le_trans (le_abs_self _)
        (by simpa only [Real.norm_eq_abs] using hC1 x hxK)) (le_max_left _ _)
    have hle : |M x i l| ≤ ∑ i : Fin d, ∑ l : Fin d, |M x i l| := by
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun i : Fin d => ∑ l : Fin d, |M x i l|)
        (fun i _ => Finset.sum_nonneg fun l _ => abs_nonneg _)
        (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun l : Fin d => |M x i l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ l)
    exact le_trans hle hsum
  refine ⟨(d : ℝ) * ((d : ℝ) * C0), by positivity, ?_⟩
  intro R hR
  have hbnd : ∀ i l : Fin d,
      |volumeAverageMat (cubeSet R) M i l| ≤ C0 := by
    intro i l
    refine abs_volumeAverage_le (isBounded_cubeSet R) (volume_cubeSet_ne_zero R) ?_
    intro y hy
    exact hentry y (hR hy) i l
  calc ‖volumeAverageMat (cubeSet R) M‖
      ≤ matrixFrobeniusNorm (volumeAverageMat (cubeSet R) M) :=
        matrixOperatorNorm_le_matrixFrobeniusNorm _
    _ ≤ ∑ i : Fin d, ∑ l : Fin d, |volumeAverageMat (cubeSet R) M i l| :=
        matrixFrobeniusNorm_le_sum_abs_entries _
    _ ≤ ∑ _i : Fin d, ∑ _l : Fin d, C0 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ => hbnd i l
    _ = (d : ℝ) * ((d : ℝ) * C0) := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The printed `ℓ¹` depth sum of `e.apply.multiscale.Poincare` as a real
number: the summand is the geometric weight `3^{-sj}` times the rooted
depth-`j` moment of the sub-cube averages. -/
def cubeMultiscaleDepthSumReal (Q : TriadicCube d) (s p : ℝ)
    (M : Vec d → Mat d) : ℝ :=
  ∑' j : ℕ, (3 : ℝ) ^ (-(s * (j : ℝ))) * cubeDepthPthMoment Q j p M ^ p⁻¹

/-- A uniform bound on the sub-cube averages bounds every rooted depth
moment. -/
theorem cubeDepthPthMoment_rpow_le_of_bound (Q : TriadicCube d) (j : ℕ)
    {p : ℝ} (hp : 0 < p) {M : Vec d → Mat d} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ R ∈ descendantsAtDepth Q j, ‖volumeAverageMat (cubeSet R) M‖ ≤ C) :
    cubeDepthPthMoment Q j p M ^ p⁻¹ ≤ C := by
  classical
  have hcardpos : (0 : ℝ) < ((descendantsAtDepth Q j).card : ℝ) := by
    have hne : (descendantsAtDepth Q j).Nonempty := descendantsAtDepth_nonempty Q j
    have : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero_of_mem hne.choose_spec
    exact lt_of_le_of_ne (by positivity) (Ne.symm this)
  have hsum : (descendantsAtDepth Q j).sum
      (fun R => ‖volumeAverageMat (cubeSet R) M‖ ^ p) ≤
      ((descendantsAtDepth Q j).card : ℝ) * C ^ p := by
    have := Finset.sum_le_sum (f := fun R => ‖volumeAverageMat (cubeSet R) M‖ ^ p)
      (g := fun _ : TriadicCube d => C ^ p) (s := descendantsAtDepth Q j)
      (fun R hR => Real.rpow_le_rpow (norm_nonneg _) (hb R hR) hp.le)
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hmom : cubeDepthPthMoment Q j p M ≤ C ^ p := by
    have hstep : ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        (descendantsAtDepth Q j).sum
          (fun R => ‖volumeAverageMat (cubeSet R) M‖ ^ p) ≤
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
          (((descendantsAtDepth Q j).card : ℝ) * C ^ p) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    calc cubeDepthPthMoment Q j p M
        = ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            (descendantsAtDepth Q j).sum
              (fun R => ‖volumeAverageMat (cubeSet R) M‖ ^ p) := rfl
      _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            (((descendantsAtDepth Q j).card : ℝ) * C ^ p) := hstep
      _ = C ^ p := by field_simp
  calc cubeDepthPthMoment Q j p M ^ p⁻¹
      ≤ (C ^ p) ^ p⁻¹ :=
        Real.rpow_le_rpow (cubeDepthPthMoment_nonneg Q j p M) hmom
          (le_of_lt (inv_pos.2 hp))
    _ = C := by
        rw [← Real.rpow_mul hC, mul_inv_cancel₀ (ne_of_gt hp), Real.rpow_one]

theorem cubeMultiscaleDepthTerm_nonneg (Q : TriadicCube d) (s p : ℝ)
    (M : Vec d → Mat d) (j : ℕ) :
    0 ≤ (3 : ℝ) ^ (-(s * (j : ℝ))) * cubeDepthPthMoment Q j p M ^ p⁻¹ := by
  have h1 : (0 : ℝ) < (3 : ℝ) ^ (-(s * (j : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (0 : ℝ) ≤ cubeDepthPthMoment Q j p M ^ p⁻¹ :=
    Real.rpow_nonneg (cubeDepthPthMoment_nonneg Q j p M) _
  positivity

/-- **The depth series converges at every sample.** For a continuous matrix
field on a triadic cube the rooted depth moments are bounded uniformly in the
depth, so the geometric weight `3^{-sj}` makes the printed depth sum a
convergent real series. -/
theorem summable_cubeMultiscaleDepthTerm (Q : TriadicCube d) {s p : ℝ}
    (hs0 : 0 < s) (hp : 0 < p) {M : Vec d → Mat d} (hM : Continuous M) :
    Summable (fun j : ℕ =>
      (3 : ℝ) ^ (-(s * (j : ℝ))) * cubeDepthPthMoment Q j p M ^ p⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_volumeAverageMat Q hM
  have hle : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) * cubeDepthPthMoment Q j p M ^ p⁻¹ ≤
        C * ((3 : ℝ) ^ (-s)) ^ j := by
    intro j
    have hmom : cubeDepthPthMoment Q j p M ^ p⁻¹ ≤ C :=
      cubeDepthPthMoment_rpow_le_of_bound Q j hp hC0
        (fun R hR => hC R (cubeSet_subset_of_mem_descendantsAtDepth hR))
    have hw : (3 : ℝ) ^ (-(s * (j : ℝ))) = ((3 : ℝ) ^ (-s)) ^ j := by
      rw [← rpow_three_mul_natCast, neg_mul_eq_neg_mul]
    rw [hw, mul_comm]
    exact mul_le_mul_of_nonneg_right hmom (by positivity)
  refine Summable.of_nonneg_of_le
    (fun j => cubeMultiscaleDepthTerm_nonneg Q s p M j) hle ?_
  refine Summable.mul_left C (summable_geometric_of_lt_one ?_ ?_)
  · exact le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])

theorem cubeMultiscaleDepthSumReal_nonneg (Q : TriadicCube d) (s p : ℝ)
    (M : Vec d → Mat d) : 0 ≤ cubeMultiscaleDepthSumReal Q s p M :=
  tsum_nonneg fun j => cubeMultiscaleDepthTerm_nonneg Q s p M j

/-- The `ℝ≥0∞` depth sum of `Section2/Norms/MultiscalePoincare.lean` is the
`ENNReal.ofReal` of the real depth sum. -/
theorem ofReal_cubeMultiscaleDepthSumReal (Q : TriadicCube d) {s p : ℝ}
    (hs0 : 0 < s) (hp : 0 < p) {M : Vec d → Mat d} (hM : Continuous M) :
    ENNReal.ofReal (cubeMultiscaleDepthSumReal Q s p M) =
      cubeMultiscaleDepthSum Q s p M := by
  rw [cubeMultiscaleDepthSumReal, cubeMultiscaleDepthSum,
    ENNReal.ofReal_tsum_of_nonneg (fun j => cubeMultiscaleDepthTerm_nonneg Q s p M j)
      (summable_cubeMultiscaleDepthTerm Q hs0 hp hM)]

/-! ## Subadditivity of the amended norm -/

private theorem ofReal_finset_sum_le {iota : Type*} (t : Finset iota)
    (a : iota → ℝ) :
    ENNReal.ofReal (∑ i ∈ t, a i) ≤ ∑ i ∈ t, ENNReal.ofReal (a i) := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact le_trans ENNReal.ofReal_add_le (add_le_add le_rfl ih)

private theorem vecMul_finset_sum {iota : Type*} (t : Finset iota) (v : Vec d)
    (A : iota → Mat d) :
    Matrix.vecMul v (∑ i ∈ t, A i) = ∑ i ∈ t, Matrix.vecMul v (A i) := by
  classical
  funext j
  simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Matrix.sum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]

/-- **The amended hatted negative norm is subadditive** on finite sums of
continuous matrix fields: the pairing density is linear in the field and the
supremum of a sum is at most the sum of the suprema. -/
theorem matHatNegENorm_finset_sum_le {Q : TriadicCube d} {s : ℝ} {p : ℝ≥0∞}
    {iota : Type*} (t : Finset iota) (F : iota → Vec d → Mat d)
    (hF : ∀ i ∈ t, Continuous (F i)) :
    matHatNegENorm Q s p (fun x => ∑ i ∈ t, F i x) ≤
      ∑ i ∈ t, matHatNegENorm Q s p (F i) := by
  classical
  refine matHatNegENorm_le fun v hv g hg => ?_
  have hdens : ∀ x : Vec d,
      matGradientPairingDensity (fun y => ∑ i ∈ t, F i y) v g x =
        ∑ i ∈ t, matGradientPairingDensity (F i) v g x := by
    intro x
    simp only [matGradientPairingDensity]
    rw [vecMul_finset_sum, map_sum]
  have hint : ∀ i ∈ t,
      IntegrableOn (matGradientPairingDensity (F i) v g) (cubeSet Q) volume :=
    fun i hi => matGradientPairingDensity_integrableOn_cubeSet (hF i hi)
      hg.contDiff v Q
  have havg : volumeAverage (cubeSet Q)
        (matGradientPairingDensity (fun y => ∑ i ∈ t, F i y) v g) =
      ∑ i ∈ t, volumeAverage (cubeSet Q)
        (matGradientPairingDensity (F i) v g) := by
    simp only [volumeAverage]
    rw [← Finset.mul_sum]
    refine congrArg (fun z : ℝ => ((volume (cubeSet Q)).toReal)⁻¹ * z) ?_
    rw [← integral_finsetSum _ hint]
    exact setIntegral_congr_fun (measurableSet_cubeSet Q) fun x _ => hdens x
  rw [havg]
  refine le_trans (ofReal_finset_sum_le t _) (Finset.sum_le_sum fun i _ => ?_)
  exact le_matHatNegENorm (F i) hv hg

end

end Norms
end Section2
end SuperdiffusionCLT
