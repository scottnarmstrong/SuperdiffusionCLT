/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5
public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section3.ResponseFields.Definitions
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Section2.Norms.FractionalHs
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Localization.BlockGaugeGroup
public import SuperdiffusionCLT.Probability.OrliczProduct
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Book.Ch02.MultiscaleEllipticity
public import Homogenization.Probability.IndependentSums.WeakOrlicz
public import Homogenization.Book.Ch02.Matrices

@[expose] public section

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

/-!
# The bell-upscale operator bound (`l.blupbounds`, display `e.blupbounds`)

The proposition `l.blupbounds` compares the coarse block matrices
`bfA_ell(U)` and `bfA_m(U)` of two levels `n < m < ell` on a cube `U`, after
the stream-cutoff increment `h_U = (k_ell - k_m)_U` is used as a gauge: it
bounds the operator norm of the upper-left blocks `(b_ell - b_m)(U)` by
`eps * |b_m(U)| + (1 + eps^{-1}) * |sigma_{m,*}^{-1/2}(U) h_U|^2 + a
`Gamma_{1/2}` tail of amplitude `C nu^{-3} ell 3^{n-m}`.

## The proof steps, as separate theorems

* `blockVecDot_blockMatVecMul_upperLeft` — `l.blupbounds#gauge-decomposition`
  (reading the upper-left block): the quadratic form of a block matrix at
  `(p, q)` expands over the four blocks; at `(p, 0)` it is `p · b p`.
* `young_cross_term` — `l.blupbounds#young-cross-term`: `2 a b <= eps a^2 +
  eps^{-1} b^2` at the scalar level.
* `matrixOperatorNorm_le_of_abs_quadratic_form_le` — the quadratic-form to
  operator-norm bridge for a symmetric matrix.

The main bound and the tail form of `e.blupbounds.remainder` are not stated in this module; the
corrected rendering of the bound is in `BellUpscaleBoundUnitSlice.lean` and `BellUpscaleBoundRemainder.lean`.

## The symmetry of the difference

The bridge to the operator norm needs the symmetry of the difference of the two coarse block
matrices: the upper-left block of `bfA_ell(U) - bfA_m(U)` is the symmetric matrix
`(b_ell - b_m)(U)`, in the matrix shape `(bL omega - bM omega).IsSymm`.  It holds for genuine
coarse block matrices because `isSymmetricBlockMat_coarseBlockMatrix` gives the symmetry of
each `bfA_j(U)` and symmetry is preserved by subtraction, cf.
`isSymmetricBlockMat_ofFullBlockMat_sub`.
-/

namespace SuperdiffusionCLT.Section3.Terms

variable {d : ℕ}

/-! ### Private vector algebra -/

private theorem vecDot_sub_left (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  ring

private theorem vecDot_sub_right (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  rw [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
  ring

private theorem vecNormSq_add (x y : Vec d) :
    vecNormSq (x + y) = vecNormSq x + vecDot x y + vecDot y x + vecNormSq y := by
  unfold vecNormSq
  rw [vecDot_add_left, vecDot_add_right, vecDot_add_right]
  ring

private theorem vecNormSq_sub (x y : Vec d) :
    vecNormSq (x - y) = vecNormSq x - vecDot x y - vecDot y x + vecNormSq y := by
  unfold vecNormSq
  rw [vecDot_sub_left, vecDot_sub_right, vecDot_sub_right]
  ring

/-- The parallelogram identity for `vecNormSq`. -/
private theorem vecNormSq_add_sub (x y : Vec d) :
    vecNormSq (x + y) + vecNormSq (x - y) = 2 * vecNormSq x + 2 * vecNormSq y := by
  rw [vecNormSq_add, vecNormSq_sub]
  ring

/-! ### Private block algebra -/

/-! ### The gauge algebra (`l.blupbounds#gauge-decomposition`) -/

/-! ### Public block algebra (`l.blupbounds#gauge-decomposition`) -/

/-- Reading the upper-left block: the quadratic form of a block matrix on the
unit-gradient slice `(p, 0)` is exactly `p · (upperLeft block) p`. -/
theorem blockVecDot_blockMatVecMul_upperLeft (A : BlockMat d) (p : Vec d) :
    blockVecDot (p, 0) (blockMatVecMul A (p, 0)) = vecDot p (matVecMul A.upperLeft p) := by
  simp [blockVecDot, blockMatVecMul_fst, blockMatVecMul_snd, matVecMul_zero,
    vecDot_zero_left, add_zero]

/-! ### Young's inequality (`l.blupbounds#young-cross-term`) -/

/-- Young's inequality `2 a b <= eps a^2 + eps^{-1} b^2` for `eps > 0`. -/
theorem young_cross_term (ep a b : ℝ) (hep : 0 < ep) :
    2 * a * b ≤ ep * a ^ 2 + ep⁻¹ * b ^ 2 := by
  have hne : ep ≠ 0 := ne_of_gt hep
  have hc : ∀ x : ℝ, ep⁻¹ * (ep * x) = x := by
    intro x
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hsq : 0 ≤ (ep * a - b) ^ 2 := sq_nonneg _
  have t1 : ep⁻¹ * ((ep * a - b) ^ 2)
      = ep⁻¹ * (ep * (ep * a ^ 2)) - 2 * (ep⁻¹ * (ep * a)) * b + ep⁻¹ * b ^ 2 := by
    ring
  -- now `t1 : ep⁻¹ * ((ep * a - b) ^ 2) = ep * a ^ 2 - 2 * a * b + ep⁻¹ * b ^ 2`
  have hnonneg : 0 ≤ ep * a ^ 2 - 2 * a * b + ep⁻¹ * b ^ 2 := by
    have h := mul_nonneg (inv_pos.mpr hep).le hsq
    rw [t1, hc (ep * a ^ 2), hc a] at h
    linarith only [h]
  linarith only [hnonneg]

/-! ### The quadratic-form to operator-norm bridge -/

/-- Polarization for a symmetric matrix: the bilinear pairing is recovered
from the quadratic form. -/
private theorem matVecMul_sub_right (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg]
  ring

private theorem vecDot_matVecMul_polarization {M : Mat d} (hM : M.IsSymm) (x y : Vec d) :
    vecDot x (matVecMul M y)
      = (vecDot (x + y) (matVecMul M (x + y))
          - vecDot (x - y) (matVecMul M (x - y))) / 4 := by
  rw [matVecMul_add M x y, matVecMul_sub_right M x y,
    vecDot_add_left x y (matVecMul M x + matVecMul M y),
    vecDot_add_right x (matVecMul M x) (matVecMul M y),
    vecDot_add_right y (matVecMul M x) (matVecMul M y),
    vecDot_sub_left x y (matVecMul M x - matVecMul M y),
    vecDot_sub_right x (matVecMul M x) (matVecMul M y),
    vecDot_sub_right y (matVecMul M x) (matVecMul M y),
    vecDot_matVecMul_comm_of_isSymm hM y x]
  ring

/-- A symmetric matrix whose quadratic form is absolutely bounded pointwise
by `B * |u|^2` has operator norm at most `B`: the Rayleigh-quotient
characterization of the Euclidean operator norm. -/
theorem matrixOperatorNorm_le_of_abs_quadratic_form_le (M : Mat d) (hM : M.IsSymm)
    (B : ℝ) (hB : 0 ≤ B)
    (hQ : ∀ u : Vec d, |vecDot u (matVecMul M u)| ≤ B * vecNormSq u) :
    matrixOperatorNorm M ≤ B := by
  -- pairing bound on unit vectors, via polarization
  have hunit : ∀ x y : Vec d, vecNormSq x = 1 → vecNormSq y = 1 →
      |vecDot x (matVecMul M y)| ≤ B := by
    intro x y hx hy
    have hadd := vecNormSq_add_sub x y
    rw [hx, hy] at hadd
    have e1 := hQ (x + y)
    have e2 := hQ (x - y)
    have htri : |vecDot (x + y) (matVecMul M (x + y))
          - vecDot (x - y) (matVecMul M (x - y))|
        ≤ |vecDot (x + y) (matVecMul M (x + y))|
          + |vecDot (x - y) (matVecMul M (x - y))| := by
      rw [sub_eq_add_neg]
      have h := abs_add_le (vecDot (x + y) (matVecMul M (x + y)))
        (-(vecDot (x - y) (matVecMul M (x - y))))
      rw [abs_neg] at h
      exact h
    have hpol := vecDot_matVecMul_polarization hM x y
    have habs : |vecDot x (matVecMul M y)|
        = |vecDot (x + y) (matVecMul M (x + y))
            - vecDot (x - y) (matVecMul M (x - y))| / 4 := by
      rw [hpol, abs_div, abs_of_pos (show (0 : ℝ) < 4 by norm_num)]
    have hcomb : |vecDot (x + y) (matVecMul M (x + y))|
          + |vecDot (x - y) (matVecMul M (x - y))|
        ≤ B * (vecNormSq (x + y) + vecNormSq (x - y)) := by
      have h := add_le_add e1 e2
      rw [← mul_add] at h
      exact h
    rw [hadd] at hcomb
    linarith only [htri, habs, hcomb]
  -- general pairing bound, by scaling
  have hpair : ∀ x y : Vec d, |vecDot x (matVecMul M y)| ≤ B * vecNorm x * vecNorm y := by
    intro x y
    by_cases hx0 : vecNorm x = 0
    · have hxz : x = 0 := vecNormSq_eq_zero_iff.mp (by
        rw [← vecNorm_sq_eq_vecNormSq, hx0]
        norm_num)
      rw [hx0, mul_zero, zero_mul, hxz, vecDot_zero_left, abs_zero]
    · by_cases hy0 : vecNorm y = 0
      · have hyz : matVecMul M y = 0 := by
          have hz0 : y = 0 := vecNormSq_eq_zero_iff.mp (by
            rw [← vecNorm_sq_eq_vecNormSq, hy0]
            norm_num)
          rw [hz0, matVecMul_zero]
        rw [hy0, mul_zero, hyz, vecDot_zero_right, abs_zero]
      · have hxpos : 0 < vecNorm x := lt_of_le_of_ne (vecNorm_nonneg x) (Ne.symm hx0)
        have hypos : 0 < vecNorm y := lt_of_le_of_ne (vecNorm_nonneg y) (Ne.symm hy0)
        have hxne : vecNorm x ≠ 0 := ne_of_gt hxpos
        have hyne : vecNorm y ≠ 0 := ne_of_gt hypos
        have hxinv : x = vecNorm x • ((vecNorm x)⁻¹ • x) := (smul_inv_smul₀ hxne x).symm
        have hyinv : y = vecNorm y • ((vecNorm y)⁻¹ • y) := (smul_inv_smul₀ hyne y).symm
        have hx1 : vecNormSq ((vecNorm x)⁻¹ • x) = 1 := by
          have h2 : vecNormSq x = vecNorm x ^ 2 := (vecNorm_sq_eq_vecNormSq x).symm
          rw [vecNormSq_smul, h2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hxne)]
        have hy1 : vecNormSq ((vecNorm y)⁻¹ • y) = 1 := by
          have h2 : vecNormSq y = vecNorm y ^ 2 := (vecNorm_sq_eq_vecNormSq y).symm
          rw [vecNormSq_smul, h2, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hyne)]
        have hscal : vecDot x (matVecMul M y)
            = vecNorm x * (vecNorm y * vecDot ((vecNorm x)⁻¹ • x)
                (matVecMul M ((vecNorm y)⁻¹ • y))) := by
          calc vecDot x (matVecMul M y)
              = vecDot (vecNorm x • ((vecNorm x)⁻¹ • x)) (matVecMul M y) := by
                conv_lhs => rw [hxinv]
            _ = vecNorm x * vecDot ((vecNorm x)⁻¹ • x) (matVecMul M y) :=
                vecDot_smul_left (vecNorm x) ((vecNorm x)⁻¹ • x) (matVecMul M y)
            _ = vecNorm x * vecDot ((vecNorm x)⁻¹ • x)
                  (matVecMul M (vecNorm y • ((vecNorm y)⁻¹ • y))) := by
                rw [← hyinv]
            _ = vecNorm x * (vecNorm y * vecDot ((vecNorm x)⁻¹ • x)
                  (matVecMul M ((vecNorm y)⁻¹ • y))) := by
                rw [matVecMul_smul M (vecNorm y) ((vecNorm y)⁻¹ • y),
                  vecDot_smul_right ((vecNorm x)⁻¹ • x)
                    (matVecMul M ((vecNorm y)⁻¹ • y)) (vecNorm y)]
        have hu := hunit ((vecNorm x)⁻¹ • x) ((vecNorm y)⁻¹ • y) hx1 hy1
        rw [hscal, abs_mul, abs_mul, abs_of_pos hxpos, abs_of_pos hypos]
        calc vecNorm x * (vecNorm y * |vecDot ((vecNorm x)⁻¹ • x)
              (matVecMul M ((vecNorm y)⁻¹ • y))|)
            ≤ vecNorm x * (vecNorm y * B) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hu (vecNorm_nonneg y)) (vecNorm_nonneg x)
          _ = B * vecNorm x * vecNorm y := by ring
  -- operator norm bound
  refine ContinuousLinearMap.opNorm_le_bound _ hB ?_
  intro x
  let ξ : Vec d := x.ofLp
  have hvec : vecNorm (matVecMul M ξ) ≤ B * vecNorm ξ := by
    by_cases hz : matVecMul M ξ = 0
    · have hz' : vecNorm (0 : Vec d) = 0 := by simp [vecNorm]
      rw [hz, hz']
      exact mul_nonneg hB (vecNorm_nonneg ξ)
    · have hn : vecNorm (matVecMul M ξ) ≠ 0 := by
        intro hcon
        have hsq : vecNormSq (matVecMul M ξ) = 0 := by
          rw [← vecNorm_sq_eq_vecNormSq, hcon]
          norm_num
        exact hz (vecNormSq_eq_zero_iff.mp hsq)
      have hnpos : 0 < vecNorm (matVecMul M ξ) :=
        lt_of_le_of_ne (vecNorm_nonneg (matVecMul M ξ)) (Ne.symm hn)
      -- pair the (normalized) response with itself: this realizes the norm
      have hpos : 0 ≤ vecDot (matVecMul M ξ) (matVecMul M ξ) :=
        vecNormSq_nonneg (matVecMul M ξ)
      have hsq : vecDot (matVecMul M ξ) (matVecMul M ξ)
          = vecNorm (matVecMul M ξ) * vecNorm (matVecMul M ξ) := by
        have h2 := vecNorm_sq_eq_vecNormSq (matVecMul M ξ)
        rw [pow_two] at h2
        exact h2.symm
      have hval : |vecDot ((vecNorm (matVecMul M ξ))⁻¹ • (matVecMul M ξ))
            (matVecMul M ξ)|
          = vecNorm (matVecMul M ξ) := by
        rw [vecDot_smul_left, abs_mul, abs_of_pos (inv_pos.mpr hnpos),
          abs_of_nonneg hpos, hsq, inv_mul_cancel_left₀ hn]
      have hp := hpair ((vecNorm (matVecMul M ξ))⁻¹ • (matVecMul M ξ)) ξ
      rw [hval] at hp
      have hsm : vecNorm ((vecNorm (matVecMul M ξ))⁻¹ • (matVecMul M ξ)) = 1 := by
        have h1 : vecNorm ((vecNorm (matVecMul M ξ))⁻¹ • (matVecMul M ξ))
            = |(vecNorm (matVecMul M ξ))⁻¹| * vecNorm (matVecMul M ξ) := by
          simp [vecNorm, norm_smul]
        rw [h1, abs_of_pos (inv_pos.mpr hnpos), inv_mul_cancel₀ hn]
      rw [hsm, mul_one] at hp
      linarith only [hp]
  have heq : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M x =
      WithLp.toLp 2 (matVecMul M ξ) := by
    conv_lhs => rw [← WithLp.toLp_ofLp (p := 2) x]
    rw [Matrix.toEuclideanCLM_toLp]
    rfl
  rw [heq]
  simpa [vecNorm, ξ] using hvec

/-! ### The scalar reduction behind the unscaled remainder bound -/

/-! ### The gauge identity (`l.blupbounds#gauge-decomposition`) -/

/-! ### The main bound (`l.blupbounds`) -/

/-! ### The remainder display (`e.blupbounds.remainder`) -/
