/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.MaximizerBridgeD
public import SuperdiffusionCLT.AKHC61.Response.CoarseAverages
public import Homogenization.CoarseGraining.QuadraticStability.CauchySchwarz
public import Homogenization.Book.Ch04.Theorems.CoarseObservables
public import Homogenization.Book.Ch04.Theorems.Expectations

/-!
# Squared weak norms, part A: block algebra under a one-sided Loewner bound

Deterministic inputs for the square-integrability of the scalar-response weak norms
(`hGradSq`/`hFluxSq` of `AKHC61/Response/JUpperBound.lean`). Everything here is samplewise and
law-free. For a symmetric, positive-semidefinite coarse block matrix `A` with
`A ≤ (1 + c)·E` in the Loewner order:

* `akhcWNSq_sq_blockVecDot_le`: `(X·AY)² ≤ (1+c)²·(X·EX)(Y·EY)` (Cauchy–Schwarz for `A`);
* `akhcWNSq_vecNormSq_snd_le`, `akhcWNSq_vecNormSq_fst_le`: the two halves of `A(−p, q)` are
  bounded by `(1+c)²` times a quantity depending on `E`, `p`, `q` only;
* `akhcWNSq_responseJ_eq`: `J(Q, p, q) = ½(−p, q)·bfA(Q)(−p, q) − p·q` at **every**
  a.e.-locally-elliptic sample (CG states it almost surely under a law carrier);
* `akhcWNSq_gradientAverage_self_le`, `akhcWNSq_fluxAverage_self_le`: the squared defects of
  the self-averages of the response gradient and flux are at most `(1+c)²` times a
  deterministic constant;
* `akhcWNSq_responseJ_le`: `J(Q, p, q) ≤ (1+c)·(½(−p,q)·E(−p,q) + |p·q|)`.

So each of these quantities is at most **quadratic** in `1 + c`, with `E`-dependent constants.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

noncomputable section

open Homogenization
open Homogenization.Book

variable {d : ℕ}

/-! ## Cauchy–Schwarz under a Loewner bound -/

/-- `(X·AY)² ≤ (1+c)²(X·EX)(Y·EY)` for a symmetric positive-semidefinite `A ≤ (1+c)E`. -/
theorem akhcWNSq_sq_blockVecDot_le {A E : BlockMat d} {c : ℝ}
    (hsym : IsSymmetricBlockMat A) (hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z))
    (hle : BlockMatLoewnerLE A ((1 + c) • E)) (X Y : BlockVec d) :
    (blockVecDot X (blockMatVecMul A Y)) ^ 2 ≤
      (1 + c) ^ 2 *
        (blockVecDot X (blockMatVecMul E X) * blockVecDot Y (blockMatVecMul E Y)) := by
  have hcs := abs_blockVecDot_blockMatVecMul_le_of_isSymmetricBlockMat hsym hpsd X Y
  have hX := blockVecDot_le_smul_of_blockMatLoewnerLE hle X
  have hY := blockVecDot_le_smul_of_blockMatLoewnerLE hle Y
  have hX0 := hpsd X
  have hY0 := hpsd Y
  have hsq :
      (blockVecDot X (blockMatVecMul A Y)) ^ 2 ≤
        blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := by
    rw [← sq_abs]
    calc
      |blockVecDot X (blockMatVecMul A Y)| ^ 2 ≤
          (Real.sqrt (blockVecDot X (blockMatVecMul A X)) *
            Real.sqrt (blockVecDot Y (blockMatVecMul A Y))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hcs 2
      _ = blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := by
        rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  calc
    (blockVecDot X (blockMatVecMul A Y)) ^ 2 ≤
        blockVecDot X (blockMatVecMul A X) * blockVecDot Y (blockMatVecMul A Y) := hsq
    _ ≤ ((1 + c) * blockVecDot X (blockMatVecMul E X)) *
          ((1 + c) * blockVecDot Y (blockMatVecMul E Y)) :=
        mul_le_mul hX hY hY0 (le_trans hX0 hX)
    _ = (1 + c) ^ 2 *
          (blockVecDot X (blockMatVecMul E X) * blockVecDot Y (blockMatVecMul E Y)) := by ring

/-! ## Coordinates of a block vector -/

theorem akhcWNSq_blockVecDot_zero_single (i : Fin d) (U : BlockVec d) :
    blockVecDot ((0 : Vec d), (Pi.single i 1 : Vec d)) U = U.2 i := by
  simp [blockVecDot, vecDot, Pi.single_apply]

theorem akhcWNSq_blockVecDot_single_zero (i : Fin d) (U : BlockVec d) :
    blockVecDot ((Pi.single i 1 : Vec d), (0 : Vec d)) U = U.1 i := by
  simp [blockVecDot, vecDot, Pi.single_apply]

/-- The `E`-constant of the lower half: `Σ_i (0,e_i)·E(0,e_i)`. -/
def akhcWNSq_lowerTrace (E : BlockMat d) : ℝ :=
  ∑ i : Fin d, blockVecDot ((0 : Vec d), (Pi.single i 1 : Vec d))
    (blockMatVecMul E ((0 : Vec d), (Pi.single i 1 : Vec d)))

/-- The `E`-constant of the upper half: `Σ_i (e_i,0)·E(e_i,0)`. -/
def akhcWNSq_upperTrace (E : BlockMat d) : ℝ :=
  ∑ i : Fin d, blockVecDot ((Pi.single i 1 : Vec d), (0 : Vec d))
    (blockMatVecMul E ((Pi.single i 1 : Vec d), (0 : Vec d)))

theorem akhcWNSq_vecNormSq_eq_sum_sq (y : Vec d) : vecNormSq y = ∑ i : Fin d, (y i) ^ 2 := by
  simp [vecNormSq, vecDot, pow_two]

/-- The lower half of `A Z` is bounded by `(1+c)²·(lowerTrace E)·(Z·EZ)`. -/
theorem akhcWNSq_vecNormSq_snd_le {A E : BlockMat d} {c : ℝ}
    (hsym : IsSymmetricBlockMat A) (hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z))
    (hle : BlockMatLoewnerLE A ((1 + c) • E)) (Z : BlockVec d) :
    vecNormSq (blockMatVecMul A Z).2 ≤
      (1 + c) ^ 2 * (akhcWNSq_lowerTrace E * blockVecDot Z (blockMatVecMul E Z)) := by
  rw [akhcWNSq_vecNormSq_eq_sum_sq, akhcWNSq_lowerTrace, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := akhcWNSq_sq_blockVecDot_le hsym hpsd hle ((0 : Vec d), (Pi.single i 1 : Vec d)) Z
  rwa [akhcWNSq_blockVecDot_zero_single] at h

/-- The upper half of `A Z` is bounded by `(1+c)²·(upperTrace E)·(Z·EZ)`. -/
theorem akhcWNSq_vecNormSq_fst_le {A E : BlockMat d} {c : ℝ}
    (hsym : IsSymmetricBlockMat A) (hpsd : ∀ Z : BlockVec d, 0 ≤ blockVecDot Z (blockMatVecMul A Z))
    (hle : BlockMatLoewnerLE A ((1 + c) • E)) (Z : BlockVec d) :
    vecNormSq (blockMatVecMul A Z).1 ≤
      (1 + c) ^ 2 * (akhcWNSq_upperTrace E * blockVecDot Z (blockMatVecMul E Z)) := by
  rw [akhcWNSq_vecNormSq_eq_sum_sq, akhcWNSq_upperTrace, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := akhcWNSq_sq_blockVecDot_le hsym hpsd hle ((Pi.single i 1 : Vec d), (0 : Vec d)) Z
  rwa [akhcWNSq_blockVecDot_single_zero] at h

/-! ## The response `J` at every a.e.-elliptic sample -/

/-- **Samplewise response identity.** At every a.e.-locally-uniformly-elliptic sample,
`J(Q, p, q) = ½(−p, q)·bfA(Q)(−p, q) − p·q`. -/
theorem akhcWNSq_responseJ_eq [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d) :
    Ch04.restrictionResponseJObservableCubeSet Q p q a =
      (1 / 2 : ℝ) *
          blockVecDot (-p, q) (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) (-p, q)) -
        vecDot p q := by
  have hId :=
    Ch02.ResponseJ_cubeSet_eq_Mu_neg_left_sub_vecDot
      (Q := Q) (a := Ch04.coeffOnOfAEEllipticOn a Q (ha Q)) p q
  rw [Ch04.coeffOnOfAEEllipticOn_toCoeffField] at hId
  have hex := Ch04.RestrictionLawCarrier.exists_coarseBlockMatrix_openCubeSet_of_aelocallyUniformlyEllipticField ha Q
  rw [Ch04.restrictionResponseJObservableCubeSet_apply, hId,
    Mu_cubeSet_eq_openCubeSet_of_triadicCube, Mu_eq_half_blockVecDot_coarseBlockMatrix hex,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]

/-- `J(Q, p, q) ≤ (1+c)·(½(−p,q)·E(−p,q) + |p·q|)` under `bfA(Q) ≤ (1+c)E`, `c ≥ 0`, no sign on `E` needed. -/
theorem akhcWNSq_responseJ_le [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q : Vec d)
    {E : BlockMat d} {c : ℝ} (hc : 0 ≤ c)
    (hle : BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a.toFun) ((1 + c) • E)) :
    Ch04.restrictionResponseJObservableCubeSet Q p q a ≤
      (1 + c) * ((1 / 2 : ℝ) * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) + |vecDot p q|) := by
  rw [akhcWNSq_responseJ_eq a ha Q p q]
  have h := blockVecDot_le_smul_of_blockMatLoewnerLE hle (-p, q)
  have habs := neg_abs_le (vecDot p q)
  have h1 : 0 ≤ c * |vecDot p q| := mul_nonneg hc (abs_nonneg _)
  nlinarith only [h, habs, h1]

/-! ## Self-averages of the response gradient and flux -/

/-- The squared defect of the self-average of the response gradient:
`|avg_Q ∇v_Q − p0|² ≤ (1+c)²·2·(lowerTrace E·(Z·EZ) + |p + p0|²)`, `Z = (−p, q)`. -/
theorem akhcWNSq_gradientAverage_self_le [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q p0 : Vec d)
    {E : BlockMat d} {c : ℝ} (hc : 0 ≤ c)
    (hsym : IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
    (hpsd : ∀ Z : BlockVec d,
      0 ≤ blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) Z))
    (hle : BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a.toFun) ((1 + c) • E)) :
    vecNormSq (Ch04.canonicalScalarResponseGradientAverageCubeSet Q Q p q a.toFun - p0) ≤
      (1 + c) ^ 2 *
        (2 * (akhcWNSq_lowerTrace E * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) +
          vecNormSq (p + p0))) := by
  rw [SuperdiffusionCLT.AKHC61.Response.akhc_canonicalScalarResponseGradientAverageCubeSet_self_eq_blockMatrix
    a ha Q p q]
  set A := coarseBlockMatrix (cubeSet Q) a.toFun with hA
  have hvec : -p + matVecMul A.lowerRight q - matVecMul A.lowerLeft p - p0 =
      (blockMatVecMul A (-p, q)).2 - (p + p0) := by
    funext i
    simp only [blockMatVecMul, matVecMul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib]
    ring
  rw [hvec]
  have h1 := vecNormSq_sub_le (blockMatVecMul A (-p, q)).2 (p + p0)
  have h2 := akhcWNSq_vecNormSq_snd_le hsym hpsd hle (-p, q)
  have hw := vecNormSq_nonneg (p + p0)
  have hsq : 1 ≤ (1 + c) ^ 2 := by nlinarith only [hc]
  have h3 : vecNormSq (p + p0) ≤ (1 + c) ^ 2 * vecNormSq (p + p0) := by
    nlinarith only [hsq, hw]
  nlinarith only [h1, h2, h3]

/-- The squared defect of the self-average of the response flux:
`|avg_Q a∇v_Q − q0|² ≤ (1+c)²·2·(upperTrace E·(Z·EZ) + |q − q0|²)`, `Z = (−p, q)`. -/
theorem akhcWNSq_fluxAverage_self_le [NeZero d] (a : RegCoeffField d)
    (ha : Ch04.AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (p q q0 : Vec d)
    {E : BlockMat d} {c : ℝ} (hc : 0 ≤ c)
    (hsym : IsSymmetricBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun))
    (hpsd : ∀ Z : BlockVec d,
      0 ≤ blockVecDot Z (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a.toFun) Z))
    (hle : BlockMatLoewnerLE (coarseBlockMatrix (cubeSet Q) a.toFun) ((1 + c) • E)) :
    vecNormSq (Ch04.canonicalScalarResponseFluxAverageCubeSet Q Q p q a.toFun - q0) ≤
      (1 + c) ^ 2 *
        (2 * (akhcWNSq_upperTrace E * blockVecDot (-p, q) (blockMatVecMul E (-p, q)) +
          vecNormSq (q - q0))) := by
  rw [SuperdiffusionCLT.AKHC61.Response.akhc_canonicalScalarResponseFluxAverageCubeSet_self_eq_blockMatrix
    a ha Q p q]
  set A := coarseBlockMatrix (cubeSet Q) a.toFun with hA
  have hvec : q + matVecMul A.upperRight q - matVecMul A.upperLeft p - q0 =
      (blockMatVecMul A (-p, q)).1 + (q - q0) := by
    funext i
    simp only [blockMatVecMul, matVecMul, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib]
    ring
  rw [hvec]
  have h1 := vecNormSq_add_le (blockMatVecMul A (-p, q)).1 (q - q0)
  have h2 := akhcWNSq_vecNormSq_fst_le hsym hpsd hle (-p, q)
  have hw := vecNormSq_nonneg (q - q0)
  have hsq : 1 ≤ (1 + c) ^ 2 := by nlinarith only [hc]
  have h3 : vecNormSq (q - q0) ≤ (1 + c) ^ 2 * vecNormSq (q - q0) := by
    nlinarith only [hsq, hw]
  nlinarith only [h1, h2, h3]

end

end SuperdiffusionCLT.AKHC61.WeakNorms
