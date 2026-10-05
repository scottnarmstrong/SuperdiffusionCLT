/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable
public import Homogenization.Ambient.Euclidean
public import Homogenization.Geometry.ConvexDomain
public import Homogenization.Geometry.CubeMeasure
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Two-point mean value for marginal shell fields

This module gives the ordinary two-point Euclidean mean-value inequality for a
marginal shell field: if the exact induced first-derivative norm
`matrixDerivativeNorm` is bounded by `B` along the Euclidean segment joining
`x` and `y`, then every entry of `j x - j y` is bounded by `B` times the
explicit Euclidean distance `euclideanDist x y`, and the matrix operator norm
`matrixOperatorNorm (j x - j y)` is bounded by the dimension constant `d` times
the same quantity. The entrywise bound is sharp; the matrix-level bound carries
the explicit constant `(d : ℝ)` because the stored derivative norm is induced
by the Euclidean vector norm while the ambient operator norm is compared
against the entrywise-controlled Frobenius norm. The same inequalities hold
when `x` and `y` both lie in the open realization `openCubeSet Q` or in the
half-open realization `cubeSet Q` of a triadic cube and `B` bounds the
derivative norm on that realization.

These are the pointwise two-point estimates behind the deterministic increment bounds of
the paper: the two-point increment `|j(x) - j(y)|` entering the shell `H^s`
clause through `min{1, 3^{-k}|x-y|}`, and the finite-increment
`L∞` bound `‖κ_m - κ_n‖_{L∞(cu_n)} ≤ √d 3^n ‖∇(κ_m - κ_n)‖_{L∞(cu_n)} +
|(κ_m - κ_n)(0)|`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization
open Homogenization.Book.Ch02
open Set
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Private scaling helpers for the stored first derivative

The exact induced derivative norm is controlled entrywise by the Euclidean size
of the direction.  These are local copies of the corresponding increment estimates of
Section 2 (`IncrementLinfty`), kept private here so that this assumptions-level module
does not depend on the Section 2 results. -/

private theorem matrixOperatorNorm_smul_real (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

private theorem vecNorm_smul_real (c : ℝ) (x : Vec d) :
    vecNorm (c • x) = |c| * vecNorm x := by
  have hsq : vecNorm (c • x) ^ 2 = (|c| * vecNorm x) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, vecNormSq_smul, mul_pow, sq_abs,
      vecNorm_sq_eq_vecNormSq]
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (vecNorm_nonneg _),
    Real.sqrt_sq (mul_nonneg (abs_nonneg c) (vecNorm_nonneg x))] at hsqrt

private theorem matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm
    (D : MatrixDerivative d) (v : Vec d) :
    matrixOperatorNorm (D v) ≤ matrixDerivativeNorm D * vecNorm v := by
  rcases eq_or_lt_of_le (vecNorm_nonneg v) with hzero | hpos
  · have hv : v = 0 := by
      refine vecNormSq_eq_zero ?_
      rw [← vecNorm_sq_eq_vecNormSq, ← hzero]
      norm_num
    rw [hv, map_zero, matrixOperatorNorm_zero]
    exact mul_nonneg (matrixDerivativeNorm_nonneg D) (vecNorm_nonneg 0)
  · have hunit : vecNorm ((vecNorm v)⁻¹ • v) ≤ 1 := by
      rw [vecNorm_smul_real, abs_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have hscale : D v = (vecNorm v) • D ((vecNorm v)⁻¹ • v) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [hscale, matrixOperatorNorm_smul_real, abs_of_nonneg hpos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (matrixOperatorNorm_apply_le_matrixDerivativeNorm D _ hunit)
      hpos.le

/-! ## The entry functional on matrices -/

private def entryCLM (i k : Fin d) : Mat d →L[ℝ] ℝ :=
  let row : Mat d →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.proj (R := ℝ) i
  let col : (Fin d → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) k
  col.comp row

@[simp] private theorem entryCLM_apply (i k : Fin d) (A : Mat d) :
    entryCLM i k A = A i k :=
  rfl

/-- The matrix operator norm is insensitive to negation. -/
theorem matrixOperatorNorm_neg_eq (A : Mat d) :
    matrixOperatorNorm (-A) = matrixOperatorNorm A := by
  unfold matrixOperatorNorm
  rw [map_neg, norm_neg]

/-! ## Euclidean size of a displacement -/

/-- The exact Euclidean vector norm is the square root of the coordinate
square sum. -/
theorem vecNorm_eq_sqrt_vecNormSq (x : Vec d) :
    vecNorm x = Real.sqrt (vecNormSq x) := by
  rw [← sq_eq_sq₀ (vecNorm_nonneg x) (Real.sqrt_nonneg _), vecNorm_sq_eq_vecNormSq,
    Real.sq_sqrt (vecNormSq_nonneg x)]

/-- The explicit Euclidean distance is the exact Euclidean vector norm of the
displacement, in either order. -/
theorem euclideanDist_eq_vecNorm_sub (x y : Vec d) :
    euclideanDist x y = vecNorm (y - x) := by
  have hswap : vecNormSq (y - x) = vecNormSq (x - y) := by
    unfold vecNormSq vecDot
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.sub_apply, sub_mul]
    ring
  calc euclideanDist x y = Real.sqrt (vecNormSq (x - y)) := rfl
    _ = Real.sqrt (vecNormSq (y - x)) := by rw [hswap]
    _ = vecNorm (y - x) := (vecNorm_eq_sqrt_vecNormSq _).symm

/-! ## Segment geometry -/

/-- Every point of the straight parametrized path from `x` to `y` lies on the
segment `[x, y]`. -/
theorem lineParam_mem_segment (x y : Vec d) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    x + t • (y - x) ∈ segment ℝ x y := by
  refine ⟨1 - t, t, ?_, ht.1, ?_, ?_⟩
  · linarith only [ht.2]
  · rw [sub_add_cancel]
  · have h1 : (1 - t) • x = x - t • x := by
      simp only [sub_smul, one_smul]
    have h2 : t • (y - x) = t • y - t • x := by
      simp only [smul_sub]
    rw [h1, h2]
    abel

/-- The half-open realization of a triadic cube is convex. -/
theorem convex_cubeSet (Q : TriadicCube d) : Convex ℝ (cubeSet Q) := by
  rw [cubeSet_eq_pi_Ico]
  refine convex_pi ?_
  intro i _
  exact convex_Ico _ _

/-! ## The two-point mean value along a segment -/

/-- The sharp two-point mean value entrywise: if the exact induced
first-derivative norm is bounded by `B` along the segment `[x, y]`, then each
entry of the value difference is bounded by `B` times the explicit Euclidean
distance.  This is the pointwise form of the manuscript's deterministic
increment bounds cited in the module docstring. -/
theorem abs_entry_sub_le_of_derivNorm_le_on_segment
    (j : ShellField d) {x y : Vec d} (B : ℝ)
    (hB : ∀ z ∈ segment ℝ x y, matrixDerivativeNorm (deriv j z) ≤ B)
    (i k : Fin d) :
    |j x i k - j y i k| ≤ B * euclideanDist x y := by
  set f : ℝ → ℝ := fun t ↦ (j (x + t • (y - x))) i k with hf
  set f' : ℝ → ℝ := fun t ↦ ((deriv j (x + t • (y - x))) (y - x)) i k with hf'
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ ↦ x + s • (y - x)) (y - x) t := by
      have hline := AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)
      have hfun : (fun s : ℝ ↦ x + s • (y - x)) = (AffineMap.lineMap x y) := by
        funext s
        rw [AffineMap.lineMap_apply_module]
        simp only [sub_smul, one_smul, smul_sub]
        abel
      rw [hfun]
      exact hline
    have hcomp : HasDerivAt (fun s : ℝ ↦ entryCLM i k (j (x + s • (y - x))))
        (entryCLM i k ((deriv j (x + t • (y - x))) (y - x))) t :=
      ((entryCLM i k).hasFDerivAt).comp_hasDerivAt t
        ((j.hasFDerivAt (x + t • (y - x))).comp_hasDerivAt t hpath)
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖f' t‖ ≤ B * euclideanDist x y := by
    intro t ht
    have hseg : x + t • (y - x) ∈ segment ℝ x y :=
      lineParam_mem_segment x y t (Ico_subset_Icc_self ht)
    calc
      ‖f' t‖ = |((deriv j (x + t • (y - x))) (y - x)) i k| :=
        Real.norm_eq_abs _
      _ ≤ matrixOperatorNorm ((deriv j (x + t • (y - x))) (y - x)) :=
        abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ matrixDerivativeNorm (deriv j (x + t • (y - x))) * vecNorm (y - x) :=
        matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ B * vecNorm (y - x) :=
        mul_le_mul_of_nonneg_right (hB _ hseg) (vecNorm_nonneg (y - x))
      _ = B * euclideanDist x y := by
        rw [euclideanDist_eq_vecNorm_sub]
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have hf1 : f 1 = j y i k := by
    show (j (x + (1 : ℝ) • (y - x))) i k = j y i k
    rw [show (x + (1 : ℝ) • (y - x) : Vec d) = y from by
      simp only [one_smul]
      abel]
  have hf0 : f 0 = j x i k := by
    simp only [hf, zero_smul, add_zero]
  rw [hf1, hf0] at hmean
  simpa only [Real.norm_eq_abs, sub_zero, mul_one, abs_sub_comm] using hmean

/-- The two-point mean value in the matrix operator norm.  The dimension
constant `(d : ℝ)` is explicit: the stored derivative norm is induced by the
Euclidean vector norm, while the operator norm of the value difference is
dominated by the entrywise-controlled Frobenius norm, so the proof compares
against the Frobenius norm over the `(d : ℝ) ^ 2` entries. -/
theorem matrixOperatorNorm_sub_le_of_derivNorm_le_on_segment
    (j : ShellField d) {x y : Vec d} (B : ℝ)
    (hB : ∀ z ∈ segment ℝ x y, matrixDerivativeNorm (deriv j z) ≤ B) :
    matrixOperatorNorm (j x - j y) ≤ (d : ℝ) * B * euclideanDist x y := by
  have hx : x ∈ segment ℝ x y := left_mem_segment ℝ x y
  have hBpos : 0 ≤ B :=
    (matrixDerivativeNorm_nonneg (deriv j x)).trans (hB x hx)
  have hentry : ∀ i k : Fin d, |(j x - j y) i k| ≤ B * euclideanDist x y := by
    intro i k
    exact abs_entry_sub_le_of_derivNorm_le_on_segment j B hB i k
  have hentrySq : ∀ i k : Fin d, ((j x - j y) i k) ^ 2 ≤
      (B * euclideanDist x y) ^ 2 := by
    intro i k
    calc
      (j x - j y) i k ^ 2 = |(j x - j y) i k| ^ 2 := (sq_abs _).symm
      _ ≤ (B * euclideanDist x y) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg hBpos (euclideanDist_nonneg x y))).mpr (hentry i k)
  have hsum : matrixFrobeniusNormSq (j x - j y) ≤
      ((d : ℝ) * (B * euclideanDist x y)) ^ 2 := by
    calc
      matrixFrobeniusNormSq (j x - j y) = ∑ i, ∑ k, (j x - j y) i k ^ 2 := rfl
      _ ≤ ∑ _i : Fin d, ∑ _k : Fin d, (B * euclideanDist x y) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun k _ ↦ hentrySq i k
      _ = ((d : ℝ) * (B * euclideanDist x y)) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
          Finset.card_univ, Fintype.card_fin, pow_two]
        ring
  have hfrob : matrixFrobeniusNorm (j x - j y) ≤
      (d : ℝ) * (B * euclideanDist x y) := by
    show Real.sqrt (matrixFrobeniusNormSq (j x - j y)) ≤
      (d : ℝ) * (B * euclideanDist x y)
    exact (Real.sqrt_le_sqrt hsum).trans
      (by rw [Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg d)
        (mul_nonneg hBpos (euclideanDist_nonneg x y)))])
  calc
    matrixOperatorNorm (j x - j y) ≤ matrixFrobeniusNorm (j x - j y) :=
      matrixOperatorNorm_le_matrixFrobeniusNorm _
    _ ≤ (d : ℝ) * (B * euclideanDist x y) := hfrob
    _ = (d : ℝ) * B * euclideanDist x y := by rw [mul_assoc]

/-! ## The cube versions -/

/-- The two-point mean value in the matrix operator norm on the open
realization of a triadic cube, with the explicit dimension constant
`(d : ℝ)`. -/
theorem matrixOperatorNorm_sub_le_of_derivNorm_le_on_openCubeSet
    (j : ShellField d) (Q : TriadicCube d) {x y : Vec d} (B : ℝ)
    (hB : ∀ z ∈ openCubeSet Q, matrixDerivativeNorm (deriv j z) ≤ B)
    (hx : x ∈ openCubeSet Q) (hy : y ∈ openCubeSet Q) :
    matrixOperatorNorm (j x - j y) ≤ (d : ℝ) * B * euclideanDist x y := by
  refine matrixOperatorNorm_sub_le_of_derivNorm_le_on_segment j B ?_
  intro z hz
  exact hB z ((convex_openCubeSet Q).segment_subset hx hy hz)

/-- The two-point mean value in the matrix operator norm on the half-open
realization of a triadic cube, with the explicit dimension constant
`(d : ℝ)`. -/
theorem matrixOperatorNorm_sub_le_of_derivNorm_le_on_cubeSet
    (j : ShellField d) (Q : TriadicCube d) {x y : Vec d} (B : ℝ)
    (hB : ∀ z ∈ cubeSet Q, matrixDerivativeNorm (deriv j z) ≤ B)
    (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet Q) :
    matrixOperatorNorm (j x - j y) ≤ (d : ℝ) * B * euclideanDist x y := by
  refine matrixOperatorNorm_sub_le_of_derivNorm_le_on_segment j B ?_
  intro z hz
  exact hB z ((convex_cubeSet Q).segment_subset hx hy hz)

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField