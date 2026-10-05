/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import SuperdiffusionCLT.Probability.GammaSigmaHelpers
public import SuperdiffusionCLT.Section2.Estimates.Stream.DerivativeConcentration
public import SuperdiffusionCLT.Section2.Estimates.Stream.PointConcentration

/-!
# Marginal finite-increment supremum envelope

This module gives the ordinary mean-value and concentration envelope behind
the manuscript's finite-increment `L∞` estimate on `cu_n`.  It does not define
or identify a literal `L∞` carrier.

The deterministic bridge controls every point of the cube by one measurable,
nonnegative random variable.  The probabilistic estimate combines the current
origin concentration and J3 derivative concentration, with no positive-gamma
scaling law or additional stochastic premise.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Estimates.Stream

open MeasureTheory
open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ShellSeq d)}

private def matrixEntryCLM (i l : Fin d) : Mat d →L[ℝ] ℝ :=
  let row : Mat d →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.proj (R := ℝ) i
  let entry : (Fin d → ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.proj (R := ℝ) l
  entry.comp row

@[simp] private theorem matrixEntryCLM_apply (i l : Fin d) (A : Mat d) :
    matrixEntryCLM i l A = A i l :=
  rfl

/-! ## Exact Euclidean norm scaling -/

/-- The exact Euclidean matrix operator norm is absolutely homogeneous. -/
theorem matrixOperatorNorm_smul_real (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  change ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (c • A)‖ =
    |c| * ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖
  rw [map_smul, norm_smul, Real.norm_eq_abs]

/-- The exact Euclidean vector norm is absolutely homogeneous. -/
theorem vecNorm_smul_real (c : ℝ) (x : Vec d) :
    vecNorm (c • x) = |c| * vecNorm x := by
  have hsq : vecNorm (c • x) ^ 2 = (|c| * vecNorm x) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, vecNormSq_smul, mul_pow, sq_abs,
      vecNorm_sq_eq_vecNormSq]
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (vecNorm_nonneg _),
    Real.sqrt_sq (mul_nonneg (abs_nonneg c) (vecNorm_nonneg x))] at hsqrt

/-- The exact induced first-derivative norm controls every matrix value, with
the Euclidean norm of the input as factor. -/
theorem matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm
    (D : ShellField.MatrixDerivative d) (v : Vec d) :
    matrixOperatorNorm (D v) ≤ ShellField.matrixDerivativeNorm D * vecNorm v := by
  rcases eq_or_lt_of_le (vecNorm_nonneg v) with hzero | hpos
  · have hv : v = 0 := by
      refine vecNormSq_eq_zero ?_
      rw [← vecNorm_sq_eq_vecNormSq, ← hzero]
      norm_num
    rw [hv, map_zero, matrixOperatorNorm_zero]
    exact mul_nonneg (ShellField.matrixDerivativeNorm_nonneg D) (vecNorm_nonneg 0)
  · have hunit : vecNorm ((vecNorm v)⁻¹ • v) ≤ 1 := by
      rw [vecNorm_smul_real, abs_of_nonneg (inv_nonneg.mpr hpos.le),
        inv_mul_cancel₀ hpos.ne']
    have hscale : D v = (vecNorm v) • D ((vecNorm v)⁻¹ • v) := by
      rw [map_smul, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
    rw [hscale, matrixOperatorNorm_smul_real, abs_of_nonneg hpos.le, mul_comm]
    exact mul_le_mul_of_nonneg_right
      (ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm D _ hunit)
      hpos.le

/-! ## Geometry of the natural origin cube -/

/-- The natural origin cube is star-shaped about the origin. -/
theorem smul_mem_openCubeSet_originCube {n : ℕ} {x : Vec d} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    t • x ∈ openCubeSet (originCube d (n : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff] at hx ⊢
  simp only [zpow_natCast] at hx ⊢
  intro i
  let R : ℝ := (3 : ℝ) ^ n / 2
  have hlo : -R < x i := by
    dsimp only [R]
    convert (hx i).1 using 1
    ring
  have hhi : x i < R := by
    dsimp only [R]
    convert (hx i).2 using 1
    ring
  have habsx : |x i| < R := (abs_lt).2 ⟨hlo, hhi⟩
  have habst : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have habsmul : |t * x i| ≤ |x i| := by
    rw [abs_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right habst (abs_nonneg (x i))
  have hlt : |t * x i| < R := habsmul.trans_lt habsx
  obtain ⟨hltLower, hltUpper⟩ := (abs_lt.mp hlt)
  have hLower : (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n < t * x i := by
    convert hltLower using 1
    dsimp only [R]
    ring
  have hUpper : t * x i < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    convert hltUpper using 1
    dsimp only [R]
    ring
  exact ⟨hLower, hUpper⟩

/-- Every point of `cu_n` has Euclidean norm at most `√d 3^n / 2`. -/
theorem vecNorm_le_of_mem_openCubeSet_originCube {n : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    vecNorm x ≤ Real.sqrt d * ((3 : ℝ) ^ n / 2) := by
  have hcube := mem_openCubeSet_originCube_iff.mp hx
  simp only [zpow_natCast] at hcube
  let R : ℝ := (3 : ℝ) ^ n / 2
  have hR_nonneg : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hsq : vecNormSq x ≤ (d : ℝ) * R ^ 2 := by
    have hstep : ∀ i : Fin d, x i * x i ≤ R ^ 2 := by
      intro i
      have hlo : -R < x i := by
        dsimp only [R]
        convert (hcube i).1 using 1
        ring
      have hhi : x i < R := by
        dsimp only [R]
        convert (hcube i).2 using 1
        ring
      have habs : |x i| ≤ R := ((abs_lt).2 ⟨hlo, hhi⟩).le
      have hsquare : (x i) ^ 2 ≤ R ^ 2 := by
        rw [sq_le_sq]
        simpa only [abs_of_nonneg hR_nonneg] using habs
      simpa only [pow_two] using hsquare
    calc
      vecNormSq x = ∑ i, x i * x i := rfl
      _ ≤ ∑ _i : Fin d, R ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hstep i
      _ = (d : ℝ) * R ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hB : 0 ≤ Real.sqrt d * R :=
    mul_nonneg (Real.sqrt_nonneg _) hR_nonneg
  have hsq' : vecNorm x ^ 2 ≤ (Real.sqrt d * R) ^ 2 := by
    rw [vecNorm_sq_eq_vecNormSq, mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg d)]
    exact hsq
  have hsqrt := Real.sqrt_le_sqrt hsq'
  dsimp only [R] at hB ⊢
  rwa [Real.sqrt_sq (vecNorm_nonneg x), Real.sqrt_sq hB] at hsqrt

/-! ## Entrywise mean value and the deterministic envelope -/

/-- The mean value estimate along the segment from the origin for one entry
of the finite increment. -/
theorem abs_entry_finiteShellIncrement_sub_origin_le
    (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) (i l : Fin d) :
    |finiteShellIncrement omega n m x i l -
        finiteShellIncrement omega n m 0 i l| ≤
      finiteShellDerivGauge n m omega * vecNorm x := by
  set f : ℝ → ℝ := fun t ↦
    matrixEntryCLM i l (finiteShellIncrement omega n m (t • x)) with hf
  set f' : ℝ → ℝ := fun t ↦
    matrixEntryCLM i l
      ((∑ k ∈ Finset.Ioc n m, ShellField.deriv (omega k) (t • x)) x) with hf'
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt f (f' t) (Set.Icc (0 : ℝ) 1) t := by
    intro t _
    have hpath : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
      have h := (hasDerivAt_id t).smul_const x
      simp only [one_smul, id] at h
      exact h
    have hsum :=
      finiteShellIncrement_hasFDerivAt_sum_shellDeriv omega n m (t • x)
    exact (((matrixEntryCLM i l).hasFDerivAt).comp_hasDerivAt t
      (hsum.comp_hasDerivAt t hpath)).hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖f' t‖ ≤ finiteShellDerivGauge n m omega * vecNorm x := by
    intro t ht
    have htx : t • x ∈ openCubeSet (originCube d (n : ℤ)) :=
      smul_mem_openCubeSet_originCube ⟨ht.1, ht.2.le⟩ hx
    calc
      ‖f' t‖ =
          |((∑ k ∈ Finset.Ioc n m,
            ShellField.deriv (omega k) (t • x)) x) i l| := rfl
      _ ≤ matrixOperatorNorm
          ((∑ k ∈ Finset.Ioc n m,
            ShellField.deriv (omega k) (t • x)) x) :=
        abs_entry_le_matrixOperatorNorm _ _ _
      _ ≤ ShellField.matrixDerivativeNorm
            (∑ k ∈ Finset.Ioc n m,
              ShellField.deriv (omega k) (t • x)) * vecNorm x :=
        matrixOperatorNorm_apply_le_matrixDerivativeNorm_mul_vecNorm _ _
      _ ≤ finiteShellDerivGauge n m omega * vecNorm x :=
        mul_le_mul_of_nonneg_right
          (matrixDerivativeNorm_sum_shellDeriv_le_finiteShellDerivGauge
            omega n m htx)
          (vecNorm_nonneg x)
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound 1
    (Set.mem_Icc.mpr ⟨by norm_num, le_rfl⟩)
  have hf1 : f 1 = finiteShellIncrement omega n m x i l := by
    simp only [hf, one_smul]
    rfl
  have hf0 : f 0 = finiteShellIncrement omega n m 0 i l := by
    simp only [hf, zero_smul]
    rfl
  rw [hf1, hf0] at hmean
  simpa only [Real.norm_eq_abs, sub_zero, mul_one] using hmean

/-- A measurable random envelope for all values of the finite increment on
`cu_n`. -/
def incrementSupBound (n m : ℕ) (omega : ShellSeq d) : ℝ :=
  matrixOperatorNorm (finiteShellIncrement omega n m 0) +
    (d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2) *
      finiteShellDerivGauge n m omega

/-- Every point of `cu_n` is dominated by the common finite-increment
envelope. -/
theorem matrixOperatorNorm_finiteShellIncrement_le_incrementSupBound
    (omega : ShellSeq d) (n m : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    matrixOperatorNorm (finiteShellIncrement omega n m x) ≤
      incrementSupBound n m omega := by
  have hG := finiteShellDerivGauge_nonneg n m omega
  have hvec := vecNorm_le_of_mem_openCubeSet_originCube (d := d) hx
  have hentries :
      ∑ i : Fin d, ∑ l : Fin d,
        |finiteShellIncrement omega n m x i l -
          finiteShellIncrement omega n m 0 i l| ≤
        (d : ℝ) ^ 2 *
          (finiteShellDerivGauge n m omega *
            (Real.sqrt d * ((3 : ℝ) ^ n / 2))) := by
    have hstep : ∀ i : Fin d, ∀ l : Fin d,
        |finiteShellIncrement omega n m x i l -
          finiteShellIncrement omega n m 0 i l| ≤
        finiteShellDerivGauge n m omega *
          (Real.sqrt d * ((3 : ℝ) ^ n / 2)) := by
      intro i l
      exact (abs_entry_finiteShellIncrement_sub_origin_le
        omega n m hx i l).trans
          (mul_le_mul_of_nonneg_left hvec hG)
    calc
      ∑ i : Fin d, ∑ l : Fin d,
          |finiteShellIncrement omega n m x i l -
            finiteShellIncrement omega n m 0 i l| ≤
          ∑ _i : Fin d, ∑ _l : Fin d,
            finiteShellDerivGauge n m omega *
              (Real.sqrt d * ((3 : ℝ) ^ n / 2)) :=
        Finset.sum_le_sum fun i _ ↦
          Finset.sum_le_sum fun l _ ↦ hstep i l
      _ = (d : ℝ) ^ 2 *
          (finiteShellDerivGauge n m omega *
            (Real.sqrt d * ((3 : ℝ) ^ n / 2))) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul, ← mul_assoc]
        ring
  refine (matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries
    (finiteShellIncrement omega n m x)
    (finiteShellIncrement omega n m 0)).trans ?_
  rw [incrementSupBound]
  exact add_le_add (le_refl _) (hentries.trans (le_of_eq (by ring)))

/-! ## Measurability and positivity -/

/-- The matrix operator norm of the finite increment at the origin is
measurable. -/
theorem measurable_matrixOperatorNorm_finiteShellIncrement_origin (n m : ℕ) :
    Measurable (fun omega : ShellSeq d ↦
      matrixOperatorNorm (finiteShellIncrement omega n m 0)) := by
  have hmatrix : Measurable (fun omega : ShellSeq d ↦
      finiteShellIncrement omega n m 0) := by
    exact measurable_matrix_of_entries fun i l ↦
      (measurable_apply_entry (0 : Vec d) i l).comp
        (measurable_finiteShellIncrement n m)
  exact ShellField.continuous_matrixOperatorNorm.measurable.comp hmatrix

/-- The finite-increment supremum envelope is measurable. -/
theorem measurable_incrementSupBound (n m : ℕ) :
    Measurable (incrementSupBound n m : ShellSeq d → ℝ) := by
  change Measurable (fun omega : ShellSeq d ↦
    matrixOperatorNorm (finiteShellIncrement omega n m 0) +
      ((d : ℝ) ^ 2 * Real.sqrt d * ((3 : ℝ) ^ n / 2)) *
        finiteShellDerivGauge n m omega)
  exact (measurable_matrixOperatorNorm_finiteShellIncrement_origin n m).add
    ((measurable_finiteShellDerivGauge n m).const_mul _)

/-- The finite-increment supremum envelope is nonnegative. -/
theorem incrementSupBound_nonneg (n m : ℕ) (omega : ShellSeq d) :
    0 ≤ incrementSupBound n m omega := by
  exact add_nonneg (matrixOperatorNorm_nonneg _)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (sq_nonneg (d : ℝ)) (Real.sqrt_nonneg d))
        (div_nonneg (pow_nonneg (by norm_num) n) (by norm_num)))
      (finiteShellDerivGauge_nonneg n m omega))

/-! ## The Gamma₂ estimate -/

/-- The explicit dimensional constant in the marginal finite-increment
supremum envelope. -/
def streamLinftyConst (d : ℕ) : ℝ :=
  IndependentSums.gammaTriangleConst 2 ^ 2 * (d : ℝ) ^ 2 *
    (Book.Ch04.gammaSigmaIndependentSumConst 2 + Real.sqrt d / 2)

/-- The explicit stream supremum constant is positive in every positive
dimension: it depends on `d` alone, so its positivity needs no probabilistic
data. -/
theorem streamLinftyConst_pos_of_pos (hd : 0 < d) : 0 < streamLinftyConst d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have htriangle : 0 < IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos
  have hbracket :
      0 < Book.Ch04.gammaSigmaIndependentSumConst 2 + Real.sqrt d / 2 :=
    lt_of_lt_of_le gammaSigmaIndependentSumConst_two_pos
      (le_add_of_nonneg_right
        (div_nonneg (Real.sqrt_nonneg d) (by norm_num)))
  rw [streamLinftyConst]
  exact mul_pos (mul_pos (sq_pos_of_pos htriangle) (sq_pos_of_pos hdR)) hbracket

/-- The explicit stream supremum constant is positive under the standing
dimension condition. -/
theorem streamLinftyConst_pos (hPrefix : ShellLawPrefix d P) :
    0 < streamLinftyConst d :=
  streamLinftyConst_pos_of_pos (lt_of_lt_of_le (by norm_num) hPrefix.dimension)

end

end SuperdiffusionCLT.Section2.Estimates.Stream
