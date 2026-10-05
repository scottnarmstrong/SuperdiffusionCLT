/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import SuperdiffusionCLT.Assumptions.ShellField.Basic
public import Homogenization.Book.Ch02.Theorems.MatrixOperatorNorm
public import Homogenization.Geometry.CubeMetric

/-!
# The marginal J3 shell observable

This module defines the induced Euclidean norms used in the marginal paper's
J3 regularity observable. The shell norms below will be taken directly on the
natural open cube at each Nat-indexed scale; no unit-cube scaling transport is
used.

The matrix value norm is
`Homogenization.Book.Ch02.matrixOperatorNorm`. Derivative inputs use
`Homogenization.Book.Ch02.vecNorm`. The stored first and second derivatives
remain bundled with the carrier's elementwise matrix norm, while their
exact Euclidean induced norms are explicit scalar suprema including zero.
-/

@[expose] public section

open scoped BigOperators Matrix.Norms.Elementwise NNReal

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Set
open Homogenization
open Homogenization.Book.Ch02

/-! ## Instance caches for the derivative carriers

These are the recurring instances for the first- and second-derivative
continuous-linear-map carriers. They are cached once at module level so the
induced-norm proofs do not repeatedly synthesize the same nested structures.
-/

private noncomputable instance instTopDerivCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instTopHessianCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instAddCommMonoidDerivCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instAddCommMonoidHessianCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instSMulDerivCarrier (d : ℕ) :
    SMul ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instSMulHessianCarrier (d : ℕ) :
    SMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instModuleDerivCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instModuleHessianCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instNormedSpaceDerivCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Mat d) := inferInstance

private noncomputable instance instNormedSpaceHessianCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

private noncomputable instance instNormedSpaceEndoCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Vec d) := inferInstance

noncomputable section

variable {d : ℕ}

/-- The stored first-derivative type of a shell field.  Its bundle uses the
elementwise matrix norm fixed by the carrier; exact Euclidean sizes are
measured separately by `matrixDerivativeNorm`. -/
abbrev MatrixDerivative (d : ℕ) := Vec d →L[ℝ] Mat d

abbrev EuclideanUnitVector (d : ℕ) :=
  {v : Vec d // vecNorm v ≤ 1}

/-- Values used for the exact Euclidean induced norm.  The `none` branch
records zero explicitly, including in dimension zero. -/
def matrixDerivativeNormValue (D : MatrixDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some v => matrixOperatorNorm (D v.1)

def matrixDerivativeNormValueSet (D : MatrixDerivative d) : Set ℝ :=
  Set.range (matrixDerivativeNormValue D)

/-- Euclidean-vector to Euclidean-matrix induced norm, evaluated on the
carrier's actual elementwise-norm continuous-linear-map bundle. -/
def matrixDerivativeNorm (D : MatrixDerivative d) : ℝ :=
  sSup (matrixDerivativeNormValueSet D)

theorem norm_vec_le_vecNorm (v : Vec d) : ‖v‖ ≤ vecNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vecNorm_nonneg v)]
  intro i
  rw [Real.norm_eq_abs]
  exact abs_le_of_sq_le_sq
    (by
      simpa only [vecNorm_sq_eq_vecNormSq] using
        sq_apply_le_vecNormSq v i)
    (vecNorm_nonneg v)

private theorem sum_abs_entries_le (A : Mat d) :
    (∑ i, ∑ j, |A i j|) ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  calc
    (∑ i, ∑ j, |A i j|) ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ := by
      gcongr with i j
      simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, pow_two]
      ring

private theorem matrixOperatorNorm_le_sq_mul_norm (A : Mat d) :
    matrixOperatorNorm A ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    ((matrixFrobeniusNorm_le_sum_abs_entries A).trans (sum_abs_entries_le A))

private theorem norm_matrixOperatorNorm_sub_le_sq_mul_norm (A B : Mat d) :
    ‖matrixOperatorNorm A - matrixOperatorNorm B‖ ≤
      (d : ℝ) ^ 2 * ‖A - B‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries B A
    have hsum := sum_abs_entries_le (B - A)
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      rw [show B - A = -(A - B) by abel, norm_neg]
    calc
      matrixOperatorNorm B ≤ matrixOperatorNorm A +
          ∑ i, ∑ j, |B i j - A i j| := h
      _ ≤ matrixOperatorNorm A + (d : ℝ) ^ 2 * ‖A - B‖ := by
        gcongr
        simpa only [hnorm, Matrix.sub_apply] using hsum
  · rw [sub_le_iff_le_add]
    have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A B
    calc
      matrixOperatorNorm A ≤ matrixOperatorNorm B +
          ∑ i, ∑ j, |A i j - B i j| := h
      _ ≤ matrixOperatorNorm B + (d : ℝ) ^ 2 * ‖A - B‖ := by
        gcongr
        exact sum_abs_entries_le (A - B)
      _ = (d : ℝ) ^ 2 * ‖A - B‖ + matrixOperatorNorm B := add_comm _ _

private theorem matrixOperatorNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixOperatorNorm : Mat d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using
    norm_matrixOperatorNorm_sub_le_sq_mul_norm A B

private theorem matrixOperatorNorm_continuous :
    Continuous (matrixOperatorNorm : Mat d → ℝ) :=
  matrixOperatorNorm_lipschitz.continuous

private theorem matrixDerivativeNormValueSet_nonempty (D : MatrixDerivative d) :
    (matrixDerivativeNormValueSet D).Nonempty := by
  exact ⟨0, none, rfl⟩

private theorem matrixDerivativeNormValue_le_sq_mul_norm (D : MatrixDerivative d)
    (o : Option (EuclideanUnitVector d)) :
    matrixDerivativeNormValue D o ≤ (d : ℝ) ^ 2 * ‖D‖ := by
  cases o with
  | none => positivity
  | some v =>
      calc
        matrixOperatorNorm (D v.1) ≤ (d : ℝ) ^ 2 * ‖D v.1‖ :=
          matrixOperatorNorm_le_sq_mul_norm _
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * ‖v.1‖) := by
          gcongr
          exact D.le_opNorm _
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * vecNorm v.1) := by
          gcongr
          exact norm_vec_le_vecNorm v.1
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * 1) := by
          gcongr
          exact v.2
        _ = (d : ℝ) ^ 2 * ‖D‖ := by ring

private theorem matrixDerivativeNormValueSet_bddAbove (D : MatrixDerivative d) :
    BddAbove (matrixDerivativeNormValueSet D) := by
  refine ⟨(d : ℝ) ^ 2 * ‖D‖, ?_⟩
  rintro r ⟨o, rfl⟩
  exact matrixDerivativeNormValue_le_sq_mul_norm D o

theorem matrixDerivativeNorm_nonneg (D : MatrixDerivative d) :
    0 ≤ matrixDerivativeNorm D := by
  exact le_csSup (matrixDerivativeNormValueSet_bddAbove D) ⟨none, rfl⟩

private theorem matrixDerivativeNormValue_le (D : MatrixDerivative d)
    (o : Option (EuclideanUnitVector d)) :
    matrixDerivativeNormValue D o ≤ matrixDerivativeNorm D := by
  exact le_csSup (matrixDerivativeNormValueSet_bddAbove D) ⟨o, rfl⟩

/-- The exact induced derivative norm controls every matrix value on the
`vecNorm` unit ball. -/
theorem matrixOperatorNorm_apply_le_matrixDerivativeNorm
    (D : MatrixDerivative d) (v : Vec d) (hv : vecNorm v ≤ 1) :
    matrixOperatorNorm (D v) ≤ matrixDerivativeNorm D :=
  matrixDerivativeNormValue_le D (some ⟨v, hv⟩)

theorem matrixDerivativeNorm_le_sq_mul_norm (D : MatrixDerivative d) :
    matrixDerivativeNorm D ≤ (d : ℝ) ^ 2 * ‖D‖ := by
  apply csSup_le (matrixDerivativeNormValueSet_nonempty D)
  rintro r ⟨o, rfl⟩
  exact matrixDerivativeNormValue_le_sq_mul_norm D o

theorem matrixDerivativeNorm_add_le (D E : MatrixDerivative d) :
    matrixDerivativeNorm (D + E) ≤ matrixDerivativeNorm D + matrixDerivativeNorm E := by
  apply csSup_le (matrixDerivativeNormValueSet_nonempty (D + E))
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact add_nonneg (matrixDerivativeNorm_nonneg D) (matrixDerivativeNorm_nonneg E)
  | some v =>
      calc
        matrixOperatorNorm ((D + E) v.1) =
            matrixOperatorNorm (D v.1 + E v.1) := rfl
        _ ≤ matrixOperatorNorm (D v.1) + matrixOperatorNorm (E v.1) := by
          simpa only [matrixOperatorNorm, map_add] using
            norm_add_le
              (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (D v.1))
              (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (E v.1))
        _ ≤ matrixDerivativeNorm D + matrixDerivativeNorm E :=
          add_le_add (matrixDerivativeNormValue_le D (some v))
            (matrixDerivativeNormValue_le E (some v))

@[simp] theorem matrixDerivativeNorm_neg (D : MatrixDerivative d) :
    matrixDerivativeNorm (-D) = matrixDerivativeNorm D := by
  unfold matrixDerivativeNorm matrixDerivativeNormValueSet
  refine congrArg sSup ?_
  ext r
  constructor
  · rintro ⟨o, rfl⟩
    refine ⟨o, ?_⟩
    cases o <;>
      simp only [matrixDerivativeNormValue, matrixOperatorNorm,
        neg_apply, map_neg, norm_neg]
  · rintro ⟨o, rfl⟩
    refine ⟨o, ?_⟩
    cases o <;>
      simp only [matrixDerivativeNormValue, matrixOperatorNorm,
        neg_apply, map_neg, norm_neg]

theorem norm_matrixDerivativeNorm_sub_le_sq_mul_norm (D E : MatrixDerivative d) :
    ‖matrixDerivativeNorm D - matrixDerivativeNorm E‖ ≤
      (d : ℝ) ^ 2 * ‖D - E‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have hDE : matrixDerivativeNorm D ≤
      matrixDerivativeNorm (D - E) + matrixDerivativeNorm E := by
    simpa only [sub_add_cancel] using matrixDerivativeNorm_add_le (D - E) E
  have hED : matrixDerivativeNorm E ≤
      matrixDerivativeNorm (E - D) + matrixDerivativeNorm D := by
    simpa only [sub_add_cancel] using matrixDerivativeNorm_add_le (E - D) D
  constructor
  · rw [neg_le_sub_iff_le_add]
    calc
      matrixDerivativeNorm E ≤ matrixDerivativeNorm (E - D) + matrixDerivativeNorm D := hED
      _ = matrixDerivativeNorm (D - E) + matrixDerivativeNorm D := by
        rw [show E - D = -(D - E) by abel, matrixDerivativeNorm_neg]
      _ ≤ (d : ℝ) ^ 2 * ‖D - E‖ + matrixDerivativeNorm D := by
        gcongr
        exact matrixDerivativeNorm_le_sq_mul_norm (D - E)
      _ = matrixDerivativeNorm D + (d : ℝ) ^ 2 * ‖D - E‖ := add_comm _ _
  · rw [sub_le_iff_le_add]
    calc
      matrixDerivativeNorm D ≤
          matrixDerivativeNorm (D - E) + matrixDerivativeNorm E := hDE
      _ ≤ (d : ℝ) ^ 2 * ‖D - E‖ + matrixDerivativeNorm E := by
        gcongr
        exact matrixDerivativeNorm_le_sq_mul_norm (D - E)

theorem matrixDerivativeNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixDerivativeNorm : MatrixDerivative d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro D E
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using
    norm_matrixDerivativeNorm_sub_le_sq_mul_norm D E

theorem matrixDerivativeNorm_continuous :
    Continuous (matrixDerivativeNorm : MatrixDerivative d → ℝ) :=
  matrixDerivativeNorm_lipschitz.continuous

/-- The stored second-derivative type of a shell field.  It is a linear map
in the first derivative direction with values in `MatrixDerivative d`. -/
abbrev MatrixSecondDerivative (d : ℕ) :=
  Vec d →L[ℝ] MatrixDerivative d

/-- Values used for the exact twice-induced Euclidean norm.  The `none`
branch records zero explicitly, including in dimension zero. -/
def matrixSecondDerivativeNormValue (H : MatrixSecondDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some u => matrixDerivativeNorm (H u.1)

def matrixSecondDerivativeNormValueSet (H : MatrixSecondDerivative d) : Set ℝ :=
  Set.range (matrixSecondDerivativeNormValue H)

/-- Exact twice-induced norm of a stored second derivative: first take the
exact induced norm of the resulting matrix derivative, then the supremum over
the first `vecNorm` unit ball. -/
def matrixSecondDerivativeNorm (H : MatrixSecondDerivative d) : ℝ :=
  sSup (matrixSecondDerivativeNormValueSet H)

private theorem matrixSecondDerivativeNormValueSet_nonempty
    (H : MatrixSecondDerivative d) :
    (matrixSecondDerivativeNormValueSet H).Nonempty := by
  exact ⟨0, none, rfl⟩

private theorem matrixSecondDerivativeNormValue_le_sq_mul_norm
    (H : MatrixSecondDerivative d) (o : Option (EuclideanUnitVector d)) :
    matrixSecondDerivativeNormValue H o ≤ (d : ℝ) ^ 2 * ‖H‖ := by
  cases o with
  | none => positivity
  | some u =>
      calc
        matrixDerivativeNorm (H u.1) ≤ (d : ℝ) ^ 2 * ‖H u.1‖ :=
          matrixDerivativeNorm_le_sq_mul_norm _
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * ‖u.1‖) := by
          gcongr
          exact H.le_opNorm _
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * vecNorm u.1) := by
          gcongr
          exact norm_vec_le_vecNorm u.1
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * 1) := by
          gcongr
          exact u.2
        _ = (d : ℝ) ^ 2 * ‖H‖ := by ring

private theorem matrixSecondDerivativeNormValueSet_bddAbove
    (H : MatrixSecondDerivative d) :
    BddAbove (matrixSecondDerivativeNormValueSet H) := by
  refine ⟨(d : ℝ) ^ 2 * ‖H‖, ?_⟩
  rintro r ⟨o, rfl⟩
  exact matrixSecondDerivativeNormValue_le_sq_mul_norm H o

theorem matrixSecondDerivativeNorm_nonneg (H : MatrixSecondDerivative d) :
    0 ≤ matrixSecondDerivativeNorm H := by
  exact le_csSup (matrixSecondDerivativeNormValueSet_bddAbove H) ⟨none, rfl⟩

private theorem matrixSecondDerivativeNormValue_le
    (H : MatrixSecondDerivative d) (o : Option (EuclideanUnitVector d)) :
    matrixSecondDerivativeNormValue H o ≤ matrixSecondDerivativeNorm H := by
  exact le_csSup (matrixSecondDerivativeNormValueSet_bddAbove H) ⟨o, rfl⟩

/-- The exact twice-induced norm controls the inner derivative norm for every
first input in the `vecNorm` unit ball. -/
theorem matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm
    (H : MatrixSecondDerivative d) (u : Vec d) (hu : vecNorm u ≤ 1) :
    matrixDerivativeNorm (H u) ≤ matrixSecondDerivativeNorm H :=
  matrixSecondDerivativeNormValue_le H (some ⟨u, hu⟩)

private theorem matrixSecondDerivativeNorm_le_add_norm_sub
    (H K : MatrixSecondDerivative d) :
    matrixSecondDerivativeNorm H ≤
      matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ := by
  apply csSup_le (matrixSecondDerivativeNormValueSet_nonempty H)
  rintro r ⟨o, rfl⟩
  cases o with
  | none =>
      exact add_nonneg (matrixSecondDerivativeNorm_nonneg K)
        (mul_nonneg (sq_nonneg (d : ℝ)) (norm_nonneg (H - K)))
  | some u =>
      calc
        matrixDerivativeNorm (H u.1) ≤
            matrixDerivativeNorm (H u.1 - K u.1) + matrixDerivativeNorm (K u.1) := by
          simpa only [sub_add_cancel] using
            matrixDerivativeNorm_add_le (H u.1 - K u.1) (K u.1)
        _ ≤ (d : ℝ) ^ 2 * ‖H u.1 - K u.1‖ + matrixSecondDerivativeNorm K :=
          add_le_add (matrixDerivativeNorm_le_sq_mul_norm _)
            (matrixSecondDerivativeNormValue_le K (some u))
        _ = (d : ℝ) ^ 2 * ‖(H - K) u.1‖ + matrixSecondDerivativeNorm K := rfl
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * ‖u.1‖) + matrixSecondDerivativeNorm K := by
          gcongr
          exact (H - K).le_opNorm _
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * vecNorm u.1) +
              matrixSecondDerivativeNorm K := by
          gcongr
          exact norm_vec_le_vecNorm u.1
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * 1) + matrixSecondDerivativeNorm K := by
          gcongr
          exact u.2
        _ = matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ := by ring

theorem norm_matrixSecondDerivativeNorm_sub_le_sq_mul_norm
    (H K : MatrixSecondDerivative d) :
    ‖matrixSecondDerivativeNorm H - matrixSecondDerivativeNorm K‖ ≤
      (d : ℝ) ^ 2 * ‖H - K‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    calc
      matrixSecondDerivativeNorm K ≤
          matrixSecondDerivativeNorm H + (d : ℝ) ^ 2 * ‖K - H‖ :=
        matrixSecondDerivativeNorm_le_add_norm_sub K H
      _ = matrixSecondDerivativeNorm H + (d : ℝ) ^ 2 * ‖H - K‖ := by
        rw [norm_sub_rev K H]
  · rw [sub_le_iff_le_add]
    simpa only [add_comm] using matrixSecondDerivativeNorm_le_add_norm_sub H K

theorem matrixSecondDerivativeNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixSecondDerivativeNorm : MatrixSecondDerivative d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro H K
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using
    norm_matrixSecondDerivativeNorm_sub_le_sq_mul_norm H K

theorem matrixSecondDerivativeNorm_continuous :
    Continuous (matrixSecondDerivativeNorm : MatrixSecondDerivative d → ℝ) :=
  matrixSecondDerivativeNorm_lipschitz.continuous

/-- Sharp characterization of the exact twice-induced norm. -/
theorem matrixSecondDerivativeNorm_le_iff
    (H : MatrixSecondDerivative d) (C : ℝ) :
    matrixSecondDerivativeNorm H ≤ C ↔
      0 ≤ C ∧ ∀ u : Vec d, vecNorm u ≤ 1 → matrixDerivativeNorm (H u) ≤ C := by
  constructor
  · intro h
    refine ⟨(matrixSecondDerivativeNorm_nonneg H).trans h, ?_⟩
    intro u hu
    exact (matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H u hu).trans h
  · rintro ⟨hC, h⟩
    unfold matrixSecondDerivativeNorm
    apply csSup_le (matrixSecondDerivativeNormValueSet_nonempty H)
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some u => exact h u.1 u.2

/-- Points of the natural open manuscript cube `cu_n`. -/
abbrev ShellOpenCubePoint (d n : ℕ) :=
  {x : Vec d // x ∈ openCubeSet (originCube d (n : ℤ))}

def shellCubeValueAtIndex (n : ℕ) (j : ShellField d) :
    Option (ShellOpenCubePoint d n) → ℝ
  | none => 0
  | some x => matrixOperatorNorm (j x.1)

def shellCubeDerivAtIndex (n : ℕ) (j : ShellField d) :
    Option (ShellOpenCubePoint d n) → ℝ
  | none => 0
  | some x => matrixDerivativeNorm (ShellField.deriv j x.1)

def shellCubeSecondDerivAtIndex (n : ℕ) (j : ShellField d) :
    Option (ShellOpenCubePoint d n) → ℝ
  | none => 0
  | some x => matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)

/-- Exact Euclidean matrix-operator `L∞` norm of the shell values on the
natural open cube `cu_n`. The defining range includes zero explicitly. -/
def shellCubeValueNorm (n : ℕ) (j : ShellField d) : ℝ :=
  sSup (Set.range (shellCubeValueAtIndex n j))

/-- Exact induced `vecNorm → matrixOperatorNorm` `L∞` norm of the stored first
derivative on the natural open cube `cu_n`. -/
def shellCubeDerivNorm (n : ℕ) (j : ShellField d) : ℝ :=
  sSup (Set.range (shellCubeDerivAtIndex n j))

/-- Exact twice-induced `vecNorm → vecNorm → matrixOperatorNorm` `L∞` norm of
the stored second derivative on the natural open cube `cu_n`. -/
def shellCubeSecondDerivNorm (n : ℕ) (j : ShellField d) : ℝ :=
  sSup (Set.range (shellCubeSecondDerivAtIndex n j))

private theorem shellOpenCubePoint_mem_closedBall (n : ℕ)
    (x : ShellOpenCubePoint d n) :
    x.1 ∈ Metric.closedBall
      (cubeCenter (originCube d (n : ℤ)))
      (cubeRadius (originCube d (n : ℤ))) := by
  apply Metric.ball_subset_closedBall
  rw [ball_cubeCenter_eq_openCubeSet]
  exact x.2

private theorem shellCubeValueAtIndex_range_bddAbove
    (n : ℕ) (j : ShellField d) :
    BddAbove (Set.range (shellCubeValueAtIndex n j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d (n : ℤ)))
    (cubeRadius (originCube d (n : ℤ)))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d (n : ℤ)))
      (cubeRadius (originCube d (n : ℤ)))
  have hcont : Continuous (fun x : Vec d => matrixOperatorNorm (j x)) :=
    matrixOperatorNorm_continuous.comp j.1.1.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := shellOpenCubePoint_mem_closedBall n x
      have h := hC x.1 hx
      have hop : matrixOperatorNorm (j x.1) ≤ C := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (matrixOperatorNorm_nonneg _)] using h
      exact hop.trans (le_max_right _ _)

private theorem shellCubeDerivAtIndex_range_bddAbove
    (n : ℕ) (j : ShellField d) :
    BddAbove (Set.range (shellCubeDerivAtIndex n j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d (n : ℤ)))
    (cubeRadius (originCube d (n : ℤ)))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d (n : ℤ)))
      (cubeRadius (originCube d (n : ℤ)))
  have hcont : Continuous
      (fun x : Vec d => matrixDerivativeNorm (ShellField.deriv j x)) :=
    matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := shellOpenCubePoint_mem_closedBall n x
      have h := hC x.1 hx
      have hD : matrixDerivativeNorm (ShellField.deriv j x.1) ≤ C := by
        calc
          matrixDerivativeNorm (ShellField.deriv j x.1) =
              |matrixDerivativeNorm (ShellField.deriv j x.1)| :=
            (abs_of_nonneg (matrixDerivativeNorm_nonneg _)).symm
          _ = ‖matrixDerivativeNorm (ShellField.deriv j x.1)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ C := h
      exact hD.trans (le_max_right _ _)

private theorem shellCubeSecondDerivAtIndex_range_bddAbove
    (n : ℕ) (j : ShellField d) :
    BddAbove (Set.range (shellCubeSecondDerivAtIndex n j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d (n : ℤ)))
    (cubeRadius (originCube d (n : ℤ)))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d (n : ℤ)))
      (cubeRadius (originCube d (n : ℤ)))
  have hcont : Continuous
      (fun x : Vec d => matrixSecondDerivativeNorm (ShellField.secondDeriv j x)) :=
    matrixSecondDerivativeNorm_continuous.comp (ShellField.secondDeriv j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := shellOpenCubePoint_mem_closedBall n x
      have h := hC x.1 hx
      have hD : matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) ≤ C := by
        calc
          matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) =
              |matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)| :=
            (abs_of_nonneg (matrixSecondDerivativeNorm_nonneg _)).symm
          _ = ‖matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ C := h
      exact hD.trans (le_max_right _ _)

theorem shellCubeValueNorm_nonneg (n : ℕ) (j : ShellField d) :
    0 ≤ shellCubeValueNorm n j := by
  exact le_csSup (shellCubeValueAtIndex_range_bddAbove n j) ⟨none, rfl⟩

/-- The scale-`n` cube value control bounds the matrix operator norm at every
point of the natural open cube. -/
theorem matrixOperatorNorm_apply_le_shellCubeValueNorm
    (n : ℕ) (j : ShellField d) (x : ShellOpenCubePoint d n) :
    matrixOperatorNorm (j x.1) ≤ shellCubeValueNorm n j := by
  exact le_csSup (shellCubeValueAtIndex_range_bddAbove n j) ⟨some x, rfl⟩

/-- Continuity of the exact Euclidean matrix-operator norm used by the J3
observable. -/
theorem continuous_matrixOperatorNorm :
    Continuous (matrixOperatorNorm : Mat d → ℝ) :=
  matrixOperatorNorm_continuous

theorem shellCubeDerivNorm_nonneg (n : ℕ) (j : ShellField d) :
    0 ≤ shellCubeDerivNorm n j := by
  exact le_csSup (shellCubeDerivAtIndex_range_bddAbove n j) ⟨none, rfl⟩

theorem shellCubeSecondDerivNorm_nonneg (n : ℕ) (j : ShellField d) :
    0 ≤ shellCubeSecondDerivNorm n j := by
  exact le_csSup (shellCubeSecondDerivAtIndex_range_bddAbove n j) ⟨none, rfl⟩

/-- Sharp characterization: the scale-`n` open-cube second-derivative norm is
the least nonnegative constant controlling the exact twice-induced norm at
every point of the natural open cube. -/
theorem shellCubeSecondDerivNorm_le_iff
    (n : ℕ) (j : ShellField d) (C : ℝ) :
    shellCubeSecondDerivNorm n j ≤ C ↔
      0 ≤ C ∧
        ∀ x : ShellOpenCubePoint d n,
          matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) ≤ C := by
  constructor
  · intro h
    refine ⟨(shellCubeSecondDerivNorm_nonneg n j).trans h, ?_⟩
    intro x
    have hx : shellCubeSecondDerivAtIndex n j (some x) ≤
        shellCubeSecondDerivNorm n j :=
      le_csSup (shellCubeSecondDerivAtIndex_range_bddAbove n j) ⟨some x, rfl⟩
    exact hx.trans h
  · rintro ⟨hC, h⟩
    unfold shellCubeSecondDerivNorm
    apply csSup_le (Set.range_nonempty (shellCubeSecondDerivAtIndex n j))
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some x => exact h x

/-- The measurable nonnegative observable underlying the manuscript's J3 tail
bound on shell `n`:
`‖j_n‖∞ + √d 3^n ‖∇j_n‖∞ + d 3^(2n) ‖∇²j_n‖∞`, all on `cu_n`. -/
def j3Observable (d n : ℕ) (j : ShellField d) : ℝ :=
  shellCubeValueNorm n j +
    (Real.sqrt d * (3 : ℝ) ^ n) * shellCubeDerivNorm n j +
    ((d : ℝ) * (3 : ℝ) ^ (2 * n)) * shellCubeSecondDerivNorm n j

/-- The J3 observable is nonnegative. -/
theorem j3Observable_nonneg (d n : ℕ) (j : ShellField d) :
    0 ≤ j3Observable d n j := by
  exact add_nonneg
    (add_nonneg (shellCubeValueNorm_nonneg n j)
      (mul_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (by norm_num) n))
        (shellCubeDerivNorm_nonneg n j)))
    (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (by norm_num) (2 * n)))
      (shellCubeSecondDerivNorm_nonneg n j))

private theorem shellCubeValueAtIndex_continuous
    (n : ℕ) (o : Option (ShellOpenCubePoint d n)) :
    Continuous (fun j : ShellField d => shellCubeValueAtIndex n j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixOperatorNorm_continuous.comp
        (ShellField.continuous_eval x.1)

private theorem shellCubeDerivAtIndex_continuous
    (n : ℕ) (o : Option (ShellOpenCubePoint d n)) :
    Continuous (fun j : ShellField d => shellCubeDerivAtIndex n j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixDerivativeNorm_continuous.comp
        (ShellField.continuous_eval_deriv x.1)

private theorem shellCubeSecondDerivAtIndex_continuous
    (n : ℕ) (o : Option (ShellOpenCubePoint d n)) :
    Continuous (fun j : ShellField d => shellCubeSecondDerivAtIndex n j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixSecondDerivativeNorm_continuous.comp
        (ShellField.continuous_eval_secondDeriv x.1)

theorem shellCubeValueNorm_lowerSemicontinuous (n : ℕ) :
    LowerSemicontinuous (shellCubeValueNorm n : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => shellCubeValueAtIndex_range_bddAbove n j)
    (fun o => (shellCubeValueAtIndex_continuous n o).lowerSemicontinuous)
  exact h

theorem shellCubeDerivNorm_lowerSemicontinuous (n : ℕ) :
    LowerSemicontinuous (shellCubeDerivNorm n : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => shellCubeDerivAtIndex_range_bddAbove n j)
    (fun o => (shellCubeDerivAtIndex_continuous n o).lowerSemicontinuous)
  exact h

theorem shellCubeSecondDerivNorm_lowerSemicontinuous (n : ℕ) :
    LowerSemicontinuous (shellCubeSecondDerivNorm n : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => shellCubeSecondDerivAtIndex_range_bddAbove n j)
    (fun o => (shellCubeSecondDerivAtIndex_continuous n o).lowerSemicontinuous)
  exact h

theorem shellCubeValueNorm_measurable (n : ℕ) :
    Measurable (shellCubeValueNorm n : ShellField d → ℝ) :=
  (shellCubeValueNorm_lowerSemicontinuous n).measurable

theorem shellCubeDerivNorm_measurable (n : ℕ) :
    Measurable (shellCubeDerivNorm n : ShellField d → ℝ) :=
  (shellCubeDerivNorm_lowerSemicontinuous n).measurable

theorem shellCubeSecondDerivNorm_measurable (n : ℕ) :
    Measurable (shellCubeSecondDerivNorm n : ShellField d → ℝ) :=
  (shellCubeSecondDerivNorm_lowerSemicontinuous n).measurable

theorem j3Observable_measurable (d n : ℕ) :
    Measurable (j3Observable d n) := by
  exact ((shellCubeValueNorm_measurable n).add
    (measurable_const.mul (shellCubeDerivNorm_measurable n))).add
      (measurable_const.mul (shellCubeSecondDerivNorm_measurable n))

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
