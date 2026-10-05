/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.TailJ3B
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellDilationB
public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable

/-!
# The J3 observable of a dilated assembled field is controlled by the unit-cube data

If every entry of the assembled skew field `assembleSkew f` has value, first and second derivative
bounded by `m` on the unit cube `(-1/2, 1/2)^d`, then for every `n` the observable
`j3Observable d n (dilate (3^n) (assembleSkew f))` is at most `d^2 (1 + √d + d) m`.  The dilation
weights `√d 3^n` and `d 3^(2n)` cancel the derivative factors `3^(-n)` and `3^(-2n)` exactly.

## Main results

* `nv_cubeCells`, `nv_cellsNear_subset_cubeCells`
* `nv_j3Observable_dilate_le`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Assumptions.ShellField
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The cells that can meet the unit cube `(-1/2, 1/2)^d`. -/
def nv_cubeCells (d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-2 : ℤ) 2

theorem card_nv_cubeCells (d : ℕ) : (nv_cubeCells d).card = 5 ^ d := by
  unfold nv_cubeCells
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc]
  simp

/-- At a point of the unit cube only the cells of `nv_cubeCells d` contribute. -/
theorem nv_cellsNear_subset_cubeCells {x : Vec d} (hx : ∀ i, |x i| < 1 / 2) :
    cellsNear x ⊆ nv_cubeCells d := by
  intro k hk
  refine Fintype.mem_piFinset.2 fun i ↦ ?_
  have h1 := Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hk i)
  have h2 := abs_lt.1 (hx i)
  have f1 : (-1 : ℤ) ≤ ⌊2 * x i⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith only [h2.1]
  have f2 : ⌊2 * x i⌋ < 1 := by
    rw [Int.floor_lt]
    push_cast
    linarith only [h2.2]
  rw [Finset.mem_Icc]
  omega

theorem nv_matOp_le (A : Mat d) {m : ℝ} (h : ∀ i j, |A i j| ≤ m) :
    matrixOperatorNorm A ≤ (d : ℝ) ^ 2 * m := by
  refine (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    ((matrixFrobeniusNorm_le_sum_abs_entries A).trans ?_)
  calc (∑ i, ∑ j, |A i j|) ≤ ∑ _i : Fin d, ∑ _j : Fin d, m := by
        gcongr with i _ j _
        exact h i j
    _ = (d : ℝ) ^ 2 * m := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem nv_matNorm_le (A : Mat d) {m : ℝ} (hm : 0 ≤ m) (h : ∀ i j, |A i j| ≤ m) : ‖A‖ ≤ m :=
  (Matrix.norm_le_iff hm).2 fun i j ↦ by simpa only [Real.norm_eq_abs] using h i j

theorem nv_abs_skewCoef_le (c : SkewIdx d → ℝ) {m : ℝ} (hm : 0 ≤ m) (h : ∀ p, |c p| ≤ m)
    (i j : Fin d) : |nv_skewCoef c i j| ≤ m := by
  unfold nv_skewCoef
  split_ifs with h1 h2
  · exact h _
  · rw [abs_neg]; exact h _
  · rwa [abs_zero]

/-- A point of the cube `cu_n` is mapped into the unit cube by the dilation. -/
theorem nv_mem_unit_of_mem_cube (n : ℕ) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    ∀ i, |((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) • x) i| < 1 / 2 := by
  intro i
  have h := (mem_openCubeSet_originCube_iff.1 hx) i
  rw [zpow_natCast] at h
  have hp : (0 : ℝ) < 3 ^ n := by positivity
  have hax : |x i| < 1 / 2 * 3 ^ n := abs_lt.2 ⟨by linarith only [h.1], h.2⟩
  rw [nv_scaleUnit_inv_val, Pi.smul_apply, smul_eq_mul, abs_mul,
    abs_of_pos (inv_pos.2 hp)]
  calc ((3 : ℝ) ^ n)⁻¹ * |x i| < ((3 : ℝ) ^ n)⁻¹ * (1 / 2 * 3 ^ n) :=
        mul_lt_mul_of_pos_left hax (inv_pos.2 hp)
    _ = 1 / 2 := by field_simp

/-- The scale factor `3 ^ (-n)` as a real number. -/
theorem nv_scale_nonneg (n : ℕ) : 0 ≤ (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) := by
  rw [nv_scaleUnit_inv_val]; positivity

section Bounds

variable (n : ℕ) (f : SkewIdx d → ScalarC2Field d) {m : ℝ}

theorem nv_cubeValue_le (hm : 0 ≤ m)
    (h0 : ∀ p y, (∀ i, |y i| < 1 / 2) → |f p y| ≤ m) :
    shellCubeValueNorm n (dilate (nv_scaleUnit n) (assembleSkew f)) ≤ (d : ℝ) ^ 2 * m := by
  unfold shellCubeValueNorm
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (sq_nonneg _) hm
  | some x =>
      show matrixOperatorNorm (dilate (nv_scaleUnit n) (assembleSkew f) x.1) ≤ _
      refine nv_matOp_le _ fun i j ↦ ?_
      rw [dilate_apply, assembleSkew_apply]
      exact nv_abs_skewCoef_le _ hm (fun p ↦ h0 p _ (nv_mem_unit_of_mem_cube n x.2)) i j

theorem nv_norm_deriv_dilate_le (hm : 0 ≤ m)
    (h1 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.deriv (f p) y‖ ≤ m) {x : Vec d}
    (hx : ∀ i, |((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) • x) i| < 1 / 2) :
    ‖ShellField.deriv (dilate (nv_scaleUnit n) (assembleSkew f)) x‖
      ≤ (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * m := by
  set s : ℝ := (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) with hs
  have hs0 : 0 ≤ s := nv_scale_nonneg n
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hs0 hm) fun v ↦ ?_
  have hmv : 0 ≤ s * m * ‖v‖ := mul_nonneg (mul_nonneg hs0 hm) (norm_nonneg v)
  refine nv_matNorm_le _ hmv fun i j ↦ ?_
  have e : ShellField.deriv (dilate (nv_scaleUnit n) (assembleSkew f)) x v i j
      = s * ShellField.deriv (assembleSkew f) (s • x) v i j := rfl
  refine le_trans (le_of_eq (congrArg abs e)) ?_
  rw [assembleSkew_deriv_apply, abs_mul, abs_of_nonneg hs0]
  have hb : |nv_skewCoef (fun p ↦ ScalarC2Field.deriv (f p) (s • x) v) i j| ≤ m * ‖v‖ := by
    refine nv_abs_skewCoef_le _ (mul_nonneg hm (norm_nonneg v)) (fun p ↦ ?_) i j
    rw [← Real.norm_eq_abs]
    exact ((ScalarC2Field.deriv (f p) (s • x)).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (h1 p _ hx) (norm_nonneg v))
  calc s * |nv_skewCoef (fun p ↦ ScalarC2Field.deriv (f p) (s • x) v) i j|
      ≤ s * (m * ‖v‖) := mul_le_mul_of_nonneg_left hb hs0
    _ = s * m * ‖v‖ := by ring

theorem nv_cubeDeriv_le (hm : 0 ≤ m)
    (h1 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.deriv (f p) y‖ ≤ m) :
    shellCubeDerivNorm n (dilate (nv_scaleUnit n) (assembleSkew f))
      ≤ (d : ℝ) ^ 2 * ((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * m) := by
  unfold shellCubeDerivNorm
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (sq_nonneg _) (mul_nonneg (nv_scale_nonneg n) hm)
  | some x =>
      show matrixDerivativeNorm (ShellField.deriv (dilate (nv_scaleUnit n) (assembleSkew f)) x.1)
        ≤ _
      refine (matrixDerivativeNorm_le_sq_mul_norm _).trans ?_
      exact mul_le_mul_of_nonneg_left
        (nv_norm_deriv_dilate_le n f hm h1 (nv_mem_unit_of_mem_cube n x.2)) (sq_nonneg _)

theorem nv_norm_secondDeriv_dilate_le (hm : 0 ≤ m)
    (h2 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.secondDeriv (f p) y‖ ≤ m) {x : Vec d}
    (hx : ∀ i, |((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) • x) i| < 1 / 2) (u : Vec d) :
    ‖ShellField.secondDeriv (dilate (nv_scaleUnit n) (assembleSkew f)) x u‖
      ≤ ((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * m) * ‖u‖ := by
  set s : ℝ := (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) with hs
  have hs0 : 0 ≤ s := nv_scale_nonneg n
  have hC : 0 ≤ s * s * m * ‖u‖ := mul_nonneg (mul_nonneg (mul_nonneg hs0 hs0) hm) (norm_nonneg u)
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun v ↦ ?_
  have hmv : 0 ≤ s * s * m * ‖u‖ * ‖v‖ := mul_nonneg hC (norm_nonneg v)
  refine nv_matNorm_le _ hmv fun i j ↦ ?_
  have e : ShellField.secondDeriv (dilate (nv_scaleUnit n) (assembleSkew f)) x u v i j
      = (s * s) * ShellField.secondDeriv (assembleSkew f) (s • x) u v i j := rfl
  refine le_trans (le_of_eq (congrArg abs e)) ?_
  rw [assembleSkew_secondDeriv_apply, abs_mul, abs_of_nonneg (mul_nonneg hs0 hs0)]
  have hb : |nv_skewCoef (fun p ↦ ScalarC2Field.secondDeriv (f p) (s • x) u v) i j|
      ≤ m * ‖u‖ * ‖v‖ := by
    refine nv_abs_skewCoef_le _ (mul_nonneg (mul_nonneg hm (norm_nonneg u)) (norm_nonneg v))
      (fun p ↦ ?_) i j
    rw [← Real.norm_eq_abs]
    have e1 := ((ScalarC2Field.secondDeriv (f p) (s • x)) u).le_opNorm v
    have e2 := (ScalarC2Field.secondDeriv (f p) (s • x)).le_opNorm u
    have e3 := h2 p _ hx
    calc ‖ScalarC2Field.secondDeriv (f p) (s • x) u v‖
        ≤ ‖ScalarC2Field.secondDeriv (f p) (s • x) u‖ * ‖v‖ := e1
      _ ≤ (‖ScalarC2Field.secondDeriv (f p) (s • x)‖ * ‖u‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right e2 (norm_nonneg v)
      _ ≤ (m * ‖u‖) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right e3 (norm_nonneg u))
            (norm_nonneg v)
  calc s * s * |nv_skewCoef (fun p ↦ ScalarC2Field.secondDeriv (f p) (s • x) u v) i j|
      ≤ s * s * (m * ‖u‖ * ‖v‖) := mul_le_mul_of_nonneg_left hb (mul_nonneg hs0 hs0)
    _ = s * s * m * ‖u‖ * ‖v‖ := by ring

theorem nv_cubeSecondDeriv_le (hm : 0 ≤ m)
    (h2 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.secondDeriv (f p) y‖ ≤ m) :
    shellCubeSecondDerivNorm n (dilate (nv_scaleUnit n) (assembleSkew f))
      ≤ (d : ℝ) ^ 2 * ((((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * m) := by
  have hs0 : 0 ≤ (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) := nv_scale_nonneg n
  unfold shellCubeSecondDerivNorm
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hs0 hs0) hm)
  | some x =>
      show matrixSecondDerivativeNorm
        (ShellField.secondDeriv (dilate (nv_scaleUnit n) (assembleSkew f)) x.1) ≤ _
      refine (matrixSecondDerivativeNorm_le_iff _ _).2 ⟨mul_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg hs0 hs0) hm), fun u hu ↦ ?_⟩
      refine (matrixDerivativeNorm_le_sq_mul_norm _).trans ?_
      have hn := nv_norm_secondDeriv_dilate_le n f hm h2 (nv_mem_unit_of_mem_cube n x.2) u
      have hu1 : ‖u‖ ≤ 1 := (norm_vec_le_vecNorm u).trans hu
      have hc : 0 ≤ (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) * m :=
        mul_nonneg (mul_nonneg hs0 hs0) hm
      refine mul_le_mul_of_nonneg_left (hn.trans ?_) (sq_nonneg _)
      calc _ ≤ _ * (1 : ℝ) := mul_le_mul_of_nonneg_left hu1 hc
        _ = _ := mul_one _

/-- **The J3 observable of the dilated assembled field** is at most `d² (1 + √d + d) m`, for
every shell index `n`, whenever all entries of `f` have value, first and second derivative at
most `m` on the unit cube. -/
theorem nv_j3Observable_dilate_le (hm : 0 ≤ m)
    (h0 : ∀ p y, (∀ i, |y i| < 1 / 2) → |f p y| ≤ m)
    (h1 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.deriv (f p) y‖ ≤ m)
    (h2 : ∀ p y, (∀ i, |y i| < 1 / 2) → ‖ScalarC2Field.secondDeriv (f p) y‖ ≤ m) :
    j3Observable d n (dilate (nv_scaleUnit n) (assembleSkew f))
      ≤ (d : ℝ) ^ 2 * (1 + Real.sqrt d + d) * m := by
  have hV := nv_cubeValue_le n f hm h0
  have hD := nv_cubeDeriv_le n f hm h1
  have hH := nv_cubeSecondDeriv_le n f hm h2
  rw [nv_scaleUnit_inv_val] at hD hH
  have hT : (0 : ℝ) < 3 ^ n := by positivity
  have hsq : (3 : ℝ) ^ (2 * n) = 3 ^ n * 3 ^ n := by rw [two_mul, pow_add]
  unfold j3Observable
  have e1 : Real.sqrt d * (3 : ℝ) ^ n * shellCubeDerivNorm n (dilate (nv_scaleUnit n)
      (assembleSkew f)) ≤ Real.sqrt d * ((d : ℝ) ^ 2 * m) := by
    calc _ ≤ Real.sqrt d * (3 : ℝ) ^ n * ((d : ℝ) ^ 2 * (((3 : ℝ) ^ n)⁻¹ * m)) :=
          mul_le_mul_of_nonneg_left hD (mul_nonneg (Real.sqrt_nonneg _) hT.le)
      _ = _ := by field_simp
  have e2 : (d : ℝ) * (3 : ℝ) ^ (2 * n) * shellCubeSecondDerivNorm n (dilate (nv_scaleUnit n)
      (assembleSkew f)) ≤ (d : ℝ) * ((d : ℝ) ^ 2 * m) := by
    calc _ ≤ (d : ℝ) * (3 : ℝ) ^ (2 * n) * ((d : ℝ) ^ 2 *
          (((3 : ℝ) ^ n)⁻¹ * ((3 : ℝ) ^ n)⁻¹ * m)) :=
          mul_le_mul_of_nonneg_left hH (mul_nonneg (Nat.cast_nonneg d) (by positivity))
      _ = _ := by rw [hsq]; field_simp
  calc _ ≤ (d : ℝ) ^ 2 * m + Real.sqrt d * ((d : ℝ) ^ 2 * m) + (d : ℝ) * ((d : ℝ) ^ 2 * m) :=
        add_le_add (add_le_add hV e1) e2
    _ = _ := by ring

end Bounds

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
