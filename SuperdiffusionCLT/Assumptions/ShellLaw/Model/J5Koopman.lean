/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5ReductionB

/-!
# Pointwise second-order Taylor bound for the entries of a shell field

For a shell field `j`, a point `x`, an axis `l` and `|t| ≤ 1/4`, the entry `(i, k)` of `j` satisfies

`|j (x + t e_l) i k - j x i k - t ∂_l j x i k| ≤ t² J(translate x j)`

where `J` is the J3 observable at scale zero. The bound uses the exact twice-induced norm of the
second derivative on the natural cube `cu_0`, and the line `s e_l`, `|s| ≤ 1/4`, lies in that cube.

* `nv_taylor_two`: the one-dimensional Taylor remainder bound.
* `nv_entry_taylor`: the bound for the entries of a shell field.
* `nv_abs_entry_le_obs`, `nv_abs_deriv_entry_le_obs`: values and first derivatives of the entries
  are bounded by the observable of the translate.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory Set
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- One-dimensional Taylor remainder bound from a bound on the second derivative. -/
theorem nv_taylor_two {f f' f'' : ℝ → ℝ} {M r t : ℝ}
    (hf : ∀ s, |s| ≤ r → HasDerivAt f (f' s) s)
    (hf' : ∀ s, |s| ≤ r → HasDerivAt f' (f'' s) s)
    (hb : ∀ s, |s| ≤ r → |f'' s| ≤ M) (ht : |t| ≤ r) :
    |f t - f 0 - t * f' 0| ≤ t ^ 2 * M := by
  have hS : Convex ℝ (Icc (-r) r) := convex_Icc _ _
  have hr : 0 ≤ r := (abs_nonneg t).trans ht
  have hmem : ∀ s : ℝ, s ∈ Icc (-r) r ↔ |s| ≤ r := fun s ↦ by
    rw [abs_le, mem_Icc]
  -- the first derivative moves by at most `M |s|`
  have hd1 : ∀ s : ℝ, |s| ≤ r → |f' s - f' 0| ≤ M * |s| := by
    intro s hs
    have h := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f') (f' := f'') (C := M)
      (x := 0) (y := s) (fun u hu ↦ (hf' u ((hmem u).1 hu)).hasDerivWithinAt)
      (fun u hu ↦ by simpa only [Real.norm_eq_abs] using hb u ((hmem u).1 hu))
      ((hmem 0).2 (by simpa only [abs_zero] using hr)) ((hmem s).2 hs)
    simpa only [Real.norm_eq_abs, sub_zero] using h
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0 (by simpa only [abs_zero] using hr))
  set g : ℝ → ℝ := fun s ↦ f s - f 0 - s * f' 0 with hg
  have hS' : Convex ℝ (Icc (-|t|) |t|) := convex_Icc _ _
  have hmem' : ∀ s : ℝ, s ∈ Icc (-|t|) |t| ↔ |s| ≤ |t| := fun s ↦ by
    rw [abs_le, mem_Icc]
  have hgd : ∀ s : ℝ, |s| ≤ r → HasDerivAt g (f' s - f' 0) s := by
    intro s hs
    have h1 := (hf s hs).sub_const (f 0)
    have h2 := (hasDerivAt_id s).mul_const (f' 0)
    have h3 := h1.sub h2
    convert h3 using 1
    · funext y
      simp [hg]
    · simp
  have h := hS'.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := fun s ↦ f' s - f' 0)
    (C := M * |t|) (x := 0) (y := t)
    (fun u hu ↦ (hgd u (((hmem' u).1 hu).trans ht)).hasDerivWithinAt)
    (fun u hu ↦ by
      have hu' := (hmem' u).1 hu
      rw [Real.norm_eq_abs]
      refine (hd1 u (hu'.trans ht)).trans ?_
      exact mul_le_mul_of_nonneg_left hu' hM0)
    ((hmem' 0).2 (by simp)) ((hmem' t).2 le_rfl)
  have hg0 : g 0 = 0 := by simp [hg]
  rw [hg0, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |f t - f 0 - t * f' 0| = |g t| := rfl
    _ ≤ M * |t| * |t| := h
    _ = t ^ 2 * M := by
      have : |t| * |t| = t ^ 2 := by rw [← sq, sq_abs]
      calc M * |t| * |t| = M * (|t| * |t|) := by ring
        _ = t ^ 2 * M := by rw [this]; ring

/-- Evaluation of a matrix at one entry, as a continuous linear map. -/
def nv_entryCLM (i k : Fin d) : Mat d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) k).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ Fin d → ℝ) i)

@[simp]
theorem nv_entryCLM_apply (i k : Fin d) (A : Mat d) : nv_entryCLM i k A = A i k :=
  rfl

theorem nv_vecNorm_single (l : Fin d) : Book.Ch02.vecNorm (Pi.single l 1 : Vec d) = 1 := by
  have hsq : Book.Ch02.vecNorm (Pi.single l 1 : Vec d) ^ 2 = 1 := by
    rw [Book.Ch02.vecNorm_sq_eq_vecNormSq, vecNormSq, vecDot, Finset.sum_eq_single l]
    · simp
    · intro j _ hij
      simp [Pi.single_eq_of_ne hij]
    · simp
  calc Book.Ch02.vecNorm (Pi.single l 1 : Vec d)
      = Real.sqrt (Book.Ch02.vecNorm (Pi.single l 1 : Vec d) ^ 2) :=
        (Real.sqrt_sq (Book.Ch02.vecNorm_nonneg _)).symm
    _ = 1 := by rw [hsq, Real.sqrt_one]

/-- A point of the line `s ↦ s e_l`, `|s| ≤ 1/4`, lies in the natural cube `cu_0`. -/
theorem nv_line_mem_cube (l : Fin d) (s : ℝ) (hs : |s| ≤ 1 / 4) :
    s • (Pi.single l 1 : Vec d) ∈ openCubeSet (originCube d ((0 : ℕ) : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have h := abs_le.mp hs
  by_cases hi : i = l
  · subst hi
    simp only [Nat.cast_zero, zpow_zero, mul_one, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    constructor <;> linarith only [h.1, h.2]
  · simp only [Nat.cast_zero, zpow_zero, mul_one, Pi.smul_apply, Pi.single_eq_of_ne hi,
      smul_zero]
    constructor <;> norm_num

/-- The second derivative of an entry along an axis on the line through `x` is bounded by the
J3 observable of the translate of `j` by `x`. -/
theorem nv_secondDeriv_entry_le (hd : 0 < d) (j : ShellField d) (x : Vec d) (l i k : Fin d)
    (s : ℝ) (hs : |s| ≤ 1 / 4) :
    |ShellField.secondDeriv j (x + s • (Pi.single l 1 : Vec d)) (Pi.single l 1) (Pi.single l 1) i k|
      ≤ ShellField.j3Observable d 0 (ShellField.translate x j) := by
  set e : Vec d := Pi.single l 1 with he
  have hen : Book.Ch02.vecNorm e ≤ 1 := (nv_vecNorm_single l).le
  have hsec : ShellField.secondDeriv j (x + s • e) =
      ShellField.secondDeriv (ShellField.translate x j) (s • e) := by
    rw [ShellField.translate_secondDeriv, add_comm]
  rw [hsec]
  set H := ShellField.secondDeriv (ShellField.translate x j) (s • e) with hH
  have h1 : |H e e i k| ≤ Book.Ch02.matrixOperatorNorm (H e e) :=
    Book.Ch02.abs_entry_le_matrixOperatorNorm _ _ _
  have h2 : Book.Ch02.matrixOperatorNorm (H e e) ≤ ShellField.matrixDerivativeNorm (H e) :=
    ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm _ _ hen
  have h3 : ShellField.matrixDerivativeNorm (H e) ≤ ShellField.matrixSecondDerivativeNorm H :=
    ShellField.matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm _ _ hen
  have h4 : ShellField.matrixSecondDerivativeNorm H ≤
      ShellField.shellCubeSecondDerivNorm 0 (ShellField.translate x j) :=
    ((ShellField.shellCubeSecondDerivNorm_le_iff 0 (ShellField.translate x j) _).1 le_rfl).2
      ⟨s • e, nv_line_mem_cube l s hs⟩
  have h5 : ShellField.shellCubeSecondDerivNorm 0 (ShellField.translate x j) ≤
      ShellField.j3Observable d 0 (ShellField.translate x j) := by
    have hn := ShellField.shellCubeSecondDerivNorm_nonneg 0 (ShellField.translate x j)
    have hv := ShellField.shellCubeValueNorm_nonneg 0 (ShellField.translate x j)
    have hdv := ShellField.shellCubeDerivNorm_nonneg 0 (ShellField.translate x j)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    unfold ShellField.j3Observable
    simp only [pow_zero, mul_one, Nat.mul_zero]
    have : 0 ≤ Real.sqrt d * ShellField.shellCubeDerivNorm 0 (ShellField.translate x j) :=
      mul_nonneg (Real.sqrt_nonneg _) hdv
    nlinarith only [hn, hv, this, hd1]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem nv_hasDerivAt_line (x e : Vec d) (s : ℝ) :
    HasDerivAt (fun u : ℝ ↦ x + u • e) e s := by
  have hline := AffineMap.hasDerivAt_lineMap (a := x) (b := x + e) (x := s)
  have hfun : (fun u : ℝ ↦ x + u • e) = AffineMap.lineMap x (x + e) := by
    funext u
    rw [AffineMap.lineMap_apply_module]
    simp only [sub_smul, one_smul, smul_add]
    abel
  rw [hfun]
  simpa only [add_sub_cancel_left] using hline

/-- **Pointwise second-order Taylor bound for an entry of a shell field.** -/
theorem nv_entry_taylor (hd : 0 < d) (j : ShellField d) (x : Vec d) (l i k : Fin d) (t : ℝ)
    (ht : |t| ≤ 1 / 4) :
    |j (x + t • (Pi.single l 1 : Vec d)) i k - j x i k -
        t * ShellField.deriv j x (Pi.single l 1) i k| ≤
      t ^ 2 * ShellField.j3Observable d 0 (ShellField.translate x j) := by
  set e : Vec d := Pi.single l 1 with he
  have hf : ∀ s : ℝ, |s| ≤ 1 / 4 →
      HasDerivAt (fun u : ℝ ↦ j (x + u • e) i k)
        (ShellField.deriv j (x + s • e) e i k) s := by
    intro s _
    have h := ((nv_entryCLM i k).hasFDerivAt).comp_hasDerivAt s
      ((j.hasFDerivAt (x + s • e)).comp_hasDerivAt s (nv_hasDerivAt_line x e s))
    exact h
  have hf' : ∀ s : ℝ, |s| ≤ 1 / 4 →
      HasDerivAt (fun u : ℝ ↦ ShellField.deriv j (x + u • e) e i k)
        (ShellField.secondDeriv j (x + s • e) e e i k) s := by
    intro s _
    have h1 := (j.deriv_hasFDerivAt (x + s • e)).comp_hasDerivAt s (nv_hasDerivAt_line x e s)
    have h2 := ((nv_entryCLM i k).comp (ContinuousLinearMap.apply ℝ (Mat d) e)).hasFDerivAt.comp_hasDerivAt
      s h1
    exact h2
  have h := nv_taylor_two (f := fun u : ℝ ↦ j (x + u • e) i k)
    (f' := fun s ↦ ShellField.deriv j (x + s • e) e i k)
    (f'' := fun s ↦ ShellField.secondDeriv j (x + s • e) e e i k)
    (M := ShellField.j3Observable d 0 (ShellField.translate x j)) (r := 1 / 4) (t := t)
    hf hf' (fun s hs ↦ nv_secondDeriv_entry_le hd j x l i k s hs) ht
  simpa only [zero_smul, add_zero] using h

/-! ## Pointwise bounds by the J3 observable -/

theorem nv_abs_entry_le_obs (j : ShellField d) (x : Vec d) (i k : Fin d) :
    |j x i k| ≤ ShellField.j3Observable d 0 (ShellField.translate x j) := by
  have h := ShellField.abs_entry_zero_le_j3Observable 0 (ShellField.translate x j) i k
  simpa only [ShellField.translate_apply, zero_add] using h

theorem nv_zero_mem_cube : (0 : Vec d) ∈ openCubeSet (originCube d ((0 : ℕ) : ℤ)) := by
  rw [mem_openCubeSet_originCube_iff]
  intro i
  simp only [Nat.cast_zero, zpow_zero, mul_one, Pi.zero_apply]
  constructor <;> norm_num

theorem nv_abs_deriv_entry_le_obs (hd : 0 < d) (j : ShellField d) (x : Vec d) (l i k : Fin d) :
    |ShellField.deriv j x (Pi.single l 1) i k| ≤
      ShellField.j3Observable d 0 (ShellField.translate x j) := by
  set e : Vec d := Pi.single l 1 with he
  have hen : Book.Ch02.vecNorm e ≤ 1 := (nv_vecNorm_single l).le
  have hder : ShellField.deriv j x = ShellField.deriv (ShellField.translate x j) 0 := by
    rw [ShellField.translate_deriv, zero_add]
  rw [hder]
  have h1 : |ShellField.deriv (ShellField.translate x j) 0 e i k| ≤
      Book.Ch02.matrixOperatorNorm (ShellField.deriv (ShellField.translate x j) 0 e) :=
    Book.Ch02.abs_entry_le_matrixOperatorNorm _ _ _
  have h2 := ShellField.matrixOperatorNorm_apply_le_matrixDerivativeNorm
    (ShellField.deriv (ShellField.translate x j) 0) e hen
  have h3 : ShellField.matrixDerivativeNorm (ShellField.deriv (ShellField.translate x j) 0) ≤
      ShellField.shellCubeDerivNorm 0 (ShellField.translate x j) :=
    ((ShellField.shellCubeDerivNorm_le_iff 0 (ShellField.translate x j) _).1 le_rfl).2
      ⟨0, nv_zero_mem_cube⟩
  have h4 : ShellField.shellCubeDerivNorm 0 (ShellField.translate x j) ≤
      ShellField.j3Observable d 0 (ShellField.translate x j) := by
    have hn := ShellField.shellCubeSecondDerivNorm_nonneg 0 (ShellField.translate x j)
    have hv := ShellField.shellCubeValueNorm_nonneg 0 (ShellField.translate x j)
    have hdv := ShellField.shellCubeDerivNorm_nonneg 0 (ShellField.translate x j)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hs1 : (1 : ℝ) ≤ Real.sqrt d := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hd1
    unfold ShellField.j3Observable
    simp only [pow_zero, mul_one, Nat.mul_zero]
    have h5 : 0 ≤ (d : ℝ) * ShellField.shellCubeSecondDerivNorm 0 (ShellField.translate x j) :=
      mul_nonneg (Nat.cast_nonneg d) hn
    nlinarith only [hv, hdv, hs1, h5]
  exact h1.trans (h2.trans (h3.trans h4))

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
