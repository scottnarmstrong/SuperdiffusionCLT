/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ShellAssembly

/-!
# Dilation of shell fields

For a nonzero real `c` the dilation `D_c j` is the field `x ↦ j (x / c)`. Its stored
first derivative is `c⁻¹ • Dj (x / c)` and its stored second derivative is
`c⁻² • D²j (x / c)`. This is the convention under which shell `n` of the model is the
dilation by `3 ^ n` of shell `0`: the range of dependence and the J3 weights
`3 ^ n`, `3 ^ n √d`, `d 3 ^ (2 n)` scale exactly in this way.

The units `ℝˣ` act on shell fields, `D_c D_μ = D_{c μ}`, `D_1 = id`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-- The contraction `x ↦ c⁻¹ • x` as a continuous linear map. -/
def nv_dilVec (c : ℝˣ) : Vec d →L[ℝ] Vec d :=
  ((c⁻¹ : ℝˣ) : ℝ) • ContinuousLinearMap.id ℝ (Vec d)

@[simp]
theorem nv_dilVec_apply (c : ℝˣ) (x : Vec d) : nv_dilVec c x = ((c⁻¹ : ℝˣ) : ℝ) • x :=
  rfl

theorem nv_comp_dilVec {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝˣ)
    (A : Vec d →L[ℝ] E) : A.comp (nv_dilVec c) = ((c⁻¹ : ℝˣ) : ℝ) • A :=
  ContinuousLinearMap.ext fun v ↦ map_smul A _ v

def dilDomain (c : ℝˣ) : C(Vec d, Vec d) :=
  ⟨nv_dilVec c, (nv_dilVec c).continuous⟩

def dilateAmbient (c : ℝˣ) : ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (dilDomain c),
    ((ScalarC2Field.nv_smulMap (Vec d →L[ℝ] Mat d) ((c⁻¹ : ℝˣ) : ℝ)).comp
        (p.2.1.comp (dilDomain c)),
      (ScalarC2Field.nv_smulMap (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))
          (((c⁻¹ : ℝˣ) : ℝ) * ((c⁻¹ : ℝˣ) : ℝ))).comp (p.2.2.comp (dilDomain c))))

private theorem continuous_dilateAmbient (c : ℝˣ) :
    Continuous (dilateAmbient (d := d) c) :=
  ((ContinuousMap.continuous_precomp _).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp _).comp
      ((ContinuousMap.continuous_precomp _).comp continuous_snd.fst)).prodMk
        ((ContinuousMap.continuous_postcomp _).comp
          ((ContinuousMap.continuous_precomp _).comp continuous_snd.snd)))

/-- **Dilation** `(D_c j)(x) = j (x / c)` with the stored derivatives
`c⁻¹ • Dj (x / c)` and `c⁻² • D²j (x / c)`. -/
def dilate (c : ℝˣ) (j : ShellField d) : ShellField d :=
  ⟨dilateAmbient c j.1, by
    set s : ℝ := ((c⁻¹ : ℝˣ) : ℝ) with hs
    refine ⟨?_, ?_, ?_⟩
    · intro x
      refine ((j.hasFDerivAt (nv_dilVec c x)).comp x (nv_dilVec c).hasFDerivAt).congr_fderiv ?_
      exact nv_comp_dilVec c _
    · intro x
      refine (((j.deriv_hasFDerivAt (nv_dilVec c x)).comp x
        (nv_dilVec c).hasFDerivAt).const_smul s).congr_fderiv ?_
      refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
      change s • (ShellField.secondDeriv j (nv_dilVec c x) (s • v)) w =
        (s * s) • ShellField.secondDeriv j (nv_dilVec c x) v w
      rw [map_smul, _root_.smul_apply, smul_smul]
    · intro x i k
      exact j.skew_entry _ i k⟩

@[simp]
theorem dilate_apply (c : ℝˣ) (j : ShellField d) (x : Vec d) :
    dilate c j x = j (((c⁻¹ : ℝˣ) : ℝ) • x) :=
  rfl

@[simp]
theorem dilate_deriv (c : ℝˣ) (j : ShellField d) (x : Vec d) :
    ShellField.deriv (dilate c j) x = ((c⁻¹ : ℝˣ) : ℝ) • ShellField.deriv j (((c⁻¹ : ℝˣ) : ℝ) • x) :=
  rfl

@[simp]
theorem dilate_secondDeriv (c : ℝˣ) (j : ShellField d) (x : Vec d) :
    ShellField.secondDeriv (dilate c j) x =
      (((c⁻¹ : ℝˣ) : ℝ) * ((c⁻¹ : ℝˣ) : ℝ)) •
        ShellField.secondDeriv j (((c⁻¹ : ℝˣ) : ℝ) • x) :=
  rfl

theorem continuous_dilate (c : ℝˣ) : Continuous (dilate (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_dilateAmbient c).comp continuous_subtype_val)
    (fun j ↦ (dilate c j).2)

/-- Dilation is measurable. -/
theorem measurable_dilate (c : ℝˣ) : Measurable (dilate (d := d) c) :=
  (continuous_dilate c).measurable

theorem dilate_one (j : ShellField d) : dilate 1 j = j := by
  ext x
  simp

/-- The dilation factor `3 ^ n` as a unit. -/
def nv_scaleUnit (n : ℕ) : ℝˣ :=
  Units.mk0 ((3 : ℝ) ^ n) (pow_ne_zero _ (by norm_num))

@[simp]
theorem nv_scaleUnit_val (n : ℕ) : ((nv_scaleUnit n : ℝˣ) : ℝ) = (3 : ℝ) ^ n :=
  rfl

theorem nv_scaleUnit_inv_val (n : ℕ) : (((nv_scaleUnit n)⁻¹ : ℝˣ) : ℝ) = ((3 : ℝ) ^ n)⁻¹ := by
  simp

theorem nv_scaleUnit_zero : nv_scaleUnit 0 = 1 := by
  ext
  simp

/-! ## Translations, negation and rotations -/

theorem translate_dilate (z : Vec d) (c : ℝˣ) (j : ShellField d) :
    ShellField.translate z (dilate c j) =
      dilate c (ShellField.translate (((c⁻¹ : ℝˣ) : ℝ) • z) j) := by
  ext x
  simp [smul_add]

theorem negate_dilate (c : ℝˣ) (j : ShellField d) :
    ShellField.negate (dilate c j) = dilate c (ShellField.negate j) := by
  ext x
  simp

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
