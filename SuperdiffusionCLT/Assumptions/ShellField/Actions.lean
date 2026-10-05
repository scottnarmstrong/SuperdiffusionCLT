/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellField.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Transformations of marginal shell fields

This module provides the ordinary translation, negation, and signed-permutation
actions on marginal shell fields. These helpers will be used to state the J4
law symmetries. The private amplitude action is only an implementation device
for negation; this module has no spatial- or shell-scaling API.
-/

@[expose] public section

namespace SuperdiffusionCLT.Frozen.Assumptions.ShellField

open Homogenization
open scoped Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## Private amplitude scaling for negation -/

def valueScaleMap (c : ℝ) : C(Mat d, Mat d) :=
  ⟨fun M ↦ c • M, continuous_id.const_smul c⟩

def derivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨fun D ↦ c • D, continuous_id.const_smul c⟩

def secondDerivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨fun H ↦ c • H, continuous_id.const_smul c⟩

def scaleAmbient (c : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((valueScaleMap c).comp p.1,
    ((derivScaleMap c).comp p.2.1,
      (secondDerivScaleMap c).comp p.2.2))

private theorem continuous_scaleAmbient (c : ℝ) :
    Continuous (scaleAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp (valueScaleMap c)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (derivScaleMap c)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_postcomp (secondDerivScaleMap c)).comp
          continuous_snd.snd))

def scale (c : ℝ) (j : ShellField d) : ShellField d :=
  ⟨scaleAmbient c j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (j.hasFDerivAt x).const_smul c
    · intro x
      exact (j.deriv_hasFDerivAt x).const_smul c
    · intro x i k
      change c * j x i k = -(c * j x k i)
      rw [j.skew_entry x i k]
      ring⟩

@[simp]
private theorem scale_apply (c : ℝ) (j : ShellField d) (x : Vec d) :
    scale c j x = c • j x :=
  rfl

private theorem continuous_scale (c : ℝ) :
    Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun j ↦ (scale c j).2)

/-! ## Real spatial translations -/

def translateMap (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩

def translateShellAmbient (z : Vec d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (translateMap z),
    (p.2.1.comp (translateMap z), p.2.2.comp (translateMap z)))

theorem continuous_translateShellAmbient (z : Vec d) :
    Continuous (translateShellAmbient (d := d) z) :=
  ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_precomp (translateMap z)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_precomp (translateMap z)).comp
          continuous_snd.snd))

/-- Real translation in the manuscript convention `j(x + z)`. -/
def translate (z : Vec d) (j : ShellField d) : ShellField d :=
  ⟨translateShellAmbient z j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (j.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · intro x
      exact (j.deriv_hasFDerivAt (x + z)).comp x
          ((hasFDerivAt_id x).add_const z)
    · intro x i k
      exact j.skew_entry (x + z) i k⟩

@[simp]
theorem translate_apply (z : Vec d) (j : ShellField d) (x : Vec d) :
    translate z j x = j (x + z) :=
  rfl

@[simp]
theorem translate_deriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    deriv (translate z j) x = deriv j (x + z) :=
  rfl

@[simp]
theorem translate_secondDeriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    secondDeriv (translate z j) x = secondDeriv j (x + z) :=
  rfl

theorem continuous_translate (z : Vec d) :
    Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateShellAmbient z).comp continuous_subtype_val)
    (fun j ↦ (translate z j).2)

theorem measurable_translate (z : Vec d) :
    Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable

/-! ## Negation -/

/-- Value and derivative negation for the marginal J4 symmetry. -/
def negate (j : ShellField d) : ShellField d :=
  scale (-1) j

@[simp]
theorem negate_apply (j : ShellField d) (x : Vec d) :
    negate j x = -j x := by
  rw [negate, scale_apply, neg_one_smul]

@[simp]
theorem negate_deriv (j : ShellField d) (x : Vec d) :
    deriv (negate j) x = -deriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  ext i k
  change (-1 : ℝ) * deriv j x v i k = -deriv j x v i k
  ring

@[simp]
theorem negate_secondDeriv (j : ShellField d) (x : Vec d) :
    secondDeriv (negate j) x = -secondDeriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  ext i k
  change (-1 : ℝ) * secondDeriv j x v w i k =
    -secondDeriv j x v w i k
  ring

theorem continuous_negate : Continuous (negate (d := d)) :=
  continuous_scale (-1)

theorem measurable_negate : Measurable (negate (d := d)) :=
  continuous_negate.measurable

/-! ## Signed-permutation conjugation -/

def matVecContinuousLinearMap (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

@[simp]
private theorem matVecContinuousLinearMap_apply (R : Mat d) (x : Vec d) :
    matVecContinuousLinearMap R x = matVecMul R x :=
  rfl

def conjugateLinearMap (R : Mat d) : Mat d →ₗ[ℝ] Mat d where
  toFun M := matTranspose R * M * R
  map_add' M N := by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

def conjugateContinuousLinearMap (R : Mat d) : Mat d →L[ℝ] Mat d :=
  ⟨conjugateLinearMap R,
    (conjugateLinearMap R).continuous_of_finiteDimensional⟩

@[simp]
private theorem conjugateContinuousLinearMap_apply (R M : Mat d) :
    conjugateContinuousLinearMap R M = matTranspose R * M * R :=
  rfl

def rotateDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] Mat d) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Mat d) (Mat d)
      (conjugateContinuousLinearMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Mat d)).flip
      (matVecContinuousLinearMap R))

@[simp]
private theorem rotateDerivativeMap_apply (R : Mat d)
    (D : Vec d →L[ℝ] Mat d) (v : Vec d) :
    rotateDerivativeMap R D v =
      matTranspose R * D (matVecMul R v) * R :=
  rfl

def rotateSecondDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (ContinuousLinearMap.compL ℝ (Vec d)
      (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] Mat d)
      (rotateDerivativeMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d)
      (Vec d →L[ℝ] Mat d)).flip
        (matVecContinuousLinearMap R))

def rotateValueMap (R : Mat d) : C(Mat d, Mat d) :=
  ⟨conjugateContinuousLinearMap R, (conjugateContinuousLinearMap R).continuous⟩

def rotateDomainMap (R : Mat d) : C(Vec d, Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩

def rotateDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩

def rotateSecondDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨rotateSecondDerivativeMap R, (rotateSecondDerivativeMap R).continuous⟩

def rotateAmbient (R : Mat d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((rotateValueMap R).comp (p.1.comp (rotateDomainMap R)),
    ((rotateDerivativeContinuousMap R).comp
      (p.2.1.comp (rotateDomainMap R)),
      (rotateSecondDerivativeContinuousMap R).comp
        (p.2.2.comp (rotateDomainMap R))))

private theorem continuous_rotateAmbient (R : Mat d) :
    Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_postcomp (rotateValueMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_fst)).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_snd.fst)).prodMk
      ((ContinuousMap.continuous_postcomp
          (rotateSecondDerivativeContinuousMap R)).comp
        ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
          continuous_snd.snd)))

/-- The signed-permutation action `j(x) ↦ Rᵀ j(Rx) R`. -/
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R)
    (j : ShellField d) : ShellField d :=
  ⟨rotateAmbient R j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have hinner := (j.hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter :=
        (conjugateContinuousLinearMap R).hasFDerivAt.comp x hinner
      exact houter
    · intro x
      have hinner := (j.deriv_hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter := (rotateDerivativeMap R).hasFDerivAt.comp x hinner
      exact houter
    · intro x i k
      have hskew : matTranspose (j (matVecMul R x)) =
          -j (matVecMul R x) :=
        j.skew (matVecMul R x)
      have hmatrix :
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
            -(matTranspose R * j (matVecMul R x) * R) := by
        calc
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
              matTranspose R * matTranspose (j (matVecMul R x)) * R := by
                simp only [matTranspose, Matrix.transpose_mul,
                  Matrix.transpose_transpose, Matrix.mul_assoc]
          _ = matTranspose R * (-j (matVecMul R x)) * R := by
                rw [hskew]
          _ = -(matTranspose R * j (matVecMul R x) * R) := by
                rw [Matrix.mul_neg, Matrix.neg_mul]
      exact congrFun (congrFun hmatrix k) i⟩

@[simp]
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (j : ShellField d) (x : Vec d) :
    rotate R hR j x = matTranspose R * j (matVecMul R x) * R :=
  rfl

theorem continuous_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Continuous (rotate (d := d) R hR) :=
  Continuous.subtype_mk
    ((continuous_rotateAmbient R).comp continuous_subtype_val)
    (fun j ↦ (rotate R hR j).2)

theorem measurable_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotate (d := d) R hR) :=
  (continuous_rotate R hR).measurable

/-! ## Compatibility with the CoarseGraining library's regular-field operations -/

end

end SuperdiffusionCLT.Frozen.Assumptions.ShellField
