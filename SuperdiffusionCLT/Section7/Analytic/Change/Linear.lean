/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.H1.Definitions
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Determinant

/-!
# Linear changes of variables for `H¹` and `H¹₀`

An invertible continuous linear map `e` of `ℝᵈ` transports `H¹(U)` to `H¹(e '' U)` and `H¹₀(U)`
to `H¹₀(e '' U)` by `u ↦ u ∘ e⁻¹`, with weak gradient `x ↦ (e⁻¹)ᵀ`-rotated gradient
`vecDot (∇u (e⁻¹ x)) (e⁻¹ eᵢ)`.

## Main definitions

* `Homogenization.H1Function.compLinearEquiv`, `Homogenization.H10Function.compLinearEquiv`.
* `SuperdiffusionCLT.Section7.matrixContinuousLinearEquiv`: an invertible matrix as a
  continuous linear equivalence.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- An invertible matrix, regarded as a continuous linear equivalence of `Vec d`. -/
def matrixContinuousLinearEquiv (A : Mat d) (hA : IsUnit A) : Vec d ≃L[ℝ] Vec d :=
  ({
    toFun := Matrix.toLin' A
    invFun := Matrix.toLin' A⁻¹
    left_inv := fun x => by
      change A⁻¹.mulVec (A.mulVec x) = x
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
        (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    right_inv := fun x => by
      change A.mulVec (A⁻¹.mulVec x) = x
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A
        (A.isUnit_iff_isUnit_det.mp hA), Matrix.one_mulVec]
    map_add' := (Matrix.toLin' A).map_add
    map_smul' := (Matrix.toLin' A).map_smul
  } : Vec d ≃ₗ[ℝ] Vec d).toContinuousLinearEquiv

@[simp]
theorem matrixContinuousLinearEquiv_apply (A : Mat d) (hA : IsUnit A) (x : Vec d) :
    matrixContinuousLinearEquiv A hA x = matVecMul A x :=
  rfl

@[simp]
theorem matrixContinuousLinearEquiv_symm_apply (A : Mat d) (hA : IsUnit A) (x : Vec d) :
    (matrixContinuousLinearEquiv A hA).symm x = matVecMul A⁻¹ x :=
  rfl

/-- The exact Jacobian for an invertible linear change of variables. -/
theorem map_linearEquiv_volume (e : Vec d ≃L[ℝ] Vec d) :
    Measure.map e (volume : Measure (Vec d)) =
      ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| • volume := by
  exact Real.map_linearMap_volume_pi_eq_smul_volume_pi
    (f := e.toLinearMap) (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')

/-- The Jacobian identity with both domain restrictions transported exactly. -/
theorem map_linearEquiv_volumeOn (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    Measure.map e (volume.restrict U) =
      ENNReal.ofReal |(LinearMap.det e.toLinearMap)⁻¹| • volume.restrict (e '' U) := by
  have hrestrict : (volume.restrict U).map e =
      (volume.map e).restrict (e '' U) := by
    have h := (e.toHomeomorph.toMeasurableEquiv.restrict_map
      (μ := volume) (s := e '' U)).symm
    change (volume.restrict (e ⁻¹' (e '' U))).map e =
      (volume.map e).restrict (e '' U) at h
    rw [Set.preimage_image_eq _ e.injective] at h
    exact h
  rw [hrestrict, map_linearEquiv_volume, Measure.restrict_smul]

/-- Exact integral transport, valid for real or vector-valued integrands. -/
theorem setIntegral_comp_linearEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in U, f (e x) =
      |(LinearMap.det e.toLinearMap)⁻¹| • ∫ y in e '' U, f y := by
  have hmap := map_linearEquiv_volumeOn e U
  have h := e.toHomeomorph.measurableEmbedding.integral_map
    (μ := volume.restrict U) f
  change (∫ y, f y ∂Measure.map e (volume.restrict U)) =
    ∫ x, f (e x) ∂volume.restrict U at h
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at h
  exact h.symm

/-- `e.symm` carries the restricted volume on `e '' U` to a constant multiple of that on `U`. -/
theorem map_symm_volumeOn (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) :
    Measure.map e.symm (volume.restrict (e '' U)) =
      ENNReal.ofReal |(LinearMap.det e.symm.toLinearMap)⁻¹| • volume.restrict U := by
  have himage : e.symm '' (e '' U) = U := by
    rw [← Set.image_comp]
    simp
  have h := map_linearEquiv_volumeOn e.symm (e '' U)
  rwa [himage] at h

/-- An `Lᵖ` field on `U` pulled forward through `e.symm` is `Lᵖ` on `e '' U`. -/
theorem memLp_comp_symm
    {E : Type*} [NormedAddCommGroup E]
    (e : Vec d ≃L[ℝ] Vec d) {U : Set (Vec d)} {p : ℝ≥0∞}
    {f : Vec d → E} (hf : MemLp f p (volume.restrict U)) :
    MemLp (fun x => f (e.symm x)) p (volume.restrict (e '' U)) := by
  apply MemLp.comp_of_map _ e.symm.continuous.measurable.aemeasurable
  rw [map_symm_volumeOn]
  exact hf.smul_measure ENNReal.ofReal_ne_top

/-- The `L²` norm of a function pulled forward through `e.symm` is a fixed finite multiple of its
`L²` norm on `U`. -/
theorem eLpNorm_two_comp_symm (e : Vec d ≃L[ℝ] Vec d) (U : Set (Vec d)) (g : Vec d → ℝ) :
    eLpNorm (fun x => g (e.symm x)) 2 (volume.restrict (e '' U)) =
      (ENNReal.ofReal |(LinearMap.det e.symm.toLinearMap)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm g 2 (volume.restrict U) := by
  have h := (e.symm.toHomeomorph.measurableEmbedding.eLpNorm_map_measure
    (μ := volume.restrict (e '' U)) (g := g) (p := 2))
  change eLpNorm g 2 (Measure.map e.symm (volume.restrict (e '' U))) = _ at h
  rw [map_symm_volumeOn, eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num)
    (by norm_num)] at h
  exact h.symm

theorem eLpNorm_two_comp_symm_const_ne_top (e : Vec d ≃L[ℝ] Vec d) :
    (ENNReal.ofReal |(LinearMap.det e.symm.toLinearMap)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
  ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

/-- A continuous linear functional is the coordinate sum of its values on the basis. -/
theorem clm_apply_eq_sum (L : Vec d →L[ℝ] ℝ) (z : Vec d) :
    L z = ∑ j, z j * L (basisVec j) := by
  have hz : z = ∑ j, z j • basisVec j := by
    ext k
    simp [basisVec, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hz]
  simp [map_sum]

/-- `L²(U)` times a continuous compactly supported function is integrable on `U`. -/
theorem integrableOn_mul_continuous_hasCompactSupport {U : Set (Vec d)} {u g : Vec d → ℝ}
    (hu : MemL2On U u) (hg : Continuous g) (hgc : HasCompactSupport g) :
    IntegrableOn (fun x => u x * g x) U volume :=
  hu.integrable_mul ((hg.memLp_of_hasCompactSupport (μ := volume) (p := 2) hgc).restrict U)

/-- Integration by parts of an `H¹(U)` function against the directional derivative of a test
function. -/
theorem integral_mul_fderiv_apply_eq_neg {U : Set (Vec d)} (u : H1Function U)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ U) (z : Vec d) :
    (∫ x in U, u x * (fderiv ℝ φ x) z ∂volume) =
      -∫ x in U, vecDot (u.grad x) z * φ x ∂volume := by
  have hDcont : ∀ j : Fin d, Continuous fun x => fderiv ℝ φ x (basisVec j) :=
    fun j => (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDc : ∀ j : Fin d, HasCompactSupport fun x => fderiv ℝ φ x (basisVec j) :=
    fun j => hc.fderiv_apply ℝ (basisVec j)
  have hleftInt : ∀ j : Fin d,
      IntegrableOn (fun x => z j * (u x * fderiv ℝ φ x (basisVec j))) U volume := by
    intro j
    have h := integrableOn_mul_continuous_hasCompactSupport u.memL2 (hDcont j) (hDc j)
    exact h.const_mul (z j)
  have hrightInt : ∀ j : Fin d,
      IntegrableOn (fun x => z j * (u.grad x j * φ x)) U volume := by
    intro j
    exact (integrableOn_mul_continuous_hasCompactSupport (u.gradMemL2 j)
      hφ.continuous hc).const_mul (z j)
  have hcoord : ∀ j : Fin d,
      (∫ x in U, z j * (u x * fderiv ℝ φ x (basisVec j)) ∂volume) =
        -∫ x in U, z j * (u.grad x j * φ x) ∂volume := by
    intro j
    rw [integral_const_mul, integral_const_mul,
      u.hasWeakGradient j φ hφ hc hsub, mul_neg]
  calc
    (∫ x in U, u x * (fderiv ℝ φ x) z ∂volume) =
        ∫ x in U, ∑ j : Fin d, z j * (u x * fderiv ℝ φ x (basisVec j)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [clm_apply_eq_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j : Fin d, ∫ x in U, z j * (u x * fderiv ℝ φ x (basisVec j)) ∂volume :=
      integral_finsetSum _ fun j _ => hleftInt j
    _ = ∑ j : Fin d, -∫ x in U, z j * (u.grad x j * φ x) ∂volume :=
      Finset.sum_congr rfl fun j _ => hcoord j
    _ = -∫ x in U, vecDot (u.grad x) z * φ x ∂volume := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => hrightInt j]
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards with x
      unfold vecDot
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring

end

end SuperdiffusionCLT.Section7

namespace Homogenization

open MeasureTheory

noncomputable section

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The weak gradient of `u ∘ e⁻¹`. -/
theorem hasWeakGradient_compLinearEquiv (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) :
    HasWeakGradientOn (e '' U) (fun x => u (e.symm x))
      (fun x i => vecDot (u.grad (e.symm x)) (e.symm (basisVec i))) := by
  intro i φ hφ hc hsub
  let ψ : Vec d → ℝ := fun x => φ (e x)
  let z : Vec d := e.symm (basisVec i)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp e.contDiff
  have hψc : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ e.toHomeomorph)
    exact hc.comp_homeomorph e.toHomeomorph
  have hψsub : tsupport ψ ⊆ U := by
    intro x hx
    have hex : e x ∈ tsupport φ := by
      rw [show ψ = φ ∘ e.toHomeomorph by rfl,
        tsupport_comp_eq_preimage φ e.toHomeomorph] at hx
      exact hx
    rcases hsub hex with ⟨y, hy, hey⟩
    simpa [e.injective hey] using hy
  have hdir := SuperdiffusionCLT.Section7.integral_mul_fderiv_apply_eq_neg u hψ hψc hψsub z
  have hderiv : ∀ y, (fderiv ℝ ψ y) z = (fderiv ℝ φ (e y)) (basisVec i) := by
    intro y
    have h : fderiv ℝ ψ y = (fderiv ℝ φ (e y)).comp (e : Vec d →L[ℝ] Vec d) :=
      ContinuousLinearEquiv.comp_right_fderiv e
    rw [h]
    simp [z]
  let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
  have hJ : J ≠ 0 := by
    apply abs_ne_zero.mpr
    exact inv_ne_zero (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')
  have hleft := SuperdiffusionCLT.Section7.setIntegral_comp_linearEquiv e U
    (fun y => u (e.symm y) * (fderiv ℝ φ y) (basisVec i))
  have hright := SuperdiffusionCLT.Section7.setIntegral_comp_linearEquiv e U
    (fun y => vecDot (u.grad (e.symm y)) z * φ y)
  simp only [e.symm_apply_apply, smul_eq_mul] at hleft hright
  simp only [hderiv] at hdir
  have hscaled : J * (∫ y in e '' U, u (e.symm y) * (fderiv ℝ φ y) (basisVec i)) =
      J * (-∫ y in e '' U, vecDot (u.grad (e.symm y)) z * φ y) := by
    rw [← hleft, mul_neg, ← hright]
    exact hdir
  exact mul_left_cancel₀ hJ hscaled

/-- Push an `H¹(U)` function forward to `H¹(e '' U)` by `u ∘ e⁻¹`. -/
def compLinearEquiv (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) : H1Function (e '' U) where
  toFun := fun x => u (e.symm x)
  grad := fun x i => vecDot (u.grad (e.symm x)) (e.symm (basisVec i))
  memL2 := SuperdiffusionCLT.Section7.memLp_comp_symm e u.memL2
  gradMemL2 := fun i => by
    unfold vecDot
    apply memLp_finsetSum Finset.univ
    intro j _hj
    have hj : MemL2On (e '' U) (fun x => u.grad (e.symm x) j) :=
      SuperdiffusionCLT.Section7.memLp_comp_symm e (u.gradMemL2 j)
    simpa only [mul_comm] using hj.mul_const (e.symm (basisVec i) j)
  hasWeakGradient := hasWeakGradient_compLinearEquiv e u

@[simp]
theorem compLinearEquiv_toFun (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) (x : Vec d) :
    (u.compLinearEquiv e).toFun x = u (e.symm x) :=
  rfl

@[simp]
theorem compLinearEquiv_grad (e : Vec d ≃L[ℝ] Vec d) (u : H1Function U) (x : Vec d)
    (i : Fin d) :
    (u.compLinearEquiv e).grad x i = vecDot (u.grad (e.symm x)) (e.symm (basisVec i)) :=
  rfl

/-- Transport an `H¹` function along an equality of domains. -/
def castSet {V : Set (Vec d)} (h : U = V) (u : H1Function U) : H1Function V := by
  subst h
  exact u

@[simp]
theorem castSet_toFun {V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (u.castSet h).toFun = u.toFun := by
  subst h
  rfl

@[simp]
theorem castSet_grad {V : Set (Vec d)} (h : U = V) (u : H1Function U) :
    (u.castSet h).grad = u.grad := by
  subst h
  rfl

end H1Function

end

end Homogenization

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace H10Function

variable {d : ℕ} {U : Set (Vec d)}

theorem tendsto_approx_comp (e : Vec d ≃L[ℝ] Vec d) (w : H10Function U) :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => w.approx n (e.symm x) - (w.toH1Function.compLinearEquiv e).toFun x)
        2 (volume.restrict (e '' U))) Filter.atTop (nhds 0) := by
  have h : ∀ n, eLpNorm (fun x => w.approx n (e.symm x) -
      (w.toH1Function.compLinearEquiv e).toFun x) 2 (volume.restrict (e '' U)) =
      (ENNReal.ofReal |(LinearMap.det e.symm.toLinearMap)⁻¹|) ^ (1 / (2 : ℝ≥0∞)).toReal *
        eLpNorm (fun x => w.approx n x - w.toH1Function.toFun x) 2 (volume.restrict U) :=
    fun n => SuperdiffusionCLT.Section7.eLpNorm_two_comp_symm e U
      (fun x => w.approx n x - w.toH1Function.toFun x)
  simp only [h]
  have := ENNReal.Tendsto.const_mul w.tendsto_approx
    (Or.inr (SuperdiffusionCLT.Section7.eLpNorm_two_comp_symm_const_ne_top e))
  simpa using this

theorem tendsto_approx_grad_comp (e : Vec d ≃L[ℝ] Vec d) (w : H10Function U)
    (i : Fin d) :
    Filter.Tendsto
      (fun n => eLpNorm (fun x => (fderiv ℝ (fun y => w.approx n (e.symm y)) x) (basisVec i) -
        (w.toH1Function.compLinearEquiv e).grad x i) 2 (volume.restrict (e '' U)))
      Filter.atTop (nhds 0) := by
  set K : ℝ≥0∞ := (ENNReal.ofReal |(LinearMap.det e.symm.toLinearMap)⁻¹|) ^
    (1 / (2 : ℝ≥0∞)).toReal with hK
  have hKtop : K ≠ ⊤ := SuperdiffusionCLT.Section7.eLpNorm_two_comp_symm_const_ne_top e
  let z : Vec d := e.symm (basisVec i)
  let h : ℕ → Fin d → Vec d → ℝ := fun n j y =>
    fderiv ℝ (w.approx n) y (basisVec j) - w.toH1Function.grad y j
  have hpoint : ∀ n x, (fderiv ℝ (fun y => w.approx n (e.symm y)) x) (basisVec i) -
      (w.toH1Function.compLinearEquiv e).grad x i =
        ∑ j, z j * h n j (e.symm x) := by
    intro n x
    have hd : fderiv ℝ (fun y => w.approx n (e.symm y)) x =
        (fderiv ℝ (w.approx n) (e.symm x)).comp (e.symm : Vec d →L[ℝ] Vec d) :=
      ContinuousLinearEquiv.comp_right_fderiv e.symm
    rw [hd]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      H1Function.compLinearEquiv_grad, h]
    rw [SuperdiffusionCLT.Section7.clm_apply_eq_sum]
    unfold vecDot
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hle : ∀ n, eLpNorm (fun x => (fderiv ℝ (fun y => w.approx n (e.symm y)) x) (basisVec i) -
        (w.toH1Function.compLinearEquiv e).grad x i) 2 (volume.restrict (e '' U)) ≤
      ∑ j, ‖z j‖ₑ * (K * eLpNorm (h n j) 2 (volume.restrict U)) := by
    intro n
    have hfun : (fun x => (fderiv ℝ (fun y => w.approx n (e.symm y)) x) (basisVec i) -
        (w.toH1Function.compLinearEquiv e).grad x i) =
        ∑ j, (fun x => z j * h n j (e.symm x)) := by
      funext x
      rw [hpoint]
      simp
    rw [hfun]
    refine (eLpNorm_sum_le (by norm_num)).trans (Finset.sum_le_sum fun j _ => ?_)
    have hc : eLpNorm (fun x => z j * h n j (e.symm x)) 2 (volume.restrict (e '' U)) =
        ‖z j‖ₑ * eLpNorm (fun x => h n j (e.symm x)) 2 (volume.restrict (e '' U)) :=
      eLpNorm_const_smul (z j) (fun x => h n j (e.symm x)) 2 _
    rw [hc, SuperdiffusionCLT.Section7.eLpNorm_two_comp_symm e U (h n j)]
  have hS : Filter.Tendsto (fun n => ∑ j, ‖z j‖ₑ * (K * eLpNorm (h n j) 2 (volume.restrict U)))
      Filter.atTop (nhds 0) := by
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin d)), Filter.Tendsto
        (fun n => ‖z j‖ₑ * (K * eLpNorm (h n j) 2 (volume.restrict U))) Filter.atTop
        (nhds 0) := by
      intro j _
      have h1 := ENNReal.Tendsto.const_mul (w.tendsto_approx_grad j) (Or.inr hKtop)
      have h2 := ENNReal.Tendsto.const_mul h1 (Or.inr (enorm_ne_top (x := z j)))
      simpa using h2
    simpa using tendsto_finsetSum _ hj
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
    (fun _ => zero_le) hle

/-- Push an `H¹₀(U)` function forward to `H¹₀(e '' U)`; the approximants are composed with
`e⁻¹`. -/
def compLinearEquiv (e : Vec d ≃L[ℝ] Vec d) (w : H10Function U) : H10Function (e '' U) where
  toH1Function := w.toH1Function.compLinearEquiv e
  approx := fun n x => w.approx n (e.symm x)
  approx_smooth := fun n => (w.approx_smooth n).comp e.symm.contDiff
  approx_hasCompactSupport := fun n => by
    show HasCompactSupport (w.approx n ∘ e.symm.toHomeomorph)
    exact (w.approx_hasCompactSupport n).comp_homeomorph e.symm.toHomeomorph
  approx_support_subset := fun n x hx => by
    have hex : e.symm x ∈ tsupport (w.approx n) := by
      rw [show (fun y => w.approx n (e.symm y)) = w.approx n ∘ e.symm.toHomeomorph by rfl,
        tsupport_comp_eq_preimage (w.approx n) e.symm.toHomeomorph] at hx
      exact hx
    exact ⟨e.symm x, w.approx_support_subset n hex, e.apply_symm_apply x⟩
  tendsto_approx := tendsto_approx_comp e w
  tendsto_approx_grad := tendsto_approx_grad_comp e w

@[simp]
theorem compLinearEquiv_toFun (e : Vec d ≃L[ℝ] Vec d) (w : H10Function U) (x : Vec d) :
    (w.compLinearEquiv e).toH1Function.toFun x = w.toH1Function.toFun (e.symm x) :=
  rfl

@[simp]
theorem compLinearEquiv_grad (e : Vec d ≃L[ℝ] Vec d) (w : H10Function U) (x : Vec d)
    (i : Fin d) :
    (w.compLinearEquiv e).toH1Function.grad x i =
      vecDot (w.toH1Function.grad (e.symm x)) (e.symm (basisVec i)) :=
  rfl

/-- Transport an `H¹₀` function along an equality of domains. -/
def castSet {V : Set (Vec d)} (h : U = V) (w : H10Function U) : H10Function V := by
  subst h
  exact w

@[simp]
theorem castSet_toH1Function {V : Set (Vec d)} (h : U = V) (w : H10Function U) :
    (w.castSet h).toH1Function = w.toH1Function.castSet h := by
  subst h
  rfl

/-- Pull an `H¹₀(e '' U)` function back to `H¹₀(U)` by `φ ∘ e`. -/
def pullbackLinearEquiv (e : Vec d ≃L[ℝ] Vec d) (φ : H10Function (e '' U)) : H10Function U :=
  (φ.compLinearEquiv e.symm).castSet (by
    rw [← Set.image_comp]
    simp)

@[simp]
theorem pullbackLinearEquiv_toFun (e : Vec d ≃L[ℝ] Vec d) (φ : H10Function (e '' U))
    (x : Vec d) :
    (φ.pullbackLinearEquiv e).toH1Function.toFun x = φ.toH1Function.toFun (e x) := by
  simp [pullbackLinearEquiv]

@[simp]
theorem pullbackLinearEquiv_grad (e : Vec d ≃L[ℝ] Vec d) (φ : H10Function (e '' U))
    (x : Vec d) (i : Fin d) :
    (φ.pullbackLinearEquiv e).toH1Function.grad x i =
      vecDot (φ.toH1Function.grad (e x)) (e (basisVec i)) := by
  simp [pullbackLinearEquiv]

end H10Function

end

end Homogenization
