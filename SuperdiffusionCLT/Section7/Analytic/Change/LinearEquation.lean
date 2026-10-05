/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Change.Linear
public import SuperdiffusionCLT.Section7.Analytic.Defs

/-!
# Linear change of variables for weak solutions

For an invertible constant matrix `T` and `e = T ·`, a weak solution `u` of
`-∇·(a∇u) = f - ∇·g` in `U` (tested against `H¹₀(U)`) gives the weak solution `u ∘ e⁻¹` in
`e '' U` of the same equation with coefficient `T a(e⁻¹ ·) Tᵀ`, source `f ∘ e⁻¹` and forcing
`T (g ∘ e⁻¹)`: all three integrals pick up the same Jacobian factor `|det T|`. The normalized
version divides all three data by `|det T|`.

## Main results

* `SuperdiffusionCLT.Section7.IsWeakSolutionOn.linearChange`
* `SuperdiffusionCLT.Section7.IsWeakSolutionOn.linearChange_normalized`
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem matVecMul_mul (A B : Mat d) (v : Vec d) :
    matVecMul (A * B) v = matVecMul A (matVecMul B v) := by
  change (A * B).mulVec v = A.mulVec (B.mulVec v)
  exact (Matrix.mulVec_mulVec v A B).symm

private theorem matVecMul_one (v : Vec d) : matVecMul (1 : Mat d) v = v :=
  Matrix.one_mulVec v

private theorem vecDot_matVecMul_eq_vecDot_matTranspose (A : Mat d) (v w : Vec d) :
    vecDot (matVecMul A v) w = vecDot v (matVecMul (matTranspose A) w) := by
  unfold vecDot matVecMul matTranspose
  simp only [Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem transpose_mul_transpose_inv_eq_one (T : Mat d) (hT : IsUnit T) :
    matTranspose T * matTranspose T⁻¹ = 1 := by
  change T.transpose * T⁻¹.transpose = 1
  rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul T (T.isUnit_iff_isUnit_det.mp hT)]
  ext i j
  by_cases hij : i = j
  · simp [Matrix.one_apply, hij]
  · simp [hij, Ne.symm hij]

private theorem transformedGradient_at_image (T : Mat d) (hT : IsUnit T) {U : Set (Vec d)}
    (u : H1Function U) (x : Vec d) :
    (u.compLinearEquiv (matrixContinuousLinearEquiv T hT)).grad
        (matrixContinuousLinearEquiv T hT x) =
      matVecMul (matTranspose T⁻¹) (u.grad x) := by
  ext i
  simp only [H1Function.compLinearEquiv_grad, matrixContinuousLinearEquiv_symm_apply,
    matrixContinuousLinearEquiv_apply]
  have hx : matVecMul T⁻¹ (matVecMul T x) = x := by
    rw [← matVecMul_mul, Matrix.nonsing_inv_mul T (T.isUnit_iff_isUnit_det.mp hT),
      matVecMul_one]
  rw [hx]
  unfold vecDot matTranspose
  apply Finset.sum_congr rfl
  intro j _hj
  have hbasis : matVecMul T⁻¹ (basisVec i) j = T⁻¹ j i := by
    simp [matVecMul, basisVec_apply]
  rw [hbasis]
  change u.grad x j * T⁻¹ j i = T⁻¹ j i * u.grad x j
  ring

private theorem pulledTestGradient (T : Mat d) (hT : IsUnit T) {U : Set (Vec d)}
    (φ : H10Function (matrixContinuousLinearEquiv T hT '' U)) (x : Vec d) :
    (φ.pullbackLinearEquiv (matrixContinuousLinearEquiv T hT)).toH1Function.grad x =
      matVecMul (matTranspose T)
        (φ.toH1Function.grad (matrixContinuousLinearEquiv T hT x)) := by
  ext i
  rw [H10Function.pullbackLinearEquiv_grad]
  unfold vecDot matVecMul matTranspose
  simp only [matrixContinuousLinearEquiv_apply, Matrix.transpose_apply, matVecMul, basisVec_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  simp [mul_comm]

private theorem transformedFlux_at_image (T : Mat d) (hT : IsUnit T) {a : CoeffField d}
    {U : Set (Vec d)} (u : H1Function U) (x : Vec d) :
    matVecMul (T * a x * matTranspose T)
        ((u.compLinearEquiv (matrixContinuousLinearEquiv T hT)).grad
          (matrixContinuousLinearEquiv T hT x)) =
      matVecMul T (matVecMul (a x) (u.grad x)) := by
  rw [transformedGradient_at_image]
  have hcancel : matVecMul (matTranspose T)
      (matVecMul (matTranspose T⁻¹) (u.grad x)) = u.grad x := by
    calc
      matVecMul (matTranspose T) (matVecMul (matTranspose T⁻¹) (u.grad x)) =
          matVecMul (matTranspose T * matTranspose T⁻¹) (u.grad x) :=
        (matVecMul_mul _ _ _).symm
      _ = u.grad x := by
        rw [transpose_mul_transpose_inv_eq_one T hT, matVecMul_one]
  rw [matVecMul_mul, matVecMul_mul, hcancel]

/-- Transport of a weak solution through an invertible constant matrix `T`, with the Jacobian
factor cancelled on all three terms: the coefficient becomes `T a(e⁻¹ ·) Tᵀ`. -/
theorem IsWeakSolutionOn.linearChange
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (T : Mat d) (hT : IsUnit T) (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn
      (fun y => T * a ((matrixContinuousLinearEquiv T hT).symm y) * matTranspose T)
      (matrixContinuousLinearEquiv T hT '' U)
      (u.compLinearEquiv (matrixContinuousLinearEquiv T hT))
      (fun y => f ((matrixContinuousLinearEquiv T hT).symm y))
      (fun y => matVecMul T (g ((matrixContinuousLinearEquiv T hT).symm y))) := by
  set e := matrixContinuousLinearEquiv T hT with he
  intro φ
  let ψ : H10Function U := φ.pullbackLinearEquiv e
  have hold := hu ψ
  have hgrad : ∀ x, ψ.toH1Function.grad x = matVecMul (matTranspose T) (φ.toH1Function.grad (e x)) :=
    fun x => pulledTestGradient T hT φ x
  have hfluxPoint : ∀ x,
      vecDot (matVecMul (T * a x * matTranspose T)
          ((u.compLinearEquiv e).grad (e x))) (φ.toH1Function.grad (e x)) =
        vecDot (matVecMul (a x) (u.grad x)) (ψ.toH1Function.grad x) := by
    intro x
    rw [transformedFlux_at_image T hT u x, hgrad x]
    exact vecDot_matVecMul_eq_vecDot_matTranspose T _ _
  have hforcePoint : ∀ x,
      vecDot (matVecMul T (g x)) (φ.toH1Function.grad (e x)) =
        vecDot (g x) (ψ.toH1Function.grad x) := by
    intro x
    rw [hgrad x]
    exact vecDot_matVecMul_eq_vecDot_matTranspose T _ _
  let J : ℝ := |(LinearMap.det e.toLinearMap)⁻¹|
  have hJ : J ≠ 0 := by
    apply abs_ne_zero.mpr
    exact inv_ne_zero (isUnit_iff_ne_zero.mp e.toLinearEquiv.isUnit_det')
  have hA := setIntegral_comp_linearEquiv e U (fun y => vecDot
    (matVecMul (T * a (e.symm y) * matTranspose T) ((u.compLinearEquiv e).grad y))
      (φ.toH1Function.grad y))
  have hB := setIntegral_comp_linearEquiv e U
    (fun y => f (e.symm y) * φ.toH1Function.toFun y)
  have hC := setIntegral_comp_linearEquiv e U
    (fun y => vecDot (matVecMul T (g (e.symm y))) (φ.toH1Function.grad y))
  simp only [e.symm_apply_apply, smul_eq_mul] at hA hB hC
  have hA' : (∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (ψ.toH1Function.grad x)) =
      J * ∫ y in e '' U, vecDot
        (matVecMul (T * a (e.symm y) * matTranspose T) ((u.compLinearEquiv e).grad y))
          (φ.toH1Function.grad y) := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hfluxPoint)]
    exact hA
  have hB' : (∫ x in U, f x * ψ.toH1Function.toFun x) =
      J * ∫ y in e '' U, f (e.symm y) * φ.toH1Function.toFun y := by
    simpa only [ψ, H10Function.pullbackLinearEquiv_toFun] using hB
  have hC' : (∫ x in U, vecDot (g x) (ψ.toH1Function.grad x)) =
      J * ∫ y in e '' U, vecDot (matVecMul T (g (e.symm y))) (φ.toH1Function.grad y) := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hforcePoint)]
    exact hC
  apply mul_left_cancel₀ hJ
  rw [← hA', hold, hB', hC']
  ring

private theorem matVecMul_smul (c : ℝ) (A : Mat d) (v : Vec d) :
    matVecMul (c • A) v = c • matVecMul A v := by
  funext i
  simp [matVecMul, Finset.mul_sum, mul_assoc]

private theorem vecDot_smul_left (c : ℝ) (v w : Vec d) :
    vecDot (c • v) w = c * vecDot v w := by
  unfold vecDot
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_assoc]

/-- Scaling the data of a weak solution by a constant. -/
theorem IsWeakSolutionOn.smul {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (c : ℝ) (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn (fun x => c • a x) U u (fun x => c * f x) (fun x => c • g x) := by
  intro φ
  have h1 : (∫ x in U, vecDot (matVecMul (c • a x) (u.grad x)) (φ.toH1Function.grad x)) =
      c * ∫ x in U, vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [matVecMul_smul, vecDot_smul_left]
  have h2 : (∫ x in U, c * f x * φ.toH1Function.toFun x) =
      c * ∫ x in U, f x * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  have h3 : (∫ x in U, vecDot (c • g x) (φ.toH1Function.grad x)) =
      c * ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot_smul_left]
  rw [h1, h2, h3, hu φ, mul_add]

/-- The normalized transport: the coefficient is `T a(e⁻¹ ·) Tᵀ / |det T|`, and the source and
forcing are divided by `|det T|` as well. -/
theorem IsWeakSolutionOn.linearChange_normalized
    {U : Set (Vec d)} {a : CoeffField d} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d}
    (T : Mat d) (hT : IsUnit T) (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn
      (fun y => |T.det|⁻¹ •
        (T * a ((matrixContinuousLinearEquiv T hT).symm y) * matTranspose T))
      (matrixContinuousLinearEquiv T hT '' U)
      (u.compLinearEquiv (matrixContinuousLinearEquiv T hT))
      (fun y => |T.det|⁻¹ * f ((matrixContinuousLinearEquiv T hT).symm y))
      (fun y => |T.det|⁻¹ • matVecMul T (g ((matrixContinuousLinearEquiv T hT).symm y))) :=
  IsWeakSolutionOn.smul (a := fun y => T * a ((matrixContinuousLinearEquiv T hT).symm y) *
    matTranspose T) (|T.det|⁻¹) (IsWeakSolutionOn.linearChange T hT hu)

end

end SuperdiffusionCLT.Section7
