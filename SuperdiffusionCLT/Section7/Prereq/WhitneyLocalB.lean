/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.Local
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.EquationRestrictionZeroExtension

/-!
# Restricting and untranslating weak solutions to a translated cube

A weak solution on `W` restricts to an open subset, and a weak solution on `U + z` pulls back to `U`
with the field `a (· + z)`.  Together: the solution on the translated cube `z + Q ⊆ W` becomes a
solution on `Q`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

open Homogenization
open SuperdiffusionCLT.Section8.Common.ExcessDecay

variable {d : ℕ}

theorem wh2_setIntegral_extendByZero {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    (F : Vec d → ℝ) (phi : H10Function V) :
    ∫ x in W, F x * (h10ExtendToSuperset phi hV hVW).toH1Function.toFun x =
      ∫ x in V, F x * phi.toH1Function.toFun x := by
  have hind : (fun x => F x * (h10ExtendToSuperset phi hV hVW).toH1Function.toFun x) =
      V.indicator (fun x => F x * phi.toH1Function.toFun x) := by
    funext x
    rw [h10ExtendToSuperset_toFun]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtension_of_mem phi hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtension_of_not_mem phi hx, Set.indicator_of_notMem hx, mul_zero]
  rw [hind, MeasureTheory.integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

theorem wh2_setIntegral_extendByZero_vec {V W : Set (Vec d)} (hV : MeasurableSet V) (hVW : V ⊆ W)
    (F : Vec d → Vec d) (phi : H10Function V) :
    ∫ x in W, vecDot (F x) ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x) =
      ∫ x in V, vecDot (F x) (phi.toH1Function.grad x) := by
  have hind : (fun x => vecDot (F x) ((h10ExtendToSuperset phi hV hVW).toH1Function.grad x)) =
      V.indicator (fun x => vecDot (F x) (phi.toH1Function.grad x)) := by
    funext x
    rw [h10ExtendToSuperset_grad]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtensionGrad_of_mem phi hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtensionGrad_of_not_mem phi hx, Set.indicator_of_notMem hx,
        vecDot_zero_right]
  rw [hind, MeasureTheory.integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVW]

/-- Weak solutions restrict to open subsets (zero right-hand side vector datum). -/
theorem wh2_isWeakSolutionOn_restrict {W V : Set (Vec d)} (hV : IsOpen V) (hVW : V ⊆ W)
    {a : CoeffField d} {u : H1Function W} {f : Vec d → ℝ}
    (h : IsWeakSolutionOn a W u f (fun _ => 0)) :
    IsWeakSolutionOn a V (u.restrict hV hVW) f (fun _ => 0) := by
  intro phi
  have h1 := h (h10ExtendToSuperset phi hV.measurableSet hVW)
  rw [wh2_setIntegral_extendByZero_vec hV.measurableSet hVW,
    wh2_setIntegral_extendByZero hV.measurableSet hVW] at h1
  have hg : (u.restrict hV hVW).grad = u.grad := rfl
  simpa only [hg, vecDot_zero_left, integral_zero, add_zero] using h1

/-- Pull a weak solution on `U + z` back to `U`. -/
theorem wh2_isWeakSolutionOn_untranslate {a : CoeffField d} {U : Set (Vec d)} (z : Vec d)
    {u : H1Function (translateSet z U)} {f : Vec d → ℝ}
    (hw : IsWeakSolutionOn a (translateSet z U) u f (fun _ => 0)) :
    IsWeakSolutionOn (fun x => a (x + z)) U (H1Function.untranslate z u) (fun x => f (x + z))
      (fun _ => 0) := by
  intro φ
  have h := hw (φ.translate z)
  have e1 := setIntegral_comp_addRight_translateSet z U
    (fun y => vecDot (matVecMul (a y) (u.grad y)) ((φ.translate z).toH1Function.grad y))
  have e2 := setIntegral_comp_addRight_translateSet z U
    (fun y => f y * (φ.translate z).toH1Function.toFun y)
  simp only [H10Function.translate_toH1Function, H1Function.translate_grad,
    H1Function.translate_toFun, add_sub_cancel_right] at e1 e2
  simp only [H10Function.translate_toH1Function, H1Function.translate_grad,
    H1Function.translate_toFun, vecDot_zero_left, integral_zero, add_zero] at h
  simp only [H1Function.untranslate_grad, vecDot_zero_left,
    integral_zero, add_zero]
  rw [e1, e2]
  exact h

theorem wh2_isOpen_translateSet {U : Set (Vec d)} (hU : IsOpen U) (z : Vec d) :
    IsOpen (translateSet z U) := by
  have : translateSet z U = (fun x => x - z) ⁻¹' U := by
    ext x
    exact mem_translateSet_iff_sub_mem
  rw [this]
  exact hU.preimage (continuous_id.sub continuous_const)

/-- The translated cube: restrict to `z + Q` and untranslate to `Q`. -/
noncomputable def wh2_cubeFun {W : Set (Vec d)} (Q : TriadicCube d) (z : Vec d)
    (hsub : translateSet z (openCubeSet Q) ⊆ W) (u : H1Function W) :
    H1Function (openCubeSet Q) :=
  H1Function.untranslate z
    (u.restrict (wh2_isOpen_translateSet (isOpen_openCubeSet Q) z) hsub)

theorem wh2_cubeFun_grad {W : Set (Vec d)} (Q : TriadicCube d) (z : Vec d)
    (hsub : translateSet z (openCubeSet Q) ⊆ W) (u : H1Function W) (x : Vec d) :
    (wh2_cubeFun Q z hsub u).grad x = u.grad (x + z) := rfl

/-- A weak solution on `W` restricts to the cube `z + Q` and pulls back to `Q`. -/
theorem wh2_isWeakSolutionOn_cube {W : Set (Vec d)} (Q : TriadicCube d)
    (z : Vec d) (hsub : translateSet z (openCubeSet Q) ⊆ W) {a : CoeffField d}
    {u : H1Function W} {f : Vec d → ℝ} (h : IsWeakSolutionOn a W u f (fun _ => 0)) :
    IsWeakSolutionOn (fun x => a (x + z)) (openCubeSet Q) (wh2_cubeFun Q z hsub u)
      (fun x => f (x + z)) (fun _ => 0) :=
  wh2_isWeakSolutionOn_untranslate z
    (wh2_isWeakSolutionOn_restrict (wh2_isOpen_translateSet (isOpen_openCubeSet Q) z) hsub h)

end SuperdiffusionCLT.Section7
