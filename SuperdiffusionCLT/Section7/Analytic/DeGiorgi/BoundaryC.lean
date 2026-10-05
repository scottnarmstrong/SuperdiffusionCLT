/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryB

/-!
# Level identity on a cube for the zero extension of an `H¹₀(U)` weak solution

The coefficient is extended off `U` by a constant matrix; the data `f`, `g` are extended by zero.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

open scoped Classical in
/-- The coefficient `a` on `U`, extended by the constant matrix `c` outside `U`. -/
noncomputable def boundaryCoeff (U : Set (Vec d)) (c : Mat d) (a : CoeffField d) : CoeffField d :=
  fun x => if x ∈ U then a x else c

theorem integral_indicator_eq_of_vanish {Q : Set (Vec d)} (hU : MeasurableSet U)
    {C : Vec d → ℝ} (h : ∀ x, x ∉ Q → C x = 0) :
    ∫ x in Q, U.indicator C x = ∫ x in U, C x := by
  rw [integral_indicator hU, Measure.restrict_restrict hU]
  exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU Set.inter_subset_left
    fun x hx => h x fun hq => hx.2 ⟨hx.1, hq⟩).symm

/-- **Level identity of the zero extension on a cube.** -/
theorem boundary_level_identity (hU : IsOpen U) (hfin : volume U ≠ ⊤) {Q : Set (Vec d)}
    (hQ : IsOpen Q) (w : H10Function U) (a : CoeffField d) (c : Mat d) (f : Vec d → ℝ)
    (g : Vec d → Vec d) (hw : IsWeakSolutionOn a U w.toH1Function f g) {k : ℝ} (hk : 0 ≤ k)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Q) :
    ∫ x in Q, vecDot (matVecMul (boundaryCoeff U c a x) ((zeroExtCube hU hQ w).grad x))
        (levelTest (zeroExtCube hU hQ w) k η x) =
      (∫ x in Q, U.indicator f x *
          (η x ^ 2 * max ((zeroExtCube hU hQ w).toFun x - k) 0)) +
        ∫ x in Q, vecDot (U.indicator g x) (levelTest (zeroExtCube hU hQ w) k η x) := by
  classical
  obtain ⟨φ, hφf, hφg⟩ := exists_levelTest_h10 hU hfin w hk hη hηc
  have hweak := hw φ
  have hUm := hU.measurableSet
  have hWf : ∀ x ∈ U, (zeroExtCube hU hQ w).toFun x = w.toH1Function.toFun x := fun x hx => by
    rw [zeroExtCube_toFun]; exact Set.indicator_of_mem hx _
  have hWg : ∀ x ∈ U, (zeroExtCube hU hQ w).grad x = w.toH1Function.grad x := fun x hx => by
    rw [zeroExtCube_grad]; exact Set.indicator_of_mem hx _
  have hWg0 : ∀ x, x ∉ U → (zeroExtCube hU hQ w).grad x = 0 := fun x hx => by
    rw [zeroExtCube_grad]; exact Set.indicator_of_notMem hx _
  have hLT : ∀ x ∈ U, levelTest (zeroExtCube hU hQ w) k η x = levelTest w.toH1Function k η x :=
    fun x hx => levelTest_congr (hWf x hx) (hWg x hx)
  have hLTQ : ∀ x, x ∉ Q → levelTest w.toH1Function k η x = 0 := fun x hx =>
    levelTest_eq_zero_of_notMem _ k fun h => hx (hηs h)
  have hη0 : ∀ x, x ∉ Q → η x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hηs h)
  have e1 : ∫ x in Q, vecDot (matVecMul (boundaryCoeff U c a x) ((zeroExtCube hU hQ w).grad x))
        (levelTest (zeroExtCube hU hQ w) k η x) =
      ∫ x in Q, U.indicator (fun x => vecDot (matVecMul (a x) (w.toH1Function.grad x))
        (levelTest w.toH1Function k η x)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx, boundaryCoeff, hx, ↓reduceIte, hWg x hx, hLT x hx]
    · simp [Set.indicator_of_notMem hx, hWg0 x hx, matVecMul, vecDot]
  have e2 : ∫ x in Q, U.indicator f x *
        (η x ^ 2 * max ((zeroExtCube hU hQ w).toFun x - k) 0) =
      ∫ x in Q, U.indicator (fun x => f x *
        (η x ^ 2 * max (w.toH1Function.toFun x - k) 0)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx, hWf x hx]
    · simp [Set.indicator_of_notMem hx]
  have e3 : ∫ x in Q, vecDot (U.indicator g x) (levelTest (zeroExtCube hU hQ w) k η x) =
      ∫ x in Q, U.indicator (fun x => vecDot (g x) (levelTest w.toH1Function k η x)) x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx, hLT x hx]
    · simp [Set.indicator_of_notMem hx, vecDot]
  rw [e1, e2, e3,
    integral_indicator_eq_of_vanish hUm (fun x hx => by simp [hLTQ x hx, vecDot, matVecMul]),
    integral_indicator_eq_of_vanish hUm (fun x hx => by simp [hη0 x hx]),
    integral_indicator_eq_of_vanish hUm (fun x hx => by simp [hLTQ x hx, vecDot])]
  have e4 : ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x))
        (levelTest w.toH1Function k η x) =
      ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    refine integral_congr_ae ?_
    filter_upwards [hφg] with x hx
    rw [hx]
  have e5 : ∫ x in U, vecDot (g x) (levelTest w.toH1Function k η x) =
      ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) := by
    refine integral_congr_ae ?_
    filter_upwards [hφg] with x hx
    rw [hx]
  have e6 : ∫ x in U, f x * (η x ^ 2 * max (w.toH1Function.toFun x - k) 0) =
      ∫ x in U, f x * φ.toH1Function.toFun x :=
    setIntegral_congr_fun hUm fun x _ => by simp only [hφf]
  rw [e4, e5, e6]
  exact hweak

end SuperdiffusionCLT.Section7
