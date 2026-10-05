/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OddReflectionGlue

/-!
# The trace measure of the boundary window: the zero extension and the slab

This module provides the trace carrier: an `H¹₀(□_m)` datum, read on a cube `A` that pokes
out of `□_m`, is an `H¹(A)` function that *vanishes identically* on the part
of `A` outside `□_m`.  That part is the development's stand-in for the trace
measure: the zero-trace hypothesis is converted into a **volume** statement,
which is the only form the carriers support (no surface measure exists in
CoarseGraining or Mathlib).  `zeroExtendH1` builds the `H¹(A)` function.

## Main results

* `fderiv_apply_eq_zero_of_notMem_tsupport` — off its topological support a function has
  vanishing derivative.
* `hasWeakGradientOn_of_univ` — a global weak-gradient graph restricts to every set.
* `zeroExtendH1`, `zeroExtendH1_grad` — the zero extension of an `H¹₀(V)` datum as an `H¹(A)`
  function.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The zero extension as an `H¹` function on an arbitrary set -/

/-- Off its topological support a function has vanishing derivative. -/
theorem fderiv_apply_eq_zero_of_notMem_tsupport {φ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport φ) (i : Fin d) : (fderiv ℝ φ x) (basisVec i) = 0 := by
  have hzero : φ =ᶠ[nhds x] 0 :=
    ((isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hx).mono
      fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [hzero.fderiv_eq]
  simp only [fderiv_zero, Pi.zero_apply, zero_apply]

/-- A global weak-gradient graph restricts to every set: the test functions of
the smaller set are test functions of the ambient space, and both integrands
vanish off their support. -/
theorem hasWeakGradientOn_of_univ {V : Set (Vec d)} {u : Vec d → ℝ}
    {Du : Vec d → Vec d} (h : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn V u Du := by
  intro i φ hφ hφc hφV
  have h1 := h i φ hφ hφc (by simp)
  rw [Measure.restrict_univ] at h1
  have hzero1 : ∀ x ∉ V, u x * (fderiv ℝ φ x) (basisVec i) = 0 := by
    intro x hx
    rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun hmem => hx (hφV hmem)) i,
      mul_zero]
  have hzero2 : ∀ x ∉ V, Du x i * φ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (hφV hmem)), mul_zero]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero1,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero2]
  exact h1

/-- **The zero extension of an `H¹₀(V)` datum, read on an arbitrary set `A`.**

The value and the gradient are the literal zero extensions of `OddReflectionGlue`;
the weak-gradient identity is its global one, restricted. -/
def zeroExtendH1 {V : Set (Vec d)} (hV : MeasurableSet V) (u : H10Function V)
    (A : Set (Vec d)) : H1Function A where
  toFun := zeroExtend V u.toFun
  grad := zeroExtendGrad V u.grad
  memL2 := (memL2_zeroExtend hV u).restrict A
  gradMemL2 := by
    intro i
    have h := gradMemL2_zeroExtendGrad hV u i
    rw [MemLpOn, Measure.restrict_univ] at h
    exact h.restrict A
  hasWeakGradient := hasWeakGradientOn_of_univ (hasWeakGradientOn_univ_zeroExtend hV u)

@[simp] theorem zeroExtendH1_toFun {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).toFun = zeroExtend V u.toFun := rfl

@[simp] theorem zeroExtendH1_grad {V : Set (Vec d)} (hV : MeasurableSet V)
    (u : H10Function V) (A : Set (Vec d)) :
    (zeroExtendH1 hV u A).grad = zeroExtendGrad V u.grad := rfl

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
