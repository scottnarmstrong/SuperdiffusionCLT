/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Iteration
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Truncation
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# Level identity for the zero extension of an `H¹₀(U)` solution

For `w ∈ H¹₀(U)` with `U` open of finite volume, `k ≥ 0` and a smooth compactly supported cutoff
`η`, the function `η² (w-k)₊` lies in `H¹₀(U)` (no regularity of `∂U` is used), with gradient
`levelTest w k η`.  Tested against the weak form on `U`, and transported to a cube `Q` containing
`tsupport η` through the zero extension, this gives the level identity of the zero extension.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- The zero extension of `w ∈ H¹₀(U)` to an open set `Q`, as an `H¹(Q)` function. -/
noncomputable def zeroExtCube (hU : IsOpen U) {Q : Set (Vec d)} (hQ : IsOpen Q)
    (w : H10Function U) : H1Function Q :=
  (w.extendByZeroToOpenSuperset hU.measurableSet (hU.union hQ)
    Set.subset_union_left).toH1Function.restrict hQ Set.subset_union_right

theorem zeroExtCube_toFun (hU : IsOpen U) {Q : Set (Vec d)} (hQ : IsOpen Q) (w : H10Function U) :
    (zeroExtCube hU hQ w).toFun = U.indicator w.toH1Function.toFun := rfl

theorem zeroExtCube_grad (hU : IsOpen U) {Q : Set (Vec d)} (hQ : IsOpen Q) (w : H10Function U) :
    (zeroExtCube hU hQ w).grad = U.indicator w.toH1Function.grad := rfl

theorem levelTest_congr {V : Set (Vec d)} {u : H1Function U} {v : H1Function V} {k : ℝ}
    {η : Vec d → ℝ} {x : Vec d} (hf : u.toFun x = v.toFun x) (hg : u.grad x = v.grad x) :
    levelTest u k η x = levelTest v k η x := by
  unfold levelTest
  by_cases h : k < u.toFun x
  · have h' : k < v.toFun x := hf ▸ h
    simp only [Set.indicator_of_mem (show x ∈ {y | k < u.toFun y} from h),
      Set.indicator_of_mem (show x ∈ {y | k < v.toFun y} from h'), hf, hg]
  · have h' : ¬ k < v.toFun x := hf ▸ h
    simp only [Set.indicator_of_notMem (show x ∉ {y | k < u.toFun y} from h),
      Set.indicator_of_notMem (show x ∉ {y | k < v.toFun y} from h'), hf]

theorem levelTest_eq_zero_of_notMem {V : Set (Vec d)} (u : H1Function V) (k : ℝ) {η : Vec d → ℝ}
    {x : Vec d} (hx : x ∉ tsupport η) : levelTest u k η x = 0 := by
  have h0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
  unfold levelTest
  simp [h0, cutoffGrad_eq_zero hx]

/-- **The `H¹₀(U)` test function `η² (w-k)₊`.** -/
theorem exists_levelTest_h10 (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : H10Function U) {k : ℝ}
    (hk : 0 ≤ k) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∃ φ : H10Function U,
      (∀ x, φ.toH1Function.toFun x = η x ^ 2 * max (w.toH1Function.toFun x - k) 0) ∧
      ∀ᵐ x ∂(volume.restrict U), φ.toH1Function.grad x = levelTest w.toH1Function k η x := by
  classical
  have hη2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => η x * η x) := hη.mul hη
  have hc2 : HasCompactSupport (fun x => η x * η x) := hηc.mul_right
  obtain ⟨v, hv⟩ := memH10_positivePart hU hfin w hk
  have hvx : ∀ x, v.toH1Function.toFun x = max (w.toH1Function.toFun x - k) 0 :=
    fun x => congrFun hv x
  refine ⟨v.mulContDiffHasCompactSupport hη2 hc2, ?_, ?_⟩
  · intro x
    rw [H10Function.mulContDiffHasCompactSupport_toFun]
    show η x * η x * v.toH1Function.toFun x = _
    rw [hvx]
    ring
  · have hgr : (v.mulContDiffHasCompactSupport hη2 hc2).toH1Function.grad =
        fun x i => η x * η x * v.toH1Function.grad x i +
          v.toH1Function.toFun x * (fderiv ℝ (fun x => η x * η x) x) (basisVec i) :=
      H1Function.mulContDiffHasCompactSupport_grad v.toH1Function hη2 hc2
    have hall : ∀ᵐ x ∂(volume.restrict U), ∀ i,
        v.toH1Function.grad x i = posPartGrad w.toH1Function k x i :=
      ae_all_iff.2 fun i => gradCoord_ae_eq_of_toFun_eq hU v.toH1Function
        (positivePartOpen hU w.toH1Function k
          (memL2On_positivePart_of_nonneg w.toH1Function hk)) hv i
    filter_upwards [hall] with x hx
    rw [hgr]
    funext i
    have hd : (fderiv ℝ (fun x => η x * η x) x) (basisVec i) =
        2 * η x * cutoffGrad η x i := by
      have h1 : HasFDerivAt (fun x => η x * η x)
          (η x • fderiv ℝ η x + η x • fderiv ℝ η x) x :=
        ((hη.differentiable (by simp)) x).hasFDerivAt.mul
          ((hη.differentiable (by simp)) x).hasFDerivAt
      rw [h1.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        cutoffGrad]
      ring
    show η x * η x * v.toH1Function.grad x i +
      v.toH1Function.toFun x * (fderiv ℝ (fun x => η x * η x) x) (basisVec i) = _
    rw [hd, hx i, hvx]
    unfold levelTest posPartGrad
    by_cases hlt : k < w.toH1Function.toFun x
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Set.indicator_of_mem (show x ∈ {y | k < w.toH1Function.toFun y} from hlt)]
      ring
    · have hm : max (w.toH1Function.toFun x - k) 0 = 0 :=
        max_eq_right (by linarith only [not_lt.mp hlt])
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Set.indicator_of_notMem (show x ∉ {y | k < w.toH1Function.toFun y} from hlt), hm]
      simp

end SuperdiffusionCLT.Section7
