/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaI

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Subtracting `c · n` from a solution

If `φ` solves `-∇·(A∇φ) = f` in the cube `Q` then `u = φ - c n` solves
`-∇·(A∇u) = f - ∇·g` with the small forcing `g = -c (A - 1) e` (`r3c_slopeField`), because the
constant field `e` has zero flux against `H¹₀`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3c_matVec_basisVec (M : Mat d) (e i : Fin d) : matVecMul M (basisVec e) i = M i e := by
  simp [matVecMul, basisVec, Pi.single_apply]

theorem r3c_one_apply_e (e i : Fin d) : (1 : Mat d) i e = basisVec e i := by
  simp [Matrix.one_apply, basisVec, Pi.single_apply, eq_comm]

theorem r3c_matVec_sub_smul (M : Mat d) (v w : Vec d) (c : ℝ) :
    matVecMul M (v - c • w) = matVecMul M v - c • matVecMul M w := by
  funext i
  simp only [matVecMul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem r3c_vecDot_sub_left (x y z : Vec d) : vecDot (x - y) z = vecDot x z - vecDot y z := by
  simp [vecDot, sub_mul, Finset.sum_sub_distrib]

/-- `φ - c n` as an `H¹` function on a cube. -/
theorem r3c_exists_sub_nrm (Q : TriadicCube d) (e : Fin d) (m : ℤ) (c : ℝ)
    (φ : H1Function (openCubeSet Q)) :
    ∃ u : H1Function (openCubeSet Q), (∀ x, u.toFun x = φ.toFun x - c * r3c_nrm e m x) ∧
      ∀ x, u.grad x = φ.grad x - c • basisVec e := by
  have hconv := r3c_isOpenBoundedConvex_cube Q
  let nH : H1Function (openCubeSet Q) := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hconv
    (f := r3c_nrm e m) ((contDiff_r3c_nrm e m).of_le (by simp))
  refine ⟨φ - c • nH, fun x => ?_, fun x => ?_⟩
  · rw [H1Function.sub_toFun]
    simp only [H1Function.smul_toFun]
    rfl
  · rw [H1Function.sub_grad]
    simp only [H1Function.smul_grad]
    funext i
    show φ.grad x i - c * fderiv ℝ (r3c_nrm e m) x (basisVec i) = φ.grad x i - (c • basisVec e) i
    rw [(hasFDerivAt_r3c_nrm e m x).fderiv]
    simp [basisVec, Pi.single_apply]
    by_cases h : e = i <;> simp [h, eq_comm]

/-- **Equation for `φ - c n`.** -/
theorem r3c_slope_equation (Q : TriadicCube d) (e : Fin d) {A : CoeffField d} {MA : ℝ}
    (hAs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (hAb : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j| ≤ MA) (c : ℝ) {f : Vec d → ℝ}
    {φ : H1Function (openCubeSet Q)}
    (hφ : IsWeakSolutionOn A (openCubeSet Q) φ f (fun _ => 0))
    {u : H1Function (openCubeSet Q)}
    (hu2 : ∀ x, u.grad x = φ.grad x - c • basisVec e) :
    IsWeakSolutionOn A (openCubeSet Q) u f (r3c_slopeField A e c) := by
  intro ψ
  have hconv := r3c_isOpenBoundedConvex_cube Q
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := hconv.isFiniteMeasure_restrict_volume
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    simpa [volumeMeasureOn] using hfin
  have hUm : MeasurableSet (openCubeSet Q) := (isOpen_openCubeSet Q).measurableSet
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet Q)) :=
    fun i j => (hAs i j).continuous.aestronglyMeasurable
  have hψg : ∀ i, MemLp (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict (openCubeSet Q)) :=
    fun i => ψ.toH1Function.grad_memL2 i
  have hφg : ∀ i, MemLp (fun x => φ.grad x i) 2 (volume.restrict (openCubeSet Q)) :=
    fun i => φ.grad_memL2 i
  have hνc : ∀ i, MemLp (fun _ : Vec d => (basisVec e : Vec d) i) 2 (volume.restrict (openCubeSet Q)) :=
    fun i => memLp_const _
  have hAν : ∀ i, MemLp (fun x => matVecMul (A x) (basisVec e) i) 2
      (volume.restrict (openCubeSet Q)) := fun i =>
    r3c_memLp_matVec hUm hAm hAb hνc i
  have hAφ : ∀ i, MemLp (fun x => matVecMul (A x) (φ.grad x) i) 2 (volume.restrict (openCubeSet Q)) :=
    fun i => r3c_memLp_matVec hUm hAm hAb hφg i
  have i1 := r3c_integrable_vecDot hAν hψg
  have i2 := r3c_integrable_vecDot hAφ hψg
  have i3 : Integrable (fun x => vecDot (basisVec e : Vec d) (ψ.toH1Function.grad x))
      (volume.restrict (openCubeSet Q)) := r3c_integrable_vecDot hνc hψg
  have h0 := hφ ψ
  simp only [vecDot_zero_left, integral_zero, add_zero] at h0
  have hz := integral_vecDot_const_zeroTraceGrad_eq_zero ψ (basisVec e : Vec d)
  -- pointwise rewriting of the integrand
  have hpt : ∀ x, vecDot (matVecMul (A x) (u.grad x)) (ψ.toH1Function.grad x) =
      vecDot (matVecMul (A x) (φ.grad x)) (ψ.toH1Function.grad x) -
        c * vecDot (matVecMul (A x) (basisVec e)) (ψ.toH1Function.grad x) := by
    intro x
    rw [hu2 x, r3c_matVec_sub_smul, r3c_vecDot_sub_left, p12_vecDot_smul_left]
  have hpt2 : ∀ x, vecDot (r3c_slopeField A e c x) (ψ.toH1Function.grad x) =
      -c * vecDot (matVecMul (A x) (basisVec e)) (ψ.toH1Function.grad x) +
        c * vecDot (basisVec e : Vec d) (ψ.toH1Function.grad x) := by
    intro x
    simp only [vecDot, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [r3c_matVec_basisVec, r3c_slopeField, r3c_one_apply_e]
    ring
  simp_rw [hpt, hpt2]
  rw [integral_sub i2 (i1.const_mul c), integral_add (i1.const_mul (-c)) (i3.const_mul c),
    integral_const_mul, integral_const_mul, integral_const_mul, h0, hz]
  ring

end SuperdiffusionCLT.Section7
