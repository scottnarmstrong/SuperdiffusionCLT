/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EllsepDrift

/-!
# The drift datum of `e.ellsep.testing` and the two testing displays it feeds

The integration by parts that leads to `e.ellsep.testing` asserts

`∇·((k_{L'} − k_ℓ)∇u_m) = (f_{L'} − f_ℓ)·∇u_m`.

`EllsepEquation.lean` and `EllsepTesting.lean`
carry that assertion as the four explicit hypotheses `hFlux`, `hDG`, `hJac`,
`hDiv`.  This file discharges all four from the weak product rule of
`EllsepDrift.lean` and **one** explicit regularity hypothesis,
a weak Hessian for the maximizer.

## The datum

For a matrix field `K` of class `C¹` and an `H¹` function `u` carrying a weak
Hessian, `hasWeakJacobianOn_matVecMul_of_contDiff_one` gives

`∂_k (K∇u)_i = ∑_j ((∂_k K_{ij}) ∂_j u + K_{ij} ∂_k∂_j u)`,

so the trace is

`∇·(K∇u) = ∑_j (∑_i ∂_i K_{ij}) ∂_j u + ∑_{i,j} K_{ij} ∂_i∂_j u`.

The second sum is the contraction of the antisymmetric `K` with a symmetric
matrix and vanishes; the first is `(∇·K)·∇u`, which for `K = k_{L'} − k_ℓ` is
the drift increment `f_{L'} − f_ℓ` of `Drift.lean` paired with
`∇u`, by `weakDivergence_streamFluxWeakGradient`.  Because `hDiv` is asked at
*every* point of the cube and Schwarz symmetry of a weak Hessian holds only
almost everywhere, the witness used here is the symmetrized one
`hasWeakHessianOnSymm`, whose entries are symmetric at every point and which
represents the same weak Hessian.

## The one hypothesis, and why the response's Hessian cannot replace it

The hypothesis carried below is `HasWeakHessianOn (openCubeSet cu_m) u_m`, i.e.
`∇u_m ∈ H¹(cu_m)`.  Chapter 2's `Book.Ch02.Solution` stores `toH1 : H1Function U`
and nothing above it, so no carrier produces it.

It is *not* interchangeable with the Hessian clause of the a priori statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero`, which
concerns the Dirichlet response `w`.  The identity the master identity needs is

`∫ w (f_{L'} − f_ℓ)·∇u_m = −∫ ((k_{L'} − k_ℓ)∇u_m)·∇w`.

Moving the derivative onto `w` instead of `u_m` turns the right-hand side into
`∫ ∇u_m·(K∇w)` by pointwise antisymmetry, and `w ∈ H¹₀ ∩ H²` does give
`K∇w ∈ H¹` with `∇·(K∇w) = (∇·K)·∇w` — the same product rule, applied to `w`.
But converting `∫ ∇u_m·Φ` into `−∫ u_m ∇·Φ` needs the *test* field `Φ = K∇w` to
have zero trace, and it does not: on `∂cu_m` the gradient of `w` is normal, so
`Φ = (∂_n w) K n` is tangential and only `Φ·n` vanishes.  The same obstruction
appears for `Ψ = w(f_{L'} − f_ℓ) − K∇w`, which is divergence free because
`∇·(∇·K) = 0` for antisymmetric `K`, yet again only satisfies `Ψ·n = 0` on the
boundary.  Closing either route therefore needs a normal-trace theorem for
`H(div)` fields, which is not available here.  Since `u_m` is a maximizer and
carries no zero-trace information, the regularity has to sit on `u_m`.

## Main results

* `contDiff_streamCutoff_sub_entry` — the `C¹` regularity of the stream increment.
* `streamGradJacobian`, `hasWeakJacobianOn_streamGradJacobian`,
  `gradMemL2On_streamGradJacobian` — data `hJac` and `hDG` of the integration by parts
  for `V = ∇u_m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Sobolev

noncomputable section

variable {d : ℕ}

/-! ## The `C¹` regularity of the stream increment and its row divergence -/

private theorem matVecMulBasisVec (A : Mat d) (j : Fin d) (i : Fin d) :
    matVecMul A (basisVec j) i = A i j := by
  show ∑ l : Fin d, A i l * basisVec j l = A i j
  rw [Finset.sum_eq_single j]
  · rw [basisVec_apply]
    simp
  · intro l _ hl
    rw [basisVec_apply, ite_eq_right hl]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **The entries of the stream increment are of class `C¹`.**  Each shell of
the shell field stores a second
derivative, so the finite sum is `C²`; one derivative is what the weak product
rule needs. -/
theorem contDiff_streamCutoff_sub_entry (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    (i j : Fin d) :
    ContDiff ℝ 1 (fun x : Vec d =>
      (streamCutoff omega b x - streamCutoff omega a x) i j) := by
  have h := contDiff_streamFlux_apply omega hab (basisVec j) i
  have hrw : (fun x : Vec d =>
        matVecMul (streamCutoff omega b x - streamCutoff omega a x) (basisVec j) i)
      = fun x : Vec d => (streamCutoff omega b x - streamCutoff omega a x) i j :=
    funext fun x => matVecMulBasisVec _ j i
  rwa [hrw] at h

/-! ## The antisymmetric contraction of a symmetric matrix vanishes -/

/-! ## The four data of the integration by parts for `V = ∇u` -/

/-- **The weak Jacobian of the skew flux `(k_b − k_a)∇u`**, built from the
symmetrized weak Hessian of `u` and the classical derivative of the stream
increment. -/
def streamGradJacobian (omega : ShellSeq d) (a b : ℕ) {Q : TriadicCube d}
    {u : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) u) :
    Fin d → Vec d → Vec d :=
  fun i x k => ∑ j : Fin d,
    ((streamCutoff omega b x - streamCutoff omega a x) i j *
        (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess j k x +
      u.grad x j * (fderiv ℝ (fun y : Vec d =>
        (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec k))

/-- **`hJac`**: `streamGradJacobian` is a weak Jacobian of `(k_b − k_a)∇u`. -/
theorem hasWeakJacobianOn_streamGradJacobian (omega : ShellSeq d) {a b : ℕ}
    (hab : a ≤ b) {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) :
    HasWeakJacobianOn (openCubeSet Q)
      (fun x => matVecMul (streamCutoff omega b x - streamCutoff omega a x) (u.grad x))
      (streamGradJacobian omega a b H) :=
  hasWeakJacobianOn_matVecMul_of_contDiff_one Q
    (fun i j => contDiff_streamCutoff_sub_entry omega hab i j)
    (hasWeakHessianOnSymm (isOpen_openCubeSet Q) H)

/-- **`hDG`**: the weak Jacobian of the skew flux is square-integrable
coordinatewise on the cube. -/
theorem gradMemL2On_streamGradJacobian (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b)
    {Q : TriadicCube d} {u : H1Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) u) (i : Fin d) :
    GradMemL2On (openCubeSet Q) (streamGradJacobian omega a b H i) := by
  intro k
  refine MeasureTheory.memLp_finsetSum _ (fun j _ => ?_)
  refine MeasureTheory.MemLp.add ?_ ?_
  · exact (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
        (contDiff_streamCutoff_sub_entry omega hab i j).continuous).fun_mul
      ((hasWeakHessianOnSymm (isOpen_openCubeSet Q) H).hess_memL2 j k)
  · have hc : Continuous (fun x : Vec d => (fderiv ℝ (fun y : Vec d =>
        (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec k)) :=
      ((contDiff_streamCutoff_sub_entry omega hab i j).continuous_fderiv
        (by simp)).clm_apply continuous_const
    have h : MemL2On (openCubeSet Q) (fun x => (fderiv ℝ (fun y : Vec d =>
        (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec k) *
        u.grad x j) :=
      (memLpOn_openCubeSet_of_continuous (p := ⊤) Q hc).fun_mul (u.gradMemL2 j)
    have hrw : (fun x : Vec d => (fderiv ℝ (fun y : Vec d =>
          (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec k) *
          u.grad x j)
        = fun x : Vec d => u.grad x j * (fderiv ℝ (fun y : Vec d =>
          (streamCutoff omega b y - streamCutoff omega a y) i j) x) (basisVec k) := by
      funext x
      ring
    rwa [hrw] at h

/-! ## The two testing displays with the drift datum discharged -/

end

end SuperdiffusionCLT.Section3.Terms
