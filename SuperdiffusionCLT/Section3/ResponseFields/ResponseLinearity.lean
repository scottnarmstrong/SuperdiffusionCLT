/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.Definitions

/-!
# Linearity of the two cube responses, and the linear function `c·x`

The proof of `l.LHS.term1` uses two structural facts about the two problems of
`e.abstract.response.equations` that the weak formulations give at once.

* **Linearity in the flux**: with
  `w_r = w_{D, j_r p}^{(m)}` and `w̃_r = w_{N, j_r p}^{(m)}` the responses of the
  single shell fluxes, the responses of `F = Σ_r j_r p` are `Σ_r w_r` and
  `Σ_r w̃_r`.  Both weak formulations are linear identities in `F` and in the
  solution, so a sum of responses is a response of the sum.
* **The constant shift**: for `r ≥ m` the print replaces
  `w̃_r` by `ṽ_r = w̃_r + (j_r p)_{cu_m}·x`, which is the Neumann response of
  the centered flux `j_r p − (j_r p)_{cu_m}`.  Adding the linear function
  `c·x` changes exactly the constant normal flux: its gradient is the constant
  `c`, so the Neumann weak form of `F` becomes the Neumann weak form of
  `F − c`.  For the Dirichlet problem the same replacement changes nothing,
  because a constant tested against a zero-trace gradient integrates to zero;
  that half is `isCubeDirichletResponse_sub_const`.

The linear function itself is packaged here as an `H¹` carrier on the open
cube: `x ↦ c·x` is smooth with constant gradient `c`, and the cube is a
bounded open convex domain, so `H1Function.ofContDiffOnIsOpenBoundedConvexDomain`
applies.  Its mean-zero normalization `H1Function.toMeanZero` subtracts the
cube average and keeps the gradient, which is the print's `(ṽ_r)_{cu_m} = 0`
without using that the cube is centered.

`H1MeanZeroFunction U` is an upstream `AddCommGroup`, so the Neumann finite sum
is the ordinary `Finset.sum`.  `H10Function U` carries `Zero`, `Add`, `Neg` and
`Sub` but no `AddCommMonoid` instance, so the Dirichlet finite sum is built
here by recursion along `Finset.toList`.

The two-term subtraction statements for the Dirichlet and Neumann responses also occur in
`SuperdiffusionCLT/Sobolev/ResponseHalfInterpolation.lean`; that module
imports `Section3/ResponseFields/LpEstimates.lean` and so sits above this one
in the import order.  They are restated here so that the additive family and
its finite-sum extension live in the namespace of the two predicates.

## Main results

* `linearH1Function`, `linearH1MeanZeroFunction`: the carrier `x ↦ c·x` and its
  mean-zero normalization, with the constant gradient `c`.
* `isCubeDirichletResponse_add`, `_sub`, `_smul`, `isCubeNeumannResponse_add`,
  `_sub`, `_smul`: linearity of the two responses in the flux.
* `h10FinsetSum`, `isCubeDirichletResponse_finsetSum`,
  `isCubeNeumannResponse_finsetSum`: the finite-sum form used in the
  proof of `l.LHS.term1`.
* `isCubeNeumannResponse_sub_const`: the Neumann half of `#centered-flux-responses`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.ResponseFields

open MeasureTheory
open Homogenization
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The linear function `c·x` as an `H¹` carrier -/

/-- The pairing with a fixed vector as a continuous linear functional on
`Vec d`. -/
def vecDotCLM (c : Vec d) : (Vec d) →L[ℝ] ℝ :=
  ∑ i, (c i) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i)

@[simp] theorem vecDotCLM_apply (c x : Vec d) : vecDotCLM c x = vecDot c x := by
  simp [vecDotCLM, vecDot]

theorem contDiff_vecDot (c : Vec d) :
    ContDiff ℝ 1 (fun x : Vec d => vecDot c x) := by
  have h : (fun x : Vec d => vecDot c x) = fun x => vecDotCLM c x := by
    funext x
    rw [vecDotCLM_apply]
  rw [h]
  exact (vecDotCLM c).contDiff.of_le le_top

/-- The partial derivatives of `x ↦ c·x` are the coordinates of `c`. -/
theorem fderiv_vecDot_basisVec (c : Vec d) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (fun y : Vec d => vecDot c y) x) (basisVec i) = c i := by
  have h : (fun y : Vec d => vecDot c y) = fun y => vecDotCLM c y := by
    funext y
    rw [vecDotCLM_apply]
  rw [h, (vecDotCLM c).fderiv]
  simp [vecDotCLM, basisVec_apply]

/-- **The linear function `c·x` on the open cube**, the carrier of the print's
`(j_r p)_{cu_m}·x`.  Its weak gradient is the constant `c`. -/
def linearH1Function (Q : TriadicCube d) (c : Vec d) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (isOpenBoundedConvexDomain_openCubeSet Q) (contDiff_vecDot c)

@[simp] theorem linearH1Function_toFun (Q : TriadicCube d) (c : Vec d) :
    (linearH1Function Q c).toFun = fun x => vecDot c x :=
  rfl

@[simp] theorem linearH1Function_grad (Q : TriadicCube d) (c : Vec d) (x : Vec d) :
    (linearH1Function Q c).grad x = c := by
  funext i
  exact fderiv_vecDot_basisVec c x i

/-- **The mean-zero normalization of `c·x` on the open cube.**  Subtracting the
cube average does not change the gradient, so this is the print's `ṽ_r` summand
with `(ṽ_r)_{cu_m} = 0` supplied by the carrier rather than by the cube being
centered. -/
def linearH1MeanZeroFunction (Q : TriadicCube d) (c : Vec d) :
    H1MeanZeroFunction (openCubeSet Q) :=
  (linearH1Function Q c).toMeanZero

@[simp] theorem linearH1MeanZeroFunction_grad (Q : TriadicCube d) (c : Vec d)
    (x : Vec d) :
    (linearH1MeanZeroFunction Q c).toH1Function.grad x = c := by
  rw [linearH1MeanZeroFunction, H1Function.toMeanZero_grad,
    linearH1Function_grad]

/-- The gradient of `w + c·x`: the print's `∇ṽ_r = ∇w̃_r + (j_r p)_{cu_m}`. -/
theorem add_linearH1MeanZeroFunction_grad {Q : TriadicCube d}
    (w : H1MeanZeroFunction (openCubeSet Q)) (c : Vec d) (x : Vec d) :
    (w + linearH1MeanZeroFunction Q c).toH1Function.grad x =
      w.toH1Function.grad x + c := by
  show (w.toH1Function + (linearH1MeanZeroFunction Q c).toH1Function).grad x =
    w.toH1Function.grad x + c
  rw [H1Function.add_grad]
  show w.toH1Function.grad x + (linearH1MeanZeroFunction Q c).toH1Function.grad x = _
  rw [linearH1MeanZeroFunction_grad]

/-! ## Linearity of the two responses in the flux -/

private theorem setIntegral_vecDot_add {Q : TriadicCube d} {F G psi : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hpsi : MemVectorL2 (openCubeSet Q) psi) :
    ∫ x in openCubeSet Q, vecDot (F x + G x) (psi x) =
      (∫ x in openCubeSet Q, vecDot (F x) (psi x)) +
        ∫ x in openCubeSet Q, vecDot (G x) (psi x) := by
  rw [← integral_add (integrableOn_vecDot_of_memVectorL2 hF hpsi)
    (integrableOn_vecDot_of_memVectorL2 hG hpsi)]
  refine setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => ?_)
  simp only [vecDot, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem setIntegral_vecDot_sub' {Q : TriadicCube d} {F G psi : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hpsi : MemVectorL2 (openCubeSet Q) psi) :
    ∫ x in openCubeSet Q, vecDot (F x - G x) (psi x) =
      (∫ x in openCubeSet Q, vecDot (F x) (psi x)) -
        ∫ x in openCubeSet Q, vecDot (G x) (psi x) := by
  rw [← integral_sub (integrableOn_vecDot_of_memVectorL2 hF hpsi)
    (integrableOn_vecDot_of_memVectorL2 hG hpsi)]
  refine setIntegral_congr_fun (measurableSet_openCubeSet Q) (fun x _ => ?_)
  simp only [vecDot, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Additivity of the Dirichlet response in the flux**: the sum of
the responses of two `L̲²` fluxes is a response of the sum. -/
theorem isCubeDirichletResponse_add {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    {u v : H10Function (openCubeSet Q)}
    (hu : IsCubeDirichletResponse Q F u) (hv : IsCubeDirichletResponse Q G v) :
    IsCubeDirichletResponse Q (fun x => F x + G x) (u + v) := by
  intro φ
  have hgrad : (u + v).toH1Function.grad =
      fun x => u.toH1Function.grad x + v.toH1Function.grad x := by
    rw [show (u + v).toH1Function = u.toH1Function + v.toH1Function from rfl]
    exact H1Function.add_grad _ _
  rw [hgrad,
    setIntegral_vecDot_add u.toH1Function.grad_memVectorL2
      v.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2,
    setIntegral_vecDot_add hF hG φ.toH1Function.grad_memVectorL2, hu φ, hv φ]
  ring

/-- **Additivity of the prescribed-flux Neumann response in the flux**. -/
theorem isCubeNeumannResponse_add {Q : TriadicCube d} {F G : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    {u v : H1MeanZeroFunction (openCubeSet Q)}
    (hu : IsCubeNeumannResponse Q F u) (hv : IsCubeNeumannResponse Q G v) :
    IsCubeNeumannResponse Q (fun x => F x + G x) (u + v) := by
  intro φ
  have hgrad : (u + v).toH1Function.grad =
      fun x => u.toH1Function.grad x + v.toH1Function.grad x := by
    rw [show (u + v).toH1Function = u.toH1Function + v.toH1Function from rfl]
    exact H1Function.add_grad _ _
  rw [hgrad,
    setIntegral_vecDot_add u.toH1Function.grad_memVectorL2
      v.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2,
    setIntegral_vecDot_add hF hG φ.toH1Function.grad_memVectorL2, hu φ, hv φ]
  ring

/-! ## Finite sums of responses -/

/-- Square integrability of a finite sum of fluxes along a list. -/
theorem memVectorL2_listSum {ι : Type*} {Q : TriadicCube d} {F : ι → Vec d → Vec d}
    (l : List ι) (hF : ∀ r ∈ l, MemVectorL2 (openCubeSet Q) (F r)) :
    MemVectorL2 (openCubeSet Q) (fun x => (l.map fun r => F r x).sum) := by
  induction l with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact MemLp.zero (μ := volumeMeasureOn (openCubeSet Q)) (p := 2)
        (ε := Vec d)
  | cons a t ih =>
      have ha : MemVectorL2 (openCubeSet Q) (F a) := hF a (List.mem_cons_self ..)
      have ht := ih fun r hr => hF r (List.mem_cons_of_mem a hr)
      simp only [List.map_cons, List.sum_cons]
      exact ha.add ht

/-- Square integrability of a finite sum of fluxes over a `Finset`. -/
theorem memVectorL2_finsetSum {ι : Type*} {Q : TriadicCube d} {F : ι → Vec d → Vec d}
    (s : Finset ι) (hF : ∀ r ∈ s, MemVectorL2 (openCubeSet Q) (F r)) :
    MemVectorL2 (openCubeSet Q) (fun x => ∑ r ∈ s, F r x) := by
  have hrw : (fun x => ∑ r ∈ s, F r x) =
      fun x => (s.toList.map fun r => F r x).sum := by
    funext x
    rw [Finset.sum_map_toList]
  rw [hrw]
  exact memVectorL2_listSum s.toList fun r hr => hF r (Finset.mem_toList.1 hr)

/-- **The finite sum of `H¹₀` functions along a list.**  `H10Function U` carries
`Zero` and `Add` upstream but no `AddCommMonoid` instance, so the finite sum is
built by recursion. -/
def h10ListSum {ι : Type*} {U : Set (Vec d)} (w : ι → H10Function U) :
    List ι → H10Function U
  | [] => 0
  | r :: t => w r + h10ListSum w t

/-- **The finite sum of `H¹₀` functions over a `Finset`**, the print's
`Σ_{r} w_r`. -/
def h10FinsetSum {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (w : ι → H10Function U) : H10Function U :=
  h10ListSum w s.toList

theorem h10ListSum_grad {ι : Type*} {U : Set (Vec d)} (w : ι → H10Function U)
    (l : List ι) (x : Vec d) :
    (h10ListSum w l).toH1Function.grad x =
      (l.map fun r => (w r).toH1Function.grad x).sum := by
  induction l with
  | nil =>
      show (0 : H1Function U).grad x = _
      simp
  | cons a t ih =>
      show ((w a).toH1Function + (h10ListSum w t).toH1Function).grad x = _
      rw [H1Function.add_grad]
      show (w a).toH1Function.grad x + (h10ListSum w t).toH1Function.grad x = _
      rw [ih, List.map_cons, List.sum_cons]

theorem h10FinsetSum_grad {ι : Type*} {U : Set (Vec d)} (s : Finset ι)
    (w : ι → H10Function U) (x : Vec d) :
    (h10FinsetSum s w).toH1Function.grad x =
      ∑ r ∈ s, (w r).toH1Function.grad x := by
  rw [h10FinsetSum, h10ListSum_grad, Finset.sum_map_toList]

theorem h1MeanZeroFinsetSum_grad {ι : Type*} {Q : TriadicCube d} (s : Finset ι)
    (w : ι → H1MeanZeroFunction (openCubeSet Q)) (x : Vec d) :
    (∑ r ∈ s, w r).toH1Function.grad x =
      ∑ r ∈ s, (w r).toH1Function.grad x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      show (0 : H1Function (openCubeSet Q)).grad x = _
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      show ((w a).toH1Function + (∑ r ∈ s, w r).toH1Function).grad x = _
      rw [H1Function.add_grad]
      show (w a).toH1Function.grad x + (∑ r ∈ s, w r).toH1Function.grad x = _
      rw [ih]

/-- The zero field has the zero Dirichlet response. -/
theorem isCubeDirichletResponse_zero (Q : TriadicCube d) :
    IsCubeDirichletResponse Q (fun _ => (0 : Vec d)) 0 := by
  intro φ
  show ∫ x in openCubeSet Q,
      vecDot ((0 : H1Function (openCubeSet Q)).grad x) (φ.toH1Function.grad x) = _
  simp [vecDot]

/-- The zero field has the zero prescribed-flux Neumann response. -/
theorem isCubeNeumannResponse_zero (Q : TriadicCube d) :
    IsCubeNeumannResponse Q (fun _ => (0 : Vec d)) 0 := by
  intro φ
  show ∫ x in openCubeSet Q,
      vecDot ((0 : H1Function (openCubeSet Q)).grad x) (φ.toH1Function.grad x) = _
  simp [vecDot]

theorem isCubeDirichletResponse_h10ListSum {ι : Type*} {Q : TriadicCube d}
    {F : ι → Vec d → Vec d} {w : ι → H10Function (openCubeSet Q)} (l : List ι)
    (hF : ∀ r ∈ l, MemVectorL2 (openCubeSet Q) (F r))
    (hw : ∀ r ∈ l, IsCubeDirichletResponse Q (F r) (w r)) :
    IsCubeDirichletResponse Q (fun x => (l.map fun r => F r x).sum)
      (h10ListSum w l) := by
  induction l with
  | nil => exact isCubeDirichletResponse_zero Q
  | cons a t ih =>
      have ha : MemVectorL2 (openCubeSet Q) (F a) := hF a (List.mem_cons_self ..)
      have hrest := ih (fun r hr => hF r (List.mem_cons_of_mem a hr))
        (fun r hr => hw r (List.mem_cons_of_mem a hr))
      exact isCubeDirichletResponse_add ha
        (memVectorL2_listSum t fun r hr => hF r (List.mem_cons_of_mem a hr))
        (hw a (List.mem_cons_self ..)) hrest

/-- **Linearity of the Dirichlet response in the flux, in finite-sum form**:
`w = Σ_r w_r` solves the Dirichlet problem for `F = Σ_r F_r`. -/
theorem isCubeDirichletResponse_finsetSum {ι : Type*} {Q : TriadicCube d}
    {F : ι → Vec d → Vec d} {w : ι → H10Function (openCubeSet Q)} (s : Finset ι)
    (hF : ∀ r ∈ s, MemVectorL2 (openCubeSet Q) (F r))
    (hw : ∀ r ∈ s, IsCubeDirichletResponse Q (F r) (w r)) :
    IsCubeDirichletResponse Q (fun x => ∑ r ∈ s, F r x) (h10FinsetSum s w) := by
  have hrw : (fun x => ∑ r ∈ s, F r x) =
      fun x => (s.toList.map fun r => F r x).sum := by
    funext x
    rw [Finset.sum_map_toList]
  rw [hrw, h10FinsetSum]
  exact isCubeDirichletResponse_h10ListSum s.toList
    (fun r hr => hF r (Finset.mem_toList.1 hr))
    (fun r hr => hw r (Finset.mem_toList.1 hr))

/-- **Linearity of the prescribed-flux Neumann response in the flux, in
finite-sum form**: `w̃ = Σ_r w̃_r` solves the Neumann problem for
`F = Σ_r F_r`.  `H1MeanZeroFunction` is an upstream `AddCommGroup`, so the sum
is the ordinary `Finset.sum`. -/
theorem isCubeNeumannResponse_finsetSum {ι : Type*} {Q : TriadicCube d}
    {F : ι → Vec d → Vec d} {w : ι → H1MeanZeroFunction (openCubeSet Q)}
    (s : Finset ι) (hF : ∀ r ∈ s, MemVectorL2 (openCubeSet Q) (F r))
    (hw : ∀ r ∈ s, IsCubeNeumannResponse Q (F r) (w r)) :
    IsCubeNeumannResponse Q (fun x => ∑ r ∈ s, F r x) (∑ r ∈ s, w r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact isCubeNeumannResponse_zero Q
  | insert a s ha ih =>
      have hFa : MemVectorL2 (openCubeSet Q) (F a) :=
        hF a (Finset.mem_insert_self a s)
      have hFs : ∀ r ∈ s, MemVectorL2 (openCubeSet Q) (F r) :=
        fun r hr => hF r (Finset.mem_insert_of_mem hr)
      have hws : ∀ r ∈ s, IsCubeNeumannResponse Q (F r) (w r) :=
        fun r hr => hw r (Finset.mem_insert_of_mem hr)
      have hrest := ih hFs hws
      have hstep := isCubeNeumannResponse_add hFa (memVectorL2_finsetSum s hFs)
        (hw a (Finset.mem_insert_self a s)) hrest
      have hfun : (fun x => F a x + ∑ r ∈ s, F r x) =
          fun x => ∑ r ∈ insert a s, F r x := by
        funext x
        rw [Finset.sum_insert ha]
      rw [hfun] at hstep
      rw [Finset.sum_insert ha]
      exact hstep

/-! ## The constant shift of the flux -/

/-- **The Neumann half of `#centered-flux-responses`**.
Adding the linear function `c·x` to the prescribed-flux Neumann response of `F`
gives the prescribed-flux Neumann response of `F − c`: the gradient of `c·x` is
the constant `c`, so the enlarged test class sees exactly the constant normal
flux that the shift produces.

This is the print's `ṽ_r = w̃_r + (j_r p)_{cu_m}·x` at `c = (j_r p)_{cu_m}`;
the Dirichlet half, where the same replacement changes nothing, is
`isCubeDirichletResponse_sub_const`. -/
theorem isCubeNeumannResponse_sub_const {Q : TriadicCube d} {F : Vec d → Vec d}
    {wN : H1MeanZeroFunction (openCubeSet Q)}
    (hF : MemVectorL2 (openCubeSet Q) F)
    (h : IsCubeNeumannResponse Q F wN) (c : Vec d) :
    IsCubeNeumannResponse Q (fun x => F x - c)
      (wN + linearH1MeanZeroFunction Q c) := by
  intro φ
  have hcL2 : MemVectorL2 (openCubeSet Q) (fun _ : Vec d => c) :=
    memVectorL2_const c
  have hgrad : (wN + linearH1MeanZeroFunction Q c).toH1Function.grad =
      fun x => wN.toH1Function.grad x + c :=
    funext fun x => add_linearH1MeanZeroFunction_grad wN c x
  rw [hgrad,
    setIntegral_vecDot_add wN.toH1Function.grad_memVectorL2 hcL2
      φ.toH1Function.grad_memVectorL2,
    setIntegral_vecDot_sub' hF hcL2 φ.toH1Function.grad_memVectorL2, h φ]
  ring

/-! ## Uniqueness of the response gradient, almost everywhere -/

/-- Two Dirichlet responses of the same flux have almost everywhere the same
gradient on the open cube.  This is the pointwise reading of
`gradToVectorL2_eq_of_isCubeDirichletResponse`. -/
theorem grad_ae_eq_of_isCubeDirichletResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {u v : H10Function (openCubeSet Q)}
    (hu : IsCubeDirichletResponse Q F u) (hv : IsCubeDirichletResponse Q F v) :
    u.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
      v.toH1Function.grad := by
  have heq := gradToVectorL2_eq_of_isCubeDirichletResponse hu hv
  have h1 := H1Function.coeFn_gradToVectorL2 u.toH1Function
  have h2 := H1Function.coeFn_gradToVectorL2 v.toH1Function
  rw [heq] at h1
  exact h1.symm.trans h2

/-- Two prescribed-flux Neumann responses of the same flux have almost
everywhere the same gradient on the open cube. -/
theorem grad_ae_eq_of_isCubeNeumannResponse {Q : TriadicCube d}
    {F : Vec d → Vec d} {u v : H1MeanZeroFunction (openCubeSet Q)}
    (hu : IsCubeNeumannResponse Q F u) (hv : IsCubeNeumannResponse Q F v) :
    u.toH1Function.grad =ᵐ[volume.restrict (openCubeSet Q)]
      v.toH1Function.grad := by
  have heq := gradToVectorL2_eq_of_isCubeNeumannResponse hu hv
  have h1 := H1Function.coeFn_gradToVectorL2 u.toH1Function
  have h2 := H1Function.coeFn_gradToVectorL2 v.toH1Function
  rw [heq] at h1
  exact h1.symm.trans h2

end

end SuperdiffusionCLT.Section3.ResponseFields
