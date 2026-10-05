/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DomainIdentification
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationB
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationGreen
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.RealResolvent
public import SuperdiffusionCLT.Section8.DivergenceForm.PenalizationEverywhere

/-!
# A classical solution is the limit of the cube resolvents

Let `u` be `C²` and tend to zero at infinity, and put `g = μ u - divForm 1 a u`.  On the cube
`□_m` the zero-Dirichlet weak solution `u_m` of `μ u_m - ∇·(a∇u_m) = g` satisfies
`sup_{□_m} |u - u_m| ≤ M` whenever `|u| ≤ M` off a compact subset of `□_m`
(`domId_abs_sub_le_of_matched`).  Letting the cube exhaust the space shows that the cube resolvents
of `g` converge pointwise to `u`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open SuperdiffusionCLT.Section8.DivergenceForm

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- Compactly supported truncations of a `C¹` function lie in `H¹₀`. -/
theorem domId_truncations_memH10 {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 1 u) {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    {M : ℝ} (hzero : ∀ x, x ∉ K → |u x| ≤ M) :
    MemH10 U (fun x ↦ max ((H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hu).toFun x - M) 0) ∧
    MemH10 U (fun x ↦ max (-(H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hu).toFun x - M) 0) := by
  set ψ := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hu with hψ
  constructor
  · obtain ⟨w, hw, -⟩ := exists_h1_max_sub_const hU ψ M
    have := memH10_of_compactSupport hU w hK hKU fun x hx ↦ by
      rw [hw]
      exact max_eq_right (by linarith only [(abs_le.mp (hzero x hx)).2, show ψ.toFun x = u x from rfl])
    rwa [hw] at this
  · obtain ⟨w, hw, -⟩ := exists_h1_max_sub_const hU (-ψ) M
    have := memH10_of_compactSupport hU w hK hKU fun x hx ↦ by
      rw [hw]
      refine max_eq_right ?_
      rw [H1Function.neg_toFun]
      linarith only [(abs_le.mp (hzero x hx)).1, show ψ.toFun x = u x from rfl]
    rw [hw] at this
    simpa only [H1Function.neg_toFun] using this


/-- **The cube bound.**  If `|u| ≤ M` off a compact subset `K` of the cube `□_m`, then the zero
Dirichlet cube resolvent of `g = μ u - divForm 1 a u` is within `M` of `u` on `□_m`. -/
theorem domId_cube_bound [NeZero d] (A : WholeSpaceAnalyticData d)
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ A.a y i j) (mu : MarkovProcess.Semigroup.PositiveShift)
    {u g : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (hgm : Measurable g) {D : ℝ}
    (hgD : ∀ x, |g x| ≤ D) (hg : ∀ x, g x = (mu : ℝ) * u x - divForm 1 A.a u x) (m : ℕ)
    {K : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ wholeSpaceCube d m) {M : ℝ} (hM : 0 ≤ M)
    (hzero : ∀ x, x ∉ K → |u x| ≤ M) :
    ∀ x ∈ wholeSpaceCube d m, |u x - A.analyticCubeResolvent mu g hgm hgD m x| ≤ M := by
  classical
  have hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  have hEll := A.cubeEllipticity m
  obtain ⟨v, -, hweak, hv2⟩ := exists_h10Function_alphaShiftedResolvent hU A.a mu.property A.hnu
    hEll (cubeDatumL2 m hgm hgD)
  have hvsol := isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution v hweak
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hψsol := domId_weak_of_classical hU ha hu
  obtain ⟨hT1, hT2⟩ := domId_truncations_memH10 hU hu1 hK hKU hzero
  have hfae := cubeDatumL2_ae m hgm hgD
  have hv_ae : v.toH1Function.toFun =ᵐ[volumeMeasureOn (wholeSpaceCube d m)]
      A.analyticCubeResolvent mu g hgm hgD m := by
    filter_upwards [v.toH1Function.coeFn_toScalarL2, A.analyticCubeResolvent_ae mu hgm hgD m]
      with x h1 h2
    rw [← h1, hv2]
    exact h2.symm
  have hrel : (fun x ↦ -(divForm 1 A.a u x) -
      (cubeDatumL2 m hgm hgD x - (mu : ℝ) * v.toH1Function.toFun x)) =ᵐ[
        volumeMeasureOn (wholeSpaceCube d m)]
      fun x ↦ -((mu : ℝ) * ((H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hu1).toFun x -
        v.toH1Function.toFun x)) := by
    filter_upwards [hfae] with x hx
    rw [hx, hg x]
    change _ = -((mu : ℝ) * (u x - v.toH1Function.toFun x))
    ring
  have hmain := domId_abs_sub_le_of_matched hU mu.property hM hEll hψsol hvsol hrel v.memH10 hT1 hT2
  have hae : ∀ᵐ x ∂volumeMeasureOn (wholeSpaceCube d m),
      |u x - A.analyticCubeResolvent mu g hgm hgD m x| ≤ M := by
    filter_upwards [hmain, hv_ae] with x h1 h2
    rw [← h2]
    exact h1
  have hcont : ContinuousOn (fun x ↦ |u x - A.analyticCubeResolvent mu g hgm hgD m x|)
      (wholeSpaceCube d m) :=
    continuous_abs.comp_continuousOn (hu1.continuous.continuousOn.sub
      (A.continuousOn_analyticCubeResolvent mu hgm hgD m))
  exact le_of_ae_le_of_continuousOn hU.isOpen hcont continuousOn_const hae

end SuperdiffusionCLT.Section8
