/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Section8.Prereq.HeatWitness
public import SuperdiffusionCLT.Section8.Brownian.HeatCoreC

/-!
# The heat semigroup satisfies the divergence-form specification

For the constant coefficient `½ Id`, the classical operator `∇·(a ∇u)` is `½ Δ u` on `C²`
functions.  Every `C²` function `u` in `C₀` with `½ Δ u` in `C₀` is the resolvent value
`R_1 (u - ½ Δ u)`: the heat resolvent of smooth compactly supported approximants of
`u - ½ Δ u` lies in the differentiable class of the heat generator, the comparison of
`HeatWitness` bounds the distance of `u` from it, and the resolvent is bounded.  Hence `u` lies
in the generator domain and the generator acts as `½ Δ`.
-/

@[expose] public section

open scoped ZeroAtInfty NNReal

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory Topology MarkovProcess.Semigroup

variable {d : ℕ}

/-- The classical operator of the constant coefficient `c Id` is `c` times the Laplacian. -/
theorem heatWitness_divForm (c : ℝ) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (x : Vec d) :
    divForm 1 (fun _ ↦ c • (1 : Mat d)) u x = c * vecLaplacian u x := by
  have hdf' : Differentiable ℝ (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num) |>.differentiable (by norm_num)
  unfold divForm
  rw [one_mul, vecLaplacian_eq_sum_fderiv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hfun : (fun y : Vec d ↦ ∑ j : Fin d,
      ((fun _ : Vec d ↦ c • (1 : Mat d)) y) i j * fderiv ℝ u y (Pi.single j 1))
      = fun y ↦ c * fderiv ℝ u y (Pi.single i 1) := by
    funext y
    simp [Matrix.one_apply]
  rw [hfun]
  have hd : HasFDerivAt (fun y ↦ c * fderiv ℝ u y (Pi.single i 1))
      (c • ((ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Vec d)).comp
        (fderiv ℝ (fderiv ℝ u) x))) x := by
    have h1 := (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1 : Vec d)).hasFDerivAt.comp x
      (hdf' x).hasFDerivAt
    exact h1.const_smul c
  rw [hd.fderiv]
  simp

/-- **A `C²` function in `C₀` with Laplacian in `C₀` is a heat resolvent value.**  If `g` is
`u - ½ Δ u` then `u = R_1 g`. -/
theorem heatWitness_resolvent_eq (u v : C₀(Vec d, ℝ)) (hu : ContDiff ℝ 2 (⇑u))
    (hv : ∀ x, v x = 2⁻¹ * vecLaplacian (⇑u) x) :
    (Convergence.heatC0Semigroup d).resolvent ⟨1, Set.mem_Ioi.mpr one_pos⟩ (u - v) = u := by
  set mu : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩ with hmu
  set S := Convergence.heatC0Semigroup d with hS
  set g : C₀(Vec d, ℝ) := u - v with hg
  have key : ∀ ε : ℝ, 0 < ε → ‖u - S.resolvent mu g‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨g', hg'mem, hg'd⟩ := (heatCore_dense_smooth d).exists_dist_lt g hε
    set f : Convergence.heatCore d := ⟨S.resolvent mu g', heatCore_resolvent_mem mu g' hg'mem.1
      hg'mem.2⟩ with hf
    have hfmem : S.resolvent mu g' ∈ S.generatorDomain := S.resolvent_mem_generatorDomain mu g'
    have hgen : S.generator ⟨S.resolvent mu g', hfmem⟩ = (mu : ℝ) • S.resolvent mu g' - g' :=
      S.generator_eq_of_resolvent_eq mu hfmem rfl
    have hgen2 := Convergence.generator_heatCore f
    have hpt : ∀ x, 2⁻¹ * vecLaplacian (⇑(S.resolvent mu g')) x
        = S.resolvent mu g' x - g' x := by
      intro x
      have h := congrArg (fun h : C₀(Vec d, ℝ) ↦ h x) (hgen.symm.trans hgen2)
      simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
        Convergence.heatCoreLaplacian_apply, smul_eq_mul] at h
      have hmu1 : (mu : ℝ) = 1 := rfl
      rw [hmu1, one_mul] at h
      exact (by simpa using h.symm : _)
    have hc : ‖u - S.resolvent mu g'‖ ≤ ‖g - g'‖ / 1 := by
      refine heatWitness_norm_sub_le u (S.resolvent mu g') hu f.2.1 one_pos (norm_nonneg _) ?_
      intro x
      have h1 := hpt x
      have h2 := hv x
      have e : 1 * (u x - S.resolvent mu g' x)
          - 2⁻¹ * (vecLaplacian (⇑u) x - vecLaplacian (⇑(S.resolvent mu g')) x)
          = g x - g' x := by
        have h3 : 2⁻¹ * (vecLaplacian (⇑u) x - vecLaplacian (⇑(S.resolvent mu g')) x)
            = v x - (S.resolvent mu g' x - g' x) := by
          rw [mul_sub, h2, h1]
        rw [h3, hg]
        simp only [ZeroAtInftyContinuousMap.sub_apply]
        ring
      rw [e]
      have := ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := g - g')
      have hb := BoundedContinuousFunction.norm_coe_le_norm (g - g').toBCF x
      rw [this, Real.norm_eq_abs] at hb
      exact hb
    have hr : ‖S.resolvent mu g - S.resolvent mu g'‖ ≤ ‖g - g'‖ / 1 := by
      rw [← map_sub]
      refine (S.resolvent mu).le_opNorm _ |>.trans ?_
      have := S.opNorm_resolvent_le mu
      have hmu1 : (mu : ℝ) = 1 := rfl
      rw [hmu1] at this
      calc ‖S.resolvent mu‖ * ‖g - g'‖ ≤ 1⁻¹ * ‖g - g'‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖g - g'‖ / 1 := by simp
    have hd : ‖g - g'‖ < ε := by rwa [← dist_eq_norm]
    calc ‖u - S.resolvent mu g‖
        = ‖(u - S.resolvent mu g') + (S.resolvent mu g' - S.resolvent mu g)‖ := by
          congr 1; abel
      _ ≤ ‖u - S.resolvent mu g'‖ + ‖S.resolvent mu g' - S.resolvent mu g‖ := norm_add_le _ _
      _ ≤ ε + ε := by
          rw [norm_sub_rev (S.resolvent mu g') (S.resolvent mu g)]
          have := div_one ‖g - g'‖
          linarith only [hc, hr, hd, this]
      _ = 2 * ε := by ring
  have h0 : ‖u - S.resolvent mu g‖ = 0 := by
    refine le_antisymm (le_of_forall_pos_le_add fun ε hε ↦ ?_) (norm_nonneg _)
    have := key (ε / 2) (by positivity)
    linarith only [this]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm

end SuperdiffusionCLT.Section8.Brownian
