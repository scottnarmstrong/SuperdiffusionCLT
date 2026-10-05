/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsH
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApiB
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Facts about the Laplacian of a smooth compactly supported function

* `gen_lap_contDiff`, `gen_lap_eq_zero`, `gen_lap_hasCompactSupport`: smoothness and support;
* `gen_integral_lap`: the integral of the Laplacian vanishes;
* `gen_lap_comp_smul`: the Laplacian of a dilation;
* `gen_isC0_of_compactSupport`: continuous compactly supported functions are in `C₀`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal Pointwise ZeroAtInfty

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_isC0_of_compactSupport {f : Vec d → ℝ} (hc : Continuous f) (hs : HasCompactSupport f) :
    IsC0Function f :=
  ⟨⟨⟨f, hc⟩, hs.is_zero_at_infty⟩, rfl⟩

theorem gen_lap_contDiff {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ 1 (Brownian.vecLaplacian u) := by
  have h1 : ContDiff ℝ 2 (fderiv ℝ u) := hu.fderiv_right (m := 2) (by simp)
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := h1.fderiv_right (m := 1) (by norm_num)
  have : Brownian.vecLaplacian u =
      fun x => ∑ i, fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) := by
    funext x; exact Brownian.vecLaplacian_eq_sum_fderiv u x
  rw [this]
  refine ContDiff.sum fun i _ => ?_
  exact (h2.clm_apply contDiff_const).clm_apply contDiff_const

theorem gen_lap_eq_zero {u : Vec d → ℝ} {x : Vec d} (hx : x ∉ tsupport u) :
    Brownian.vecLaplacian u x = 0 := by
  have h0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [Brownian.vecLaplacian_eq_sum_fderiv]
  have h1 : fderiv ℝ u =ᶠ[nhds x] 0 := by
    have := h0.fderiv (𝕜 := ℝ)
    simpa using this
  have h2 := h1.fderiv_eq (𝕜 := ℝ)
  simp [h2]

theorem gen_lap_hasCompactSupport {u : Vec d → ℝ} (hc : HasCompactSupport u) :
    HasCompactSupport (Brownian.vecLaplacian u) :=
  HasCompactSupport.intro hc.isCompact fun _ hx => gen_lap_eq_zero hx

theorem gen_integral_lap {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    ∫ x, Brownian.vecLaplacian u x = 0 := by
  have hi : ∀ i : Fin d, ∫ x, fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) = 0 := by
    intro i
    have hφ : ContDiff ℝ (⊤ : ℕ∞) fun x => fderiv ℝ u x (Pi.single i 1) :=
      (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    have hφc : HasCompactSupport fun x => fderiv ℝ u x (Pi.single i 1) :=
      hc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
    have := domId_ibp_coord (F := fun _ => (1 : ℝ)) contDiff_const hφ hφc i
    simp only [one_mul] at this
    have e : (fun x => fderiv ℝ (fun x => fderiv ℝ u x (Pi.single i 1)) x (Pi.single i 1)) =
        fun x => fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) := by
      funext x
      have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
        ((hu.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
      have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single i (1 : ℝ) : Vec d) x)).fderiv
      simp [this]
    rw [← e, this]
    simp
  have hint : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fderiv ℝ u) x (Pi.single i 1)
      (Pi.single i 1)) := fun i => by
    have h1 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
      (hu.fderiv_right (m := 2) (by simp)).fderiv_right (m := 1) (by norm_num)
    have hc2 : Continuous fun x => fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) :=
      (h1.continuous.clm_apply continuous_const).clm_apply continuous_const
    have hcs : HasCompactSupport fun x => fderiv ℝ (fderiv ℝ u) x (Pi.single i 1) (Pi.single i 1) := by
      refine HasCompactSupport.intro hc.isCompact fun x hx => ?_
      have := gen_lap_eq_zero hx
      have h0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
      have h1' : fderiv ℝ u =ᶠ[nhds x] 0 := by
        have := h0.fderiv (𝕜 := ℝ); simpa using this
      simp [h1'.fderiv_eq (𝕜 := ℝ)]
    exact hc2.integrable_of_hasCompactSupport hcs
  simp only [Brownian.vecLaplacian_eq_sum_fderiv]
  rw [integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_eq_zero fun i _ => hi i

theorem gen_lap_comp_smul {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {t : ℝ} (ht : t ≠ 0) (z : Vec d) :
    Brownian.vecLaplacian (fun y => f (t • y)) z = t ^ 2 * Brownian.vecLaplacian f (t • z) := by
  have hf' : ContDiff ℝ 2 fun y : Vec d => f (t • y) := hf.comp (contDiff_const_smul t)
  have h := divForm_comp_smul 1 (fun _ => (1 : ℝ) • (1 : Mat d)) f ht z
  rw [divForm_const_smul_one 1 _ hf', divForm_const_smul_one 1 _ hf] at h
  simpa using h

theorem gen_divForm_scaled (c c' : ℝ) (hc' : c' ≠ 0) (A : CoeffField d) (u : Vec d → ℝ)
    (x : Vec d) :
    divForm c A u x = (c / c') * divForm 1 (fun y => c' • A y) u x := by
  rw [divForm_smul_coeff A hc']
  have h1 : divForm c A u x = c * divForm 1 A u x := by simp [divForm]
  rw [h1]
  field_simp

theorem gen_divForm_dilate (nu c : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (U : Vec d → ℝ) (z : Vec d) :
    divForm c (epCoeff nu omega ε) (fun x => U (ρ⁻¹ • x)) z =
      (ρ⁻¹) ^ 2 * divForm c (epCoeff nu omega (ε / ρ)) U (ρ⁻¹ • z) := by
  rw [divForm_comp_smul c (epCoeff nu omega ε) U (inv_ne_zero hρ.ne')]
  congr 2
  funext y
  simp only [epCoeff, inv_inv, smul_smul]
  congr 2
  field_simp

end SuperdiffusionCLT.Section8
