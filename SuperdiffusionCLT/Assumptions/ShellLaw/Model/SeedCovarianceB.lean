/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovariance

/-!
# The covariance of the seed field

`nvCov x y = ∫ z, ψ (x - z) * ψ (y - z)` is the stationary covariance of the seed field
(scale `ε = 1`); it equals `∑ k, ∑ p, c_{k,p}(x) c_{k,p}(y)` where `c_{k,p}` are the frame
coefficients of the cell kernels, because the squares of the cell weights form a partition of unity.

## Main results

* `nvCov`, `nvCov_comm`, `nvCov_self_pos`
* `nv_sum_cell_integral`: the cell kernels sum up to the covariance
* `nvCov_translate`: dependence on `x - y` only
* `nvCov_eq_zero_of_one_le`: vanishing at distance at least `1`
* `nvCov_signedPerm`: symmetry under signed permutations
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The stationary covariance of the seed field: `∫ ψ (x - z) ψ (y - z) dz`, i.e.
`(ψ ∗ ψ̌) (x - y)`. -/
def nvCov (x y : Vec d) : ℝ := ∫ z, radialBump d (x - z) * radialBump d (y - z)

theorem nv_continuous_bump_sub (x : Vec d) : Continuous fun z : Vec d ↦ radialBump d (x - z) :=
  radialBump_contDiff.continuous.comp (continuous_const.sub continuous_id)

theorem nv_hasCompactSupport_bump_sub (x : Vec d) :
    HasCompactSupport fun z : Vec d ↦ radialBump d (x - z) :=
  radialBump_hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)

theorem nvCov_comm (x y : Vec d) : nvCov x y = nvCov y x := by
  unfold nvCov
  simp_rw [mul_comm]

theorem nvCov_self_pos (x : Vec d) : 0 < nvCov x x := by
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) ?_ ?_
    (fun _ ↦ mul_nonneg (radialBump_nonneg _) (radialBump_nonneg _)) (by simp)
  · exact (nv_continuous_bump_sub x).mul (nv_continuous_bump_sub x)
  · exact (nv_hasCompactSupport_bump_sub x).mul_left

/-- Translation invariance of the covariance. -/
theorem nvCov_translate (x y v : Vec d) : nvCov (x + v) (y + v) = nvCov x y := by
  unfold nvCov
  rw [← integral_add_right_eq_self
    (fun z : Vec d ↦ radialBump d (x + v - z) * radialBump d (y + v - z)) v]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  have e1 : x + v - (z + v) = x - z := by abel
  have e2 : y + v - (z + v) = y - z := by abel
  simp only [e1, e2]

/-- The covariance vanishes when the squared Euclidean distance is at least `1`. -/
theorem nvCov_eq_zero_of_one_le {x y : Vec d} (h : 1 ≤ ∑ i, (x i - y i) ^ 2) :
    nvCov x y = 0 := by
  unfold nvCov
  refine (integral_congr_ae (g := fun _ ↦ (0 : ℝ)) (Filter.Eventually.of_forall fun z ↦ ?_)).trans
    (integral_zero _ _)
  by_contra hne
  have hx : radialBump d (x - z) ≠ 0 := left_ne_zero_of_mul hne
  have hy : radialBump d (y - z) ≠ 0 := right_ne_zero_of_mul hne
  have hx' : ∑ i, (x i - z i) ^ 2 < 1 / 4 := by
    by_contra hc
    exact hx (radialBump_eq_zero_of_le (by simpa using not_lt.1 hc))
  have hy' : ∑ i, (y i - z i) ^ 2 < 1 / 4 := by
    by_contra hc
    exact hy (radialBump_eq_zero_of_le (by simpa using not_lt.1 hc))
  have hle : ∑ i, (x i - y i) ^ 2 ≤ ∑ i, (2 * (x i - z i) ^ 2 + 2 * (y i - z i) ^ 2) :=
    Finset.sum_le_sum fun i _ ↦ by nlinarith only [sq_nonneg (x i + y i - 2 * z i)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hle
  linarith only [h, hle, hx', hy']

/-- The same statement with the Euclidean norm. -/
theorem nvCov_eq_zero_of_one_le_vecNorm {x y : Vec d} (h : 1 ≤ Book.Ch02.vecNorm (x - y)) :
    nvCov x y = 0 := by
  refine nvCov_eq_zero_of_one_le ?_
  have h1 := Book.Ch02.vecNorm_sq_eq_vecNormSq (x - y)
  have h2 : vecNormSq (x - y) = ∑ i, (x i - y i) ^ 2 := by
    simp [vecNormSq, vecDot, pow_two]
  rw [← h2, ← h1]
  nlinarith only [h]

/-! ## Signed permutations -/

/-- A signed permutation of the coordinates. -/
def nv_signedPerm (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (x : Vec d) : Vec d :=
  fun i ↦ s i * x (σ i)

theorem radialBump_signedPerm (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (x : Vec d) :
    radialBump d (nv_signedPerm σ s x) = radialBump d x := by
  unfold nv_signedPerm
  rw [radialBump_mul_sign s hs (fun i ↦ x (σ i)), radialBump_comp_perm σ x]

theorem nv_signedPerm_sub (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (x y : Vec d) :
    nv_signedPerm σ s (x - y) = nv_signedPerm σ s x - nv_signedPerm σ s y := by
  funext i
  simp [nv_signedPerm, mul_sub]

theorem nv_measurePreserving_signedPerm (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    MeasurePreserving (nv_signedPerm σ s) (volume : Measure (Vec d)) volume := by
  have h1 : MeasurePreserving (fun x : Vec d ↦ fun i ↦ x (σ i))
      (volume : Measure (Vec d)) volume := by
    have := volume_measurePreserving_piCongrLeft (fun _ : Fin d ↦ ℝ) σ.symm
    convert this using 1
    funext x i
    have h := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin d ↦ ℝ) σ.symm x (σ i)
    simpa [MeasurableEquiv.piCongrLeft] using h.symm
  have h2 : MeasurePreserving (fun x : Vec d ↦ fun i ↦ s i * x i)
      (volume : Measure (Vec d)) volume := by
    refine volume_preserving_pi (fun i ↦ ?_)
    rcases hs i with h | h
    · rw [h]
      convert MeasurePreserving.id (volume : Measure ℝ) using 1
      funext x; simp
    · rw [h]
      convert Measure.measurePreserving_neg (volume : Measure ℝ) using 1
      funext x; simp
  exact h2.comp h1

/-- Invariance of the covariance under signed permutations of the coordinates. -/
theorem nvCov_signedPerm (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (x y : Vec d) :
    nvCov (nv_signedPerm σ s x) (nv_signedPerm σ s y) = nvCov x y := by
  unfold nvCov
  have hm := nv_measurePreserving_signedPerm σ s hs
  set H : Vec d → ℝ := fun z ↦ radialBump d (nv_signedPerm σ s x - z) *
    radialBump d (nv_signedPerm σ s y - z) with hH
  have hHc : Continuous H := (nv_continuous_bump_sub _).mul (nv_continuous_bump_sub _)
  have h := integral_map (μ := (volume : Measure (Vec d))) hm.measurable.aemeasurable
    (φ := nv_signedPerm σ s) (f := H)
    (by rw [hm.map_eq]; exact hHc.aestronglyMeasurable)
  rw [hm.map_eq] at h
  show ∫ z, H z = _
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp only [hH, ← nv_signedPerm_sub, radialBump_signedPerm σ s hs]

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
