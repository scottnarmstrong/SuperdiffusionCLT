/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.Carriers
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxDirichlet
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeMoments
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Moments of the origin cube

For the origin cube `□_n = (-3^n/2, 3^n/2)^d` and the normalized measure `μ_n` on it,
`∫ xᵢ dμ_n = 0` and `∫ xᵢ xⱼ dμ_n = δᵢⱼ 3^{2n}/12`.  Consequently the slope of an `L²` function
is the coefficient vector of its `L²(μ_n)` pairing with the linear functions.
-/

@[expose] public section

open scoped ENNReal

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The normalized measure of `□_n` as a multiple of Lebesgue measure on the open box. -/
theorem e0c_mu_eq (n : ℕ) :
    normalizedCubeMeasure (originCube d (n : ℤ)) =
      ENNReal.ofReal ((((3 : ℝ) ^ n) ^ d)⁻¹) •
        volume.restrict (axisCube (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) ((3 : ℝ) ^ n)) := by
  have hz : (fun j : Fin d => ((((originCube d (n : ℤ)).index j : ℤ) : ℝ) - (1 / 2 : ℝ)) *
      cubeScaleFactor (originCube d (n : ℤ))) = fun _ => -(((3 : ℝ) ^ n) / 2) := by
    funext j
    simp [originCube, cubeScaleFactor]
    ring
  have hs : cubeScaleFactor (originCube d (n : ℤ)) = (3 : ℝ) ^ n := by
    simp [cubeScaleFactor, originCube]
  unfold normalizedCubeMeasure cubeMeasure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    HarmonicApprox.openCubeSet_eq_axisCube_triadic, hz, hs, cubeVolume_eq_scaleFactor_pow, hs]


theorem e0c_integral_eq (n : ℕ) (g : Vec d → ℝ) :
    ∫ x, g x ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((((3 : ℝ) ^ n) ^ d)⁻¹) *
        ∫ x in axisCube (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) ((3 : ℝ) ^ n), g x := by
  rw [e0c_mu_eq, integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

theorem e0c_integrable (n : ℕ) {g : Vec d → ℝ} (hg : Continuous g) :
    Integrable g (normalizedCubeMeasure (originCube d (n : ℤ))) := by
  rw [e0c_mu_eq]
  exact (SuperdiffusionCLT.Section8.Common.ExcessDecay.integrableOn_axisCube_of_continuous
    hg _ _).smul_measure ENNReal.ofReal_ne_top

theorem e0c_memLp (n : ℕ) {g : Vec d → ℝ} (hg : Continuous g) :
    MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ))) :=
  (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 (e0c_integrable n (hg.pow 2))

theorem e0c_int_coord (n : ℕ) (i : Fin d) :
    ∫ x, x i ∂normalizedCubeMeasure (originCube d (n : ℤ)) = 0 := by
  have h := SuperdiffusionCLT.Section8.Common.ExcessDecay.setIntegral_axisCube_centered
    (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) (L := (3 : ℝ) ^ n) (by positivity) i
  have e : ∀ x : Vec d, x i - SuperdiffusionCLT.Section8.Common.ExcessDecay.axisCubeCenter
      (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) ((3 : ℝ) ^ n) i = x i := by
    intro x
    simp only [SuperdiffusionCLT.Section8.Common.ExcessDecay.axisCubeCenter_apply]
    ring
  simp only [e] at h
  rw [e0c_integral_eq, h, mul_zero]

theorem e0c_int_coord_mul (n : ℕ) (i j : Fin d) :
    ∫ x, x i * x j ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      if i = j then ((3 : ℝ) ^ n) ^ 2 / 12 else 0 := by
  have h := SuperdiffusionCLT.Section8.Common.ExcessDecay.setIntegral_axisCube_centered_mul
    (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) (L := (3 : ℝ) ^ n) (by positivity) i j
  have e : ∀ (x : Vec d) (k : Fin d),
      x k - SuperdiffusionCLT.Section8.Common.ExcessDecay.axisCubeCenter
        (fun _ : Fin d => -(((3 : ℝ) ^ n) / 2)) ((3 : ℝ) ^ n) k = x k := by
    intro x k
    simp only [SuperdiffusionCLT.Section8.Common.ExcessDecay.axisCubeCenter_apply]
    ring
  simp only [e] at h
  rw [e0c_integral_eq, h]
  have hne : (((3 : ℝ) ^ n) ^ d) ≠ 0 := by positivity
  split_ifs
  · field_simp
  · simp

theorem e0c_continuous_vecDot (p : Vec d) : Continuous fun x : Vec d => vecDot p x := by
  unfold vecDot
  fun_prop

theorem e0c_int_ell_x (n : ℕ) (p : Vec d) (i : Fin d) :
    ∫ x, vecDot p x * x i ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * p i := by
  have hpt : ∀ x : Vec d, vecDot p x * x i = ∑ j, p j * (x j * x i) := by
    intro x
    simp only [vecDot, Finset.sum_mul, mul_assoc]
  simp only [hpt]
  rw [integral_finsetSum _ (fun j _ => (e0c_integrable n (by fun_prop)).const_mul (p j))]
  simp only [integral_const_mul, e0c_int_coord_mul]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' (Finset.univ) i]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem e0c_int_ell (n : ℕ) (p : Vec d) :
    ∫ x, vecDot p x ∂normalizedCubeMeasure (originCube d (n : ℤ)) = 0 := by
  have hpt : ∀ x : Vec d, vecDot p x = ∑ j, p j * x j := fun x => rfl
  simp only [hpt]
  rw [integral_finsetSum _ (fun j _ => (e0c_integrable n (by fun_prop)).const_mul (p j))]
  simp [integral_const_mul, e0c_int_coord]

theorem e0c_int_mul_ell (n : ℕ) {g : Vec d → ℝ}
    (hg : ∀ i, Integrable (fun x => g x * x i) (normalizedCubeMeasure (originCube d (n : ℤ))))
    (q : Vec d) :
    ∫ x, g x * vecDot q x ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ∑ i, q i * ∫ x, g x * x i ∂normalizedCubeMeasure (originCube d (n : ℤ)) := by
  have hpt : ∀ x : Vec d, g x * vecDot q x = ∑ i, q i * (g x * x i) := by
    intro x
    simp only [vecDot, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ (fun i _ => (hg i).const_mul (q i))]
  simp only [integral_const_mul]

theorem e0c_int_ell_ell (n : ℕ) (p q : Vec d) :
    ∫ x, vecDot p x * vecDot q x ∂normalizedCubeMeasure (originCube d (n : ℤ)) =
      ((3 : ℝ) ^ n) ^ 2 / 12 * vecDot p q := by
  rw [e0c_int_mul_ell n (fun i => e0c_integrable n ((e0c_continuous_vecDot p).mul (continuous_apply i)))]
  simp only [e0c_int_ell_x]
  unfold vecDot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

theorem e0c_slope_apply (n : ℕ) (f : Vec d → ℝ) (i : Fin d) :
    ((3 : ℝ) ^ n) ^ 2 / 12 * affSlope n f i =
      ∫ x, f x * x i ∂normalizedCubeMeasure (originCube d (n : ℤ)) := by
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [affSlope, inv_pow]
  field_simp

theorem e0c_cubeL2_sq (n : ℕ) {g : Vec d → ℝ}
    (hg : MemLp g 2 (normalizedCubeMeasure (originCube d (n : ℤ)))) :
    cubeL2 n g ^ 2 = ∫ x, g x ^ 2 ∂normalizedCubeMeasure (originCube d (n : ℤ)) :=
  toReal_eLpNorm_two_sq_eq_integral_sq hg

end SuperdiffusionCLT.Section6
