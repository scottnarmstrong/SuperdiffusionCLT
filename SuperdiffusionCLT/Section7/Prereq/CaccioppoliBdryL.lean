/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryK

/-!
# Comparison of the gradient on a good cube with the weighted gradient

On a grid cube inside the domain the gradient norm is bounded by the weighted gradient norm of the
cutoff (Harnack inequality of the cutoff on interior cubes, lower bound of the larger cutoff on
near cubes).
-/

@[expose] public section

open scoped ENNReal NNReal
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- On an interior grid cube the weighted quantity `M e` is controlled by the weighted energy. -/
theorem ca2_M_le [NeZero d] {D : Set (Vec d)} (u : H1Function D) {a : ℝ} (ha : 0 < a)
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ D)
    (hint : ∀ k, |triadicCubeShift R k| + 3 / 2 * cubeScaleFactor R ≤ a) :
    12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
      12 * 64 ^ d * 64 ^ d * a⁻¹ *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x))) := by
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hGφ := ca1_memLp_phi_mul R a hG
  have hℓ : 0 < cubeScaleFactor R := by simp [cubeScaleFactor]; positivity
  have hpt : ∀ x ∈ openCubeSet R, ca1_phi a (triadicCubeShift R) ≤ 64 ^ d * ca1_phi a x := by
    intro x hx
    refine ca1_phi_harnack (a := a) (η := cubeScaleFactor R) ha hℓ.le (x := x) (y := triadicCubeShift R)
      (fun k => ?_) (fun k => ?_)
    · have := ca1_abs_le_center R hx k
      linarith only [this, hint k, hℓ]
    · have := (ca1_mem_openCube_iff R x).1 hx k
      rw [abs_sub_comm] at this
      exact this.le.trans (by linarith only [hℓ])
  have h1 := ca1_cubeLpNorm_le R (F := fun x => ca1_phi a (triadicCubeShift R) * Real.sqrt (vecNormSq (u.grad x)))
    (G := fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))
    ((hG.const_mul _).aestronglyMeasurable) hGφ (M := 64 ^ d) (by positivity)
    (ca1_ae_openR R fun x hx => by
      rw [abs_mul, abs_mul, abs_of_nonneg (ca1_phi_nonneg a _), abs_of_nonneg (ca1_phi_nonneg a x)]
      have := hpt x hx
      have h0 : 0 ≤ |Real.sqrt (vecNormSq (u.grad x))| := abs_nonneg _
      calc ca1_phi a (triadicCubeShift R) * |Real.sqrt (vecNormSq (u.grad x))|
          ≤ (64 ^ d * ca1_phi a x) * |Real.sqrt (vecNormSq (u.grad x))| :=
            mul_le_mul_of_nonneg_right this h0
        _ = _ := by ring)
  rw [cubeLpNorm_const_mul, Real.norm_of_nonneg (ca1_phi_nonneg a _)] at h1
  have h12 : 0 ≤ 12 * 64 ^ d * a⁻¹ := by positivity
  calc 12 * 64 ^ d * a⁻¹ * ca1_phi a (triadicCubeShift R) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x)))
      = 12 * 64 ^ d * a⁻¹ * (ca1_phi a (triadicCubeShift R) * cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x)))) := by ring
    _ ≤ 12 * 64 ^ d * a⁻¹ * (64 ^ d * cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi a x * Real.sqrt (vecNormSq (u.grad x)))) :=
        mul_le_mul_of_nonneg_left h1 h12
    _ = _ := by ring

/-- Near the support of the cutoff the gradient is controlled by the weighted gradient of the larger
cutoff. -/
theorem ca2_e_le [NeZero d] {D : Set (Vec d)} (u : H1Function D)
    {R : TriadicCube d} (hRQ : openCubeSet R ⊆ D) {ac : ℝ}
    (hlow : ∀ x ∈ openCubeSet R, ∀ k, |x k| ≤ 2 / 3 * ac) (hac : 0 < ac) :
    cubeLpNorm R (2 : ℝ≥0∞) (fun x => Real.sqrt (vecNormSq (u.grad x))) ≤
      ((125 / 729 : ℝ) ^ d)⁻¹ *
        cubeLpNorm R (2 : ℝ≥0∞) (fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) := by
  let ur : H1Function (openCubeSet R) := u.restrict (isOpen_openCubeSet R) hRQ
  have hG : MemLp (fun x => Real.sqrt (vecNormSq (u.grad x))) 2 (normalizedCubeMeasure R) :=
    r1_memLp_grad_eucNorm R ur
  have hGφ := ca1_memLp_phi_mul R ac hG
  have hc0 : 0 < ((125 / 729 : ℝ) ^ d) := by positivity
  have h1 := ca1_cubeLpNorm_le R (F := fun x => Real.sqrt (vecNormSq (u.grad x)))
    (G := fun x => ca1_phi ac x * Real.sqrt (vecNormSq (u.grad x))) hG.aestronglyMeasurable hGφ
    (M := ((125 / 729 : ℝ) ^ d)⁻¹) (by positivity)
    (ca1_ae_openR R fun x hx => by
      have hl := ca1_phi_lower hac (hlow x hx)
      have h0 : 0 ≤ Real.sqrt (vecNormSq (u.grad x)) := Real.sqrt_nonneg _
      rw [abs_of_nonneg h0, abs_mul, abs_of_nonneg (ca1_phi_nonneg ac x), abs_of_nonneg h0]
      have h2 : 1 ≤ ((125 / 729 : ℝ) ^ d)⁻¹ * ca1_phi ac x := by
        rw [← div_eq_inv_mul, le_div_iff₀ hc0]; linarith only [hl]
      calc Real.sqrt (vecNormSq (u.grad x)) = 1 * Real.sqrt (vecNormSq (u.grad x)) := (one_mul _).symm
        _ ≤ (((125 / 729 : ℝ) ^ d)⁻¹ * ca1_phi ac x) * Real.sqrt (vecNormSq (u.grad x)) :=
            mul_le_mul_of_nonneg_right h2 h0
        _ = _ := by ring)
  exact h1


end SuperdiffusionCLT.Section7
