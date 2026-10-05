/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaK

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Geometry of the flat cutoff: the translation onto the half cube
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The translation carrying the face centre `r3c_z0 e m` to the origin. -/
noncomputable def r3c_shift (e : Fin d) (m : ℤ) : Vec d := fun i => if i = e then (3 : ℝ) ^ m / 2 else 0

theorem r3c_z0_add_shift (e : Fin d) (m : ℤ) : r3c_z0 e m + r3c_shift e m = 0 := by
  funext i
  by_cases h : i = e <;> simp [r3c_z0, r3c_shift, h]

theorem r3c_nrm_eq (e : Fin d) (m : ℤ) (x : Vec d) : r3c_nrm e m x = (x + r3c_shift e m) e := by
  simp [r3c_nrm, r3c_shift]

theorem r3c_mem_halfCube_iff (e : Fin d) (m : ℤ) (x : Vec d) :
    x + r3c_shift e m ∈ flatHalfCube e (m - 1) ↔
      (∀ i, i ≠ e → |x i| < (3 : ℝ) ^ m / 6) ∧ 0 < r3c_nrm e m x ∧ r3c_nrm e m x < (3 : ℝ) ^ m / 6 := by
  have h3 : (3 : ℝ) ^ (m - 1) = (3 : ℝ) ^ m / 3 := by rw [zpow_sub_one₀ (by norm_num)]; ring
  have hp : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  unfold flatHalfCube
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hc_mem_openCubeSet_originCube_iff, h3]
  rw [← r3c_nrm_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, h2, ?_⟩
    · have := h1 i
      simp only [Pi.add_apply, r3c_shift, hi, ite_false, add_zero] at this
      rw [abs_lt]; constructor <;> linarith only [this.1, this.2]
    · have := h1 e
      simp only [Pi.add_apply, r3c_shift, ite_true] at this
      unfold r3c_nrm
      linarith only [this.2]
  · rintro ⟨h1, h2, h3'⟩
    refine ⟨fun i => ?_, h2⟩
    by_cases hi : i = e
    · subst hi
      simp only [Pi.add_apply, r3c_shift, ite_true]
      unfold r3c_nrm at h2 h3'
      constructor <;> linarith only [h2, h3', hp]
    · have := h1 i hi
      rw [abs_lt] at this
      simp only [Pi.add_apply, r3c_shift, hi, ite_false, add_zero]
      constructor <;> linarith only [this.1, this.2, hp]

/-- The preimage of the half cube under the translation lies in the cube. -/
theorem r3c_halfCube_preimage_subset (e : Fin d) (m : ℤ) :
    {x : Vec d | x + r3c_shift e m ∈ flatHalfCube e (m - 1)} ⊆ openCubeSet (originCube d m) := by
  intro x hx
  have hx' := (r3c_mem_halfCube_iff e m x).1 hx
  have hp : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [hc_mem_openCubeSet_originCube_iff]
  intro i
  by_cases hi : i = e
  · subst hi
    have h2 := hx'.2.1
    have h3 := hx'.2.2
    unfold r3c_nrm at h2 h3
    constructor <;> linarith only [h2, h3, hp]
  · have := hx'.1 i hi
    rw [abs_lt] at this
    constructor <;> linarith only [this.1, this.2, hp]

/-- Points of the cube within sup-distance `5 3^m/48` of the face centre are in the preimage. -/
theorem r3c_near_face_mem (e : Fin d) (m : ℤ) {x : Vec d} (hxD : x ∈ openCubeSet (originCube d m))
    (hx : ∀ i, |x i - r3c_z0 e m i| ≤ 5 * ((3 : ℝ) ^ m / 3) / 16) :
    x + r3c_shift e m ∈ flatHalfCube e (m - 1) := by
  have hp : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  rw [r3c_mem_halfCube_iff]
  refine ⟨fun i hi => ?_, r3c_nrm_pos_of_mem e m hxD, ?_⟩
  · have := hx i
    simp only [r3c_z0, hi, ite_false, sub_zero] at this
    rw [abs_lt] at *
    have h5 := (abs_le.1 this)
    constructor <;> linarith only [h5.1, h5.2, hp]
  · have := hx e
    simp only [r3c_z0, ite_true] at this
    have h5 := abs_le.1 this
    unfold r3c_nrm
    linarith only [h5.2, hp]

/-- Subtracting `c n` keeps the localized zero trace on the face. -/
theorem r3c_localized_sub (e : Fin d) (m : ℤ) (c : ℝ)
    {φ u : H1Function (openCubeSet (originCube d m))}
    (hZ : LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m))
      {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 2} φ.toFun)
    (hu : ∀ x, u.toFun x = φ.toFun x - c * r3c_nrm e m x) :
    LocalizedZeroTraceFunctionOn (openCubeSet (originCube d m))
      {x | ∀ i, |x i - r3c_z0 e m i| < (3 : ℝ) ^ m / 2} u.toFun := by
  intro η hη hηc hηT
  obtain ⟨Wφ, hWφ⟩ := hZ η hη hηc hηT
  obtain ⟨Wn, hWn⟩ := r3c_memH10_mul_nrm e m (η := fun x => c * η x) (contDiff_const.mul hη)
    (hηc.mul_left) ((tsupport_mul_subset_right (f := fun _ : Vec d => c) (g := η)).trans hηT)
  refine ⟨h10Sub Wφ Wn, ?_⟩
  funext x
  have h1 := congrFun hWφ x
  have h2 := congrFun hWn x
  show (Wφ.toH1Function - Wn.toH1Function).toFun x = η x * u.toFun x
  rw [H1Function.sub_toFun]
  simp only at h1 h2 ⊢
  rw [h1, h2, hu x]
  ring

end SuperdiffusionCLT.Section7
