/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.IndicatorMultiscaleC
public import SuperdiffusionCLT.Section7.Prereq.CenteringC

@[expose] public section

open scoped Pointwise

namespace SuperdiffusionCLT.Section7

open MeasureTheory Homogenization

variable {d : ℕ}

theorem kc3_toReal_smul {c : ℝ} (hc : 0 < c) (A : Set (Vec d)) :
    (volume (c • A)).toReal = c ^ d * (volume A).toReal := by
  rw [Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg hc.le _)]

theorem kc3_volumeAverage_smul {c : ℝ} (hc : 0 < c) (A : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage (c • A) f = volumeAverage A (fun x => f (c • x)) := by
  unfold volumeAverage
  have h1 := kc3_toReal_smul hc A
  have h2 := Measure.setIntegral_comp_smul_of_pos (volume : Measure (Vec d)) f A hc
  rw [Module.finrank_fin_fun] at h2
  have hcd : c ^ d ≠ 0 := (pow_pos hc d).ne'
  have h3 : ∫ x in c • A, f x = c ^ d * ∫ x in A, f (c • x) := by
    rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hcd, one_mul]
  rw [h1, h3, mul_inv]
  show _ = _ * ∫ x in A, f (c • x)
  field_simp


/-! ### Triadic cells of the unit cube and sub-cubes of `□_m` -/

/-- `(3^t - 1) / 2`, the shift between the index of a cell of `[-1/2, 1/2)^d` and the index of the
corresponding centred triadic cube. -/
def kc3_h : ℕ → ℤ
  | 0 => 0
  | t + 1 => 3 * kc3_h t + 1

theorem kc3_two_h (t : ℕ) : 2 * kc3_h t + 1 = 3 ^ t := by
  induction t with
  | zero => simp [kc3_h]
  | succ t ih => simp only [kc3_h, pow_succ]; linarith only [ih]

/-- The depth-`t` descendant of `□_m` that corresponds to the cell with index `n`. -/
def kc3_cube (d m t : ℕ) (n : Fin d → ℤ) : TriadicCube d :=
  { scale := (m : ℤ) - t, index := fun i => n i - kc3_h t }

theorem kc3_coord {s T x nn h : ℝ} (hs : 0 < s) (hT : 2 * h + 1 = T) :
    ((nn - h) - 1 / 2) * s ≤ s * T * x ∧ s * T * x < ((nn - h) + 1 / 2) * s ↔
      nn ≤ T * (x + 1 / 2) ∧ T * (x + 1 / 2) < nn + 1 := by
  have e1 : s * T * x = s * (T * x) := by ring
  have e2 : ((nn - h) - 1 / 2) * s = s * ((nn - h) - 1 / 2) := by ring
  have e3 : ((nn - h) + 1 / 2) * s = s * ((nn - h) + 1 / 2) := by ring
  rw [e1, e2, e3, mul_le_mul_iff_right₀ hs, mul_lt_mul_iff_right₀ hs]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2, hT]


theorem kc3_scale_mul (m t : ℕ) :
    (3 : ℝ) ^ ((m : ℤ) - (t : ℤ)) * (3 : ℝ) ^ t = (3 : ℝ) ^ m := by
  rw [← zpow_natCast (3 : ℝ) t, ← zpow_natCast (3 : ℝ) m, ← zpow_add₀ (by norm_num)]
  congr 1
  ring

/-- Inside the unit cube, the generation-`t` cell of `x` is `n` exactly when `3^m x` lies in the
corresponding sub-cube of `□_m`. -/
theorem kc3_mem_cube_iff (m t : ℕ) (n : Fin d → ℤ) {x : Vec d} (hx : x ∈ kc2_Q0 d) :
    kc2_proj t x = n ↔ (3 : ℝ) ^ m • x ∈ cubeSet (kc3_cube d m t n) := by
  have hs : (0 : ℝ) < (3 : ℝ) ^ ((m : ℤ) - (t : ℤ)) := by positivity
  have hp : kc2_proj t x = kc2_idx t x := by simp only [kc2_proj, hx, ↓reduceIte]
  rw [hp]
  have hfun : kc2_idx t x = n ↔ ∀ i, ⌊(3 : ℝ) ^ t * (x i + 1 / 2)⌋ = n i :=
    ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hfun]
  refine forall_congr' fun i => ?_
  rw [Int.floor_eq_iff]
  have hc : ((3 : ℝ) ^ m • x) i = (3 : ℝ) ^ ((m : ℤ) - (t : ℤ)) * (3 : ℝ) ^ t * x i := by
    simp only [Pi.smul_apply, smul_eq_mul, kc3_scale_mul]
  have hT : 2 * (kc3_h t : ℝ) + 1 = (3 : ℝ) ^ t := by
    exact_mod_cast kc3_two_h t
  have := kc3_coord (s := (3 : ℝ) ^ ((m : ℤ) - (t : ℤ))) (T := (3 : ℝ) ^ t) (x := x i)
    (nn := (n i : ℝ)) (h := (kc3_h t : ℝ)) hs hT
  rw [← this]
  simp only [kc3_cube, cubeScaleFactor, hc, Int.cast_sub]


/-- Dilating the unit cube by `3^m` gives `□_m`. -/
theorem kc3_smul_Q0 (m : ℕ) : (3 : ℝ) ^ m • kc2_Q0 d = cubeSet (originCube d (m : ℤ)) := by
  have hc : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', kc2_mem_Q0, mem_cubeSet_originCube_iff]
  refine forall_congr' fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, zpow_natCast]
  rw [le_inv_mul_iff₀ hc, inv_mul_lt_iff₀ hc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]

/-- The sub-cube of a cell is a child of the sub-cube of its parent cell. -/
theorem kc3_child_mem (m t : ℕ) (n : Fin d → ℤ) :
    kc3_cube d m (t + 1) n ∈ childCubes (kc3_cube d m t (fun i => n i / 3)) := by
  rw [childCubes, Finset.mem_image]
  refine ⟨fun i => ⟨((n i) % 3).toNat, ?_⟩, Finset.mem_univ _, ?_⟩
  · have h1 := Int.emod_nonneg (n i) (by norm_num : (3 : ℤ) ≠ 0)
    have h2 := Int.emod_lt_of_pos (n i) (by norm_num : (0 : ℤ) < 3)
    omega
  · simp only [kc3_cube, TriadicCube.mk.injEq, kc3_h]
    refine ⟨by omega, funext fun i => ?_⟩
    have h1 := Int.emod_nonneg (n i) (by norm_num : (3 : ℤ) ≠ 0)
    have h3 := Int.mul_ediv_add_emod (n i) 3
    simp only [Int.toNat_of_nonneg h1]
    omega

/-- Every cell of positive measure is the dilate of a descendant of `□_m`. -/
theorem kc3_cube_mem_descendants (m : ℕ) :
    ∀ (t : ℕ) (n : Fin d → ℤ), (∃ x ∈ kc2_Q0 d, kc2_proj t x = n) →
      kc3_cube d m t n ∈ descendantsAtDepth (originCube d (m : ℤ)) t := by
  intro t
  induction t with
  | zero =>
    rintro n ⟨x, hx, rfl⟩
    have h0 : kc2_proj 0 x = 0 := by
      simp only [kc2_proj, hx, ↓reduceIte]
      funext i
      obtain ⟨h1, h2⟩ := kc2_mem_Q0.1 hx i
      show ⌊(3 : ℝ) ^ 0 * (x i + 1 / 2)⌋ = 0
      rw [Int.floor_eq_zero_iff]
      simp only [pow_zero, one_mul]
      constructor <;>
        linarith only [h1, h2]
    rw [h0, descendantsAtDepth, Finset.mem_singleton]
    simp only [kc3_cube, originCube, kc3_h, TriadicCube.mk.injEq]
    exact ⟨by simp, funext fun i => by simp⟩
  | succ t ih =>
    rintro n ⟨x, hx, rfl⟩
    have hP := ih (fun i => kc2_proj (t + 1) x i / 3) ⟨x, hx, kc2_proj_succ t x⟩
    rw [descendantsAtDepth, Finset.mem_biUnion]
    exact ⟨_, hP, kc3_child_mem m t _⟩


/-- The sub-cube of `□_m` is the dilate of the cell. -/
theorem kc3_cube_eq_smul (m t : ℕ) {n : Fin d → ℤ} (hn : ∃ x ∈ kc2_Q0 d, kc2_proj t x = n) :
    cubeSet (kc3_cube d m t n) = (3 : ℝ) ^ m • (kc2_cell t n ∩ kc2_Q0 d) := by
  have hc : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hsub := cubeSet_subset_of_mem_descendantsAtDepth (kc3_cube_mem_descendants m t n hn)
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne']
  have hy : (3 : ℝ) ^ m • ((3 : ℝ) ^ m)⁻¹ • y = y := smul_inv_smul₀ hc.ne' y
  constructor
  · intro hyQ
    have h0 : y ∈ (3 : ℝ) ^ m • kc2_Q0 d := by
      rw [kc3_smul_Q0]; exact hsub hyQ
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne'] at h0
    refine ⟨?_, h0⟩
    show kc2_proj t (((3 : ℝ) ^ m)⁻¹ • y) = n
    rw [kc3_mem_cube_iff m t n h0, hy]
    exact hyQ
  · rintro ⟨hcell, hx⟩
    have := (kc3_mem_cube_iff m t n hx).1 hcell
    rwa [hy] at this

theorem kc3_cellavg_eq (t : ℕ) (n : Fin d → ℤ) (κ : Vec d → ℝ) :
    kc2_cellavg κ t n = volumeAverage (kc2_cell t n ∩ kc2_Q0 d) κ := by
  unfold kc2_cellavg volumeAverage
  rw [kc2_μ, Measure.restrict_restrict (kc2_cell_measurable t n),
    Measure.restrict_apply (kc2_cell_measurable t n), div_eq_inv_mul]

/-- **Cell averages are averages over sub-cubes of `□_m`.** -/
theorem kc3_cellavg_dilate (m t : ℕ) {n : Fin d → ℤ} (hn : ∃ x ∈ kc2_Q0 d, kc2_proj t x = n)
    (f : Vec d → ℝ) :
    kc2_cellavg (fun x => f ((3 : ℝ) ^ m • x)) t n = volumeAverage (cubeSet (kc3_cube d m t n)) f := by
  rw [kc3_cellavg_eq, kc3_cube_eq_smul m t hn, kc3_volumeAverage_smul (by positivity)]


section Elementwise

open scoped Matrix.Norms.Elementwise

/-- Entries of a `C¹` matrix field are continuous. -/
theorem kc3_entry_continuous {Φ : Vec d → Mat d} (h : ContDiff ℝ 1 Φ) (i j : Fin d) :
    Continuous fun x => Φ x i j :=
  continuous_pi_iff.1 (continuous_pi_iff.1 h.continuous i) j

end Elementwise

end SuperdiffusionCLT.Section7
