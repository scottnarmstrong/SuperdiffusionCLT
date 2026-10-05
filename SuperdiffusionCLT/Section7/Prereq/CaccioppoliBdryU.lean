/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryR
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryT
public import SuperdiffusionCLT.Section7.Prereq.CaccioppoliBdryO

/-!
# The geometric constants of the boundary Caccioppoli inequality

For the translated dilate `W = t U - y` of a smooth domain, the part `B` of the support zone not
covered by good grid cubes has measure at most `Cϑ (3^n/3^j) |□_j|`, and `W` fills a fixed
proportion of the inner cube.
-/

@[expose] public section

open scoped ENNReal NNReal Pointwise
open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The constant of the measure of the uncovered part. -/
noncomputable def ca2_Cth (d : ℕ) (ρ0 M₁ : ℝ) : ℝ :=
  6 * d + (8 / ρ0 + 2) ^ d * ca2_pieceConst (d - 1) 1 M₁ * ρ0 ^ (d - 1)

theorem ca2_Cth_nonneg (d : ℕ) {ρ0 : ℝ} (hρ0 : 0 < ρ0) (M₁ : ℝ) : 0 ≤ ca2_Cth d ρ0 M₁ := by
  unfold ca2_Cth
  rcases d with _ | n
  · simp only [ca2_pieceConst]
    have := layerSlope_pos 0 M₁
    positivity
  · have := layerSlope_pos n M₁
    simp only [Nat.add_sub_cancel]
    unfold ca2_pieceConst
    positivity

theorem ca2w_measure_B [NeZero d] (hd : 2 ≤ d) {U : Set (Vec d)} {r0 M₁ M₂ D0 : ℝ}
    (hUu : IsUniformC11Domain U r0 M₁ M₂ D0) {t : ℝ} (y : Vec d) (hy : y ∈ t • U) (j h n : ℕ)
    (hnh : n + h = j) (hh : 3 ≤ h) (hjt : (3 : ℝ) ^ j ≤ t)
    (hx : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (j : ℤ) ≤ min r0 1 / 2) :
    (volume (ca2_Bset (j : ℤ) h ((3 : ℝ) ^ (j : ℤ) / 4) (translateSet (-y) (t • U)))).toReal ≤
      ca2_Cth d (min r0 1) M₁ * ((3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (j : ℤ)) *
        cubeVolume (originCube d (j : ℤ)) := by
  obtain ⟨n', rfl⟩ : ∃ n', d = n' + 1 := ⟨d - 1, by omega⟩
  have hr0 : 0 < r0 := hUu.2.1
  have hρ0 : 0 < min r0 1 := lt_min hr0 one_pos
  have hρ01 : min r0 1 ≤ 1 := min_le_right _ _
  have hL : (0 : ℝ) < (3 : ℝ) ^ (j : ℤ) := by positivity
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hjt
  have hW := ca2_W_uniform hUu ht y
  have hWo : IsOpen (translateSet (-y) (t • U)) := hW.1
  have hne : (translateSet (-y) (t • U)).Nonempty := ⟨0, y, hy, by simp⟩
  have hF := ca2_frontier_nonempty hW hne
  set ℓ : ℝ := (3 : ℝ) ^ (n : ℤ) with hℓdef
  set L : ℝ := (3 : ℝ) ^ (j : ℤ) with hLdef
  have hℓ0 : 0 < ℓ := by positivity
  have hjn : (j : ℤ) - (h : ℤ) = (n : ℤ) := by
    have : (j : ℤ) = n + h := by exact_mod_cast hnh.symm
    omega
  have hsc : 27 * ℓ ≤ L := by
    have := ca1_scale_facts (j : ℤ) h hh
    rw [hjn] at this
    exact this
  have hℓL : ℓ ≤ min r0 1 * L / 2 := by
    rw [div_le_iff₀ hL] at hx
    linarith only [hx]
  have hℓa : 2 * ℓ < L / 4 := by linarith only [hsc, hℓ0]
  have hρr : min r0 1 * L ≤ t * r0 := by
    have h1 : min r0 1 * L ≤ r0 * L := mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
    have h2 : r0 * L ≤ r0 * t := mul_le_mul_of_nonneg_left (by simpa [hLdef] using hjt) hr0.le
    linarith only [h1, h2]
  have hlayer := ca2_layer_cube2 (U := translateSet (-y) (t • U)) (n := n') hW
    hF 0 (j : ℤ) hρ0 hρ01 (by rw [← hLdef]; exact hρr) (τ := ℓ) hℓ0 (by rw [← hLdef]; exact hℓL)
  rw [rc_shiftCube_zero] at hlayer
  have hLb0 : 0 ≤ (8 / min r0 1 + 2) ^ (n' + 1) * ca2_pieceConst n' 1 M₁ * (min r0 1) ^ n' * ℓ * L ^ n' := by
    have := layerSlope_pos n' M₁
    unfold ca2_pieceConst
    positivity
  have hBv := ca2_vol_Bset (j : ℤ) h hWo (a := L / 4) (ℓ := ℓ) (by positivity) hℓa
    (fun R hR => by
      have := scale_eq_sub_of_mem_descendantsAtDepth hR
      simp [cubeScaleFactor, this, originCube, hjn, hℓdef]) hlayer hℓ0 hLb0
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBv).trans ?_
  rw [ENNReal.toReal_ofReal (by positivity), ca2_cubeVolume_originCube]
  unfold ca2_Cth
  simp only [Nat.add_sub_cancel]
  have h1 : (L / 4 + ℓ) ^ n' ≤ (L / 2) ^ n' := by
    refine pow_le_pow_left₀ (by positivity) ?_ _
    linarith only [hℓa, hL]
  have h2 : 3 * ((n' + 1 : ℕ) : ℝ) * ℓ * 2 ^ (n' + 1) * (L / 4 + ℓ) ^ n' ≤ 6 * ((n' + 1 : ℕ) : ℝ) * ℓ * L ^ n' := by
    calc 3 * ((n' + 1 : ℕ) : ℝ) * ℓ * 2 ^ (n' + 1) * (L / 4 + ℓ) ^ n'
        ≤ 3 * ((n' + 1 : ℕ) : ℝ) * ℓ * 2 ^ (n' + 1) * (L / 2) ^ n' := by gcongr
      _ = 6 * ((n' + 1 : ℕ) : ℝ) * ℓ * L ^ n' := by
        rw [div_pow, pow_succ]; field_simp; ring
  have e : (3 : ℝ) ^ (n : ℤ) / (3 : ℝ) ^ (j : ℤ) * (L ^ (n' + 1)) = ℓ * L ^ n' := by
    rw [← hℓdef, ← hLdef]; field_simp; ring
  simp only [← hLdef, ← hℓdef] at *
  have e2 : (6 * ((n' + 1 : ℕ) : ℝ) + (8 / min r0 1 + 2) ^ (n' + 1) * ca2_pieceConst n' 1 M₁ * min r0 1 ^ n') *
      (ℓ / L) * L ^ (n' + 1) = (6 * ((n' + 1 : ℕ) : ℝ) + (8 / min r0 1 + 2) ^ (n' + 1) *
        ca2_pieceConst n' 1 M₁ * min r0 1 ^ n') * (ℓ * L ^ n') := by
    rw [mul_assoc, e]
  rw [e2]
  nlinarith only [h2, hLb0]

end SuperdiffusionCLT.Section7
