/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartD

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The dyadic chain of flat affine approximations

The flat boundary decay produces, at each scale `s`, an affine function `a + ⟨b, x - z₀⟩`.  Here the
slopes `b` at the dyadic scales `s_j = 3^m / (36 · 2^j)` are compared with each other (the slope
lemmas for affine functions on cubes) and with the slope of any reference affine function (through
the mean square excess), so that the slopes stay bounded by the reference slope plus a multiple of
the excess datum.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_vecDot_sub_left (a b w : Vec d) : vecDot (a - b) w = vecDot a w - vecDot b w := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The face cube of side `s` touching the face `x_e = -3^m/2`. -/
noncomputable def r3e_F (e : Fin d) (m : ℤ) (s : ℝ) : Set (Vec d) :=
  axisCube (r3c_z0 e m + r3c_faceBase e s) s

theorem r3e_F_mono (e : Fin d) (m : ℤ) {s s' : ℝ} (h : s' ≤ s) :
    r3e_F e m s' ⊆ r3e_F e m s := by
  intro x hx j hj
  have h1 := hx j hj
  simp only [Set.mem_Ioo, Pi.add_apply, r3c_faceBase] at h1 ⊢
  by_cases hje : j = e
  · simp only [hje, ite_true, add_zero] at h1 ⊢
    constructor <;> linarith only [h1.1, h1.2, h]
  · simp only [hje, ite_false] at h1 ⊢
    constructor <;> linarith only [h1.1, h1.2, h]

theorem r3e_F_subset_cube (e : Fin d) (m : ℤ) {s : ℝ} (h : s ≤ (3 : ℝ) ^ m / 2) :
    r3e_F e m s ⊆ openCubeSet (originCube d m) := by
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro j
  have h1 := hx j (Set.mem_univ j)
  simp only [Set.mem_Ioo, Pi.add_apply, r3c_faceBase, r3c_z0] at h1
  by_cases hje : j = e
  · simp only [hje, ite_true, add_zero] at h1 ⊢
    constructor <;> linarith only [h1.1, h1.2, h, hℓ]
  · simp only [hje, ite_false, zero_add] at h1 ⊢
    constructor <;> linarith only [h1.1, h1.2, h, hℓ]

theorem r3e_volume_F (e : Fin d) (m : ℤ) {s : ℝ} (hs : 0 < s) :
    (volume (r3e_F e m s)).toReal = s ^ d := by
  have hle : (r3c_z0 e m + r3c_faceBase e s) ≤
      fun i => (r3c_z0 e m + r3c_faceBase e s) i + s := fun i => by
    simp only [le_add_iff_nonneg_right]; exact hs.le
  have h : (volume (r3e_F e m s)).toReal = ∏ _i : Fin d, s := by
    rw [r3e_F, axisCube, Real.volume_pi_Ioo_toReal hle]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem r3e_volume_F_ne_top (e : Fin d) (m : ℤ) (s : ℝ) : volume (r3e_F e m s) ≠ ⊤ := by
  have h : volume (r3e_F e m s) = ∏ i, ENNReal.ofReal (((r3c_z0 e m + r3c_faceBase e s) i + s) -
      (r3c_z0 e m + r3c_faceBase e s) i) := by
    rw [r3e_F, axisCube, Real.volume_pi_Ioo]
  rw [h]
  exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

/-- Two affine approximations on nested face cubes have close slopes. -/
theorem r3e_slope_diff (e : Fin d) (m : ℤ) {s s' : ℝ} (hs' : 0 < s') (hss : s' ≤ s)
    {φ : Vec d → ℝ} {a a' E E' : ℝ} {b b' : Vec d} (hE : 0 ≤ E) (hE' : 0 ≤ E')
    (h : ∀ᵐ x ∂(volume.restrict (r3e_F e m s)), |φ x - (a + vecDot b (x - r3c_z0 e m))| ≤ E)
    (h' : ∀ᵐ x ∂(volume.restrict (r3e_F e m s')),
      |φ x - (a' + vecDot b' (x - r3c_z0 e m))| ≤ E') :
    ‖b - b'‖ ≤ 2 * (E + E') / s' := by
  have h1 : ∀ᵐ x ∂(volume.restrict (r3e_F e m s')),
      |φ x - (a + vecDot b (x - r3c_z0 e m))| ≤ E :=
    ae_restrict_of_ae_restrict_of_subset (r3e_F_mono e m hss) h
  have h2 : ∀ᵐ x ∂(volume.restrict (r3e_F e m s')),
      |(a' - a) + vecDot (b' - b) (x - r3c_z0 e m)| ≤ E + E' := by
    filter_upwards [h1, h'] with x hx hx'
    have : (a' - a) + vecDot (b' - b) (x - r3c_z0 e m) =
        (φ x - (a + vecDot b (x - r3c_z0 e m))) - (φ x - (a' + vecDot b' (x - r3c_z0 e m))) := by
      rw [r3e_vecDot_sub_left]; ring
    rw [this]
    calc _ ≤ |φ x - (a + vecDot b (x - r3c_z0 e m))| +
          |φ x - (a' + vecDot b' (x - r3c_z0 e m))| := abs_sub _ _
      _ ≤ E + E' := add_le_add hx hx'
  have hsl := fun i => r3e_slope_sup (c := r3c_z0 e m + r3c_faceBase e s') hs' h2 i
  rw [norm_sub_rev]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hs']
  have := hsl i
  simpa [Pi.sub_apply] using this

end SuperdiffusionCLT.Section7
