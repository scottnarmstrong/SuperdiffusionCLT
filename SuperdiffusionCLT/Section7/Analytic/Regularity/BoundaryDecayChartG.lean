/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartF

@[expose] public section

open Homogenization MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

/-!
# The slope at the top scale against a reference affine function

An affine function which approximates `v` on the face box of side `3^m / 36` up to `E` has a slope
which differs from the slope of any reference affine function `ℓ₀` by at most a multiple of the
`L²` excess of `v` over `ℓ₀` and `E`, divided by `3^m`.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem r3e_slope_step (e : Fin d) (m : ℤ) {v : Vec d → ℝ} {a₀ a₁ E : ℝ} {b₀ b₁ : Vec d}
    (hE : 0 ≤ E)
    (h : ∀ᵐ x ∂(volume.restrict (r3e_F e m ((3 : ℝ) ^ m / 36))),
      |v x - (a₁ + vecDot b₁ (x - r3c_z0 e m))| ≤ E)
    (hv : MemLp (fun x => v x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) 2
      (normalizedCubeMeasure (originCube d m))) :
    ‖b₁ - b₀‖ ≤ 288 * (6 ^ d * (eLpNorm (fun x => v x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) 2
      (normalizedCubeMeasure (originCube d m))).toReal + E) / (3 : ℝ) ^ m := by
  have hR : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  set R : ℝ := (3 : ℝ) ^ m with hRd
  set s : ℝ := R / 36 with hsd
  have hs : 0 < s := by positivity
  set w : Vec d → ℝ := fun x => v x - (a₀ + vecDot b₀ (x - r3c_z0 e m)) with hw
  set N : ℝ := (eLpNorm w 2 (normalizedCubeMeasure (originCube d m))).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hNsq : N ^ 2 = (R ^ d)⁻¹ * ∫ x in openCubeSet (originCube d m), w x ^ 2 :=
    r3d_norm_sq_normalized m hv
  have hRd0 : 0 < R ^ d := pow_pos hR d
  have hIQ : ∫ x in openCubeSet (originCube d m), w x ^ 2 = R ^ d * N ^ 2 := by
    rw [hNsq]; field_simp
  have hvQ : MemLp w 2 (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_restrict_of_normalized _ hv
  have hint : IntegrableOn (fun x => w x ^ 2) (openCubeSet (originCube d m)) :=
    hvQ.integrable_sq
  have hFQ : r3e_F e m s ⊆ openCubeSet (originCube d m) :=
    r3e_F_subset_cube e m (by rw [hsd]; linarith only [hR])
  have hFm : MeasurableSet (r3e_F e m s) := r3e_measurableSet_axisCube _ _
  have hintF : IntegrableOn (fun x => w x ^ 2) (r3e_F e m s) := hint.mono_set hFQ
  have hFle : ∫ x in r3e_F e m s, w x ^ 2 ≤ R ^ d * N ^ 2 := by
    rw [← hIQ]
    exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall hFQ)
  set a : ℝ := a₁ - a₀ with ha
  set γ : Vec d := b₁ - b₀ with hγ
  have hgpt : ∀ᵐ x ∂(volume.restrict (r3e_F e m s)),
      (a + vecDot γ (x - r3c_z0 e m)) ^ 2 ≤ 2 * w x ^ 2 + 2 * E ^ 2 := by
    filter_upwards [h] with x hx
    have hid : a + vecDot γ (x - r3c_z0 e m) =
        (v x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) - (v x - (a₁ + vecDot b₁ (x - r3c_z0 e m))) := by
      simp only [ha, hγ, r3e_vecDot_sub_left]; ring
    rw [hid]
    have h2 : (v x - (a₁ + vecDot b₁ (x - r3c_z0 e m))) ^ 2 ≤ E ^ 2 := by
      have := sq_le_sq' (by linarith only [abs_le.1 hx, hE]) (abs_le.1 hx).2
      exact this
    have h3 := sq_nonneg ((v x - (a₀ + vecDot b₀ (x - r3c_z0 e m))) +
      (v x - (a₁ + vecDot b₁ (x - r3c_z0 e m))))
    have h4 : w x = v x - (a₀ + vecDot b₀ (x - r3c_z0 e m)) := rfl
    rw [← h4]
    nlinarith only [h2, h3]
  have hcont : Continuous (fun x : Vec d => (a + vecDot γ (x - r3c_z0 e m)) ^ 2) :=
    (r3e_continuous_affine a γ (r3c_z0 e m)).pow 2
  have hFfin : IntegrableOn (fun x : Vec d => (a + vecDot γ (x - r3c_z0 e m)) ^ 2) (r3e_F e m s) :=
    r3e_integrableOn_axisCube hcont le_rfl
  have hvolF : volume (r3e_F e m s) ≠ ⊤ := r3e_volume_F_ne_top e m s
  have hconstF : ∫ x in r3e_F e m s, (2 * E ^ 2) = 2 * E ^ 2 * s ^ d := by
    rw [setIntegral_const, measureReal_def, r3e_volume_F e m hs, smul_eq_mul, mul_comm]
  have hgint : ∫ x in r3e_F e m s, (a + vecDot γ (x - r3c_z0 e m)) ^ 2 ≤
      2 * (R ^ d * N ^ 2) + 2 * E ^ 2 * s ^ d := by
    calc ∫ x in r3e_F e m s, (a + vecDot γ (x - r3c_z0 e m)) ^ 2
        ≤ ∫ x in r3e_F e m s, (2 * w x ^ 2 + 2 * E ^ 2) :=
          integral_mono_ae hFfin ((hintF.const_mul 2).add (integrableOn_const hvolF)) hgpt
      _ = 2 * (∫ x in r3e_F e m s, w x ^ 2) + 2 * E ^ 2 * s ^ d := by
          rw [integral_add (hintF.const_mul 2) (integrableOn_const hvolF), integral_const_mul,
            hconstF]
      _ ≤ _ := by linarith only [hFle]
  have hsl : ∀ i, |γ i| ^ 2 * s ^ (d + 2) ≤ 32 * (2 * (R ^ d * N ^ 2) + 2 * E ^ 2 * s ^ d) := by
    intro i
    have := r3e_slope_L2 (c := r3c_z0 e m + r3c_faceBase e s) (z := r3c_z0 e m) (γ := γ) (α := a)
      hs i
    exact this.trans (mul_le_mul_of_nonneg_left hgint (by norm_num))
  have hRs : R = 36 * s := by rw [hsd]; ring
  have hRds : R ^ d = 36 ^ d * s ^ d := by rw [hRs, mul_pow]
  have hsd0 : 0 < s ^ d := pow_pos hs d
  have hcoord : ∀ i, |γ i| * s ≤ 8 * (6 ^ d * N + E) := by
    intro i
    have h1 := hsl i
    rw [pow_add, hRd, hRds] at h1
    have h2 : (|γ i| * s) ^ 2 ≤ (8 * (6 ^ d * N + E)) ^ 2 := by
      have h3 : s ^ d * ((|γ i| * s) ^ 2) ≤ s ^ d * (64 * (36 ^ d * N ^ 2 + E ^ 2)) := by
        have : s ^ d * ((|γ i| * s) ^ 2) = |γ i| ^ 2 * (s ^ d * s ^ 2) := by ring
        rw [this]
        nlinarith only [h1]
      have h4 := le_of_mul_le_mul_left h3 hsd0
      have h5 : (36 : ℝ) ^ d = (6 ^ d) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [h5] at h4
      have h6 : 0 ≤ (6 : ℝ) ^ d * N * E := by positivity
      nlinarith only [h4, h6]
    exact (abs_le_of_sq_le_sq' h2 (by positivity)).2
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs, le_div_iff₀ hR]
  have := hcoord i
  rw [hRs]
  nlinarith only [this, hs]

end SuperdiffusionCLT.Section7
