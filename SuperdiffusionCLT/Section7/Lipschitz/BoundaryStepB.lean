/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryStep

/-!
# The boundary one-step inequality: the pinned decay with a localized zero trace

The cutoff of the localization lemma reduces the pinned boundary decay to the case of an `H¹₀`
solution.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The pinned decay for an `H¹` solution with a localized zero trace**: the cutoff of
`lip_localize` reduces it to `lip_patch_decay`.  The right-hand side and the function enter the
bracket through their restrictions to the ball where the cutoff is `1`. -/
theorem lip_patch_decay_loc (d : ℕ) [NeZero d] (hd : 2 ≤ d) (M₁ : ℝ) {p : ℝ}
    (hp : (d : ℝ) < p) :
    ∃ ε C c K : ℝ, 0 < ε ∧ 0 < C ∧ 0 < c ∧ 1 ≤ K ∧
      ∀ (V W B : Set (Vec d)) (rW M₂ DW R₀ : ℝ) (m₁ : ℤ) (x₀ : Vec d),
        IsOpen V → IsBoundedDomain V → IsOpen B → IsUniformC11Domain W rW M₁ M₂ DW →
        x₀ ∈ frontier W → V ∩ Metric.ball x₀ R₀ = W ∩ Metric.ball x₀ R₀ →
        M₂ * (3 : ℝ) ^ m₁ ≤ ε → K * (3 : ℝ) ^ m₁ ≤ rW → K * (3 : ℝ) ^ m₁ ≤ R₀ →
        Metric.closedBall x₀ (K * (3 : ℝ) ^ m₁) ⊆ B →
        ∀ (φ : H1Function V) (F : Vec d → ℝ), MemScalarL2 V F →
          IsWeakSolutionOn (fun _ => (1 : Mat d)) V φ F (fun _ => 0) →
          LocalizedZeroTraceFunctionOn V B φ.toFun →
          MemLp F (ENNReal.ofReal p)
            (volume.restrict (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁))) →
          ∀ (b₀ : Vec d) (ρ : ℝ), 0 < ρ → ρ ≤ c * (3 : ℝ) ^ m₁ → ρ ≤ (3 : ℝ) ^ m₁ →
            ∃ b : Vec d, ∀ᵐ y ∂(volume.restrict (V ∩ Metric.ball x₀ ρ)),
              |φ.toFun y - vecDot b (y - x₀)| ≤
                C * ρ * (ρ / (3 : ℝ) ^ m₁) ^ (1 - (d : ℝ) / p) *
                  (((3 : ℝ) ^ m₁)⁻¹ * (eLpNorm (fun y => φ.toFun y -
                        vecDot b₀ (y - x₀)) 2
                      (p12_nmeas ((3 : ℝ) ^ m₁)
                        (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal +
                    M₂ * (3 : ℝ) ^ m₁ * ‖b₀‖ +
                    (3 : ℝ) ^ m₁ * (eLpNorm F (ENNReal.ofReal p)
                      (p12_nmeas ((3 : ℝ) ^ m₁)
                        (V ∩ Metric.ball x₀ (K * (3 : ℝ) ^ m₁)))).toReal) := by
  obtain ⟨ε, C, c, K, hε, hC, hc, hK, hdec⟩ := lip_patch_decay d hd M₁ hp
  refine ⟨ε, C, c, K, hε, hC, hc, hK, ?_⟩
  intro V W B rW M₂ DW R₀ m₁ x₀ hVo hVb hBo hW hx₀ hVR hM2 hKr hKR hKB φ F hF hφ hz hFp b₀ ρ hρ hρc hρ1
  have hℓ : (0 : ℝ) < (3 : ℝ) ^ m₁ := by positivity
  set R : ℝ := K * (3 : ℝ) ^ m₁ with hR
  have hR0 : 0 < R := by positivity
  obtain ⟨χ, hχ, hχc, hχB, hχ1⟩ := lip_exists_cutoff (isCompact_closedBall x₀ R) hBo hKB
  obtain ⟨φ', F', hF', hφ'eq, hF'eq, hφ'sol⟩ := lip_localize d hVo hVb φ F hF hφ hz χ hχ hχc hχB
  have hSo : IsOpen (V ∩ Metric.ball x₀ R) := hVo.inter Metric.isOpen_ball
  have hSm : MeasurableSet (V ∩ Metric.ball x₀ R) := hSo.measurableSet
  -- on the ball the cutoff is `1`
  have hχ1' : ∀ y ∈ Metric.ball x₀ R, χ y = 1 := fun y hy => hχ1 y (Metric.ball_subset_closedBall hy)
  have hφeq : ∀ y ∈ Metric.ball x₀ R, φ'.toH1Function.toFun y = φ.toFun y := fun y hy => by
    rw [hφ'eq, hχ1' y hy, one_mul]
  have hFeq : ∀ y ∈ Metric.ball x₀ R, F' y = F y := fun y hy => by
    refine hF'eq y ?_
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz' using hχ1' z hz'
  have hae : ∀ ν : Measure (Vec d), ν ≪ volume.restrict (V ∩ Metric.ball x₀ R) →
      ∀ᵐ y ∂ν, y ∈ V ∩ Metric.ball x₀ R := fun ν hν =>
    hν.ae_le (ae_restrict_mem hSm)
  have hFp' : MemLp F' (ENNReal.ofReal p) (volume.restrict (V ∩ Metric.ball x₀ R)) := by
    refine hFp.ae_eq ?_
    filter_upwards [ae_restrict_mem hSm] with y hy using (hFeq y hy.2).symm
  obtain ⟨b, hb⟩ := hdec V W rW M₂ DW R₀ m₁ x₀ hVo hW hx₀ hVR hM2 hKr hKR φ' F'
    hφ'sol hFp' b₀ ρ hρ hρc
  refine ⟨b, ?_⟩
  have hp12 := lip_bdry_step_p12_ac ((3 : ℝ) ^ m₁) (V ∩ Metric.ball x₀ R)
  have hmemS := hae _ hp12
  have e1 : eLpNorm (fun y => φ'.toH1Function.toFun y - vecDot b₀ (y - x₀)) 2
      (p12_nmeas ((3 : ℝ) ^ m₁) (V ∩ Metric.ball x₀ R)) =
      eLpNorm (fun y => φ.toFun y - vecDot b₀ (y - x₀)) 2
      (p12_nmeas ((3 : ℝ) ^ m₁) (V ∩ Metric.ball x₀ R)) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hmemS] with y hy
    rw [hφeq y hy.2]
  have e2 : eLpNorm F' (ENNReal.ofReal p) (p12_nmeas ((3 : ℝ) ^ m₁) (V ∩ Metric.ball x₀ R)) =
      eLpNorm F (ENNReal.ofReal p) (p12_nmeas ((3 : ℝ) ^ m₁) (V ∩ Metric.ball x₀ R)) := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [hmemS] with y hy
    rw [hFeq y hy.2]
  rw [e1, e2] at hb
  have hρR : Metric.ball x₀ ρ ⊆ Metric.ball x₀ R := by
    refine Metric.ball_subset_ball (hρ1.trans ?_)
    rw [hR]
    exact le_mul_of_one_le_left hℓ.le hK
  filter_upwards [hb, ae_restrict_mem (hVo.inter Metric.isOpen_ball).measurableSet] with y hy hyS
  rw [← hφeq y (hρR hyS.2)]
  exact hy


theorem lip_bdry_step_vol_ball {S : Set (Vec d)} {c : Vec d} {r ℓ : ℝ} (hr : 0 < r) (hℓ : 0 < ℓ)
    (hS : S ⊆ Metric.ball c r) :
    volume S ≠ ⊤ ∧ (ℓ ^ d)⁻¹ * (volume S).toReal ≤ (2 * r / ℓ) ^ d := by
  have hv : volume (Metric.ball c r) = ENNReal.ofReal ((2 * r) ^ d) := by
    rw [Real.volume_pi_ball c hr, Fintype.card_fin]
  have hle : volume S ≤ ENNReal.ofReal ((2 * r) ^ d) := hv ▸ measure_mono hS
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ?_⟩
  have h1 : (volume S).toReal ≤ (2 * r) ^ d :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans
      (le_of_eq (ENNReal.toReal_ofReal (by positivity)))
  calc (ℓ ^ d)⁻¹ * (volume S).toReal ≤ (ℓ ^ d)⁻¹ * (2 * r) ^ d :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (2 * r / ℓ) ^ d := by rw [div_pow, div_eq_mul_inv, mul_comm]

theorem lip_bdry_step_pow_mul_le {k k₀ m : ℕ} (h1 : m ≤ k₀) (h2 : k₀ ≤ k) :
    (3 : ℝ) ^ (k - k₀) * 3 ^ m ≤ 3 ^ k := by
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem lip_bdry_step_dist_small {z x₀ : Vec d} {k k₀ ag : ℕ} (hag : ag + 1 ≤ k₀) (hk : k₀ ≤ k)
    (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2) :
    ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 3 ^ ag / 6 := by
  have h := lip_bdry_step_pow_mul_le hag hk
  have h3 : (3 : ℝ) ^ (ag + 1) = 3 * 3 ^ ag := by rw [pow_succ]; ring
  have hpos : (0 : ℝ) < 3 ^ ag := by positivity
  have h4 : (3 : ℝ) ^ (k - k₀) ≤ (3 : ℝ) ^ k / 3 ^ ag / 3 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    calc (3 : ℝ) ^ (k - k₀) * (3 ^ ag * 3) = (3 : ℝ) ^ (k - k₀) * 3 ^ (ag + 1) := by rw [h3]; ring
      _ ≤ 3 ^ k := h
  linarith only [hx₀, h4]

theorem lip_bdry_step_ball_win {z x₀ : Vec d} {k k₀ ag : ℕ} (hag : ag + 1 ≤ k₀) (hk : k₀ ≤ k)
    (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2) :
    Metric.ball x₀ ((3 : ℝ) ^ k / 3 ^ ag / 3) ⊆ Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) := by
  have h := lip_bdry_step_dist_small hag hk hx₀
  refine Metric.ball_subset_ball' ?_
  rw [dist_eq_norm]
  linarith only [h]

theorem lip_bdry_step_closedBall_win {z x₀ : Vec d} {k k₀ ag : ℕ} {R : ℝ} (hag : ag + 1 ≤ k₀)
    (hk : k₀ ≤ k) (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ k / 3 ^ ag / 6)
    (hR : R ≤ (3 : ℝ) ^ k / 3 ^ ag / 9) :
    Metric.closedBall x₀ R ⊆ Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) := by
  have _ := hag
  have _ := hk
  have hq : (0 : ℝ) < (3 : ℝ) ^ k / 3 ^ ag := by positivity
  refine Metric.closedBall_subset_ball' ?_
  rw [dist_eq_norm]
  linarith only [hR, hx₀, hq]

theorem lip_bdry_step_Dm_sub {W V : Set (Vec d)} {z : Vec d} {k k₀ ag : ℕ} (hag : ag ≤ k₀)
    (hk : k₀ ≤ k) (hBV : Metric.ball z ((3 : ℝ) ^ k / 3 ^ ag / 2) ∩ W ⊆ V) :
    shiftCube z (((k - k₀ : ℕ) : ℕ) : ℤ) ∩ W ⊆ V := by
  intro y hy
  refine hBV ⟨?_, hy.2⟩
  have h1 := hy.1
  rw [lip_bdry_approx_shiftCube_eq_ball] at h1
  refine Metric.ball_subset_ball ?_ h1
  have h := lip_bdry_step_pow_mul_le hag hk
  have hpos : (0 : ℝ) < 3 ^ ag := by positivity
  have : (3 : ℝ) ^ (k - k₀) ≤ (3 : ℝ) ^ k / 3 ^ ag := by
    rw [le_div_iff₀ hpos]; exact h
  linarith only [this]

theorem lip_bdry_step_Dm_ball {z x₀ : Vec d} {k k₀ : ℕ}
    (hx₀ : ‖x₀ - z‖ ≤ (3 : ℝ) ^ (k - k₀) / 2) :
    shiftCube z (((k - k₀ : ℕ) : ℕ) : ℤ) ⊆ Metric.ball x₀ ((3 : ℝ) ^ (k - k₀)) := by
  intro y hy
  rw [lip_bdry_approx_shiftCube_eq_ball, Metric.mem_ball, dist_eq_norm] at hy
  rw [Metric.mem_ball, dist_eq_norm]
  have := norm_sub_le_norm_sub_add_norm_sub y z x₀
  rw [norm_sub_rev z x₀] at this
  linarith only [this, hy, hx₀]

end SuperdiffusionCLT.Section7
