/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.InteriorDet

/-!
# The deterministic core of the interior estimate in the frame of the centre

From the interior engine on the scales `[n + 1, m]` and one Caccioppoli step, the interior
Lipschitz estimate between the scales `n` and `m`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory

variable {d : ℕ}

/-- The set average on an origin cube is the cube average. -/
theorem lip_interior_origin_avg [NeZero d] (n : ℕ) (f : Vec d → ℝ) :
    ⨍ w in Section6.engCube d n, f w = cubeAverage (originCube d (n : ℤ)) f := by
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  rw [setAverage_eq, Measure.real, smul_eq_mul]

/-- The flatness of `u` on `□_n` in terms of the carriers of the target. -/
theorem lip_interior_origin_flat [NeZero d] (n : ℕ) (f : Vec d → ℝ) :
    ((3 : ℝ)⁻¹) ^ n * lipL2 (Section6.engCube d n)
        (fun x => f x - ⨍ w in Section6.engCube d n, f w) = Section6.cubeFlat n f := by
  rw [lipL2_engCube, lip_interior_origin_avg]
  rfl

/-- **The engine on `[n + 1, m]` plus one Caccioppoli step.**  The constants depend on `d` and
`Cin` only. -/
theorem lip_interior_origin_core (d : ℕ) [NeZero d] (Cin : ℝ) (hCin : 1 ≤ Cin) :
    ∃ (C c : ℝ) (k₀ : ℕ), 1 ≤ C ∧ 0 < c ∧
      ∀ (a : CoeffField d) (nu : ℝ) (s δ : ℕ → ℝ) (n m : ℕ),
        0 < nu → k₀ + 2 ≤ n → n < m →
        (∀ k, n ≤ k → k ≤ m → 0 < s k ∧ s m ≤ 2 * s k ∧ s k ≤ 2 * s m) →
        (∀ k, n ≤ k → k ≤ m → 0 ≤ δ k) →
        ∑ k ∈ Finset.Icc (n + 1) m, δ k ≤ c →
        (∀ k, n + 1 ≤ k → k ≤ m →
          LipCaccInt a nu (s k) Cin 1 k ∧ LipHarmInt a (s k) (δ k) Cin k) →
        LipIntAt a nu (s m) C 0 n m := by
  obtain ⟨Cd, cd, k₀, hCd, hcd, hdet⟩ := lip_int_det d Cin hCin
  have hCr : (1 : ℝ) ≤ (3 : ℝ) ^ (d + 2) := one_le_pow₀ (by norm_num)
  refine ⟨(3 : ℝ) ^ (d + 2) * Cd + 2 * Cin * (Cd + 1), cd, k₀, ?_, hcd, ?_⟩
  · have h1 : 1 ≤ (3 : ℝ) ^ (d + 2) * Cd := one_le_mul_of_one_le_of_one_le hCr hCd
    have h2 : 0 ≤ 2 * Cin * (Cd + 1) := by
      have : 0 ≤ Cd + 1 := by linarith only [hCd]
      exact mul_nonneg (by linarith only [hCin]) this
    linarith only [h1, h2]
  intro a nu s δ n m hnu hn hnm hs hδ hsum hblk f F u hu hF hfF
  have hsm : 0 < s m := (hs m hnm.le le_rfl).1
  have e := shiftCube_zero_eq_engCube (d := d) m
  generalize hS : shiftCube (0 : Vec d) (m : ℤ) = S at u hu hfF ⊢
  rw [e] at hS
  subst hS
  rw [shiftCube_zero_eq_engCube n]
  rw [lipGradL2_engCube, lip_interior_origin_flat n, lip_interior_origin_flat m]
  have hkn : n + 1 ≤ m := hnm
  have hP := hdet a nu s δ 1 (n + 1) m hnu le_rfl (by norm_num) (by omega) hkn
    (fun k h1 h2 => hs k (by omega) h2) (fun k h1 h2 => hδ k (by omega) h2) hsum hblk
    f F u hu hF hfF (n + 1) le_rfl hkn
  have hP1 := hP.1
  -- the restriction to the scale `n`
  have hr := lip_int_det_restr (f := u.toFun) (lip_int_det_memLp hkn u) (0 : Vec d)
  have e1 : (fun x => u.toFun x - vecDot (0 : Vec d) x) = u.toFun := by
    funext x; simp [vecDot]
  rw [e1] at hr
  -- one Caccioppoli step at the scale `n + 1`
  obtain ⟨hsol, hfk⟩ := lip_int_det_restrict (a := a) hkn hu hfF
  obtain ⟨hk1, hk2, hk3⟩ := hs (n + 1) (by omega) hkn
  have hcacc : LipCaccInt a nu (s m) (2 * Cin) 1 (n + 1) :=
    ((hblk (n + 1) le_rfl hkn).1).mono hk1 hk3 hk2 (by linarith only [hCin]) le_rfl
  have h1 := hcacc f F _ hsol hF hfk
  rw [Nat.add_sub_cancel] at h1
  have hsq : 0 < Real.sqrt (s m) := Real.sqrt_pos.2 hsm
  have hr0 : 0 ≤ (Real.sqrt (s m))⁻¹ := inv_nonneg.2 hsq.le
  have hrr : (Real.sqrt (s m))⁻¹ * (Real.sqrt (s m))⁻¹ = (s m)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hsm.le]
  have hrs : (Real.sqrt (s m))⁻¹ * Real.sqrt (s m) = 1 := inv_mul_cancel₀ hsq.ne'
  have h2 := mul_le_mul_of_nonneg_left h1 hr0
  have h3 : (Real.sqrt (s m))⁻¹ * (2 * Cin * (Real.sqrt (s m) * Section6.cubeFlat (n + 1) u.toFun +
      (Real.sqrt (s m))⁻¹ * (3 : ℝ) ^ (n + 1) * F)) =
      2 * Cin * (Section6.cubeFlat (n + 1) u.toFun +
        (s m)⁻¹ * (3 : ℝ) ^ (n + 1) * F) := by
    rw [← hrr]
    calc _ = 2 * Cin * (((Real.sqrt (s m))⁻¹ * Real.sqrt (s m)) *
          Section6.cubeFlat (n + 1) u.toFun +
          (Real.sqrt (s m))⁻¹ * (Real.sqrt (s m))⁻¹ * (3 : ℝ) ^ (n + 1) * F) := by ring
      _ = _ := by rw [hrs, one_mul]
  have hF2 : (s m)⁻¹ * (3 : ℝ) ^ (n + 1) * F ≤ (s m)⁻¹ * (3 : ℝ) ^ m * F := by
    have : (3 : ℝ) ^ (n + 1) ≤ (3 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) hkn
    have h0 : 0 ≤ (s m)⁻¹ := inv_nonneg.2 hsm.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0) hF
  have hF0 := Section6.cubeFlat_nonneg m u.toFun
  have h4 : Section6.cubeFlat (n + 1) u.toFun + (s m)⁻¹ * (3 : ℝ) ^ (n + 1) * F ≤
      (Cd + 1) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
    have h5 : (s m)⁻¹ * (3 : ℝ) ^ m * F ≤
        Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F := by linarith only [hF0]
    linarith only [hP1, hF2, h5]
  have h6 := mul_le_mul_of_nonneg_left h4 (by linarith only [hCin] : (0 : ℝ) ≤ 2 * Cin)
  have h7 : (Real.sqrt (s m))⁻¹ * (Real.sqrt nu * Section6.cubeGradL2 n u.grad) ≤
      2 * Cin * (Cd + 1) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) := by
    calc _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := h6
      _ = _ := by ring
  have h8 : (Real.sqrt (s m))⁻¹ * Real.sqrt nu * Section6.cubeGradL2 n u.grad =
      (Real.sqrt (s m))⁻¹ * (Real.sqrt nu * Section6.cubeGradL2 n u.grad) := by ring
  have h9 := mul_le_mul_of_nonneg_left hP1 (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (d + 2))
  have hflat : Section6.cubeFlat n u.toFun ≤ (3 : ℝ) ^ (d + 2) * (Cd *
      (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F)) :=
    hr.trans (mul_le_mul_of_nonneg_left hP1 (by positivity))
  calc (Real.sqrt (s m))⁻¹ * Real.sqrt nu * Section6.cubeGradL2 n u.grad +
        Section6.cubeFlat n u.toFun
      ≤ 2 * Cin * (Cd + 1) * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F) +
        (3 : ℝ) ^ (d + 2) * (Cd * (Section6.cubeFlat m u.toFun + (s m)⁻¹ * (3 : ℝ) ^ m * F)) := by
        linarith only [h7, h8, hflat]
    _ = _ := by ring

end SuperdiffusionCLT.Section7
