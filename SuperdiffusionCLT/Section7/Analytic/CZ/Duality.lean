/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs

/-!
# Norming lemma for the normalized `L^p` norm

If `F` is tested against bounded measurable fields `G` with
`|⨍_U F·G| ≤ M · lpBar U p' G`, then `lpBar U p F ≤ M`. The test fields are the truncated
`|F|^{p-2} F`. The norm on `Vec d` is the sup norm, for which the constant is exactly `1`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The componentwise map `v ↦ |v|^{P-2} v`. -/
noncomputable def p14_phi (P : ℝ) (v : Vec d) : Vec d := fun i => v i * |v i| ^ (P - 2)

theorem p14_mul_phi {P : ℝ} (hP : 1 < P) (a : ℝ) : a * (a * |a| ^ (P - 2)) = |a| ^ P := by
  by_cases ha : a = 0
  · rw [ha]
    simp only [zero_mul, abs_zero]
    rw [Real.zero_rpow (by linarith only [hP])]
  · have hpos : 0 < |a| := abs_pos.mpr ha
    have h1 : a * a = |a| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs, sq]
    calc a * (a * |a| ^ (P - 2)) = (a * a) * |a| ^ (P - 2) := by ring
      _ = |a| ^ (2 : ℝ) * |a| ^ (P - 2) := by rw [h1]
      _ = |a| ^ P := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring

theorem p14_abs_phi {P : ℝ} (hP : 1 < P) (a : ℝ) : |a * |a| ^ (P - 2)| = |a| ^ (P - 1) := by
  by_cases ha : a = 0
  · rw [ha]
    simp only [zero_mul, abs_zero]
    rw [Real.zero_rpow (by linarith only [hP])]
  · have hpos : 0 < |a| := abs_pos.mpr ha
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
    calc |a| * |a| ^ (P - 2) = |a| ^ (1 : ℝ) * |a| ^ (P - 2) := by rw [Real.rpow_one]
      _ = |a| ^ (P - 1) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring

theorem p14_norm_phi_le {P : ℝ} (hP : 1 < P) (v : Vec d) : ‖p14_phi P v‖ ≤ ‖v‖ ^ (P - 1) := by
  have h0 : 0 ≤ ‖v‖ ^ (P - 1) := Real.rpow_nonneg (norm_nonneg _) _
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => ?_
  rw [Real.norm_eq_abs]
  simp only [p14_phi]
  rw [p14_abs_phi hP]
  exact Real.rpow_le_rpow (abs_nonneg _) (by simpa using norm_le_pi_norm v i)
    (by linarith only [hP])

theorem p14_norm_pow_le_sum {P : ℝ} (hP : 1 < P) (v : Vec d) :
    ‖v‖ ^ P ≤ ∑ i, |v i| ^ P := by
  by_cases h0 : ‖v‖ = 0
  · rw [h0, Real.zero_rpow (by linarith only [hP])]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  · have hpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ∃ i, ‖v‖ ≤ |v i| := by
      by_contra hc
      push Not at hc
      have := (pi_norm_lt_iff hpos).2 fun i => by rw [Real.norm_eq_abs]; exact hc i
      exact lt_irrefl _ this
    obtain ⟨i, hi⟩ := this
    calc ‖v‖ ^ P ≤ |v i| ^ P := Real.rpow_le_rpow (norm_nonneg _) hi (by linarith only [hP])
      _ ≤ ∑ j, |v j| ^ P :=
        Finset.single_le_sum (f := fun j => |v j| ^ P)
          (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)

theorem p14_dot_phi {P : ℝ} (hP : 1 < P) (v : Vec d) :
    vecDot v (p14_phi P v) = ∑ i, |v i| ^ P := by
  simp only [vecDot, p14_phi]
  exact Finset.sum_congr rfl fun i _ => p14_mul_phi hP (v i)

theorem p14_measurable_phi (P : ℝ) : Measurable (p14_phi (d := d) P) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold p14_phi
  have hi : Measurable (fun v : Vec d => v i) := measurable_pi_apply i
  exact hi.mul ((continuous_abs.measurable.comp hi).pow_const _)

/-- The truncated test field `1_{|F| ≤ n} |F|^{P-2} F`. -/
noncomputable def p14_G (P n : ℝ) (F : Vec d → Vec d) (x : Vec d) : Vec d :=
  if ‖F x‖ ≤ n then p14_phi P (F x) else 0

/-- The truncated power `1_{|F| ≤ n} |F|^P`. -/
noncomputable def p14_T (P n : ℝ) (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  if ‖F x‖ ≤ n then ‖F x‖ ^ P else 0

theorem p14_measurable_G (P n : ℝ) {F : Vec d → Vec d} (hF : Measurable F) :
    Measurable (p14_G P n F) :=
  Measurable.ite (measurableSet_le hF.norm measurable_const)
    ((p14_measurable_phi P).comp hF) measurable_const

theorem p14_measurable_T (P n : ℝ) {F : Vec d → Vec d} (hF : Measurable F) :
    Measurable (p14_T P n F) :=
  Measurable.ite (measurableSet_le hF.norm measurable_const)
    (hF.norm.pow_const _) measurable_const

theorem p14_norm_G_le {P : ℝ} (hP : 1 < P) {n : ℝ} (hn : 0 ≤ n) (F : Vec d → Vec d)
    (x : Vec d) : ‖p14_G P n F x‖ ≤ n ^ (P - 1) := by
  unfold p14_G
  split_ifs with h
  · exact (p14_norm_phi_le hP _).trans
      (Real.rpow_le_rpow (norm_nonneg _) h (by linarith only [hP]))
  · simpa using Real.rpow_nonneg hn _

theorem p14_T_nonneg (P n : ℝ) (F : Vec d → Vec d) (x : Vec d) : 0 ≤ p14_T P n F x := by
  unfold p14_T
  split_ifs
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · exact le_refl _

theorem p14_T_le_dot {P : ℝ} (hP : 1 < P) (n : ℝ) (F : Vec d → Vec d) (x : Vec d) :
    p14_T P n F x ≤ vecDot (F x) (p14_G P n F x) := by
  unfold p14_T p14_G
  split_ifs with h
  · rw [p14_dot_phi hP]
    exact p14_norm_pow_le_sum hP _
  · simp [vecDot]

theorem p14_dot_le {P : ℝ} (hP : 1 < P) {n : ℝ} (hn : 0 ≤ n) (F : Vec d → Vec d)
    (x : Vec d) : |vecDot (F x) (p14_G P n F x)| ≤ d * n ^ P := by
  unfold p14_G
  split_ifs with h
  · rw [p14_dot_phi hP, abs_of_nonneg (Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg _) _)]
    calc ∑ i, |F x i| ^ P ≤ ∑ _i : Fin d, n ^ P :=
          Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (abs_nonneg _)
            (by simpa using (norm_le_pi_norm (F x) i).trans h) (by linarith only [hP])
      _ = d * n ^ P := by simp
  · simpa [vecDot] using mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg hn P)

theorem p14_enorm_G_pow_le {P Q : ℝ} (hP : 1 < P) (hQ : (P - 1) * Q = P) (hQ0 : 0 < Q)
    (F : Vec d → Vec d) (n : ℝ) (x : Vec d) :
    ‖p14_G P n F x‖ₑ ^ Q ≤ ENNReal.ofReal (p14_T P n F x) := by
  unfold p14_G p14_T
  split_ifs with h
  · rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hQ0.le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖p14_phi P (F x)‖ ^ Q ≤ (‖F x‖ ^ (P - 1)) ^ Q :=
          Real.rpow_le_rpow (norm_nonneg _) (p14_norm_phi_le hP _) hQ0.le
      _ = ‖F x‖ ^ P := by rw [← Real.rpow_mul (norm_nonneg _), hQ]
  · simp [hQ0]

end SuperdiffusionCLT.Section7
