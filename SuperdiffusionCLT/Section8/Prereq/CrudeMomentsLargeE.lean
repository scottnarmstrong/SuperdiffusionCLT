/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsLargeD
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The fourth moment at the origin for times at least one

The displacement tail at the origin (`CrudeMomentsLargeD`) is a stretched exponential
`exp (-κ sqrt s)` in the dimensionless radius `s` beyond the cutting radius `(W₀ ℓ) ^ (2 n)`.  The
layer cake gives the fourth moment `C (W₀ ℓ) ^ (8 n) t ^ 2` with the logarithmic scale
`ℓ = 2 log (1 + 2 d) + log (K ^ 2 + t)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set Filter
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal

noncomputable section

/-- The cubic budget of the stretched exponential `exp (-κ sqrt s)`. -/
def crudeMomL_budget (κ : ℝ) : ℝ :=
  (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-(κ * Real.sqrt s)) * s ^ 3)).toReal

theorem crudeMomL_integrableOn_cube {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun s : ℝ ↦ Real.exp (-(κ * Real.sqrt s)) * s ^ 3) (Ioi 0) := by
  rw [← integrableOn_Ioi_comp_rpow_iff'
    (fun s : ℝ ↦ Real.exp (-(κ * Real.sqrt s)) * s ^ 3) (p := 2) (by norm_num)]
  have hmajor : IntegrableOn (fun x : ℝ ↦ x ^ (7 : ℝ) * Real.exp (-κ * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (s := (7 : ℝ)) (p := (1 : ℝ)) (by norm_num)
      (by norm_num) hκ
  refine hmajor.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  have h2 : x ^ (2 : ℝ) = x ^ 2 := Real.rpow_two x
  have hsq : Real.sqrt (x ^ 2) = x := Real.sqrt_sq hx0.le
  have h7 : x ^ (7 : ℝ) = x ^ 7 := by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp only [smul_eq_mul]
  rw [h2, hsq, Real.rpow_one, h7, show (2 : ℝ) - 1 = ((1 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have : (x ^ 2) ^ 3 = x ^ 6 := by ring
  rw [this]
  rw [show -κ * x = -(κ * x) by ring]
  ring

theorem crudeMomL_lintegral_cube_ne_top {κ : ℝ} (hκ : 0 < κ) :
    (∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-(κ * Real.sqrt s)) * s ^ 3)) ≠ ⊤ := by
  have hcont : Continuous fun s : ℝ ↦ Real.exp (-(κ * Real.sqrt s)) * s ^ 3 :=
    (Real.continuous_exp.comp (continuous_const.mul Real.continuous_sqrt).neg).mul
      (continuous_id.pow 3)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
      fun s : ℝ ↦ Real.exp (-(κ * Real.sqrt s)) * s ^ 3 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (le_of_lt (zero_lt_one.trans hs)) 3)
  refine (lintegral_ofReal_ne_top_iff_integrable hcont.aestronglyMeasurable hnonneg).2 ?_
  exact (crudeMomL_integrableOn_cube hκ).mono_set (fun s (hs : 1 < s) ↦ (zero_lt_one.trans hs : (0:ℝ) < s))

theorem crudeMomL_budget_nonneg (κ : ℝ) : 0 ≤ crudeMomL_budget κ := ENNReal.toReal_nonneg

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

/-- **The fourth moment at the origin for times at least one, with the explicit constant.** -/
theorem RoughLogBounds.crudeMomL_fourth_moment (Rb : RoughLogBounds Sp)
    (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) {t : ℝ≥0} (ht1 : 1 ≤ t) :
    ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(R.kernelSemigroup t 0) ≤
      ENNReal.ofReal (14641 * ((((crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n *
        crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ)) ^ (2 * Rb.n)) ^ 4 +
          8 * Real.exp 1 * crudeMomL_budget (crudeMomL_kap d A.nu Rb.c0 Rb.n)) * (t : ℝ) ^ 2)) := by
  have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
  have htpos : (0 : ℝ) < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht1'
  have hinv : (0 : ℝ) < (t : ℝ)⁻¹ := inv_pos.mpr htpos
  let mu : PositiveShift := ⟨(t : ℝ)⁻¹, hinv⟩
  have hmu1 : (mu : ℝ) ≤ 1 := inv_le_one_of_one_le₀ ht1'
  have hmut : (mu : ℝ) * (t : ℝ) = 1 := inv_mul_cancel₀ htpos.ne'
  have hsqrt : Real.sqrt (mu : ℝ) * Real.sqrt (t : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by positivity), hmut, Real.sqrt_one]
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hθ : (0 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [hd0]
  set ℓ : ℝ := crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (t : ℝ) with hℓ
  have hℓeq : crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (mu : ℝ)⁻¹ = ℓ := by
    simp only [mu, inv_inv, hℓ]
  obtain ⟨hℓ1, -⟩ := crudeMomL_ell_ge Rb.two_le_Kc hθ ht1'
  set a : ℝ := (crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n * ℓ) ^ (2 * Rb.n) with ha
  have hcut1 := one_le_crudeMomL_cut (d := d) A.nu Rb.c0 Rb.amp Rb.n
  have ha1 : 1 ≤ a := one_le_pow₀ (by nlinarith only [hcut1, hℓ1])
  have ha0 : 0 ≤ a := by linarith only [ha1]
  set κ : ℝ := crudeMomL_kap d A.nu Rb.c0 Rb.n with hκdef
  have hκ : 0 < κ := crudeMomL_kap_pos A.hnu Rb.c0_nonneg Rb.n
  have hB0 := crudeMomL_budget_nonneg κ
  have he0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hlevel : ∀ s : ℝ, a < s →
      (R.kernelSemigroup t 0) {z | s < dist z 0 / (11 * Real.sqrt (t : ℝ))} ≤
        ENNReal.ofReal (2 * Real.exp 1 * Real.exp (-(κ * Real.sqrt s))) := by
    intro s hsa
    have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one (ha1.trans hsa.le)
    have hr : 0 < Real.sqrt (t : ℝ) * s := mul_pos hsqt hs0
    have hscale : Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) = s := by
      rw [← mul_assoc, hsqrt, one_mul]
    have hrs : (crudeMomL_cut d A.nu Rb.c0 Rb.amp Rb.n *
        crudeMomL_ell Rb.Kc (2 * (d : ℝ)) (mu : ℝ)⁻¹) ^ (2 * Rb.n) ≤
        Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) := by
      rw [hscale, hℓeq]; exact hsa.le
    have htail := Rb.crudeMomL_tail_at_origin R hcons hid mu hmu1 hmut hr hrs
    rw [hscale] at htail
    refine le_trans (measure_mono ?_) htail
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right,
      not_lt] at hz ⊢
    rw [lt_div_iff₀ (by positivity)] at hz
    nlinarith only [hz, hsqt, hs0]
  have hint : ∫⁻ s in Set.Ioi a, ENNReal.ofReal
      ((2 * Real.exp 1 * Real.exp (-(κ * Real.sqrt s))) * s ^ 3) ≤
      ENNReal.ofReal (2 * Real.exp 1 * crudeMomL_budget κ) := by
    have h2e : (0 : ℝ) ≤ 2 * Real.exp 1 := by positivity
    have hrw : ∀ s : ℝ, ENNReal.ofReal
        ((2 * Real.exp 1 * Real.exp (-(κ * Real.sqrt s))) * s ^ 3) =
        ENNReal.ofReal (2 * Real.exp 1) *
          ENNReal.ofReal (Real.exp (-(κ * Real.sqrt s)) * s ^ 3) := by
      intro s
      rw [← ENNReal.ofReal_mul h2e, mul_assoc]
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul h2e]
    gcongr
    calc ∫⁻ s in Set.Ioi a, ENNReal.ofReal (Real.exp (-(κ * Real.sqrt s)) * s ^ 3)
        ≤ ∫⁻ s in Set.Ioi (1 : ℝ), ENNReal.ofReal (Real.exp (-(κ * Real.sqrt s)) * s ^ 3) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi ha1)
      _ = ENNReal.ofReal (crudeMomL_budget κ) := by
          unfold crudeMomL_budget
          rw [ENNReal.ofReal_toReal (crudeMomL_lintegral_cube_ne_top hκ)]
  have : IsProbabilityMeasure (R.kernelSemigroup t 0) := ⟨hcons t 0⟩
  have hcake := crudeMom_lintegral_edist_pow_le (nu := R.kernelSemigroup t 0)
    (le_of_eq measure_univ) (0 : Vec d) (c := 11 * Real.sqrt (t : ℝ)) (by positivity) ha0
    (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1 * crudeMomL_budget κ)
    (psi := fun s ↦ 2 * Real.exp 1 * Real.exp (-(κ * Real.sqrt s)))
    (fun s ↦ mul_nonneg (by positivity) (Real.exp_pos _).le) hlevel hint
  refine hcake.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc4 : (11 * Real.sqrt (t : ℝ)) ^ 4 = 14641 * (t : ℝ) ^ 2 := by
    have : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := by
      rw [show Real.sqrt (t : ℝ) ^ 4 = (Real.sqrt (t : ℝ) ^ 2) ^ 2 by ring,
        Real.sq_sqrt htpos.le]
    rw [mul_pow, this]
    norm_num
  rw [hc4]
  apply le_of_eq
  ring

end

end SuperdiffusionCLT.Section8
