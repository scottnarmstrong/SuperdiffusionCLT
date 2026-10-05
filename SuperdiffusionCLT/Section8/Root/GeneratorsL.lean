/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.GeneratorsK
public import SuperdiffusionCLT.Section8.Prereq.DomainIdentificationB
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApiB

/-!
# Limits along `ε → 0⁺` for the approximate corrector

* `gen_scale_ratio_tendsto`: `opScale(ε/ρ) / opScale(ε) → 1`;
* `gen_logpow_tendsto`: `|log(ε/ρ)|^{-α} → 0`;
* `gen_ep_contDiff`, `gen_divForm_isC0`: `L^ε u ∈ C₀` for a smooth compactly supported `u`.
-/

@[expose] public section

open Homogenization MeasureTheory Filter Topology SuperdiffusionCLT.Section6
open scoped ENNReal Pointwise Matrix.Norms.Elementwise

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem gen_nhdsGT_div (ρ : ℝ) (hρ : 0 < ρ) :
    Tendsto (fun ε : ℝ => ε / ρ) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have := (continuous_id.div_const ρ).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hρ

theorem gen_negLog_tendsto : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
  tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

theorem gen_logpow_tendsto {ρ α : ℝ} (hρ : 0 < ρ) (hα : 0 < α) :
    Tendsto (fun ε : ℝ => |Real.log (ε / ρ)| ^ (-α)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => |Real.log (ε / ρ)|) (𝓝[>] 0) atTop :=
    tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp (gen_nhdsGT_div ρ hρ))
  exact (tendsto_rpow_neg_atTop hα).comp h1

theorem gen_scale_ratio_tendsto {cs ρ : ℝ} (hcs : 0 < cs) (hρ : 0 < ρ) :
    Tendsto (fun ε : ℝ => opScale cs (ε / ρ) / opScale cs ε) (𝓝[>] 0) (𝓝 1) := by
  have hL := gen_negLog_tendsto
  set c : ℝ := Real.log ρ with hc
  have hr : Tendsto (fun ε : ℝ => (1 + c / (-Real.log ε))⁻¹) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ε : ℝ => c / (-Real.log ε)) (𝓝[>] 0) (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hL
    have := (tendsto_const_nhds.add h1).inv₀ (by norm_num : (1 + 0 : ℝ) ≠ 0)
    simpa using this
  have hr2 : Tendsto (fun ε : ℝ => ((1 + c / (-Real.log ε))⁻¹) ^ ((1 : ℝ) / 2)) (𝓝[>] 0)
      (𝓝 1) := by
    have := hr.rpow_const (p := (1 : ℝ) / 2) (Or.inr (by norm_num))
    simpa using this
  refine hr2.congr' ?_
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε < min 1 ρ := by
    have : Set.Iio (min 1 ρ) ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds (lt_min one_pos hρ)
    exact eventually_nhdsWithin_of_eventually_nhds this
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε0
  have hε0' : 0 < ε := hε0
  have hε1 : ε < 1 := lt_of_lt_of_le hε (min_le_left _ _)
  have hερ : ε < ρ := lt_of_lt_of_le hε (min_le_right _ _)
  have hlog : Real.log ε < 0 := Real.log_neg hε0' hε1
  have hε'1 : ε / ρ < 1 := by rw [div_lt_one hρ]; exact hερ
  have hlog' : Real.log (ε / ρ) < 0 := Real.log_neg (div_pos hε0' hρ) hε'1
  have e1 : |Real.log ε| = -Real.log ε := abs_of_neg hlog
  have e2 : |Real.log (ε / ρ)| = -Real.log ε + c := by
    rw [abs_of_neg hlog', Real.log_div hε0'.ne' hρ.ne']; ring
  unfold opScale
  rw [e1, e2]
  have hA : 0 < 2 * cs * (-Real.log ε) := by have := neg_pos.2 hlog; positivity
  have hB : 0 < 2 * cs * (-Real.log ε + c) := by
    have := e2 ▸ abs_pos.2 hlog'.ne; positivity
  have hB' : 0 < -Real.log ε + c := by
    have := e2 ▸ abs_pos.2 hlog'.ne; exact this
  have hA' : 0 < -Real.log ε := neg_pos.2 hlog
  have hp : ∀ x : ℝ, 0 < x → 0 < x ^ ((1 : ℝ) / 2) := fun x hx => Real.rpow_pos_of_pos hx _
  have key : (1 / 2 * ((2 * cs * (-Real.log ε + c)) ^ ((1 : ℝ) / 2))⁻¹) /
      (1 / 2 * ((2 * cs * (-Real.log ε)) ^ ((1 : ℝ) / 2))⁻¹) =
      ((2 * cs * (-Real.log ε)) ^ ((1 : ℝ) / 2)) / ((2 * cs * (-Real.log ε + c)) ^ ((1 : ℝ) / 2)) := by
    have h1 := (hp _ hA).ne'
    have h2 := (hp _ hB).ne'
    field_simp
  have e3 : (1 + c / (-Real.log ε))⁻¹ =
      (2 * cs * (-Real.log ε)) / (2 * cs * (-Real.log ε + c)) := by
    rw [one_add_div hA'.ne', inv_div, mul_div_mul_left _ _ (by positivity : (2 * cs) ≠ 0)]
  rw [key, ← Real.div_rpow hA.le hB.le, e3]

theorem gen_ep_contDiff (nu : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε : ℝ) (hS : ContDiff ℝ 2 (fullStreamRecentered omega)) (i j : Fin d) :
    ContDiff ℝ 2 fun y : Vec d => epCoeff nu omega ε y i j := by
  have h1 : ContDiff ℝ 2 fun y : Vec d => fullStreamRecentered omega (ε⁻¹ • y) :=
    hS.comp (contDiff_const_smul _)
  have h2 : ContDiff ℝ 2 fun y : Vec d => fullStreamRecentered omega (ε⁻¹ • y) i j :=
    contDiff_pi.1 (contDiff_pi.1 h1 i) j
  simp only [epCoeff, fullCoefficientRecentered, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.mul contDiff_const |>.add h2

theorem gen_divForm_isC0 (nu c : ℝ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (ε : ℝ) (hS : ContDiff ℝ 2 (fullStreamRecentered omega)) {u : Vec d → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hc : HasCompactSupport u) :
    IsC0Function (divForm c (epCoeff nu omega ε) u) := by
  have h1 : divForm c (epCoeff nu omega ε) u =
      fun x => c * divForm 1 (epCoeff nu omega ε) u x := by
    funext x; simp [divForm]
  have hcont : Continuous (divForm c (epCoeff nu omega ε) u) := by
    rw [h1]
    exact continuous_const.mul (domId_divForm_continuous
      (fun i j => (gen_ep_contDiff nu omega ε hS i j).of_le (by norm_num))
      (hu.of_le (by simp)))
  refine gen_isC0_of_compactSupport hcont (HasCompactSupport.intro hc.isCompact fun x hx => ?_)
  have h0 : u =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [divForm_congr_of_eventuallyEq c (a' := epCoeff nu omega ε) (u' := 0) Filter.EventuallyEq.rfl h0]
  simp [divForm]

end SuperdiffusionCLT.Section8
