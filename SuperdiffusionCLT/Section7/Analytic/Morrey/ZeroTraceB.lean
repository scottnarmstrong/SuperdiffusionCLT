/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.W1p.ZeroExtensionGraph
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import SuperdiffusionCLT.Section7.Analytic.Morrey.ZeroTrace
public import Homogenization.Sobolev.Foundations.AxisCube
public import Homogenization.Sobolev.H1.Algebra.H10Function

@[expose] public section

open MeasureTheory Homogenization Convolution

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem pow_two_mul_le {L e : ℝ} (hL : 0 < L) (he : e ≤ 1) :
    (2 * L) ^ e ≤ 2 * L ^ e := by
  rw [Real.mul_rpow (by norm_num) hL.le]
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hL.le _)
  calc (2 : ℝ) ^ e ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
    _ = 2 := Real.rpow_one 2

/-- **Morrey's inequality for zero-trace functions.** -/
theorem h10_essSup_le_morrey (hd0 : 0 < d) {z : Vec d} {L : ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) (hUc : U ⊆ axisCube z L) (φ : H10Function U) {p : ℝ} (hp : (d : ℝ) < p) :
    eLpNorm φ.toFun ⊤ (volume.restrict U) ≤
      ENNReal.ofReal (4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * L ^ (1 - (d : ℝ) / p)) *
        eLpNorm (fun x => ‖φ.grad x‖) (ENNReal.ofReal p) (volume.restrict U) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hp1 : 1 < p := by linarith only [hd1, hp]
  have hp0 : 0 < p := by linarith only [hp1]
  have hdp : (d : ℝ) / p < 1 := (div_lt_one hp0).2 hp
  have hden : 0 < 1 - (d : ℝ) / p := by linarith only [hdp]
  by_cases hL : L ≤ 0
  · have hUe : U = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h := hUc hx ⟨0, hd0⟩ (Set.mem_univ _)
      simp only [Set.mem_Ioo] at h
      linarith only [h.1, h.2, hL]
    subst hUe
    rw [Measure.restrict_empty, eLpNorm_measure_zero]
    simp
  replace hL := not_le.1 hL
  set E := eLpNorm (fun x => ‖φ.grad x‖) (ENNReal.ofReal p) (volume.restrict U) with hE
  set c : ℝ := 4 * (d : ℝ) * (1 / (1 - (d : ℝ) / p)) * L ^ (1 - (d : ℝ) / p) with hc
  have hcpos : 0 < c := by
    have : 0 < L ^ (1 - (d : ℝ) / p) := Real.rpow_pos_of_pos hL _
    rw [hc]; positivity
  by_cases hEt : E = ⊤
  · rw [hEt, ENNReal.mul_top (ENNReal.ofReal_pos.2 hcpos).ne']; exact le_top
  have hmeas := hU.measurableSet
  set u0 := φ.zeroExtension with hu0def
  set Du := φ.zeroExtensionGrad with hDudef
  have hw : HasWeakGradientOn Set.univ u0 Du := φ.hasWeakGradientOn_univ_zeroExtension hmeas
  have hu0 : MemLp u0 2 volume := φ.memLp_zeroExtension hmeas φ.toH1Function.memL2
  have hDu : ∀ i, MemLp (fun x => Du x i) 2 volume := by
    intro i
    have := φ.gradMemLp_zeroExtensionGrad hmeas φ.toH1Function.gradMemL2 i
    simpa only [MemLpOn, Measure.restrict_univ] using this
  have hsupp : ∀ x, x ∉ axisCube z L → u0 x = 0 := fun x hx =>
    φ.zeroExtension_apply_of_not_mem fun h => hx (hUc h)
  have hGeq : (fun x => (d : ℝ) * ‖Du x‖) = U.indicator (fun x => (d : ℝ) • ‖φ.grad x‖) := by
    ext x
    by_cases hx : x ∈ U
    · simp [Set.indicator_of_mem hx, hDudef, φ.zeroExtensionGrad_apply_of_mem hx]
    · simp [Set.indicator_of_notMem hx, hDudef, φ.zeroExtensionGrad_apply_of_not_mem hx]
  have hGnorm : eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume =
      ENNReal.ofReal d * E := by
    rw [hGeq, eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    have : (fun x => (d : ℝ) • ‖φ.grad x‖) = (d : ℝ) • fun x => ‖φ.grad x‖ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal (Nat.cast_nonneg d)]
  have hG : MemLp (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume := by
    rw [memLp_iff, hGnorm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hEt)
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hεpos : ∀ n, 0 < unitConvexApproxScale n := fun n => by
    simp only [unitConvexApproxScale]; positivity
  have hr : 0 < L / 4 := by linarith only [hL]
  have hconv := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel hρ
    (p := 2) (g := u0) (by norm_num) (by simp) hu0 hr tendsto_unitConvexApproxScale_zero
    (Filter.Eventually.of_forall hεpos)
  have hmeasure : TendstoInMeasure volume (fun n x =>
      (scaledConvexApproxKernel unitConvexApproxKernel (unitConvexApproxScale n * (L / 4)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) x) Filter.atTop u0 :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, -, hae⟩ := hmeasure.exists_seq_tendsto_ae
  have hbound : ∀ n, ∀ x ∈ axisCube (z - fun _ => L / 2) (2 * L),
      |(scaledConvexApproxKernel unitConvexApproxKernel (unitConvexApproxScale n * (L / 4)) ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] u0) x| ≤
      2 * (1 / (1 - (d : ℝ) / p)) * (2 * L) ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume).toReal := by
    intro n x hx
    exact abs_mollify_le hd0 hρ (mul_pos (hεpos n) hr) hL
      (by nlinarith only [unitConvexApproxScale_le_one n, hL]) hu0 hDu hw hsupp hp hG hx
  set B : ℝ := 2 * (1 / (1 - (d : ℝ) / p)) * (2 * L) ^ (1 - (d : ℝ) / p) *
    (eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume).toReal with hB
  have hUK : U ⊆ axisCube (z - fun _ => L / 2) (2 * L) := by
    intro x hx j _
    have h := hUc hx j (Set.mem_univ j)
    simp only [Set.mem_Ioo, Pi.sub_apply] at h ⊢
    constructor <;> linarith only [h.1, h.2, hL]
  have hae2 : ∀ᵐ x ∂(volume.restrict U), ‖φ.toFun x‖ ≤ B := by
    rw [ae_restrict_iff' hmeas]
    filter_upwards [hae] with x hx hxU
    have hxu : u0 x = φ.toFun x := φ.zeroExtension_apply_of_mem hxU
    rw [← hxu, Real.norm_eq_abs]
    exact le_of_tendsto (hx.abs) (Filter.Eventually.of_forall fun n =>
      hbound (ns n) x (hUK hxU))
  rw [eLpNorm_exponent_top]
  refine (eLpNormEssSup_le_of_ae_bound hae2).trans ?_
  have hBle : B ≤ c * E.toReal := by
    have hGr : (eLpNorm (fun x => (d : ℝ) * ‖Du x‖) (ENNReal.ofReal p) volume).toReal =
        d * E.toReal := by
      rw [hGnorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg d)]
    rw [hB, hGr, hc]
    have h2 := pow_two_mul_le hL (e := 1 - (d : ℝ) / p) (by linarith only [div_nonneg (Nat.cast_nonneg d) hp0.le])
    have hE0 : 0 ≤ E.toReal := ENNReal.toReal_nonneg
    have hq : 0 ≤ 1 / (1 - (d : ℝ) / p) := by positivity
    calc 2 * (1 / (1 - (d : ℝ) / p)) * (2 * L) ^ (1 - (d : ℝ) / p) * (d * E.toReal)
        ≤ 2 * (1 / (1 - (d : ℝ) / p)) * (2 * L ^ (1 - (d : ℝ) / p)) * (d * E.toReal) := by
          gcongr
      _ = _ := by ring
  calc ENNReal.ofReal B ≤ ENNReal.ofReal (c * E.toReal) := ENNReal.ofReal_le_ofReal hBle
    _ = ENNReal.ofReal c * E := by
        rw [ENNReal.ofReal_mul hcpos.le, ENNReal.ofReal_toReal hEt]
  · exact φ.toH1Function.memL2.aestronglyMeasurable

/-- Satisfiability witness: the hypotheses hold for `d = 1`, `p = 2`, the unit interval and the
zero function. -/
example : eLpNorm (0 : H10Function (axisCube (0 : Vec 1) 1)).toFun ⊤
      (volume.restrict (axisCube (0 : Vec 1) 1)) ≤
    ENNReal.ofReal (4 * ((1 : ℕ) : ℝ) * (1 / (1 - ((1 : ℕ) : ℝ) / 2)) * (1 : ℝ) ^ (1 - ((1 : ℕ) : ℝ) / 2)) *
      eLpNorm (fun x => ‖(0 : H10Function (axisCube (0 : Vec 1) 1)).grad x‖) (ENNReal.ofReal 2)
        (volume.restrict (axisCube (0 : Vec 1) 1)) :=
  h10_essSup_le_morrey (d := 1) one_pos (isOpen_axisCube _ _) subset_rfl _ (by norm_num)

end SuperdiffusionCLT.Section7
