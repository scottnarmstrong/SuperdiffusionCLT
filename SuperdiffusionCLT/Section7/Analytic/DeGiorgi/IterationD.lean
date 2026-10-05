/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Sobolev
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.CaccioppoliB

/-!
# Sobolev and Hölder on a cube: the quadratic form used in the De Giorgi step

For `w ∈ H¹₀(Q)` vanishing off a set `E ⊆ Q`:
`∫_Q w² ≤ C L^{2 d/2^* + 2 - d} (∫_Q |∇w|²) |E|^{1 - 2/2^*}`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem eLpNorm_two_toReal_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h0 : 0 ≤ ∫ a, ‖f a‖ ^ (2 : ℝ≥0∞).toReal ∂μ :=
    integral_nonneg fun x => by positivity
  rw [ENNReal.toReal_ofReal (by positivity)]
  have e2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [e2] at h0 ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

theorem memLp_eucNorm_grad {U : Set (Vec d)} (u : H1Function U) :
    MemLp (fun x => eucNorm (u.grad x)) 2 (volume.restrict U) := by
  have hm : AEStronglyMeasurable (fun x => eucNorm (u.grad x)) (volume.restrict U) := by
    unfold eucNorm vecNormSq vecDot
    refine Real.continuous_sqrt.comp_aestronglyMeasurable ?_
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (u.gradMemL2 i).aestronglyMeasurable.mul (u.gradMemL2 i).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have : (fun x => eucNorm (u.grad x) ^ 2) = fun x => ∑ i, u.grad x i ^ 2 := by
    funext x
    rw [eucNorm_sq]
    unfold vecNormSq vecDot
    exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [this]
  exact integrable_finsetSum _ fun i _ => (u.gradMemL2 i).integrable_sq

theorem integral_eucNorm_grad_sq {U : Set (Vec d)} (u : H1Function U) :
    ∫ x in U, eucNorm (u.grad x) ^ 2 = ∫ x in U, vecNormSq (u.grad x) :=
  integral_congr_ae (Filter.Eventually.of_forall fun _ => eucNorm_sq _)

theorem rpow_sq_eq {L : ℝ} (hL : 0 < L) (x : ℝ) : (L ^ x) ^ 2 = L ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
  norm_num
  ring_nf

/-- Sobolev at `2^*` combined with Hölder on the set where `w` does not vanish. -/
theorem sobolev_holder_sq (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ (w : H10Function (axisCube z L))
      (E : Set (Vec d)), E ⊆ axisCube z L → Function.support w.toH1Function.toFun ⊆ E →
      ∫ x in axisCube z L, w.toH1Function.toFun x ^ 2 ≤
        C * L ^ (2 * ((d : ℝ) / sobStar d) + 2 - d) *
          (∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x)) *
          (volume E).toReal ^ (1 - 2 / sobStar d) := by
  obtain ⟨C0, hC0, hS⟩ := cube_sobolev_sobStar hd
  refine ⟨C0 ^ 2, by positivity, fun z L hL w E hEQ hsupp => ?_⟩
  have hp : 2 < sobStar d := two_lt_sobStar hd
  have hp0 : 0 < sobStar d := by linarith only [hp]
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hQm : MeasurableSet (axisCube z L) := hQo.measurableSet
  set μ : Measure (Vec d) := volume.restrict (axisCube z L) with hμ
  have hconv := isOpenBoundedConvexDomain_axisCube z L
  have hfin : IsFiniteMeasure μ := hconv.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hμE : μ E = volume E := by
    rw [hμ, Measure.restrict_apply' hQm, Set.inter_eq_left.2 hEQ]
  have hVlt : volume E < ⊤ := by
    rw [← hμE]; exact measure_lt_top μ E
  set p := sobStar d with hpdef
  set κ : ℝ := 1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal with hκ
  have hκ' : κ = 1 / 2 - 1 / p := by
    rw [hκ, ENNReal.toReal_ofReal hp0.le]; norm_num
  have hκ0 : 0 ≤ κ := by
    rw [hκ']
    have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp.le
    linarith only [this]
  have hwm : AEStronglyMeasurable w.toH1Function.toFun μ :=
    w.toH1Function.memL2.aestronglyMeasurable
  -- Hölder on a measurable hull of `E`
  set S : Set (Vec d) := toMeasurable μ E with hSdef
  have hSm : MeasurableSet S := measurableSet_toMeasurable μ E
  have hSμ : μ S = μ E := measure_toMeasurable E
  have hsuppS : Function.support w.toH1Function.toFun ⊆ S := hsupp.trans (subset_toMeasurable μ E)
  have hH1 : eLpNorm w.toH1Function.toFun 2 μ = eLpNorm w.toH1Function.toFun 2 (μ.restrict S) :=
    (eLpNorm_restrict_eq_of_support_subset hwm hsuppS).symm
  have hH2 : eLpNorm w.toH1Function.toFun 2 (μ.restrict S) ≤
      eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) (μ.restrict S) *
        (μ.restrict S) Set.univ ^ κ := by
    refine eLpNorm_le_eLpNorm_mul_rpow_measure_univ ?_ hwm.restrict
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal hp.le
  have hH3 : eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) (μ.restrict S) ≤
      eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hunivS : (μ.restrict S) Set.univ = μ E := by
    rw [Measure.restrict_apply_univ, hSμ]
  have hAH : eLpNorm w.toH1Function.toFun 2 μ ≤
      eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ * (μ E) ^ κ := by
    rw [hH1]
    refine hH2.trans ?_
    rw [hunivS]
    exact mul_le_mul_left hH3 _
  -- Sobolev
  have hSob := hS z L hL w
  set K : ℝ := L ^ ((d : ℝ) / p) * (C0 * L ^ (1 - (d : ℝ) / 2)) with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hb : eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ ≠ ⊤ :=
    (memLp_eucNorm_grad w.toH1Function).eLpNorm_ne_top
  have hP : eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal K * eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ := by
    have e1 : ENNReal.ofReal (L ^ ((d : ℝ) / p)) * ENNReal.ofReal (L ^ (-(d : ℝ) / p)) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hL]
      have : (d : ℝ) / p + -(d : ℝ) / p = 0 := by ring
      rw [this]; simp
    calc eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ
        = ENNReal.ofReal (L ^ ((d : ℝ) / p)) * (ENNReal.ofReal (L ^ (-(d : ℝ) / p)) *
            eLpNorm w.toH1Function.toFun (ENNReal.ofReal p) μ) := by
          rw [← mul_assoc, e1, one_mul]
      _ ≤ ENNReal.ofReal (L ^ ((d : ℝ) / p)) * (ENNReal.ofReal (C0 * L ^ (1 - (d : ℝ) / 2)) *
            eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ) := mul_le_mul_right hSob _
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have hVfin : (μ E) ≠ ⊤ := by rw [hμE]; exact hVlt.ne
  have hA : (eLpNorm w.toH1Function.toFun 2 μ).toReal ≤
      K * (eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ).toReal * (volume E).toReal ^ κ := by
    have h := hAH.trans (mul_le_mul_left hP ((μ E) ^ κ))
    have hfin2 : ENNReal.ofReal K * eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ *
        (μ E) ^ κ ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hb)
        (ENNReal.rpow_ne_top_of_nonneg hκ0 hVfin)
    have := ENNReal.toReal_mono hfin2 h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hK0, hμE,
      ← ENNReal.toReal_rpow] at this
  -- squares
  set A := (eLpNorm w.toH1Function.toFun 2 μ).toReal with hAdef
  set B := (eLpNorm (fun x => eucNorm (w.toH1Function.grad x)) 2 μ).toReal with hBdef
  set V := (volume E).toReal with hVdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hAsq : A ^ 2 = ∫ x in axisCube z L, w.toH1Function.toFun x ^ 2 :=
    eLpNorm_two_toReal_sq w.toH1Function.memL2
  have hBsq : B ^ 2 = ∫ x in axisCube z L, vecNormSq (w.toH1Function.grad x) := by
    rw [hBdef, eLpNorm_two_toReal_sq (memLp_eucNorm_grad w.toH1Function),
      integral_eucNorm_grad_sq w.toH1Function]
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hsq : A ^ 2 ≤ (K * B * V ^ κ) ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have hVκ : (V ^ κ) ^ 2 = V ^ (1 - 2 / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hV0, hκ']
    congr 1
    push_cast
    ring
  have hK2 : K ^ 2 = C0 ^ 2 * L ^ (2 * ((d : ℝ) / p) + 2 - d) := by
    rw [hKdef, mul_pow, mul_pow, rpow_sq_eq hL, rpow_sq_eq hL]
    have : (2 * ((d : ℝ) / p) + 2 - d) = 2 * ((d : ℝ) / p) + 2 * (1 - (d : ℝ) / 2) := by ring
    rw [this, Real.rpow_add hL]
    ring
  rw [← hAsq, ← hBsq]
  calc A ^ 2 ≤ (K * B * V ^ κ) ^ 2 := hsq
    _ = K ^ 2 * B ^ 2 * (V ^ κ) ^ 2 := by ring
    _ = _ := by rw [hK2, hVκ]

end SuperdiffusionCLT.Section7
