/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RootCarriers
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Analytic.Change.DilationB

/-!
# The `H^{-1}` seminorm of a vector field

Facts about `hMinusOneVec`: the bound of the seminorm of a gradient by the normalized `L²` norm
of the function (integration by parts against `H¹₀`), the triangle inequality, homogeneity,
and the behaviour under dilation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal NNReal Pointwise

variable {d : ℕ}

/-- Hölder pairing of two `L²` functions on a set, in `ℝ≥0∞`. -/
theorem rc_pairing_le (U : Set (Vec d)) (h u : Vec d → ℝ) (hh : MemLp h 2 (volume.restrict U))
    (hu : MemLp u 2 (volume.restrict U)) :
    ENNReal.ofReal |∫ x in U, h x * u x| ≤
      eLpNorm h 2 (volume.restrict U) * eLpNorm u 2 (volume.restrict U) := by
  have h1 : ENNReal.ofReal |∫ x in U, h x * u x| ≤ ∫⁻ x in U, ‖h x * u x‖ₑ := by
    rw [← Real.enorm_eq_ofReal_abs]
    exact enorm_integral_le_lintegral_enorm _
  have h2 : eLpNorm (fun x => h x * u x) 1 (volume.restrict U) ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm h 2 (volume.restrict U) * eLpNorm u 2 (volume.restrict U) :=
    eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) (fun a b : ℝ => a * b) 1
      (by fun_prop) hh.aestronglyMeasurable hu.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  rw [eLpNorm_one_eq_lintegral_enorm (f := fun x => h x * u x)
    (hh.aestronglyMeasurable.mul hu.aestronglyMeasurable)] at h2
  simpa using h1.trans h2

/-- Continuity of the `L²` pairing along `L²`-convergent sequences. -/
theorem rc_tendsto_integral_mul (U : Set (Vec d)) {h f : Vec d → ℝ} {fn : ℕ → Vec d → ℝ}
    (hh : MemLp h 2 (volume.restrict U)) (hf : MemLp f 2 (volume.restrict U))
    (hfn : ∀ n, MemLp (fn n) 2 (volume.restrict U))
    (hlim : Filter.Tendsto (fun n => eLpNorm (fun x => fn n x - f x) 2 (volume.restrict U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, h x * fn n x) Filter.atTop
      (nhds (∫ x in U, h x * f x)) := by
  have hdiff : ∀ n, ENNReal.ofReal |(∫ x in U, h x * fn n x) - ∫ x in U, h x * f x| ≤
      eLpNorm h 2 (volume.restrict U) * eLpNorm (fun x => fn n x - f x) 2 (volume.restrict U) := by
    intro n
    have hs : (∫ x in U, h x * fn n x) - ∫ x in U, h x * f x =
        ∫ x in U, h x * (fn n x - f x) := by
      have := integral_sub (hh.integrable_mul (hfn n)) (hh.integrable_mul hf)
      simp only [Pi.mul_apply] at this
      rw [← this]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hs]
    exact rc_pairing_le U h _ hh ((hfn n).sub hf)
  have hup : Filter.Tendsto (fun n => eLpNorm h 2 (volume.restrict U) *
      eLpNorm (fun x => fn n x - f x) 2 (volume.restrict U)) Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hlim (Or.inr hh.eLpNorm_ne_top)
  have h0 : Filter.Tendsto (fun n => ENNReal.ofReal
      |(∫ x in U, h x * fn n x) - ∫ x in U, h x * f x|) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) hdiff
  rw [← ENNReal.ofReal_zero] at h0
  have h1 : Filter.Tendsto (fun n => |(∫ x in U, h x * fn n x) - ∫ x in U, h x * f x|)
      Filter.atTop (nhds 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp h0
    simpa [Function.comp_def, abs_nonneg] using this
  have h2 := (tendsto_zero_iff_abs_tendsto_zero _).2 h1
  simpa using h2.add_const (∫ x in U, h x * f x)

/-- Integration by parts of an `H¹` function against an `H¹₀` function: `∫ ∂ᵢw ψ = -∫ w ∂ᵢψ`. -/
theorem rc_ibp {U : Set (Vec d)} (w : H1Function U) (ψ : H10Function U) (i : Fin d) :
    ∫ x in U, w.grad x i * ψ.toH1Function.toFun x =
      -∫ x in U, w.toFun x * ψ.toH1Function.grad x i := by
  have hw : MemLp w.toFun 2 (volume.restrict U) := w.memL2
  have hgw : MemLp (fun x => w.grad x i) 2 (volume.restrict U) := w.gradMemL2 i
  have hψ : MemLp ψ.toH1Function.toFun 2 (volume.restrict U) := ψ.toH1Function.memL2
  have hgψ : MemLp (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U) :=
    ψ.toH1Function.gradMemL2 i
  have hcont : ∀ n, Continuous (fun x => fderiv ℝ (ψ.approx n) x (basisVec i)) := fun n =>
    ((ψ.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  have happ : ∀ n, MemLp (ψ.approx n) 2 (volume.restrict U) := fun n =>
    ((ψ.approx_smooth n).continuous).memLp_of_hasCompactSupport (ψ.approx_hasCompactSupport n)
  have hder : ∀ n, MemLp (fun x => fderiv ℝ (ψ.approx n) x (basisVec i)) 2
      (volume.restrict U) := fun n =>
    (hcont n).memLp_of_hasCompactSupport
      ((ψ.approx_hasCompactSupport n).fderiv_apply ℝ (basisVec i))
  have h1 := rc_tendsto_integral_mul U hw hgψ hder (ψ.tendsto_approx_grad i)
  have h2 := rc_tendsto_integral_mul U hgw hψ happ ψ.tendsto_approx
  have h3 : ∀ n, ∫ x in U, w.toFun x * fderiv ℝ (ψ.approx n) x (basisVec i) =
      -∫ x in U, w.grad x i * ψ.approx n x := fun n =>
    w.hasWeakGradient i (ψ.approx n) (ψ.approx_smooth n) (ψ.approx_hasCompactSupport n)
      (ψ.approx_support_subset n)
  have h4 := h2.neg
  have h5 : (fun n => -∫ x in U, w.grad x i * ψ.approx n x) =
      fun n => ∫ x in U, w.toFun x * fderiv ℝ (ψ.approx n) x (basisVec i) :=
    funext fun n => (h3 n).symm
  rw [h5] at h4
  have h6 := tendsto_nhds_unique h1 h4
  linarith only [h6]

/-- Normalized `L²` norm in terms of the plain one, for a set of positive finite measure. -/
theorem rc_lpBar_two_eq {E : Type*} [NormedAddCommGroup E] (V : Set (Vec d)) (F : Vec d → E)
    (hF : AEStronglyMeasurable F (volume.restrict V)) :
    lpBar V 2 F = (volume V)⁻¹ ^ (1 / 2 : ℝ) * eLpNorm F 2 (volume.restrict V) := by
  unfold lpBar
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num) F]
  · simp [one_div]
  · exact hF

theorem rc_sqrt_inv_mul_self (m : ℝ≥0∞) (h0 : m ≠ 0) (ht : m ≠ ⊤) :
    (m⁻¹ ^ (1 / 2 : ℝ)) * (m⁻¹ ^ (1 / 2 : ℝ)) = ENNReal.ofReal m.toReal⁻¹ := by
  have hi0 : m⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ht
  have hit : m⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr h0
  rw [← ENNReal.rpow_add _ _ hi0 hit, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
    ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 ht),
    ENNReal.ofReal_toReal ht]

theorem rc_conj_two : (2 : ℝ≥0∞).conjExponent = 2 := by
  have h : (2 : ℝ≥0∞) = 1 + 1 := one_add_one_eq_two.symm
  unfold ENNReal.conjExponent
  rw [show (2 : ℝ≥0∞) - 1 = 1 by
    rw [h]; exact ENNReal.add_sub_cancel_left ENNReal.one_ne_top]
  simp only [inv_one]
  exact h.symm

/-- A coordinate of an `H¹` gradient is controlled by the gradient in the sup norm. -/
theorem rc_lpBar_coord_le (V : Set (Vec d)) (G : Vec d → Vec d) (i : Fin d)
    (hG : AEStronglyMeasurable G (volume.restrict V)) :
    lpBar V 2 (fun x => G x i) ≤ lpBar V 2 G := by
  unfold lpBar
  refine eLpNorm_mono_ae
    (((continuous_apply i).comp_aestronglyMeasurable hG).smul_measure _)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (norm_le_pi_norm (G x) i)

/-- **The `H^{-1}` seminorm of a partial derivative** is at most the normalized `L²` norm of
the function (integration by parts against `H¹₀`), on a set of positive finite measure. -/
theorem rc_wMinusOneBar_partial_le (U : Set (Vec d)) (h0 : volume U ≠ 0) (ht : volume U ≠ ⊤)
    (w : H1Function U) (i : Fin d) :
    wMinusOneBar U 2 (fun x => w.grad x i) ≤ lpBar U 2 w.toFun := by
  have hw : MemLp w.toFun 2 (volume.restrict U) := w.memL2
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  have hgψ : AEStronglyMeasurable ψ.toH1Function.grad (volume.restrict U) :=
    AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.mpr fun j =>
      (ψ.toH1Function.gradMemL2 j).aestronglyMeasurable.aemeasurable)
  have hci : MemLp (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U) :=
    ψ.toH1Function.gradMemL2 i
  rw [rc_conj_two] at hψ
  have hψ' : (volume U)⁻¹ ^ (1 / 2 : ℝ) *
      eLpNorm (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U) ≤ 1 := by
    rw [← rc_lpBar_two_eq U _ hci.aestronglyMeasurable]
    exact (rc_lpBar_coord_le U _ i hgψ).trans hψ
  rw [rc_ibp w ψ i, abs_mul, abs_neg,
    ENNReal.ofReal_mul (abs_nonneg _), abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg),
    rc_lpBar_two_eq U _ hw.aestronglyMeasurable, ← rc_sqrt_inv_mul_self _ h0 ht]
  set k : ℝ≥0∞ := (volume U)⁻¹ ^ (1 / 2 : ℝ) with hk
  calc k * k * ENNReal.ofReal |∫ x in U, w.toFun x * ψ.toH1Function.grad x i|
      ≤ k * k * (eLpNorm w.toFun 2 (volume.restrict U) *
          eLpNorm (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U)) := by
        gcongr
        exact rc_pairing_le U _ _ hw hci
    _ = (k * eLpNorm (fun x => ψ.toH1Function.grad x i) 2 (volume.restrict U)) *
          (k * eLpNorm w.toFun 2 (volume.restrict U)) := by ring
    _ ≤ 1 * (k * eLpNorm w.toFun 2 (volume.restrict U)) := by gcongr
    _ = k * eLpNorm w.toFun 2 (volume.restrict U) := one_mul _

/-- **`‖∇w‖_{H^{-1}(U)} ≤ d ‖w‖_{L̲²(U)}`** for `w ∈ H¹(U)` (in particular `w ∈ H¹₀(U)`). -/
theorem rc_hMinusOneVec_grad_le (U : Set (Vec d)) (h0 : volume U ≠ 0) (ht : volume U ≠ ⊤)
    (w : H1Function U) :
    hMinusOneVec U w.grad ≤ (d : ℝ≥0∞) * lpBar U 2 w.toFun := by
  unfold hMinusOneVec
  calc ∑ i : Fin d, wMinusOneBar U 2 (fun x => w.grad x i)
      ≤ ∑ _i : Fin d, lpBar U 2 w.toFun :=
        Finset.sum_le_sum fun i _ => rc_wMinusOneBar_partial_le U h0 ht w i
    _ = (d : ℝ≥0∞) * lpBar U 2 w.toFun := by simp

/-- The `H^{-1}` seminorm of the zero field vanishes. -/
theorem rc_hMinusOneVec_zero (U : Set (Vec d)) : hMinusOneVec U (fun _ => 0) = 0 := by
  simp [hMinusOneVec, wMinusOneBar]

/-- Witness: the unit cube's standard function `0` is an `H¹` function with gradient `0`, and
the bound reads `0 ≤ d * 0` on a set of positive finite measure. -/
example : hMinusOneVec (Set.univ.pi fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1)
    (fun _ => 0) ≤ (2 : ℝ≥0∞) * 0 := by
  rw [rc_hMinusOneVec_zero]
  simp

end SuperdiffusionCLT.Section7
