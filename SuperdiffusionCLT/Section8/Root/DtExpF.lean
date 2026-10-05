/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpE
public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsE

/-!
# The quenched second moment: removal of the stopping event

Cauchy-Schwarz against an indicator, the abstract removal of an exit event from first and second
moments, the mean stopped time, and the passage from fourth moments of the sup norm to the second
moment of the squared Euclidean length.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory MarkovProcess
open scoped Pointwise ENNReal NNReal Topology

/-- **Cauchy-Schwarz against an indicator.** -/
theorem dtExp_cs {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) (hf2 : Integrable (fun x => f x ^ 2) μ)
    {A : Set α} (hA : MeasurableSet A) :
    ∫ x, A.indicator f x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ.real A) := by
  have hmem : MemLp f 2 μ := (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).2 hf2
  have h1 : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 μ :=
    (memLp_const (1 : ℝ)).indicator hA
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := f) (g := A.indicator (fun _ => (1 : ℝ)))
    (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (by simpa using hmem) (by simpa using h1)
  have e1 : ∀ x, A.indicator f x = f x * A.indicator (fun _ => (1 : ℝ)) x := by
    intro x; by_cases hx : x ∈ A <;> simp [hx]
  simp_rw [e1]
  refine h.trans (le_of_eq ?_)
  have e2 : (∫ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) = Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow]; simp_rw [Real.rpow_two]
  have e3 : (∫ a, A.indicator (fun _ => (1 : ℝ)) a ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) =
      Real.sqrt (μ.real A) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    simp_rw [Real.rpow_two]
    have : ∀ a, A.indicator (fun _ => (1 : ℝ)) a ^ 2 = A.indicator (fun _ => (1 : ℝ)) a := by
      intro a; by_cases ha : a ∈ A <;> simp [ha]
    simp_rw [this]
    rw [integral_indicator hA]; simp
  rw [e2, e3]

theorem dtExp_vecNormSq_nonneg {d : ℕ} (y : Vec d) : 0 ≤ vecNormSq y := by
  unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem dtExp_abs_coord_le {d : ℕ} (y : Vec d) (i : Fin d) : |y i| ≤ Real.sqrt (vecNormSq y) := by
  refine Real.abs_le_sqrt ?_
  unfold vecNormSq vecDot
  have := Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)
  nlinarith only [this]

/-- **Removal of a stopping event.**  Abstract form: `X = Y` off a measurable event `A`, `Y` is
bounded in Euclidean length by `√R2`, and the squared length of `X` has a bounded second moment. -/
theorem dtExp_remove {d : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {X Y : α → Vec d} (hX : Measurable X) (hY : Measurable Y)
    {A : Set α} (hA : MeasurableSet A) (hXY : ∀ᵐ x ∂μ, x ∉ A → X x = Y x) {R2 : ℝ}
    (hR : ∀ᵐ x ∂μ, vecNormSq (Y x) ≤ R2) {m4 : ℝ}
    (h4 : Integrable (fun x => vecNormSq (X x) ^ 2) μ) (hm4 : ∫ x, vecNormSq (X x) ^ 2 ∂μ ≤ m4) :
    Integrable (fun x => vecNormSq (X x)) μ ∧ ∫ x, vecNormSq (X x) ∂μ ≤ Real.sqrt m4 ∧
    |∫ x, vecNormSq (X x) ∂μ - ∫ x, vecNormSq (Y x) ∂μ| ≤
      Real.sqrt m4 * Real.sqrt (μ.real A) + R2 * μ.real A ∧
    ∀ i : Fin d, |∫ x, X x i ∂μ - ∫ x, Y x i ∂μ| ≤
      Real.sqrt (Real.sqrt m4) * Real.sqrt (μ.real A) + Real.sqrt R2 * μ.real A := by
  have hvm : Measurable (fun y : Vec d => vecNormSq y) := by
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul (measurable_pi_apply i)
  set f : α → ℝ := fun x => vecNormSq (X x) with hf
  set g : α → ℝ := fun x => vecNormSq (Y x) with hg
  have hf0 : ∀ x, 0 ≤ f x := fun x => dtExp_vecNormSq_nonneg _
  have hg0 : ∀ x, 0 ≤ g x := fun x => dtExp_vecNormSq_nonneg _
  have hfm : Measurable f := hvm.comp hX
  have hgm : Measurable g := hvm.comp hY
  have hfint : Integrable f μ := by
    refine ((integrable_const (1 : ℝ)).add h4).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (hf0 x)]
    simp only [Pi.add_apply]
    nlinarith only [sq_nonneg (f x - 1)]
  have hpA : 0 ≤ μ.real A := measureReal_nonneg
  have hm4' : ∫ x, f x ^ 2 ∂μ ≤ m4 := hm4
  have hsq : Real.sqrt (∫ x, f x ^ 2 ∂μ) ≤ Real.sqrt m4 := Real.sqrt_le_sqrt hm4'
  have hint_f : ∫ x, f x ∂μ ≤ Real.sqrt m4 := by
    have h := dtExp_cs (μ := μ) hf0 hfm h4 MeasurableSet.univ
    simp only [Set.indicator_univ, probReal_univ, Real.sqrt_one, mul_one] at h
    exact h.trans hsq
  have hcsA : ∫ x, A.indicator f x ∂μ ≤ Real.sqrt m4 * Real.sqrt (μ.real A) :=
    (dtExp_cs (μ := μ) hf0 hfm h4 hA).trans
      (mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _))
  have hconst : ∀ c : ℝ, ∫ x, A.indicator (fun _ => c) x ∂μ = c * μ.real A := by
    intro c; rw [integral_indicator hA]; simp [mul_comm]
  refine ⟨hfint, hint_f, ?_, fun i => ?_⟩
  · have hgint : Integrable g μ := by
      refine Integrable.of_bound hgm.aestronglyMeasurable R2 (hR.mono fun x hx => ?_)
      rw [Real.norm_of_nonneg (hg0 x)]; exact hx
    have hpt : ∀ᵐ x ∂μ, |f x - g x| ≤ A.indicator f x + A.indicator (fun _ => R2) x := by
      filter_upwards [hR, hXY] with x hRx hXYx
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        rw [abs_le]; constructor <;> linarith only [hf0 x, hg0 x, hRx]
      · simp only [Set.indicator_of_notMem hx, add_zero]
        have : X x = Y x := hXYx hx
        simp [hf, hg, this]
    have hind1 : Integrable (A.indicator f) μ := hfint.indicator hA
    have hind2 : Integrable (A.indicator (fun _ => R2)) μ := (integrable_const R2).indicator hA
    calc |∫ x, f x ∂μ - ∫ x, g x ∂μ| = |∫ x, (f x - g x) ∂μ| := by rw [integral_sub hfint hgint]
      _ ≤ ∫ x, |f x - g x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (A.indicator f x + A.indicator (fun _ => R2) x) ∂μ :=
          integral_mono_ae (hfint.sub hgint).abs (hind1.add hind2) hpt
      _ = ∫ x, A.indicator f x ∂μ + R2 * μ.real A := by
          rw [integral_add hind1 hind2, hconst]
      _ ≤ _ := by linarith only [hcsA]
  · set h : α → ℝ := fun x => Real.sqrt (f x) with hh
    have hh0 : ∀ x, 0 ≤ h x := fun x => Real.sqrt_nonneg _
    have hhm : Measurable h := hfm.sqrt
    have hh2 : ∀ x, h x ^ 2 = f x := fun x => Real.sq_sqrt (hf0 x)
    have hh2i : Integrable (fun x => h x ^ 2) μ := by simpa [hh2] using hfint
    have hcs2 := dtExp_cs (μ := μ) hh0 hhm hh2i hA
    simp only [hh2] at hcs2
    have hcs2' : ∫ x, A.indicator h x ∂μ ≤ Real.sqrt (Real.sqrt m4) * Real.sqrt (μ.real A) :=
      hcs2.trans (mul_le_mul_of_nonneg_right
        (Real.sqrt_le_sqrt hint_f) (Real.sqrt_nonneg _))
    have hXi : Integrable (fun x => X x i) μ := by
      refine ((integrable_const (1 : ℝ)).add hfint).mono'
        ((measurable_pi_apply i).comp hX).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      have h1 := dtExp_abs_coord_le (X x) i
      simp only [Pi.add_apply]
      have h2 : Real.sqrt (f x) ≤ 1 + f x := by
        have := Real.sqrt_le_sqrt (show f x ≤ (1 + f x) ^ 2 by nlinarith only [hf0 x])
        rwa [Real.sqrt_sq (by linarith only [hf0 x])] at this
      exact h1.trans h2
    have hYi : Integrable (fun x => Y x i) μ := by
      refine Integrable.of_bound ((measurable_pi_apply i).comp hY).aestronglyMeasurable
        (Real.sqrt R2) (hR.mono fun x hx => ?_)
      rw [Real.norm_eq_abs]
      exact (dtExp_abs_coord_le (Y x) i).trans (Real.sqrt_le_sqrt hx)
    have hpt : ∀ᵐ x ∂μ, |X x i - Y x i| ≤
        A.indicator h x + A.indicator (fun _ => Real.sqrt R2) x := by
      filter_upwards [hR, hXY] with x hRx hXYx
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx]
        have h1 := dtExp_abs_coord_le (X x) i
        have h2 : |Y x i| ≤ Real.sqrt R2 :=
          (dtExp_abs_coord_le (Y x) i).trans (Real.sqrt_le_sqrt hRx)
        have h3 := abs_sub (X x i) (Y x i)
        linarith only [h1, h2, h3]
      · simp only [Set.indicator_of_notMem hx, add_zero]
        have : X x = Y x := hXYx hx
        simp [this]
    have hind1 : Integrable (A.indicator h) μ := by
      refine Integrable.indicator ?_ hA
      refine ((integrable_const (1 : ℝ)).add hfint).mono' hhm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (hh0 x)]
      simp only [Pi.add_apply]
      have := Real.sqrt_le_sqrt (show f x ≤ (1 + f x) ^ 2 by nlinarith only [hf0 x])
      rw [Real.sqrt_sq (by linarith only [hf0 x])] at this
      exact this
    have hind2 : Integrable (A.indicator (fun _ => Real.sqrt R2)) μ :=
      (integrable_const _).indicator hA
    calc |∫ x, X x i ∂μ - ∫ x, Y x i ∂μ| = |∫ x, (X x i - Y x i) ∂μ| := by
          rw [integral_sub hXi hYi]
      _ ≤ ∫ x, |X x i - Y x i| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, (A.indicator h x + A.indicator (fun _ => Real.sqrt R2) x) ∂μ :=
          integral_mono_ae (hXi.sub hYi).abs (hind1.add hind2) hpt
      _ = ∫ x, A.indicator h x ∂μ + Real.sqrt R2 * μ.real A := by
          rw [integral_add hind1 hind2, hconst]
      _ ≤ _ := by linarith only [hcs2']

section Paths

variable {d : ℕ}

/-- Off the exit event the truncated exit time is the horizon. -/
theorem dtExp_trunc_eq (U : Set (Vec d)) (K : NNReal) (w : ContinuousPath (Vec d))
    (h : ¬ ContinuousPath.exitTime U w ≤ (K : ℝ≥0∞)) :
    ContinuousPath.exitTimeTrunc U K w = K := by
  have h1 := ContinuousPath.coe_exitTimeTrunc_ennreal U K w
  rw [min_eq_right (not_le.1 h).le] at h1
  exact_mod_cast h1

/-- The exit event is measurable. -/
theorem dtExp_exit_event_measurable {U : Set (Vec d)} (hU : IsOpen U) (K : NNReal) :
    MeasurableSet {w : ContinuousPath (Vec d) | ContinuousPath.exitTime U w ≤ (K : ℝ≥0∞)} :=
  (ContinuousPath.measurable_exitTime U hU) measurableSet_Iic

theorem dtExp_trunc_measurable {U : Set (Vec d)} (hU : IsOpen U) (K : NNReal) :
    Measurable fun w : ContinuousPath (Vec d) =>
      ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ) := by
  have h := SubMarkovKernelSemigroup.measurable_coe_exitTimeTrunc U hU K
  have h2 : Measurable fun w : ContinuousPath (Vec d) =>
      (((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ≥0∞)).toReal := h.ennreal_toReal
  simpa using h2

/-- **The mean stopped time is the horizon, up to the exit probability.** -/
theorem dtExp_trunc_gap {U : Set (Vec d)} (hU : IsOpen U) (K : NNReal)
    {μ : Measure (ContinuousPath (Vec d))} [IsProbabilityMeasure μ] :
    |∫ w, ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ) ∂μ - K| ≤
      K * μ.real {w | ContinuousPath.exitTime U w ≤ (K : ℝ≥0∞)} := by
  set A := {w : ContinuousPath (Vec d) | ContinuousPath.exitTime U w ≤ (K : ℝ≥0∞)} with hA
  have hAm := dtExp_exit_event_measurable hU K
  have hm := dtExp_trunc_measurable hU K
  have hint : Integrable (fun w : ContinuousPath (Vec d) =>
      ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ)) μ :=
    Integrable.of_bound hm.aestronglyMeasurable K (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast ContinuousPath.exitTimeTrunc_le U K w)
  have hind : Integrable (A.indicator (fun _ => (K : ℝ))) μ := (integrable_const _).indicator hAm
  have hpt : ∀ w, |(K : ℝ) - ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ)| ≤
      A.indicator (fun _ => (K : ℝ)) w := by
    intro w
    have hle : ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ) ≤ K := by
      exact_mod_cast ContinuousPath.exitTimeTrunc_le U K w
    by_cases hw : w ∈ A
    · rw [Set.indicator_of_mem hw, abs_of_nonneg (by linarith only [hle])]
      linarith only [NNReal.coe_nonneg (ContinuousPath.exitTimeTrunc U K w)]
    · rw [Set.indicator_of_notMem hw, dtExp_trunc_eq U K w hw]; simp
  have : ∫ w, ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ) ∂μ - K =
      -∫ w, ((K : ℝ) - ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ)) ∂μ := by
    rw [integral_sub (integrable_const _) hint]; simp
  rw [this, abs_neg]
  calc |∫ w, ((K : ℝ) - ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ)) ∂μ|
      ≤ ∫ w, |(K : ℝ) - ((ContinuousPath.exitTimeTrunc U K w : NNReal) : ℝ)| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ w, A.indicator (fun _ => (K : ℝ)) w ∂μ :=
        integral_mono ((integrable_const _).sub hint).abs hind hpt
    _ = K * μ.real A := by rw [integral_indicator hAm]; simp [hA, mul_comm]

end Paths

section Four

variable {d : ℕ}

theorem dtExp_vecNormSq_le_sup (y : Vec d) : vecNormSq y ≤ d * ‖y‖ ^ 2 := by
  unfold vecNormSq vecDot
  have h : ∀ i : Fin d, y i * y i ≤ ‖y‖ ^ 2 := fun i => by
    have h1 := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at h1
    have h2 : |y i| ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    linarith only [h2, sq (y i)]
  calc ∑ i, y i * y i ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => h i
    _ = d * ‖y‖ ^ 2 := by simp

/-- A fourth-moment bound for the sup norm bounds the second moment of the squared Euclidean
length. -/
theorem dtExp_four_moment {ν : Measure (Vec d)} [IsProbabilityMeasure ν] {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂ν ≤ ENNReal.ofReal B) :
    Integrable (fun y : Vec d => vecNormSq y ^ 2) ν ∧
      ∫ y, vecNormSq y ^ 2 ∂ν ≤ (d : ℝ) ^ 2 * B := by
  have hvm : Measurable (fun y : Vec d => vecNormSq y) := by
    unfold vecNormSq vecDot
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul (measurable_pi_apply i)
  have hg : ∀ z : Vec d, edist z (0 : Vec d) ^ (4 : ℝ) = ENNReal.ofReal (‖z‖ ^ 4) := by
    intro z
    rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
      (by norm_num)]
    norm_num
  have hl : ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 4) ∂ν ≤ ENNReal.ofReal B := by
    simpa only [hg] using h
  have hint : Integrable (fun z : Vec d => ‖z‖ ^ 4) ν := by
    refine ⟨(measurable_norm.pow_const 4).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by positivity)]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  have hbd : ∀ y : Vec d, vecNormSq y ^ 2 ≤ (d : ℝ) ^ 2 * ‖y‖ ^ 4 := fun y => by
    have h1 := dtExp_vecNormSq_le_sup y
    have h0 : 0 ≤ vecNormSq y := by
      unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    calc vecNormSq y ^ 2 ≤ ((d : ℝ) * ‖y‖ ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = (d : ℝ) ^ 2 * ‖y‖ ^ 4 := by ring
  have hI : Integrable (fun y : Vec d => vecNormSq y ^ 2) ν := by
    refine (hint.const_mul ((d : ℝ) ^ 2)).mono' (hvm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hbd y
  refine ⟨hI, ?_⟩
  have h2 : ∫ z, ‖z‖ ^ 4 ∂ν ≤ B := by
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 (by rwa [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun z => by positivity)])
  calc ∫ y, vecNormSq y ^ 2 ∂ν ≤ ∫ y, (d : ℝ) ^ 2 * ‖y‖ ^ 4 ∂ν :=
        integral_mono hI (hint.const_mul _) hbd
    _ = (d : ℝ) ^ 2 * ∫ y, ‖y‖ ^ 4 ∂ν := integral_const_mul _ _
    _ ≤ (d : ℝ) ^ 2 * B := by gcongr

end Four

end SuperdiffusionCLT.Section8
