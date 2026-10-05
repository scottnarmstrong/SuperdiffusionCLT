/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.ZeroExtension
public import Homogenization.Sobolev.Truncation.Basic
public import Homogenization.Sobolev.Truncation.LevelSets
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-!
# Positive-part truncation of `H¹` on arbitrary open sets

The convex-domain positive-part theorem `Homogenization.exists_h1_max_sub_const` is transported to
an arbitrary open set `U` by locality (`hasWeakGradientOn_of_local_ball`): on every sup-norm ball
inside `U` the truncation of the restriction has weak gradient `1_{u > c} ∇u`.  As a consequence
the weak gradient vanishes a.e. on level sets, for open sets of finite measure.
-/

@[expose] public section

open scoped ENNReal
open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

theorem isOpenBoundedConvexDomain_ball (x : Vec d) (r : ℝ) :
    IsOpenBoundedConvexDomain (Metric.ball x r) :=
  ⟨Metric.isOpen_ball, Homogenization.Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball,
    convex_ball x r⟩

theorem locallyIntegrableOn_of_memL2On {f : Vec d → ℝ} (h : MemL2On U f) :
    LocallyIntegrableOn f U volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (h.locallyIntegrable (by norm_num))

/-- The truncated gradient `1_{u > c} ∇u`. -/
noncomputable def posPartGrad (u : H1Function U) (c : ℝ) : Vec d → Vec d :=
  {y | c < u.toFun y}.indicator u.grad

theorem posPartGrad_gradMemL2 (u : H1Function U) (c : ℝ) :
    GradMemL2On U (posPartGrad u c) := by
  intro i
  have hset : NullMeasurableSet {y | c < u.toFun y} (volumeMeasureOn U) :=
    nullMeasurableSet_lt aemeasurable_const u.memL2.aemeasurable
  have heq : (fun x => posPartGrad u c x i) =
      {y | c < u.toFun y}.indicator (fun x => u.grad x i) := by
    funext x
    by_cases hx : x ∈ {y | c < u.toFun y} <;> simp [posPartGrad, hx]
  rw [heq]
  refine (u.gradMemL2 i).mono ((u.gradMemL2 i).aestronglyMeasurable.indicator₀ hset)
    (Filter.Eventually.of_forall fun x => norm_indicator_le_norm_self _ _)

/-- The truncated value belongs to `L²(U)` when the level is nonnegative. -/
theorem memL2On_positivePart_of_nonneg (u : H1Function U) {c : ℝ} (hc : 0 ≤ c) :
    MemL2On U (fun x => max (u.toFun x - c) 0) := by
  refine u.memL2.mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const)
  · simp only [Real.norm_eq_abs]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h, abs_of_nonneg h]
      exact (by linarith only [le_abs_self (u.toFun x), hc] : u.toFun x - c ≤ |u.toFun x|)

/-- The truncated value belongs to `L²(U)` when `U` has finite measure. -/
theorem memL2On_positivePart_of_finite (u : H1Function U) (hfin : volume U ≠ ⊤) (c : ℝ) :
    MemL2On U (fun x => max (u.toFun x - c) 0) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [volumeMeasureOn] using hfin.lt_top⟩
  have hc : MemL2On U (fun x => u.toFun x - c) := u.memL2.sub (memLp_const c)
  refine hc.mono ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const)
  · simp only [Real.norm_eq_abs]
    rcases le_total (u.toFun x - c) 0 with h | h
    · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
    · rw [max_eq_left h]

/-- **Weak gradient of the positive part on an arbitrary open set.** -/
theorem hasWeakGradientOn_positivePart (hU : IsOpen U) (u : H1Function U) (c : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - c) 0)) :
    HasWeakGradientOn U (fun x => max (u.toFun x - c) 0) (posPartGrad u c) := by
  refine hasWeakGradientOn_of_local_ball hU (locallyIntegrableOn_of_memL2On hmem)
    (fun i => locallyIntegrableOn_of_memL2On (posPartGrad_gradMemL2 u c i)) ?_
  intro x hx
  obtain ⟨r, hr, hsub⟩ := exists_ball_subset hU hx
  refine ⟨r, hr, hsub, fun i => ?_⟩
  obtain ⟨v, hvf, hvg⟩ := exists_h1_max_sub_const (isOpenBoundedConvexDomain_ball x r)
    (u.restrict Metric.isOpen_ball hsub) c
  have hw := v.hasWeakGradient i
  rw [hvf] at hw
  refine hasWeakPartialDerivOn_congr_ae hw ?_
  filter_upwards [hvg] with y hy
  rw [hy]
  rfl

/-- Positive-part truncation `(u - c)₊` of an `H¹` function on an arbitrary open set, with
gradient `1_{u > c} ∇u`.  The `L²` membership of the truncated value is a (simple)
hypothesis, discharged by `memL2On_positivePart_of_nonneg` (for `c ≥ 0`) and
`memL2On_positivePart_of_finite` (for finite-measure `U`). -/
noncomputable def positivePartOpen (hU : IsOpen U) (u : H1Function U) (c : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - c) 0)) : H1Function U where
  toFun := fun x => max (u.toFun x - c) 0
  grad := posPartGrad u c
  memL2 := hmem
  gradMemL2 := posPartGrad_gradMemL2 u c
  hasWeakGradient := hasWeakGradientOn_positivePart hU u c hmem

theorem integrableOn_mul_fderiv_test (hU : IsOpen U) {u : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (i : Fin d) :
    IntegrableOn (fun x => u x * (fderiv ℝ φ x) (basisVec i)) U := by
  have hcont : Continuous (fun x => (fderiv ℝ φ x) (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsupp : Function.support (fun x => (fderiv ℝ φ x) (basisVec i)) ⊆ tsupport φ :=
    fun x hx => by
      by_contra h
      apply hx
      simp [fderiv_of_notMem_tsupport ℝ h]
  have hdc : HasCompactSupport (fun x => (fderiv ℝ φ x) (basisVec i)) := hφc.mono' hdsupp
  have hdU : tsupport (fun x => (fderiv ℝ φ x) (basisVec i)) ⊆ U :=
    (closure_minimal hdsupp (isClosed_tsupport _)).trans hφU
  exact integrableOn_mul_of_compactSupport hU hu hcont hdc hdU

/-- Weak gradient of a shifted function: `∇(u - c) = ∇u`. -/
theorem hasWeakPartialDerivOn_sub_const (hU : IsOpen U) (u : H1Function U) (c : ℝ)
    (i : Fin d) :
    HasWeakPartialDerivOn U i (fun x => u.toFun x - c) (fun x => u.grad x i) := by
  have hconst : HasWeakPartialDerivOn U i (fun _ : Vec d => -c) (fun _ => 0) := by
    have := HasWeakPartialDerivOn.of_contDiff (U := U) (i := i)
      (contDiff_const (c := -c) : ContDiff ℝ 1 fun _ : Vec d => -c)
    simpa using this
  have hu := u.hasWeakGradient i
  intro φ hφ hφc hφU
  have h1 := hu φ hφ hφc hφU
  have h2 := hconst φ hφ hφc hφU
  have hI1 := integrableOn_mul_fderiv_test hU (locallyIntegrableOn_of_memL2On u.memL2) hφ hφc hφU i
  have hI2 := integrableOn_mul_fderiv_test hU (locallyIntegrableOn_const (-c)) hφ hφc hφU i
  have e : (fun x => (u.toFun x - c) * (fderiv ℝ φ x) (basisVec i)) =
      fun x => u.toFun x * (fderiv ℝ φ x) (basisVec i) + (-c) * (fderiv ℝ φ x) (basisVec i) := by
    funext x; ring
  rw [e, integral_add hI1 hI2, h1, h2]
  simp

/-- **The weak gradient vanishes a.e. on every level set**, on any open set of finite measure. -/
theorem grad_ae_zero_on_level_set (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    (u : H1Function U) (c : ℝ) :
    ∀ᵐ x ∂(volumeMeasureOn U), u.toFun x = c → u.grad x = 0 := by
  let v₁ := positivePartOpen hU u c (memL2On_positivePart_of_finite u hfin c)
  let v₂ := positivePartOpen hU (-u) (-c) (memL2On_positivePart_of_finite (-u) hfin (-c))
  let v : H1Function U := v₁ - v₂
  have hcoord : ∀ i : Fin d, (fun x => v.grad x i) =ᵐ[volumeMeasureOn U] (fun x => u.grad x i) := by
    intro i
    refine HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_memL2On (v.gradMemL2 i))
      (locallyIntegrableOn_of_memL2On (u.gradMemL2 i)) ?_
      (hasWeakPartialDerivOn_sub_const hU u c i)
    have h := v.hasWeakPartialDerivOn i
    have hval : v.toFun = fun x => u.toFun x - c := by
      funext x
      simp only [v, v₁, v₂, H1Function.sub_toFun, positivePartOpen, H1Function.neg_toFun]
      rcases le_total (u.toFun x - c) 0 with h | h
      · rw [max_eq_right h, max_eq_left (by linarith only [h])]; ring
      · rw [max_eq_left h, max_eq_right (by linarith only [h])]; ring
    rwa [hval] at h
  have hall : ∀ᵐ x ∂(volumeMeasureOn U), ∀ i, v.grad x i = u.grad x i := ae_all_iff.mpr hcoord
  filter_upwards [hall] with x hx hxc
  funext i
  rw [← hx i]
  have hvg : v.grad x = posPartGrad u c x - posPartGrad (-u) (-c) x := by
    simp only [v, v₁, v₂, H1Function.sub_grad, positivePartOpen]
  rw [hvg]
  have h1 : posPartGrad u c x = 0 := by
    simp [posPartGrad, hxc]
  have h2 : posPartGrad (-u) (-c) x = 0 := by
    simp [posPartGrad, hxc]
  simp [h1, h2]

/-- Witness: the hypotheses of the level-set theorem are met on the unit ball, for the zero
function. -/
example : ∀ᵐ x ∂(volumeMeasureOn (Metric.ball (0 : Vec 2) 1)),
    (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x = 0 →
      (0 : H1Function (Metric.ball (0 : Vec 2) 1)).grad x = 0 :=
  grad_ae_zero_on_level_set Metric.isOpen_ball
    (measure_ball_lt_top (x := (0 : Vec 2)) (r := 1)).ne _ _

/-- Witness: `positivePartOpen` is applicable on the unit ball at a nonnegative level. -/
example : Nonempty (H1Function (Metric.ball (0 : Vec 2) 1)) :=
  ⟨positivePartOpen Metric.isOpen_ball (0 : H1Function (Metric.ball (0 : Vec 2) 1)) 0
    (memL2On_positivePart_of_nonneg _ le_rfl)⟩

end SuperdiffusionCLT.Section7
