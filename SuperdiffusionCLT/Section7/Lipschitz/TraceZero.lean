/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Truncation
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.BoundaryTraceMeasure
public import Homogenization.Sobolev.Foundations.PoincareMeanZero

/-!
# The trace of an `H¹₀` function at a chart point

An `H¹₀(V)` function cannot be bounded below by a positive constant near a frontier point of `V`
that has a graph chart: truncating and zero-extending produces `1_V` in `H¹` of a small ball,
whose weak gradient vanishes, so that it is a.e. constant; both `V` and its complement have
positive measure in the ball.
-/

@[expose] public section

open MeasureTheory Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_h10_trace_zero_const {B : Set (Vec d)} (hB : IsOpenBoundedConvexDomain B)
    (g : H1Function B) (h0 : ∀ᵐ x ∂volume.restrict B, g.grad x = 0) :
    ∃ m : ℝ, ∀ᵐ x ∂volume.restrict B, g.toFun x = m := by
  have : IsFiniteMeasure (volumeMeasureOn B) := hB.isFiniteMeasure_restrict_volume
  obtain ⟨C, hC0, hC⟩ := exists_poincare_constant_of_isOpenBoundedConvexDomain hB
  have hP := hC g.toMeanZero
  have hgrad : g.toMeanZero.gradientL2Norm = 0 := by
    unfold H1MeanZeroFunction.gradientL2Norm
    have hz : g.toMeanZero.toH1Function.gradToVectorL2 = 0 := by
      apply Lp.ext
      filter_upwards [H1Function.coeFn_gradToVectorL2 g.toMeanZero.toH1Function, h0,
        Lp.coeFn_zero (E := Vec d) (p := 2) (μ := volumeMeasureOn B)] with x h1 h2 h3
      rw [h1, h3]
      have := H1Function.toMeanZero_grad g x
      rw [this, h2]; rfl
    change ‖g.toMeanZero.toH1Function.gradToVectorL2‖ = 0
    rw [hz, norm_zero]
  rw [hgrad, mul_zero] at hP
  have hv : g.toMeanZero.valueL2Norm = 0 := le_antisymm hP (norm_nonneg _)
  unfold H1MeanZeroFunction.valueL2Norm at hv
  have hs : g.toMeanZero.toH1Function.toScalarL2 = 0 := norm_eq_zero.mp hv
  refine ⟨integralAverage B g.toFun, ?_⟩
  filter_upwards [H1Function.coeFn_toScalarL2 g.toMeanZero.toH1Function,
    Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeMeasureOn B)] with x h1 h2
  rw [hs] at h1
  have h3 := H1Function.toMeanZero_apply g x
  have h5 : (0 : ℝ) = g.toMeanZero.toH1Function.toFun x := by
    rw [← h1]; exact h2.symm
  have h4 : g.toMeanZero.toH1Function.toFun x = g.toFun x - integralAverage B g.toFun := h3
  linarith only [h5, h4]

/-- A property holding a.e. on a set holds somewhere on every nonempty open subset. -/
theorem lip_h10_trace_zero_exists {B O : Set (Vec d)} (hB : MeasurableSet B) (hO : IsOpen O)
    (hne : O.Nonempty) (hOB : O ⊆ B) {p : Vec d → Prop}
    (h : ∀ᵐ x ∂volume.restrict B, p x) : ∃ x ∈ O, p x := by
  by_contra hcon
  push Not at hcon
  have h1 := (ae_restrict_iff' hB).1 h
  have hsub : O ⊆ {x | ¬ (x ∈ B → p x)} := fun x hx hh => hcon x hx (hh (hOB hx))
  have h0 : volume O = 0 := measure_mono_null hsub (ae_iff.1 h1)
  exact (hO.measure_pos volume hne).ne' h0

theorem lip_h10_trace_zero_vecNorm_le {e : Vec d} (he : vecNormSq e = 1) : ‖e‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have h1 : e i * e i ≤ vecNormSq e := by
    unfold vecNormSq vecDot
    exact Finset.single_le_sum (f := fun j => e j * e j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  rw [he] at h1
  rw [Real.norm_eq_abs]
  exact abs_le_one_iff_mul_self_le_one.2 h1

/-- The chart function `y ↦ e·y - ψ(y - (e·y) e)`. -/
theorem lip_h10_trace_zero_chart_shift {e : Vec d} {ψ : Vec d → ℝ} (he : vecNormSq e = 1)
    {x₀ : Vec d} (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e)) (t : ℝ) :
    vecDot e (x₀ + t • e) - ψ ((x₀ + t • e) - vecDot e (x₀ + t • e) • e) = t := by
  have h1 : vecDot e (x₀ + t • e) = vecDot e x₀ + t := by
    rw [vecDot_add_right, vecDot_smul_right]
    have : vecDot e e = 1 := he
    rw [this, mul_one]
  rw [h1]
  have h2 : (x₀ + t • e) - (vecDot e x₀ + t) • e = x₀ - vecDot e x₀ • e := by
    rw [add_smul]; abel
  rw [h2, ← hx₀]; ring

theorem lip_h10_trace_zero_g_ae {V B : Set (Vec d)} (hV : IsOpen V) {ρ : ℝ}
    {x₀ : Vec d} {r : ℝ} (hr : r ≤ ρ) (φ : H10Function V) {A : ℝ}
    (hA : ∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ), A ≤ φ.toH1Function.toFun y)
    (hB : B = Metric.ball x₀ r) (w : H1Function B)
    (hw : w.toFun = V.indicator φ.toH1Function.toFun) (A0 : 0 < A) :
    ∀ᵐ x ∂volume.restrict B,
      A⁻¹ * (max (w.toFun x - 0) 0 - max (w.toFun x - A) 0) = V.indicator (fun _ => (1 : ℝ)) x := by
  have h1 := (ae_restrict_iff' (hV.measurableSet.inter Metric.isOpen_ball.measurableSet)).1 hA
  rw [ae_restrict_iff' (hB ▸ Metric.isOpen_ball.measurableSet)]
  filter_upwards [h1] with x hx hxB
  rw [hw]
  by_cases hxV : x ∈ V
  · have hxρ : x ∈ Metric.ball x₀ ρ := by
      have : x ∈ Metric.ball x₀ r := hB ▸ hxB
      exact Metric.ball_subset_ball hr this
    have hAx := hx ⟨hxV, hxρ⟩
    rw [Set.indicator_of_mem hxV, Set.indicator_of_mem hxV]
    rw [max_eq_left (by linarith only [hAx, A0]), max_eq_left (by linarith only [hAx])]
    field_simp
    ring
  · rw [Set.indicator_of_notMem hxV, Set.indicator_of_notMem hxV]
    simp
    exact Or.inr A0.le

open Section8.Common.ExcessDecay in
/-- **BT1 — the trace of an `H¹₀` function at a chart point is zero**: an `H¹₀(V)` function cannot
be bounded below by a positive constant near a boundary point with a graph chart. -/
theorem lip_h10_trace_zero (d : ℕ) [NeZero d] {V : Set (Vec d)} (hV : IsOpen V) {x₀ e : Vec d}
    {ψ : Vec d → ℝ} {R₀ : ℝ} (hR₀ : 0 < R₀) (he : vecNormSq e = 1)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hx₀ : vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e))
    (hch : ∀ y ∈ Metric.ball x₀ R₀, (y ∈ V ↔ vecDot e y < ψ (y - vecDot e y • e)))
    (φ : H10Function V) {A ρ : ℝ} (hρ : 0 < ρ)
    (hA : ∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ ρ), A ≤ φ.toH1Function.toFun y) :
    A ≤ 0 := by
  by_contra hA0
  have A0 : 0 < A := not_le.mp hA0
  set r : ℝ := min ρ R₀ with hrdef
  have hr0 : 0 < r := lt_min hρ hR₀
  have hrρ : r ≤ ρ := min_le_left _ _
  have hrR : r ≤ R₀ := min_le_right _ _
  set B : Set (Vec d) := Metric.ball x₀ r with hBdef
  have hBo : IsOpenBoundedConvexDomain B := isOpenBoundedConvexDomain_ball x₀ r
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  let w : H1Function B := zeroExtendH1 hV.measurableSet φ B
  have hw : w.toFun = V.indicator φ.toH1Function.toFun := rfl
  let v₁ : H1Function B := positivePartOpen Metric.isOpen_ball w 0
    (memL2On_positivePart_of_nonneg w le_rfl)
  let v₂ : H1Function B := positivePartOpen Metric.isOpen_ball w A
    (memL2On_positivePart_of_nonneg w A0.le)
  let gg : H1Function B := A⁻¹ • (v₁ - v₂)
  have hgg : ∀ x, gg.toFun x = A⁻¹ * (max (w.toFun x - 0) 0 - max (w.toFun x - A) 0) := fun x => by
    simp only [gg, v₁, v₂, H1Function.smul_toFun, H1Function.sub_toFun, positivePartOpen]
  have hfin : volume B ≠ ⊤ := (measure_ball_lt_top (x := x₀) (r := r)).ne
  have hae := lip_h10_trace_zero_g_ae hV hrρ φ hA rfl w hw A0
  have hz0 := grad_ae_zero_on_level_set Metric.isOpen_ball hfin gg 0
  have hz1 := grad_ae_zero_on_level_set Metric.isOpen_ball hfin gg 1
  have hgrad : ∀ᵐ x ∂volume.restrict B, gg.grad x = 0 := by
    filter_upwards [hae, hz0, hz1] with x hx h0 h1
    by_cases hxV : x ∈ V
    · rw [Set.indicator_of_mem hxV] at hx
      exact h1 (by rw [hgg]; exact hx)
    · rw [Set.indicator_of_notMem hxV] at hx
      exact h0 (by rw [hgg]; exact hx)
  obtain ⟨m, hm⟩ := lip_h10_trace_zero_const hBo gg hgrad
  have hind : ∀ᵐ x ∂volume.restrict B, V.indicator (fun _ => (1 : ℝ)) x = m := by
    filter_upwards [hae, hm] with x h1 h2
    rw [← h1, ← hgg, h2]
  -- the chart function
  let h : Vec d → ℝ := fun y => vecDot e y - ψ (y - vecDot e y • e)
  have hcont : Continuous h := by
    have hc : Continuous (fun y : Vec d => vecDot e y) := by unfold vecDot; fun_prop
    exact hc.sub (hψ.continuous.comp (continuous_id.sub (hc.smul continuous_const)))
  have he1 : ‖e‖ ≤ 1 := lip_h10_trace_zero_vecNorm_le he
  have hdist : ∀ t : ℝ, |t| < r → x₀ + t • e ∈ B := by
    intro t ht
    rw [hBdef, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖e‖ ≤ |t| * 1 := mul_le_mul_of_nonneg_left he1 (abs_nonneg _)
      _ < r := by linarith only [ht]
  have hmem : ∀ y ∈ B, y ∈ V ↔ h y < 0 := fun y hy => by
    have := hch y (Metric.ball_subset_ball hrR hy)
    simp only [h, sub_neg]; exact this
  -- the two open sets
  have hO1 : IsOpen (B ∩ {y | h y < 0}) := Metric.isOpen_ball.inter (isOpen_lt hcont continuous_const)
  have hO2 : IsOpen (B ∩ {y | 0 < h y}) := Metric.isOpen_ball.inter (isOpen_lt continuous_const hcont)
  have hne1 : (B ∩ {y | h y < 0}).Nonempty := by
    refine ⟨x₀ + (-(r / 2)) • e, hdist _ ?_, ?_⟩
    · rw [abs_neg, abs_of_pos (by linarith only [hr0])]; linarith only [hr0]
    · have := lip_h10_trace_zero_chart_shift he hx₀ (-(r / 2))
      show h _ < 0
      simp only [h]; rw [this]; linarith only [hr0]
  have hne2 : (B ∩ {y | 0 < h y}).Nonempty := by
    refine ⟨x₀ + (r / 2) • e, hdist _ ?_, ?_⟩
    · rw [abs_of_pos (by linarith only [hr0])]; linarith only [hr0]
    · have := lip_h10_trace_zero_chart_shift he hx₀ (r / 2)
      show 0 < h _
      simp only [h]; rw [this]; linarith only [hr0]
  obtain ⟨y1, hy1, hm1⟩ := lip_h10_trace_zero_exists hBm hO1 hne1 Set.inter_subset_left hind
  obtain ⟨y2, hy2, hm2⟩ := lip_h10_trace_zero_exists hBm hO2 hne2 Set.inter_subset_left hind
  have hy1V : y1 ∈ V := (hmem y1 hy1.1).2 hy1.2
  have hy2V : y2 ∉ V := fun hv => by
    have := (hmem y2 hy2.1).1 hv
    exact absurd hy2.2 (not_lt.mpr this.le)
  rw [Set.indicator_of_mem hy1V] at hm1
  rw [Set.indicator_of_notMem hy2V] at hm2
  linarith only [hm1, hm2]

/-- Witness: the hypotheses of `lip_h10_trace_zero` (all but a positive lower bound) hold on the
half space `{y | e · y < 0}` at the origin, with the zero function. -/
example : ∃ (V : Set (Vec 2)) (e x₀ : Vec 2) (ψ : Vec 2 → ℝ) (φ : H10Function V),
    IsOpen V ∧ vecNormSq e = 1 ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
    vecDot e x₀ = ψ (x₀ - vecDot e x₀ • e) ∧
    (∀ y ∈ Metric.ball x₀ 1, (y ∈ V ↔ vecDot e y < ψ (y - vecDot e y • e))) ∧
    (∀ᵐ y ∂volume.restrict (V ∩ Metric.ball x₀ 1), (0 : ℝ) ≤ φ.toH1Function.toFun y) := by
  refine ⟨{y | vecDot (Pi.single 0 1 : Vec 2) y < 0}, Pi.single 0 1, 0, fun _ => 0, 0, ?_, ?_,
    contDiff_const, ?_, ?_, ?_⟩
  · have hc : Continuous (fun y : Vec 2 => vecDot (Pi.single 0 1 : Vec 2) y) := by
      unfold vecDot; fun_prop
    exact isOpen_lt hc continuous_const
  · simp [vecNormSq, vecDot, Fin.sum_univ_two]
  · simp [vecDot]
  · intro y _; rfl
  · exact Filter.Eventually.of_forall fun y => le_rfl

end SuperdiffusionCLT.Section7
