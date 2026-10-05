/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Limit
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Truncation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Positive-part truncation of `H¹₀` functions on open sets

For `u ∈ H¹₀(U)` on an open set `U` of finite volume and a level `t ≥ 0`, the truncation `(u - t)₊`
is in `H¹₀(U)`.  The approximants are `(φₙ - t)₊`, where `φₙ` are smooth compactly supported
approximants of `u` along an almost-everywhere convergent subsequence; since `t ≥ 0` they are
compactly supported in `U`, so lie in `H¹₀(U)` (`toH10OfCompact`).  Their gradients converge by
dominated convergence, using that `∇u = 0` a.e. on `{u = t}`.
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- A family pointwise dominated in norm by one `L^p` function is uniformly integrable at every
finite exponent `p ≥ 1`. -/
theorem unifIntegrable_of_ae_norm_le
    {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ι → α → E} {bound : α → E}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hboundMem : MemLp bound p μ)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ ‖bound x‖) :
    UnifIntegrable F p μ := by
  rw [unifIntegrable_iff']
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hboundMem.eLpNorm_indicator_le hp hpTop hε
  refine ⟨δ, hδ, fun i s hs hμs => ?_⟩
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  refine (eLpNorm_mono_ae ((hF i).indicator hs) ?_).trans (hsmall s hs hμs)
  filter_upwards [hbound i] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]
    exact hx
  · simp only [Set.indicator_of_notMem hxs, norm_zero]
    exact le_rfl

/-- Dominated almost-everywhere convergence implies convergence in finite-exponent `L^p` on a
finite measure space. -/
theorem tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    [IsFiniteMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ∞)
    {F : ℕ → α → E} {f bound : α → E}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hf : MemLp f p μ) (hboundMem : MemLp bound p μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖bound x‖)
    (hFf : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => eLpNorm (F n - f) p μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendsto_ae hp hpTop hF hf
    (unifIntegrable_of_ae_norm_le hp hpTop hF hboundMem hbound) hFf

/-- Gradient convergence for truncations along an almost-everywhere convergent sequence. -/
theorem tendsto_posPartGrad_eLpNorm (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H1Function U)
    (F : ℕ → H1Function U) (t : ℝ)
    (hgrad : ∀ i, Tendsto (fun k => eLpNorm (fun x => (F k).grad x i - u.grad x i) 2 (volumeMeasureOn U))
      atTop (𝓝 0))
    (hae : ∀ᵐ x ∂(volumeMeasureOn U), Tendsto (fun k => (F k).toFun x) atTop (𝓝 (u.toFun x)))
    (i : Fin d) :
    Tendsto (fun k => eLpNorm (fun x => posPartGrad (F k) t x i - posPartGrad u t x i) 2
      (volumeMeasureOn U)) atTop (𝓝 0) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [volumeMeasureOn] using hfin.lt_top⟩
  have hlev := grad_ae_zero_on_level_set hU hfin u t
  have hset : ∀ v : H1Function U, NullMeasurableSet {y | t < v.toFun y} (volumeMeasureOn U) :=
    fun v => nullMeasurableSet_lt aemeasurable_const v.memL2.aemeasurable
  -- the difference of the two indicators of the fixed gradient `∇u`
  let B : ℕ → Vec d → ℝ := fun k =>
    {y | t < (F k).toFun y}.indicator (fun x => u.grad x i) -
      {y | t < u.toFun y}.indicator (fun x => u.grad x i)
  have hBmeas : ∀ k, AEStronglyMeasurable (B k) (volumeMeasureOn U) := fun k =>
    ((u.grad_memL2 i).aestronglyMeasurable.indicator₀ (hset (F k))).sub
      ((u.grad_memL2 i).aestronglyMeasurable.indicator₀ (hset u))
  have hB : Tendsto (fun k => eLpNorm (B k - 0) 2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    refine SuperdiffusionCLT.Section7.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated (by norm_num) (by norm_num)
      hBmeas MemLp.zero (bound := fun x => u.grad x i) (u.grad_memL2 i) ?_ ?_
    · intro n
      refine Eventually.of_forall fun x => ?_
      by_cases h1 : t < (F n).toFun x <;> by_cases h2 : t < u.toFun x <;>
        simp [B, h1, h2]
    · filter_upwards [hae, hlev] with x hx hx0
      rcases lt_trichotomy (u.toFun x) t with h | h | h
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hx.eventually (gt_mem_nhds h)] with k hk
        simp [B, not_lt.2 hk.le, not_lt.2 h.le]
      · have hg : u.grad x = 0 := hx0 h
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun k => ?_)
        have hg' : u.grad x i = 0 := by simp [hg]
        by_cases a : t < (F k).toFun x <;> by_cases b : t < u.toFun x <;> simp [B, a, b, hg']
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [hx.eventually (lt_mem_nhds h)] with k hk
        simp [B, hk, h]
  have hA := hgrad i
  have hsum := hA.add hB
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => bot_le)
    (fun k => ?_)
  have heq : (fun x => posPartGrad (F k) t x i - posPartGrad u t x i) =
      {y | t < (F k).toFun y}.indicator (fun x => (F k).grad x i - u.grad x i) + B k := by
    funext x
    by_cases h1 : t < (F k).toFun x <;> by_cases h2 : t < u.toFun x <;>
      simp [B, posPartGrad, h1, h2]
  have hm1 : AEStronglyMeasurable
      ({y | t < (F k).toFun y}.indicator (fun x => (F k).grad x i - u.grad x i)) (volumeMeasureOn U) :=
    (((F k).grad_memL2 i).aestronglyMeasurable.sub
      (u.grad_memL2 i).aestronglyMeasurable).indicator₀ (hset (F k))
  rw [heq]
  refine (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ?_ ?_)
  · exact eLpNorm_mono hm1 fun x => norm_indicator_le_norm_self _ _
  · simp

/-- **`(u - t)₊ ∈ H¹₀`.**  For `u ∈ H¹₀(U)` on a bounded open set and `t ≥ 0`, the positive-part
truncation belongs to `H¹₀(U)`. -/
theorem memH10_positivePart (hU : IsOpen U) (hfin : volume U ≠ ⊤) (u : H10Function U)
    {t : ℝ} (ht : 0 ≤ t) :
    MemH10 U (positivePartOpen hU u.toH1Function t
      (memL2On_positivePart_of_nonneg u.toH1Function ht)).toFun := by
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) u.tendsto_approx).exists_seq_tendsto_ae
  let φ : ℕ → H10Function U := fun n =>
    H10Function.ofContDiff hU (u.approx_smooth n) (u.approx_hasCompactSupport n)
      (u.approx_support_subset n)
  have hφfun : ∀ n, (φ n).toH1Function.toFun = u.approx n := fun n => rfl
  let F : ℕ → H1Function U := fun k =>
    positivePartOpen hU (φ (σ k)).toH1Function t
      (memL2On_positivePart_of_nonneg (φ (σ k)).toH1Function ht)
  have hσt : Tendsto σ atTop atTop := hσ.tendsto_atTop
  refine SuperdiffusionCLT.Section7.memH10_of_tendsto_H1 hU _ F (fun k => ?_) ?_ (fun i => ?_)
  · have hz : ∀ x ∈ U, x ∉ tsupport (u.approx (σ k)) → (F k).toFun x = 0 := by
      intro x _ hx
      have h0 : u.approx (σ k) x = 0 := image_eq_zero_of_notMem_tsupport hx
      show max ((φ (σ k)).toH1Function.toFun x - t) 0 = 0
      rw [hφfun, h0]
      simp [ht]
    exact ⟨toH10OfCompact hU (F k) (u.approx_support_subset (σ k))
      (u.approx_hasCompactSupport (σ k)) hz,
      congrArg H1Function.toFun
        (toH10OfCompact_toH1Function hU (F k) (u.approx_support_subset (σ k))
          (u.approx_hasCompactSupport (σ k)) hz)⟩
  · have h1 : Tendsto (fun k => eLpNorm (fun x => u.toH1Function.toFun x -
        (φ (σ k)).toH1Function.toFun x) 2 (volumeMeasureOn U)) atTop (𝓝 0) :=
      ((u.tendsto_approx.comp hσt).congr fun k => Homogenization.eLpNorm_sub_swap _ _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1 (fun k => bot_le)
      (fun k => ?_)
    refine eLpNorm_mono
      ((positivePartOpen hU u.toH1Function t
        (memL2On_positivePart_of_nonneg u.toH1Function ht)).memL2.aestronglyMeasurable.sub
        (F k).memL2.aestronglyMeasurable) (fun x => ?_)
    show ‖max (u.toH1Function.toFun x - t) 0 - max ((φ (σ k)).toH1Function.toFun x - t) 0‖ ≤ _
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [sub_sub_sub_cancel_right]
  · have hgr : ∀ i, Tendsto (fun k => eLpNorm (fun x => (φ (σ k)).toH1Function.grad x i -
        u.toH1Function.grad x i) 2 (volumeMeasureOn U)) atTop (𝓝 0) := fun i =>
      u.tendsto_approx_grad i |>.comp hσt
    have := tendsto_posPartGrad_eLpNorm hU hfin u.toH1Function (fun k => (φ (σ k)).toH1Function)
      t hgr (by simpa [hφfun] using hae) i
    exact (this.congr fun k => Homogenization.eLpNorm_sub_swap _ _)


/-- OPEN-TRUNC (port of ER `Sobolev/Ch4/H10Truncation.memH10_positivePart`): `(u - t)₊ ∈ H¹₀(U)`
for `u ∈ H¹₀(U)`, `t ≥ 0`, `U` open of finite volume. -/
theorem openH10PositivePart (d : ℕ) :
  ∀ {U : Set (Vec d)}, IsOpen U → volume U ≠ ⊤ → ∀ (u : H10Function U) {t : ℝ}, 0 ≤ t →
    MemH10 U (fun x => max (u.toH1Function.toFun x - t) 0) :=
  fun hU hfin u _ ht => memH10_positivePart hU hfin u ht

/-- Witness: the hypotheses of `openH10PositivePart` are met on the unit ball, for the zero
function (smooth, compactly supported) at level `1`. -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (fun x => max ((H10Function.ofContDiff (U := Metric.ball (0 : Vec 2) 1)
      Metric.isOpen_ball (f := fun _ => (0 : ℝ)) contDiff_const
      (HasCompactSupport.zero) (by simp)).toH1Function.toFun x - 1) 0) :=
  openH10PositivePart 2 Metric.isOpen_ball (measure_ball_lt_top (x := (0 : Vec 2)) (r := 1)).ne
    _ zero_le_one

end SuperdiffusionCLT.Section7
