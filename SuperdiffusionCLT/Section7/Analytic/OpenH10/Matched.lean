/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.H10Truncation
public import Homogenization.Sobolev.Truncation.MatchedTrace

/-!
# Matched truncation on open sets

If `w₁ - w₂ ∈ H¹₀(U)` on an open set `U` of finite volume, then
`(w₁ - c)₊ - (w₂ - c)₊ ∈ H¹₀(U)`.  This is the open-set version of
`Homogenization.memH10_max_sub_matched` (which needs a convex domain).
-/

@[expose] public section

open scoped ENNReal Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

/-- **Matched truncation on an open set.** -/
theorem memH10_max_sub_matched_open {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w₁ w₂ : H1Function U)
    (hmatch : MemH10 U (fun x => w₁.toFun x - w₂.toFun x)) (c : ℝ) :
    MemH10 U (fun x => max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0) := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn U) := ⟨by simpa [volumeMeasureOn] using hfin.lt_top⟩
  -- `h := w₁ − w₂` and its `H¹₀` witness `W`.
  set h : H1Function U := w₁ - w₂ with hh_def
  obtain ⟨W, hWtf⟩ := hmatch
  have hWh : W.toH1Function.toFun = h.toFun := by
    rw [hWtf, hh_def, H1Function.sub_toFun]
  set Φ : ℕ → H1Function U := fun n =>
    (H10Function.ofContDiff hU (W.approx_smooth n) (W.approx_hasCompactSupport n)
      (W.approx_support_subset n)).toH1Function with hΦ_def
  set S : ℕ → H1Function U := fun n => w₂ + Φ n with hS_def
  -- D1 truncations of `w₂`, `w₁`, and each `w₂ + φ_n`.
  have hD1 : ∀ n, ∃ v : H1Function U,
      v.toFun = (fun x => max ((S n).toFun x - c) 0) ∧
      (∀ᵐ x ∂(volumeMeasureOn U),
        v.grad x = {y | c < (S n).toFun y}.indicator (S n).grad x) :=
    fun n => ⟨positivePartOpen hU (S n) c (memL2On_positivePart_of_finite (S n) hfin c),
      rfl, Filter.Eventually.of_forall fun x => rfl⟩
  obtain ⟨V2, hV2f, hV2g⟩ : ∃ v : H1Function U,
      v.toFun = (fun x => max (w₂.toFun x - c) 0) ∧
      (∀ᵐ x ∂(volumeMeasureOn U),
        v.grad x = {y | c < w₂.toFun y}.indicator w₂.grad x) :=
    ⟨positivePartOpen hU w₂ c (memL2On_positivePart_of_finite w₂ hfin c),
      rfl, Filter.Eventually.of_forall fun x => rfl⟩
  obtain ⟨V1', hV1'f, hV1'g⟩ : ∃ v : H1Function U,
      v.toFun = (fun x => max (w₁.toFun x - c) 0) ∧
      (∀ᵐ x ∂(volumeMeasureOn U),
        v.grad x = {y | c < w₁.toFun y}.indicator w₁.grad x) :=
    ⟨positivePartOpen hU w₁ c (memL2On_positivePart_of_finite w₁ hfin c),
      rfl, Filter.Eventually.of_forall fun x => rfl⟩
  choose V1 hV1f hV1g using hD1
  -- Target `H¹` function `T := (w₁−c)₊ − (w₂−c)₊`.
  set T : H1Function U := V1' - V2 with hT_def
  have hTtf : T.toFun = fun x => max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0 := by
    funext x
    rw [hT_def, H1Function.sub_toFun]
    show V1'.toFun x - V2.toFun x = _
    rw [congrFun hV1'f x, congrFun hV2f x]
  rw [show (fun x => max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0) = T.toFun from hTtf.symm]
  -- Weak-gradient uniqueness bridge `W.grad =ᵐ h.grad`.
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hWgrad : ∀ i : Fin d,
      (fun x => W.toH1Function.grad x i) =ᵐ[volumeMeasureOn U] (fun x => h.grad x i) := by
    intro i
    have hw := W.toH1Function.hasWeakGradient i
    rw [hWh] at hw
    exact HasWeakPartialDerivOn.ae_eq hU (hloc _ i) (hloc _ i) hw (h.hasWeakGradient i)
  -- Level-set vanishing of `∇w₁`.
  have hD2 : ∀ᵐ x ∂(volumeMeasureOn U), w₁.toFun x = c → w₁.grad x = 0 :=
    grad_ae_zero_on_level_set hU hfin w₁ c
  -- Measurability of Heaviside factors.
  have hind_aesm : ∀ (g : Vec d → ℝ), AEStronglyMeasurable g (volumeMeasureOn U) →
      AEStronglyMeasurable (fun x => if c < g x then (1:ℝ) else 0) (volumeMeasureOn U) := by
    intro g hg
    have hk : Measurable (fun t : ℝ => if c < t then (1:ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const
    exact (hk.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
  -- Each `Ψ_n = V1 n − V2` lies in `H¹₀`.
  have hΨmem : ∀ n, MemH10 U (V1 n - V2).toFun := by
    intro n
    have hz : ∀ x ∈ U, x ∉ tsupport (W.approx n) → (V1 n - V2).toFun x = 0 := by
      intro x _ hx
      have hφ0 : W.approx n x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hSx : (S n).toFun x = w₂.toFun x := by
        show w₂.toFun x + (Φ n).toFun x = w₂.toFun x
        rw [show (Φ n).toFun x = W.approx n x from rfl, hφ0, add_zero]
      have e1 : (V1 n).toFun x = max ((S n).toFun x - c) 0 := congrFun (hV1f n) x
      have e2 : V2.toFun x = max (w₂.toFun x - c) 0 := congrFun hV2f x
      show (V1 n - V2).toFun x = 0
      rw [H1Function.sub_toFun]
      show (V1 n).toFun x - V2.toFun x = 0
      rw [e1, e2, hSx]; ring
    exact ⟨toH10OfCompact hU (V1 n - V2) (W.approx_support_subset n)
      (W.approx_hasCompactSupport n) hz,
      congrArg H1Function.toFun
        (toH10OfCompact_toH1Function hU (V1 n - V2) (W.approx_support_subset n)
          (W.approx_hasCompactSupport n) hz)⟩
  -- L² convergence of `φ_n → h` (function side).
  have hWconv : Tendsto
      (fun n => eLpNorm (fun x => W.approx n x - h.toFun x) 2 (volumeMeasureOn U))
      atTop (nhds 0) := by
    refine W.tendsto_approx.congr (fun n => ?_)
    rw [hWh]
  -- a.e.-convergent subsequence.
  obtain ⟨σ, hσ_mono, hσ_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hWconv).exists_seq_tendsto_ae
  -- Assemble via the `H¹₀`-limit lemma.
  refine memH10_of_tendsto_H1 hU T (fun n => V1 (σ n) - V2) (fun n => hΨmem (σ n)) ?_ ?_
  · -- Function convergence.
    have hlip : ∀ A B : ℝ, |max A 0 - max B 0| ≤ |A - B| := by
      intro A B
      calc |max A 0 - max B 0| ≤ max |A - B| |(0:ℝ) - 0| := abs_max_sub_max_le_max A 0 B 0
        _ = |A - B| := by rw [sub_self, abs_zero]; exact max_eq_left (abs_nonneg _)
    have hub : Tendsto
        (fun n => eLpNorm (fun x => h.toFun x - W.approx (σ n) x) 2 (volumeMeasureOn U))
        atTop (nhds 0) := by
      have hswap : ∀ n,
          eLpNorm (fun x => h.toFun x - W.approx (σ n) x) 2 (volumeMeasureOn U)
            = eLpNorm (fun x => W.approx (σ n) x - h.toFun x) 2 (volumeMeasureOn U) :=
        fun n => eLpNorm_sub_swap _ _
      simp_rw [hswap]
      exact hWconv.comp hσ_mono.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun n => zero_le) (fun n => ?_)
    refine eLpNorm_mono
      (T.memL2.aestronglyMeasurable.fun_sub (V1 (σ n) - V2).memL2.aestronglyMeasurable)
      (fun x => ?_)
    have hTx : T.toFun x = max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0 := congrFun hTtf x
    have hΨx : (V1 (σ n) - V2).toFun x
        = max ((S (σ n)).toFun x - c) 0 - max (w₂.toFun x - c) 0 := by
      rw [H1Function.sub_toFun]
      show (V1 (σ n)).toFun x - V2.toFun x = _
      rw [congrFun (hV1f (σ n)) x, congrFun hV2f x]
    rw [hTx, hΨx, Real.norm_eq_abs, Real.norm_eq_abs,
      show max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0 -
            (max ((S (σ n)).toFun x - c) 0 - max (w₂.toFun x - c) 0)
          = max (w₁.toFun x - c) 0 - max ((S (σ n)).toFun x - c) 0 from by ring]
    refine (hlip _ _).trans (le_of_eq ?_)
    rw [show (w₁.toFun x - c) - ((S (σ n)).toFun x - c) = h.toFun x - W.approx (σ n) x from by
      have hSrfl : (S (σ n)).toFun x = w₂.toFun x + W.approx (σ n) x := rfl
      rw [hSrfl, show h.toFun x = w₁.toFun x - w₂.toFun x from
        congrFun (H1Function.sub_toFun w₁ w₂) x]
      ring]
  · -- Gradient convergence (coordinatewise).
    intro i
    have haesm_ind' :
        AEStronglyMeasurable (fun x => if c < w₁.toFun x then (1:ℝ) else 0) (volumeMeasureOn U) :=
      hind_aesm w₁.toFun w₁.memL2.aestronglyMeasurable
    have haesm_indn : ∀ n,
        AEStronglyMeasurable (fun x => if c < (S n).toFun x then (1:ℝ) else 0)
          (volumeMeasureOn U) :=
      fun n => hind_aesm (S n).toFun (S n).memL2.aestronglyMeasurable
    set TA : ℕ → Vec d → ℝ :=
      fun n x => (if c < (S n).toFun x then (1:ℝ) else 0) * (h.grad x i - (Φ n).grad x i)
      with hTA_def
    set TB : ℕ → Vec d → ℝ :=
      fun n x => ((if c < w₁.toFun x then (1:ℝ) else 0)
          - (if c < (S n).toFun x then (1:ℝ) else 0)) * w₁.grad x i with hTB_def
    have indic : ∀ (Sset : Set (Vec d)) (g : Vec d → Vec d) (x : Vec d),
        (Sset.indicator g x) i = if x ∈ Sset then g x i else 0 := by
      intro Sset g x
      by_cases hxs : x ∈ Sset
      · rw [Set.indicator_of_mem hxs, ite_eq_left hxs]
      · rw [Set.indicator_of_notMem hxs, ite_eq_right hxs]; rfl
    -- The actual gradient difference equals `TA + TB` a.e.
    have hkey : ∀ n, (fun x => V1'.grad x i - (V1 n).grad x i)
        =ᵐ[volumeMeasureOn U] (fun x => TA n x + TB n x) := by
      intro n
      filter_upwards [hV1'g, hV1g n] with x hx' hxn
      have e' : V1'.grad x i = if c < w₁.toFun x then w₁.grad x i else 0 := by
        rw [hx', indic]; simp only [Set.mem_ofPred_eq]
      have en : (V1 n).grad x i = if c < (S n).toFun x then (S n).grad x i else 0 := by
        rw [hxn, indic]; simp only [Set.mem_ofPred_eq]
      have eSg : (S n).grad x i = w₂.grad x i + (Φ n).grad x i := rfl
      have hw1g : w₁.grad x i = w₂.grad x i + h.grad x i := by
        have hsg : h.grad x i = w₁.grad x i - w₂.grad x i :=
          congrFun (congrFun (H1Function.sub_grad w₁ w₂) x) i
        linarith only [hsg]
      rw [e', en, eSg]
      simp only [hTA_def, hTB_def]
      rw [hw1g]
      split_ifs <;> ring
    have haesm_TA : ∀ n, AEStronglyMeasurable (TA n) (volumeMeasureOn U) := by
      intro n
      exact (haesm_indn n).mul
        ((h.gradMemL2 i).aestronglyMeasurable.sub ((Φ n).gradMemL2 i).aestronglyMeasurable)
    have haesm_TB : ∀ n, AEStronglyMeasurable (TB n) (volumeMeasureOn U) := by
      intro n
      exact (haesm_ind'.sub (haesm_indn n)).mul (w₁.gradMemL2 i).aestronglyMeasurable
    -- `‖TA_n‖ ≤ ‖∇φ_n − ∇h‖` → 0 in L².
    have hEconv : Tendsto
        (fun n => eLpNorm (fun x => h.grad x i - (Φ n).grad x i) 2 (volumeMeasureOn U))
        atTop (nhds 0) := by
      have heq : ∀ n,
          eLpNorm (fun x => h.grad x i - (Φ n).grad x i) 2 (volumeMeasureOn U)
            = eLpNorm (fun x => (Φ n).grad x i - W.toH1Function.grad x i) 2
                (volumeMeasureOn U) := by
        intro n
        rw [eLpNorm_sub_swap (fun x => h.grad x i) (fun x => (Φ n).grad x i)]
        exact eLpNorm_congr_ae (by filter_upwards [hWgrad i] with x hx; rw [hx])
      simp_rw [heq]
      exact W.tendsto_approx_grad i
    have hTA_conv : Tendsto (fun n => eLpNorm (TA n) 2 (volumeMeasureOn U)) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hEconv
        (fun n => zero_le) (fun n => ?_)
      refine eLpNorm_mono (haesm_TA n) (fun x => ?_)
      simp only [hTA_def]
      rw [norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs]
      by_cases hc : c < (S n).toFun x <;> simp [hc]
    -- `‖TB_{σn}‖ → 0` in L² by dominated convergence.
    have hTB_conv : Tendsto
        (fun n => eLpNorm (fun x => TB (σ n) x) 2 (volumeMeasureOn U)) atTop (nhds 0) := by
      have hdom : MemLp (fun x => ‖w₁.grad x i‖) 2 (volumeMeasureOn U) := (w₁.gradMemL2 i).norm
      have hbnd : ∀ n, ∀ᵐ x ∂(volumeMeasureOn U), ‖TB (σ n) x‖ ≤ ‖w₁.grad x i‖ := by
        intro n
        filter_upwards with x
        simp only [hTB_def]
        rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs]
        by_cases hA : c < w₁.toFun x <;> by_cases hB : c < (S (σ n)).toFun x <;> simp [hA, hB]
      have hae : ∀ᵐ x ∂(volumeMeasureOn U), Tendsto (fun n => TB (σ n) x) atTop (nhds 0) := by
        filter_upwards [hσ_ae, hD2] with x hxconv hxD2
        have hSconv : Tendsto (fun n => w₂.toFun x + W.approx (σ n) x) atTop
            (nhds (w₁.toFun x)) := by
          have hcur := (tendsto_const_nhds (x := w₂.toFun x)).add hxconv
          rwa [show w₂.toFun x + h.toFun x = w₁.toFun x from by
            rw [show h.toFun x = w₁.toFun x - w₂.toFun x from
              congrFun (H1Function.sub_toFun w₁ w₂) x]; ring] at hcur
        rcases lt_trichotomy c (w₁.toFun x) with hlt | heqc | hgt
        · have hev : ∀ᶠ n in atTop, c < (S (σ n)).toFun x := by
            filter_upwards [hSconv.eventually_const_lt hlt] with n hn using hn
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [hev] with n hn
          simp only [hTB_def]; rw [ite_eq_left hlt, ite_eq_left hn]; ring
        · have hg0 : w₁.grad x i = 0 := by simp [hxD2 heqc.symm]
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards with n
          simp only [hTB_def, hg0, mul_zero]
        · have hev : ∀ᶠ n in atTop, ¬ c < (S (σ n)).toFun x := by
            filter_upwards [hSconv.eventually_lt_const hgt] with n hn using not_lt.mpr hn.le
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [hev] with n hn
          simp only [hTB_def]; rw [ite_eq_right (not_lt.mpr hgt.le), ite_eq_right hn]; ring
      have hmain := tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
        (fun n => haesm_TB (σ n)) (memLp_const (0:ℝ)) hdom hbnd hae
      simpa using hmain
    -- Combine.
    have hsum : Tendsto (fun n => eLpNorm (TA (σ n)) 2 (volumeMeasureOn U)
        + eLpNorm (fun x => TB (σ n) x) 2 (volumeMeasureOn U)) atTop (nhds 0) := by
      simpa using (hTA_conv.comp hσ_mono.tendsto_atTop).add hTB_conv
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun n => zero_le) (fun n => ?_)
    have hVcancel : (fun x => T.grad x i - (V1 (σ n) - V2).grad x i)
        = (fun x => V1'.grad x i - (V1 (σ n)).grad x i) := by
      funext x
      simp only [hT_def, H1Function.sub_grad, Pi.sub_apply]
      ring
    rw [hVcancel, eLpNorm_congr_ae (hkey (σ n))]
    exact eLpNorm_add_le (by norm_num)


/-- OPEN-MATCHED (CoarseGraining `memH10_max_sub_matched`, generalized from convex to open `U`). -/
theorem openH10Matched (d : ℕ) :
  ∀ {U : Set (Vec d)}, IsOpen U → volume U ≠ ⊤ → ∀ (w₁ w₂ : H1Function U),
    MemH10 U (fun x => w₁.toFun x - w₂.toFun x) → ∀ c : ℝ,
      MemH10 U (fun x => max (w₁.toFun x - c) 0 - max (w₂.toFun x - c) 0) :=
  fun hU hfin w₁ w₂ hm c => memH10_max_sub_matched_open hU hfin w₁ w₂ hm c

/-- Witness: the hypotheses of `openH10Matched` hold on the unit ball for the zero function. -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (fun x => max ((0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x - 1) 0 -
      max ((0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x - 1) 0) :=
  openH10Matched 2 Metric.isOpen_ball (measure_ball_lt_top (x := (0 : Vec 2)) (r := 1)).ne 0 0
    ⟨H10Function.ofContDiff (U := Metric.ball (0 : Vec 2) 1) Metric.isOpen_ball
      (f := fun _ => (0 : ℝ)) contDiff_const HasCompactSupport.zero (by simp), by
      funext x; simp [H10Function.ofContDiff, H1Function.ofContDiff]⟩ 1

end SuperdiffusionCLT.Section7
