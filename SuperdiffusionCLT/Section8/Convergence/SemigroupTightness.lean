/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupFdd

/-!
# Uniform small-time estimates from convergence of Feller semigroups

Let `S n` and `T` be Feller kernel semigroups on a proper metric space whose `C₀` semigroups
converge strongly.  Then the displacement of the process of `S n` in time `s` is small
uniformly in the starting point on a compact set, uniformly in `s ≤ h` and in all large `n`:
for every compact `K`, `r > 0` and `ε > 0` there are `h > 0` and `n₀` with
`S n s y {z | r ≤ dist z y} ≤ ε` for `n ≥ n₀`, `s ≤ h`, `y ∈ K`.  No moment bound is used.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Uniform

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [LocallyCompactSpace α]

/-- Strong convergence of the semigroups is uniform on bounded time intervals. -/
theorem sgConv_tendstoUniformlyOn_orbit
    {S : ℕ → SubMarkovKernelSemigroup α} {T : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hT : T.IsFellerKernelSemigroup)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    (f : C₀(α, ℝ)) (b : ℝ≥0) :
    TendstoUniformlyOn (fun n (t : ℝ≥0) ↦ (hS n).c0Semigroup t f)
      (fun t ↦ hT.c0Semigroup t f) atTop (Set.Iic b) := by
  let μ : Semigroup.PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  refine Semigroup.StronglyContinuousContractionSemigroup.tendstoUniformlyOn_operator_of_tendsto_resolvent
    (S := fun n ↦ (hS n).c0Semigroup) (S' := hT.c0Semigroup) (μ := μ) (fun y ↦ ?_) f b
  exact Semigroup.StronglyContinuousContractionSemigroup.tendsto_resolvent_of_tendsto_operator
    (fun t ↦ hconv t y) μ

end Uniform

section Bump

variable {α : Type*} [MetricSpace α] [ProperSpace α]

/-- The tent function `z ↦ (1 - dist z y / r)⁺` as an element of `C₀`. -/
def sgConv_bump (r : ℝ) (hr : 0 < r) (y : α) : C₀(α, ℝ) where
  toFun z := max 0 (1 - dist z y / r)
  continuous_toFun := by fun_prop
  zero_at_infty' := by
    refine tendsto_nhds_of_eventually_eq ?_
    have h : (Metric.closedBall y r)ᶜ ∈ cocompact α :=
      (isCompact_closedBall y r).compl_mem_cocompact
    filter_upwards [h] with z hz
    have hz' : r < dist z y := by simpa only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] using hz
    have : 1 - dist z y / r < 0 := by
      have : 1 < dist z y / r := by rw [lt_div_iff₀ hr]; linarith only [hz']
      linarith only [this]
    simp [max_eq_left this.le]

theorem sgConv_bump_apply (r : ℝ) (hr : 0 < r) (y z : α) :
    sgConv_bump r hr y z = max 0 (1 - dist z y / r) := rfl

theorem sgConv_bump_le_one (r : ℝ) (hr : 0 < r) (y z : α) : sgConv_bump r hr y z ≤ 1 := by
  rw [sgConv_bump_apply]
  refine max_le zero_le_one ?_
  have : 0 ≤ dist z y / r := by positivity
  linarith only [this]

theorem sgConv_bump_self (r : ℝ) (hr : 0 < r) (y : α) : sgConv_bump r hr y y = 1 := by
  simp [sgConv_bump_apply]

theorem sgConv_bump_eq_zero (r : ℝ) (hr : 0 < r) {y z : α} (h : r ≤ dist z y) :
    sgConv_bump r hr y z = 0 := by
  rw [sgConv_bump_apply]
  have : 1 ≤ dist z y / r := by rw [le_div_iff₀ hr]; linarith only [h]
  exact max_eq_left (by linarith only [this])

omit [ProperSpace α] in
theorem sgConv_norm_c0_le {f : C₀(α, ℝ)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ x, |f x| ≤ C) :
    ‖f‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le hC).mpr fun x ↦ by simpa only [ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using h x

omit [ProperSpace α] in
theorem sgConv_abs_apply_le_norm (f : C₀(α, ℝ)) (x : α) : |f x| ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  simpa only [ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, ZeroAtInftyContinuousMap.toBCF_apply, Real.norm_eq_abs] using f.toBCF.norm_coe_le_norm x

theorem sgConv_norm_bump_sub_le (r : ℝ) (hr : 0 < r) (y y' : α) :
    ‖sgConv_bump r hr y - sgConv_bump r hr y'‖ ≤ dist y y' / r := by
  refine sgConv_norm_c0_le (by positivity) fun z ↦ ?_
  have h1 : ((sgConv_bump r hr y - sgConv_bump r hr y' : C₀(α, ℝ)) z) =
      sgConv_bump r hr y z - sgConv_bump r hr y' z := rfl
  rw [h1, sgConv_bump_apply, sgConv_bump_apply]
  have hd : |dist z y - dist z y'| ≤ dist y y' := by
    rw [abs_le]; constructor
    · linarith only [dist_triangle z y y']
    · linarith only [dist_triangle z y' y, dist_comm y' y]
  have key := abs_max_sub_max_le_abs (1 - dist z y / r) (1 - dist z y' / r) 0
  rw [max_comm 0, max_comm 0 (1 - dist z y' / r)]
  refine key.trans ?_
  have : (1 - dist z y / r) - (1 - dist z y' / r) = (dist z y' - dist z y) / r := by ring
  rw [this, abs_div, abs_of_pos hr, abs_sub_comm]
  exact div_le_div_of_nonneg_right hd hr.le

theorem sgConv_measure_far_le (r : ℝ) (hr : 0 < r) (y : α) [MeasurableSpace α] [BorelSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    μ {z | r ≤ dist z y} ≤ ENNReal.ofReal (1 - ∫ z, sgConv_bump r hr y z ∂μ) := by
  have hA : MeasurableSet {z : α | r ≤ dist z y} :=
    measurableSet_le measurable_const (by fun_prop)
  have hint : Integrable (fun z ↦ sgConv_bump r hr y z) μ :=
    (sgConv_bump r hr y).toBCF.integrable μ
  have h1 : ∫ z, sgConv_bump r hr y z ∂μ + μ.real {z | r ≤ dist z y} ≤ 1 := by
    have hind : ∫ z, Set.indicator {z : α | r ≤ dist z y} (fun _ ↦ (1 : ℝ)) z ∂μ =
        μ.real {z | r ≤ dist z y} := by
      rw [integral_indicator hA]; simp
    rw [← hind, ← integral_add hint ((integrable_const (1 : ℝ)).indicator hA)]
    calc ∫ z, (sgConv_bump r hr y z + Set.indicator {z : α | r ≤ dist z y} (fun _ ↦ (1 : ℝ)) z) ∂μ
        ≤ ∫ _z, (1 : ℝ) ∂μ := by
          refine integral_mono (hint.add ((integrable_const (1 : ℝ)).indicator hA))
            (integrable_const _) fun z ↦ ?_
          by_cases hz : r ≤ dist z y
          · simp [Set.indicator_of_mem (show z ∈ {z : α | r ≤ dist z y} from hz),
              sgConv_bump_eq_zero r hr hz]
          · simp [Set.indicator_of_notMem (show z ∉ {z : α | r ≤ dist z y} from hz),
              sgConv_bump_le_one r hr y z]
      _ = 1 := by simp
  rw [← ofReal_measureReal (μ := μ) (s := {z | r ≤ dist z y})]
  exact ENNReal.ofReal_le_ofReal (by linarith only [h1])

end Bump

section SmallTime

variable {α : Type*} [MetricSpace α] [ProperSpace α] [MeasurableSpace α] [BorelSpace α]

/-- **Uniform small-time estimate.**  Along strongly convergent Feller semigroups, the transition
measures put at most `ε` of their mass outside the ball of radius `r` about the starting point,
uniformly for starting points in a compact set, small times and large indices. -/
theorem sgConv_small_time
    {S : ℕ → SubMarkovKernelSemigroup α} {T : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T.IsFellerKernelSemigroup)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {K : Set α} (hK : IsCompact K) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ h : ℝ≥0, 0 < h ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s : ℝ≥0, s ≤ h → ∀ y ∈ K,
      S n s y {z | r ≤ dist z y} ≤ ENNReal.ofReal ε := by
  obtain ⟨t, htK, htfin, htcov⟩ := hK.finite_cover_balls (e := r * ε / 8) (by positivity)
  have hε₁ : 0 < ε / 4 := by positivity
  -- small times, finitely many bumps
  have hsmall : ∀ᶠ s in nhds (0 : ℝ≥0), ∀ y ∈ t,
      ‖hT.c0Semigroup s (sgConv_bump r hr y) - sgConv_bump r hr y‖ < ε / 4 := by
    rw [Filter.eventually_all_finite htfin]
    intro y _
    have := hT.c0Semigroup.tendsto 0 (sgConv_bump r hr y)
    rw [hT.c0Semigroup.zero_apply] at this
    exact (Metric.tendsto_nhds.mp this (ε / 4) hε₁).mono fun s hs ↦ by
      simpa only [dist_eq_norm] using hs
  obtain ⟨δ, hδ, hδs⟩ := Metric.eventually_nhds_iff.mp hsmall
  -- large indices, finitely many bumps, uniformly on `[0,1]`
  have hlarge : ∀ᶠ n in atTop, ∀ y ∈ t, ∀ s ∈ Set.Iic (1 : ℝ≥0),
      dist (hT.c0Semigroup s (sgConv_bump r hr y)) ((hS n).c0Semigroup s (sgConv_bump r hr y))
        < ε / 4 := by
    rw [Filter.eventually_all_finite htfin]
    intro y _
    exact Metric.tendstoUniformlyOn_iff.mp
      (sgConv_tendstoUniformlyOn_orbit hS hT hconv (sgConv_bump r hr y) 1) (ε / 4) hε₁
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨min (Real.toNNReal (δ / 2)) 1, ?_, n₀, fun n hn s hs y hy ↦ ?_⟩
  · exact lt_min (Real.toNNReal_pos.mpr (half_pos hδ)) one_pos
  · obtain ⟨y₁, hy₁t, hy₁⟩ := Set.mem_iUnion₂.mp (htcov hy)
    have hsδ : dist s 0 < δ := by
      rw [NNReal.dist_eq]
      simp only [NNReal.coe_zero, sub_zero, NNReal.abs_eq]
      have := (hs.trans (min_le_left _ _))
      have h2 : (s : ℝ) ≤ δ / 2 := by
        have := (NNReal.coe_le_coe.mpr this)
        rwa [Real.coe_toNNReal _ (half_pos hδ).le] at this
      linarith only [h2, hδ]
    have hs1 : s ∈ Set.Iic (1 : ℝ≥0) := hs.trans (min_le_right _ _)
    have hA := hδs hsδ y₁ hy₁t
    have hB := hn₀ n hn y₁ hy₁t s hs1
    have hprob : IsProbabilityMeasure (S n s y) := (hSc n).isMarkovKernel s |>.isProbabilityMeasure y
    refine (sgConv_measure_far_le r hr y (S n s y)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hint : ∫ z, sgConv_bump r hr y z ∂S n s y = (hS n).c0Semigroup s (sgConv_bump r hr y) y :=
      rfl
    rw [hint]
    set f₁ := sgConv_bump r hr y₁
    set f := sgConv_bump r hr y
    have hdy : dist y y₁ < r * ε / 8 := hy₁
    have hff : ‖f - f₁‖ ≤ dist y y₁ / r := sgConv_norm_bump_sub_le r hr y y₁
    have hff' : dist y y₁ / r < ε / 8 := by
      rw [div_lt_iff₀ hr]; linarith only [hdy]
    have hop : ‖(hS n).c0Semigroup s (f₁ - f)‖ ≤ ‖f₁ - f‖ :=
      (hS n).c0Semigroup.norm_apply_le s _
    have hone : 1 - (hS n).c0Semigroup s f y ≤ ‖f - (hS n).c0Semigroup s f‖ := by
      have := sgConv_abs_apply_le_norm (f - (hS n).c0Semigroup s f) y
      have h1 : (f - (hS n).c0Semigroup s f) y = 1 - (hS n).c0Semigroup s f y := by
        change f y - (hS n).c0Semigroup s f y = _
        rw [show f y = 1 from sgConv_bump_self r hr y]
      rw [h1] at this
      exact (le_abs_self _).trans this
    have hdec : f - (hS n).c0Semigroup s f = (f - f₁) + (f₁ - hT.c0Semigroup s f₁) +
        (hT.c0Semigroup s f₁ - (hS n).c0Semigroup s f₁) + (hS n).c0Semigroup s (f₁ - f) := by
      rw [map_sub]; abel
    have hnorm : ‖f - (hS n).c0Semigroup s f‖ ≤ ‖f - f₁‖ + ‖f₁ - hT.c0Semigroup s f₁‖ +
        ‖hT.c0Semigroup s f₁ - (hS n).c0Semigroup s f₁‖ +
        ‖(hS n).c0Semigroup s (f₁ - f)‖ := by
      rw [hdec]
      exact norm_add₄_le
    have h2 : ‖f₁ - hT.c0Semigroup s f₁‖ < ε / 4 := by rw [norm_sub_rev]; exact hA
    have h3 : ‖hT.c0Semigroup s f₁ - (hS n).c0Semigroup s f₁‖ < ε / 4 := by
      rw [← dist_eq_norm]; exact hB
    have h4 : ‖(hS n).c0Semigroup s (f₁ - f)‖ ≤ ‖f - f₁‖ := by
      rw [norm_sub_rev f f₁] at *; exact hop
    have h5 := hone.trans hnorm
    have h6 : ‖f - f₁‖ < ε / 8 := lt_of_le_of_lt hff hff'
    linarith only [h5, h2, h3, h4, h6, hε]

end SmallTime

end

end SuperdiffusionCLT.Section8.Convergence
