/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.SemigroupPathConvergence
public import MarkovProcess.Continuity.PathTightness

/-!
# Tightness and convergence in law of the path laws of convergent Feller semigroups

Let `S n`, `T₀` be conservative Feller kernel semigroups on a proper metric space with
`S n t f → T₀ t f` in `C₀` for all `t` and `f`, `x n → x₀`, and `Q n`, `Q₀` probability laws on
continuous paths with the finite-dimensional distributions of `S n` from `x n`, resp. of `T₀` from
`x₀`.  Then `{Q₀} ∪ {Q n}` is tight (`sgConv_isTightMeasureSet`) and `Q n → Q₀` in distribution
(`sgConv_tendsto_pathLaw`).  No moment bound is assumed anywhere.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence
open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty BoundedContinuousFunction

noncomputable section

section Tight

variable {α : Type*} [MetricSpace α] [ProperSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

theorem sgConv_exists_pos_add_le (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η + ENNReal.ofReal η ≤ ε := by
  by_cases htop : ε = ⊤
  · exact ⟨1, one_pos, by simp [htop]⟩
  · refine ⟨ε.toReal / 2, by have := ENNReal.toReal_pos hε.ne' htop; positivity, ?_⟩
    rw [← ENNReal.ofReal_add (by have := ENNReal.toReal_pos hε.ne' htop; positivity)
      (by have := ENNReal.toReal_pos hε.ne' htop; positivity)]
    rw [add_halves, ENNReal.ofReal_toReal htop]

/-- **T2.  Tightness of the path laws from convergence of the semigroups.**  Let `S n`, `T₀` be
conservative Feller semigroups on a proper metric space with `S n t f → T₀ t f` in `C₀` for all
`t, f`, let `x n → x₀`, and let `Q n`, `Q₀` be probability laws on continuous paths with the
finite-dimensional distributions of `S n` from `x n`, resp. of `T₀` from `x₀`.  Then the family
`{Q₀} ∪ {Q n}` is tight.  No moment bound is assumed. -/
theorem sgConv_isTightMeasureSet
    {S : ℕ → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup) (hTc : T₀.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {x : ℕ → α} {x₀ : α} (hx : Tendsto x atTop (nhds x₀))
    {Q : ℕ → Measure (ContinuousPath α)} {Q₀ : Measure (ContinuousPath α)}
    [∀ n, IsProbabilityMeasure (Q n)] [IsProbabilityMeasure Q₀]
    (hfdd : ∀ n (I : Finset ℝ≥0), (Q n).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (S n) I (x n))
    (hfdd₀ : ∀ I : Finset ℝ≥0, Q₀.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel T₀ I x₀) :
    IsTightMeasureSet (insert Q₀ (Set.range Q)) := by
  obtain ⟨R0, hR0⟩ := (hx.isCompact_insert_range.isBounded).subset_closedBall x₀
  have hx0 : ∀ n, x n ∈ Metric.closedBall x₀ R0 := fun n ↦
    hR0 (Set.mem_insert_of_mem _ (Set.mem_range_self n))
  have hx00 : x₀ ∈ Metric.closedBall x₀ R0 := hR0 (Set.mem_insert _ _)
  refine ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le
    (K0 := Metric.closedBall x₀ R0) (isCompact_closedBall x₀ R0) ?_ ?_
  · have hsub : ∀ y, y ∈ Metric.closedBall x₀ R0 →
        {ω : ContinuousPath α | ω 0 ∉ Metric.closedBall x₀ R0} ⊆ {ω | ω 0 ≠ y} :=
      fun y hy ω (hω : ω 0 ∉ Metric.closedBall x₀ R0) (h : ω 0 = y) ↦ hω (h ▸ hy)
    rintro μ (rfl | ⟨n, rfl⟩)
    · exact measure_mono_null (hsub x₀ hx00) (sgConv_start_ae T₀ hTc x₀ hfdd₀)
    · exact measure_mono_null (hsub (x n) (hx0 n)) (sgConv_start_ae (S n) (hSc n) (x n) (hfdd n))
  · intro T r hr eps heps
    by_cases hrtop : r = ⊤
    · refine ⟨1, one_pos, fun μ _ ↦ ?_⟩
      have : (ContinuousPath.modulusSet (alpha := α) T 1 r)ᶜ = ∅ := by
        ext ω
        simp [ContinuousPath.modulusSet, hrtop]
      simp [this]
    set κ : ℝ := r.toReal with hκ
    have hκpos : 0 < κ := ENNReal.toReal_pos hr.ne' hrtop
    have hreq : r = ENNReal.ofReal κ := (ENNReal.ofReal_toReal hrtop).symm
    obtain ⟨η, hη, hηeps⟩ := sgConv_exists_pos_add_le eps heps
    obtain ⟨R, n₁, hn₁⟩ := sgConv_compact_containment hS hSc hT hTc hconv hx hfdd hfdd₀ T hη
    set Rm : ℝ := max R R0 with hRm
    have hKcpt : IsCompact (Metric.closedBall x₀ Rm) := isCompact_closedBall x₀ Rm
    have hxK : ∀ n, x n ∈ Metric.closedBall x₀ Rm := fun n ↦ by
      have := Metric.mem_closedBall.mp (hx0 n)
      exact Metric.mem_closedBall.mpr (this.trans (le_max_right _ _))
    obtain ⟨δ₀, hδ₀, n₀, hn₀⟩ := sgConv_modEvent_le_semigroup hS hSc hT hconv (Q := Q) hfdd hKcpt
      hxK (r := κ / 4) (by positivity) T hη
    obtain ⟨δ₁, hδ₁, h₁⟩ := sgConv_exists_modulus_le_finite Q T hr heps (max n₁ n₀)
    obtain ⟨δ₂, hδ₂, h₂⟩ := sgConv_exists_modulus_le Q₀ T hr heps
    refine ⟨min (δ₀ : ℝ≥0∞) (min δ₁ δ₂), lt_min (by exact_mod_cast hδ₀) (lt_min hδ₁ hδ₂), ?_⟩
    rintro μ (rfl | ⟨n, rfl⟩)
    · exact (measure_mono (sgConv_modulus_compl_anti T
        ((min_le_right _ _).trans (min_le_right _ _)))).trans h₂
    · by_cases hn : n < max n₁ n₀
      · exact (measure_mono (sgConv_modulus_compl_anti T
          ((min_le_right _ _).trans (min_le_left _ _)))).trans (h₁ n hn)
      · have hn' : max n₁ n₀ ≤ n := not_lt.mp hn
        have hnn1 : n₁ ≤ n := (le_max_left _ _).trans hn'
        have hnn0 : n₀ ≤ n := (le_max_right _ _).trans hn'
        have hsub := sgConv_modulus_compl_subset x₀ Rm hκpos.le T δ₀
        rw [← hreq] at hsub
        have hmono := sgConv_modulus_compl_anti (α := α) T (r := r)
          ((min_le_left _ _) : min (δ₀ : ℝ≥0∞) (min δ₁ δ₂) ≤ δ₀)
        calc Q n (ContinuousPath.modulusSet T (min (δ₀ : ℝ≥0∞) (min δ₁ δ₂)) r)ᶜ
            ≤ Q n (sgConv_exitSet x₀ T Rm ∪ sgConv_modEvent (Metric.closedBall x₀ Rm) T δ₀ κ) :=
              measure_mono (hmono.trans hsub)
          _ ≤ Q n (sgConv_exitSet x₀ T Rm) + Q n (sgConv_modEvent (Metric.closedBall x₀ Rm) T δ₀ κ) :=
              measure_union_le _ _
          _ ≤ ENNReal.ofReal η + ENNReal.ofReal η := by
              refine add_le_add ?_ ?_
              · exact (measure_mono (sgConv_exitSet_antitone x₀ T (le_max_left R R0))).trans
                  (hn₁ n hnn1)
              · have := hn₀ n hnn0
                rwa [show 4 * (κ / 4) = κ by ring] at this
          _ ≤ eps := hηeps

/-- **Convergence of the expectations of bounded continuous path functionals.** -/
theorem sgConv_tendsto_integral
    {S : ℕ → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup) (hTc : T₀.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {x : ℕ → α} {x₀ : α} (hx : Tendsto x atTop (nhds x₀))
    {Q : ℕ → Measure (ContinuousPath α)} {Q₀ : Measure (ContinuousPath α)}
    [∀ n, IsProbabilityMeasure (Q n)] [IsProbabilityMeasure Q₀]
    (hfdd : ∀ n (I : Finset ℝ≥0), (Q n).map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel (S n) I (x n))
    (hfdd₀ : ∀ I : Finset ℝ≥0, Q₀.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel T₀ I x₀)
    (F : ContinuousPath α →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ ω, F ω ∂(Q n)) atTop (nhds (∫ ω, F ω ∂Q₀)) := by
  have htight := sgConv_isTightMeasureSet hS hSc hT hTc hconv hx hfdd hfdd₀
  rw [Metric.tendsto_nhds]
  intro eps heps
  set eps5 : ℝ := eps / 5 with heps5def
  have heps5 : 0 < eps5 := by positivity
  set Ctot : ℝ := ‖F‖ + (‖F‖ + eps5) with hCtotdef
  have hCtotpos : 0 < Ctot := by
    rw [hCtotdef]
    have := norm_nonneg F
    linarith only [this, heps5]
  set eta : ℝ := eps5 / Ctot with hetadef
  have hetapos : 0 < eta := div_pos heps5 hCtotpos
  obtain ⟨Kp, hKpcompact, hKmass⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight (ENNReal.ofReal eta)
      (ENNReal.ofReal_pos.mpr hetapos)
  obtain ⟨G, hGcyl, hGnorm, hGapprox⟩ :=
    ContinuousPath.exists_boundedCylinder_approx F hKpcompact heps5
  have hKpmeas : MeasurableSet Kp := hKpcompact.isClosed.measurableSet
  have herror : ∀ mu : Measure (ContinuousPath α), IsProbabilityMeasure mu →
      mu Kpᶜ ≤ ENNReal.ofReal eta →
      |(∫ omega, F omega ∂mu) - ∫ omega, G omega ∂mu| ≤ 2 * eps5 := by
    intro mu hmuprob hmass
    have hmassreal : mu.real Kpᶜ ≤ eta := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal hetapos.le hmass
    have hbase := abs_integral_sub_le_of_approx_on mu F G hKpmeas heps5.le hGapprox
    have hFG : ‖F‖ + ‖G‖ ≤ Ctot := by
      rw [hCtotdef]
      linarith only [hGnorm]
    have hprod : (‖F‖ + ‖G‖) * mu.real Kpᶜ ≤ eps5 := by
      calc (‖F‖ + ‖G‖) * mu.real Kpᶜ ≤ Ctot * eta :=
            mul_le_mul hFG hmassreal measureReal_nonneg hCtotpos.le
        _ = eps5 := by
            rw [hetadef]
            field_simp
    linarith only [hbase, hprod]
  obtain ⟨I, g, hg⟩ := hGcyl
  have hcyl : Tendsto (fun n ↦ ∫ omega, G omega ∂(Q n)) atTop
      (nhds (∫ omega, G omega ∂Q₀)) := by
    simp only [hg]
    exact sgConv_tendsto_integral_finsetEvaluation hS hSc hT hTc hconv hx hfdd hfdd₀ I g
  have hnear : ∀ᶠ n in atTop, |(∫ omega, G omega ∂(Q n)) - ∫ omega, G omega ∂Q₀| < eps5 := by
    have h := Metric.tendsto_nhds.mp hcyl eps5 heps5
    simpa only [Real.dist_eq] using h
  filter_upwards [hnear] with n hinear
  rw [Real.dist_eq]
  have h1 := herror (Q n) inferInstance (hKmass (Q n) (Set.mem_insert_of_mem _ ⟨n, rfl⟩))
  have h2 := herror Q₀ inferInstance (hKmass Q₀ (Set.mem_insert _ _))
  have h2' : |(∫ omega, G omega ∂Q₀) - ∫ omega, F omega ∂Q₀| ≤ 2 * eps5 := by
    rw [abs_sub_comm]
    exact h2
  have htri1 := abs_sub_le (∫ omega, F omega ∂(Q n)) (∫ omega, G omega ∂(Q n))
    (∫ omega, F omega ∂Q₀)
  have htri2 := abs_sub_le (∫ omega, G omega ∂(Q n)) (∫ omega, G omega ∂Q₀)
    (∫ omega, F omega ∂Q₀)
  rw [heps5def] at h1 h2' hinear
  linarith only [htri1, htri2, h1, h2', hinear]

/-- **Convergence in law of the path laws, along a sequence** (the conclusion of the
convergence step): in the space of probability measures on `C(ℝ≥0, α)` with its topology of
convergence in distribution, `Q n → Q₀`. -/
theorem sgConv_tendsto_pathLaw
    {S : ℕ → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ n, (S n).IsFellerKernelSemigroup) (hSc : ∀ n, (S n).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup) (hTc : T₀.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun n ↦ (hS n).c0Semigroup t f) atTop (nhds (hT.c0Semigroup t f)))
    {x : ℕ → α} {x₀ : α} (hx : Tendsto x atTop (nhds x₀))
    {Q : ℕ → ProbabilityMeasure (ContinuousPath α)} {Q₀ : ProbabilityMeasure (ContinuousPath α)}
    (hfdd : ∀ n (I : Finset ℝ≥0),
      (Q n : Measure (ContinuousPath α)).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel (S n) I (x n))
    (hfdd₀ : ∀ I : Finset ℝ≥0,
      (Q₀ : Measure (ContinuousPath α)).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel T₀ I x₀) :
    Tendsto Q atTop (nhds Q₀) :=
  ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr fun F ↦
    sgConv_tendsto_integral hS hSc hT hTc hconv hx (Q := fun n ↦ (Q n : Measure _))
      (Q₀ := (Q₀ : Measure _)) hfdd hfdd₀ F

/-- The same along any countably generated filter, by the sequential characterisation. -/
theorem sgConv_tendsto_pathLaw_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {S : ι → SubMarkovKernelSemigroup α} {T₀ : SubMarkovKernelSemigroup α}
    (hS : ∀ i, (S i).IsFellerKernelSemigroup) (hSc : ∀ i, (S i).IsConservative)
    (hT : T₀.IsFellerKernelSemigroup) (hTc : T₀.IsConservative)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(α, ℝ)),
      Tendsto (fun i ↦ (hS i).c0Semigroup t f) l (nhds (hT.c0Semigroup t f)))
    {x : ι → α} {x₀ : α} (hx : Tendsto x l (nhds x₀))
    {Q : ι → ProbabilityMeasure (ContinuousPath α)} {Q₀ : ProbabilityMeasure (ContinuousPath α)}
    (hfdd : ∀ i (I : Finset ℝ≥0),
      (Q i : Measure (ContinuousPath α)).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel (S i) I (x i))
    (hfdd₀ : ∀ I : Finset ℝ≥0,
      (Q₀ : Measure (ContinuousPath α)).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel T₀ I x₀) :
    Tendsto Q l (nhds Q₀) := by
  refine tendsto_iff_seq_tendsto.mpr fun u hu ↦ ?_
  exact sgConv_tendsto_pathLaw (S := fun n ↦ S (u n)) (fun n ↦ hS (u n)) (fun n ↦ hSc (u n)) hT
    hTc (fun t f ↦ (hconv t f).comp hu) (hx.comp hu) (Q := fun n ↦ Q (u n)) (Q₀ := Q₀)
    (fun n I ↦ hfdd (u n) I) hfdd₀

end Tight

section Witness

/-- Satisfiability of `sgConv_tendsto_pathLaw`: the constant sequence of heat semigroups, started
at a convergent sequence of points, with the laws of Brownian motion. -/
example (d : ℕ) {x : ℕ → Vec d} {x₀ : Vec d} (hx : Tendsto x atTop (nhds x₀)) :
    ∃ (Q : ℕ → ProbabilityMeasure (ContinuousPath (Vec d)))
      (Q₀ : ProbabilityMeasure (ContinuousPath (Vec d))), Tendsto Q atTop (nhds Q₀) := by
  refine ⟨fun n ↦ ⟨Brownian.brownianMotion d (x n), inferInstance⟩,
    ⟨Brownian.brownianMotion d x₀, inferInstance⟩, ?_⟩
  refine sgConv_tendsto_pathLaw (S := fun _ ↦ Brownian.heatSemigroup d)
    (T₀ := Brownian.heatSemigroup d) (fun _ ↦ Brownian.isFellerKernelSemigroup_heatSemigroup d)
    (fun _ ↦ Brownian.isConservative_heatSemigroup d)
    (Brownian.isFellerKernelSemigroup_heatSemigroup d)
    (Brownian.isConservative_heatSemigroup d) (fun _ _ ↦ tendsto_const_nhds) hx
    (x := x) (x₀ := x₀) (fun n I ↦ ?_) (fun I ↦ ?_)
  · show (Brownian.brownianMotion d (x n)).map (ContinuousPath.finsetEvaluation I) = _
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
      Brownian.brownianMotion_map_finsetEvaluation]
  · show (Brownian.brownianMotion d x₀).map (ContinuousPath.finsetEvaluation I) = _
    rw [← Kernel.map_apply _ (ContinuousPath.measurable_finsetEvaluation I),
      Brownian.brownianMotion_map_finsetEvaluation]

end Witness

end
end SuperdiffusionCLT.Section8.Convergence
