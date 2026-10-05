/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.RealizationDivFree
public import SuperdiffusionCLT.Probability.StationaryProjectionConditional
public import SuperdiffusionCLT.Probability.RealizationSecondConjunctC
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import SuperdiffusionCLT.Probability.RealizationConjunctTwo
public import Homogenization.Sobolev.Foundations.CoerciveH10
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Closing the first left-hand-side estimate

Countable density of compactly supported gradients follows from finite-coordinate
L² convergence and separability. Bounded smears give horizontal gradients, and
Fubini transfers their solenoidal pairings to spatial test functions. Indicator
tests and invariance remove the representative and exceptional-set issues.
-/

@[expose] public section

open scoped Topology
noncomputable section
namespace SuperdiffusionCLT.Probability.Stationary
variable {d : ℕ} {U : Set (Homogenization.Vec d)}

def lhsClosing_coordEmbed (i : Fin d) : ℝ →L[ℝ] Homogenization.HilbertVec d :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight
    (Homogenization.HilbertVec.ofVec (Homogenization.basisVec i))

theorem lhsClosing_sum_coe (s : Finset (Fin d))
    (f : Fin d → Homogenization.HilbertVectorL2 U) :
    (fun x => (∑ i ∈ s, f i) x) =ᵐ[Homogenization.volumeMeasureOn U]
      fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero _ _ _
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [MeasureTheory.Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hx hi
    exact hx.trans (congrArg (fun z => f a x + z) hi)

theorem lhsClosing_gradient_sum (u : Homogenization.H1Function U) :
    u.gradToHilbertVectorL2 = ∑ i : Fin d,
      (lhsClosing_coordEmbed i).compLpL 2 (Homogenization.volumeMeasureOn U)
        (u.gradCoordToScalarL2 i) := by
  apply MeasureTheory.Lp.ext
  have hc := fun i => ((lhsClosing_coordEmbed i).coeFn_compLpL (u.gradCoordToScalarL2 i)).trans
      ((Homogenization.H1Function.coeFn_gradCoordToScalarL2 u i).fun_comp
        (lhsClosing_coordEmbed i))
  filter_upwards [Homogenization.H1Function.coeFn_gradToHilbertVectorL2 u,
    lhsClosing_sum_coe Finset.univ (fun i => (lhsClosing_coordEmbed i).compLpL 2
      (Homogenization.volumeMeasureOn U) (u.gradCoordToScalarL2 i)),
    MeasureTheory.ae_all_iff.mpr hc] with x hu hs hc
  rw [hu, hs]
  simp only [hc]
  apply PiLp.ext
  intro j
  simp [lhsClosing_coordEmbed, Homogenization.basisVec,
    Homogenization.hilbertifyVecField, Pi.single_apply]

/-- The smooth H¹₀ approximants converge in the vector gradient norm. -/
theorem lhsClosing_tendsto_gradient (hU : IsOpen U) (u : Homogenization.H10Function U) :
    Filter.Tendsto (fun n => (Homogenization.H10Function.approxH1 hU u n).gradToHilbertVectorL2)
      Filter.atTop (𝓝 u.toH1Function.gradToHilbertVectorL2) := by
  simp only [lhsClosing_gradient_sum]
  apply tendsto_finsetSum
  intro i _
  exact ((lhsClosing_coordEmbed i).compLpL 2 (Homogenization.volumeMeasureOn U)).continuous.tendsto _ |>.comp
    (Homogenization.H10Function.tendsto_approxH1_gradCoordToScalarL2 hU u i)

/-- A map into a second-countable metric space has a countable image with the same closure. -/
theorem lhsClosing_countable_range {A E : Type*} [PseudoMetricSpace E]
    [SecondCountableTopology E] [Nonempty A] (f : A → E) :
    ∃ a : ℕ → A, closure (Set.range (fun n => f (a n))) = closure (Set.range f) := by
  classical
  let : Nonempty (Set.range f) := ⟨⟨f (Classical.arbitrary A), Set.mem_range_self _⟩⟩
  obtain ⟨s, hs⟩ := TopologicalSpace.exists_dense_seq (Set.range f)
  choose a ha using fun n => (s n).property
  refine ⟨a, subset_antisymm (closure_mono ?_) (closure_minimal ?_ isClosed_closure)⟩
  · rintro _ ⟨n, rfl⟩
    exact Set.mem_range_self _
  · rintro x ⟨b, rfl⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨n, hn⟩ := hs.exists_dist_lt (⟨f b, Set.mem_range_self b⟩ : Set.range f) hε
    exact ⟨f (a n), Set.mem_range_self n, by simpa only [ha n, Subtype.dist_eq] using hn⟩

theorem lhsClosing_countable_smooth_gradients (hU : IsOpen U) :
    ∃ (θs : ℕ → Homogenization.Vec d → ℝ)
      (hθ : ∀ j, ContDiff ℝ 1 (θs j) ∧ HasCompactSupport (θs j) ∧ tsupport (θs j) ⊆ U),
      ∀ u : Homogenization.H10Function U,
        u.toH1Function.gradToHilbertVectorL2 ∈ closure (Set.range fun j =>
          (Homogenization.H1Function.ofContDiff hU (hθ j).1 (hθ j).2.1).gradToHilbertVectorL2) := by
  classical
  let A := {θ : Homogenization.Vec d → ℝ //
    ContDiff ℝ 1 θ ∧ HasCompactSupport θ ∧ tsupport θ ⊆ U}
  let : Nonempty A := ⟨⟨0, contDiff_const, HasCompactSupport.zero, by simp⟩⟩
  let f : A → Homogenization.HilbertVectorL2 U := fun θ =>
    (Homogenization.H1Function.ofContDiff hU θ.property.1 θ.property.2.1).gradToHilbertVectorL2
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨a, ha⟩ := lhsClosing_countable_range f
  refine ⟨fun n => (a n).val, fun n => (a n).property, fun u => ?_⟩
  change u.toH1Function.gradToHilbertVectorL2 ∈ closure (Set.range (fun n => f (a n)))
  rw [ha]
  apply isClosed_closure.mem_of_tendsto (lhsClosing_tendsto_gradient hU u)
  apply Filter.Eventually.of_forall
  intro n
  apply subset_closure
  refine ⟨⟨u.approx n, (u.approx_smooth n).of_le (by simp),
    u.approx_hasCompactSupport n, u.approx_support_subset n⟩, rfl⟩

/-- Compactly supported test gradients have a countable dense family on every cube. -/
theorem lhsClosing_countableTestGradientsDense (Q : Homogenization.TriadicCube d) :
    CountableTestGradientsDense Q :=
  lhsClosing_countable_smooth_gradients (Homogenization.isOpen_openCubeSet Q)

open scoped ENNReal InnerProductSpace
def lhsClosing_kernelDifferenceQuotient (θ : Homogenization.Vec d → ℝ) (i : Fin d) (t : ℝ) (y : Homogenization.Vec d) : ℝ :=
  t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y) -
    fderiv ℝ θ y (Homogenization.basisVec i)

theorem lhsClosing_tendsto_integral_abs_kernelDifferenceQuotient
    {θ : Homogenization.Vec d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (i : Fin d) :
    Filter.Tendsto
      (fun t : ℝ => ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| ∂(MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  classical
  
  obtain ⟨S, hS⟩ := (hθc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hθ.continuous_fderiv (by simp))
  
  obtain ⟨R, hR⟩ := hθc.isCompact.isBounded.subset_closedBall (0 : Homogenization.Vec d)
  set Sabs : ℝ := max S 0
  have hSabs0 : 0 ≤ Sabs := le_max_right _ _
  set K : Set (Homogenization.Vec d) := Metric.closedBall (0 : Homogenization.Vec d) (R + 1)
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  
  set bd : Homogenization.Vec d → ℝ := fun y => 2 * Sabs * K.indicator (fun _ => (1 : ℝ)) y with hbd
  have hbd_int : MeasureTheory.Integrable bd (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := by
    have hfin : (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) K ≠ ∞ := by
      rw [show K = Metric.closedBall (0 : Homogenization.Vec d) (R + 1) from rfl]
      exact MeasureTheory.measure_closedBall_lt_top.ne
    have h1 : MeasureTheory.Integrable (K.indicator (fun _ : Homogenization.Vec d => (1 : ℝ))) (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
      (MeasureTheory.integrable_indicator_iff hKmeas).2 (MeasureTheory.integrableOn_const hfin)
    exact h1.const_mul (2 * Sabs)
  have : (𝓝[≠] (0 : ℝ)).IsCountablyGenerated := inferInstance
  have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (l := 𝓝[≠] (0 : ℝ))
    (F := fun t : ℝ => fun y : Homogenization.Vec d => |lhsClosing_kernelDifferenceQuotient θ i t y|)
    (f := fun _ : Homogenization.Vec d => (0 : ℝ)) bd ?_ ?_ hbd_int ?_
  simpa using hmain
  · 
    filter_upwards with t
    have hcont : Continuous (fun y : Homogenization.Vec d => lhsClosing_kernelDifferenceQuotient θ i t y) := by
      unfold lhsClosing_kernelDifferenceQuotient
      exact (continuous_const.mul
        ((hθ.continuous.comp (continuous_id.add continuous_const)).sub hθ.continuous)).sub
        ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
    exact hcont.abs.aestronglyMeasurable
  · 
    have hsmall : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| ≤ 1 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
      rw [Metric.mem_ball, Real.dist_eq] at ht
      exact le_of_lt (by simpa using ht)
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hsmall,
      self_mem_nhdsWithin] with t ht hne
    filter_upwards with y
    simp only [hbd, Real.norm_eq_abs, abs_abs]
    by_cases hy : y ∈ K
    · 
      rw [Set.indicator_of_mem hy, mul_one]
      have hMVT : ‖θ (y + t • Homogenization.basisVec i) - θ y‖ ≤ S * |t| := by
        have hseg : Convex ℝ (segment ℝ y (y + t • Homogenization.basisVec i)) :=
          convex_segment _ _
        have hmain := Convex.norm_image_sub_le_of_norm_fderiv_le
          (f := θ) (s := segment ℝ y (y + t • Homogenization.basisVec i)) (C := S)
          (fun z _ => hθ.differentiable (by simp) z)
          (fun z _ => hS z) hseg
          (left_mem_segment ℝ y (y + t • Homogenization.basisVec i))
          (right_mem_segment ℝ y (y + t • Homogenization.basisVec i))
        calc ‖θ (y + t • Homogenization.basisVec i) - θ y‖
            ≤ S * ‖(y + t • Homogenization.basisVec i) - y‖ := hmain
          _ = S * |t| := by
              rw [add_sub_cancel_left, norm_smul, Homogenization.norm_basisVec, mul_one,
                Real.norm_eq_abs]
      have hterm : |t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y)| ≤ S := by
        rw [abs_mul, abs_inv]
        have hpos : 0 < |t| := abs_pos.mpr hne
        calc |t|⁻¹ * |θ (y + t • Homogenization.basisVec i) - θ y|
            ≤ |t|⁻¹ * (S * |t|) := mul_le_mul_of_nonneg_left hMVT (inv_nonneg.mpr (abs_nonneg _))
          _ = S := by field_simp
      have hder : ‖fderiv ℝ θ y (Homogenization.basisVec i)‖ ≤ S := by
        calc ‖fderiv ℝ θ y (Homogenization.basisVec i)‖
            ≤ ‖fderiv ℝ θ y‖ * ‖Homogenization.basisVec i‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ θ y‖ := by simp
          _ ≤ S := hS y
      have hSle : S ≤ Sabs := le_max_left _ _
      have hderAbs : |fderiv ℝ θ y (Homogenization.basisVec i)| ≤ S := by
        rwa [Real.norm_eq_abs] at hder
      have hA1 : -(S) ≤ t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y) :=
        (abs_le.mp hterm).1
      have hA2 : t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y) ≤ S :=
        (abs_le.mp hterm).2
      have hB1 : -(S) ≤ fderiv ℝ θ y (Homogenization.basisVec i) :=
        (abs_le.mp hderAbs).1
      have hB2 : fderiv ℝ θ y (Homogenization.basisVec i) ≤ S :=
        (abs_le.mp hderAbs).2
      have hle' : |t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y) -
          fderiv ℝ θ y (Homogenization.basisVec i)| ≤ 2 * Sabs := by
        rw [abs_sub_le_iff]
        exact ⟨by linarith only [hA2, hB1, hSle], by linarith only [hB2, hA1, hSle]⟩
      simpa only [lhsClosing_kernelDifferenceQuotient] using hle'
    · 
      rw [Set.indicator_of_notMem hy, mul_zero]
      have hyR : y ∉ Metric.closedBall (0 : Homogenization.Vec d) R := by
        intro hmem
        exact hy (Metric.closedBall_subset_closedBall (by linarith only) hmem)
      have hyts : y ∉ tsupport θ := fun hmem => hyR (hR hmem)
      have hθy : θ y = 0 := image_eq_zero_of_notMem_tsupport hyts
      have hfy : fderiv ℝ θ y = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hyts
      have hytR : y + t • Homogenization.basisVec i ∉ Metric.closedBall (0 : Homogenization.Vec d) R := by
        intro hmem
        have hdmem : dist (y + t • Homogenization.basisVec i) 0 ≤ R :=
          Metric.mem_closedBall.mp hmem
        have hydist : dist y 0 > R + 1 := by
          have := hy
          rw [Metric.mem_closedBall, not_le] at this
          simpa using this
        have hge : dist y 0 ≤ dist (y + t • Homogenization.basisVec i) 0 + |t| := by
          have h := norm_add_le (y + t • Homogenization.basisVec i)
            (-(t • Homogenization.basisVec i))
          rw [add_neg_cancel_right, norm_neg, norm_smul, Homogenization.norm_basisVec,
            mul_one, Real.norm_eq_abs] at h
          simpa only [dist_eq_norm, sub_zero] using h
        linarith only [hdmem, hydist, ht, hge]
      have hyt : θ (y + t • Homogenization.basisVec i) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hmem => hytR (hR hmem))
      have hzero : lhsClosing_kernelDifferenceQuotient θ i t y = 0 := by
        unfold lhsClosing_kernelDifferenceQuotient
        rw [hyt, hθy, sub_zero, mul_zero, hfy]
        simp
      rw [hzero, abs_zero]
  · 
    filter_upwards with y
    have hcurve : HasDerivAt (fun s : ℝ => θ (y + s • Homogenization.basisVec i))
        (fderiv ℝ θ y (Homogenization.basisVec i)) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => y + s • Homogenization.basisVec i)
          (Homogenization.basisVec i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
          (Homogenization.basisVec i)).const_add y
      have hl : HasFDerivAt θ (fderiv ℝ θ y) y := (hθ.differentiable (by simp) y).hasFDerivAt
      have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) hl h1
        (by simp : y = y + (0 : ℝ) • Homogenization.basisVec i)
      exact hcomp
    have hslope := hcurve.tendsto_slope_zero
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul] at hslope
    have hk : Filter.Tendsto (fun t : ℝ => lhsClosing_kernelDifferenceQuotient θ i t y)
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have := hslope.sub_const (fderiv ℝ θ y (Homogenization.basisVec i))
      simpa [lhsClosing_kernelDifferenceQuotient] using this
    simpa using hk.abs

theorem lhsClosing_hasCompactSupport_shift {g : Homogenization.Vec d → ℝ} (hg : HasCompactSupport g) (c : Homogenization.Vec d) :
    HasCompactSupport (fun y : Homogenization.Vec d => g (y + c)) :=
  hg.comp_homeomorph (Homeomorph.addRight c)

theorem lhsClosing_integrable_mul_slice {g : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    MeasureTheory.Integrable (fun y : Homogenization.Vec d => g y * f ((-y) +ᵥ ω)) (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := by
  refine MeasureTheory.Integrable.congr (f := fun y : Homogenization.Vec d => f ((-y) +ᵥ ω) * g y) ?_
    (Filter.Eventually.of_forall fun y => mul_comm _ _)
  refine hg.bdd_mul (c := Cf) (f := fun y : Homogenization.Vec d => f ((-y) +ᵥ ω)) ?_ ?_
  · exact (hfm.comp ((measurable_negVadd_shellSeq (d := d)).comp
      ((measurable_const : Measurable (fun _ : Homogenization.Vec d => ω)).prodMk measurable_id))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hf _

theorem lhsClosing_integrable_kernelDifferenceQuotient
    {θ : Homogenization.Vec d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (i : Fin d) (t : ℝ) :
    MeasureTheory.Integrable (fun y : Homogenization.Vec d => lhsClosing_kernelDifferenceQuotient θ i t y) (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := by
  have h1 : MeasureTheory.Integrable (fun y : Homogenization.Vec d => θ (y + t • Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    (hθ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (lhsClosing_hasCompactSupport_shift hθc (t • Homogenization.basisVec i))
  have h2 : MeasureTheory.Integrable θ (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    hθ.continuous.integrable_of_hasCompactSupport hθc
  have h3 : MeasureTheory.Integrable (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hθc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i))
  have h4 : MeasureTheory.Integrable (fun y : Homogenization.Vec d => t⁻¹ * (θ (y + t • Homogenization.basisVec i) - θ y))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := (h1.sub h2).const_mul t⁻¹
  exact h4.sub h3

theorem lhsClosing_differenceQuotient_smearScalar_eq_integral
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ) (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    t⁻¹ * (smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - smearScalar θ f ω) -
        smearGrad θ f ω i
      = ∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω) := by
  have hS : MeasureTheory.Integrable (fun y : Homogenization.Vec d => θ (y + t • Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    (hθ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (lhsClosing_hasCompactSupport_shift hθc (t • Homogenization.basisVec i))
  have hA : MeasureTheory.Integrable θ (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    hθ.continuous.integrable_of_hasCompactSupport hθc
  have hD : MeasureTheory.Integrable (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hθc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i))
  have hSω := lhsClosing_integrable_mul_slice hS hfm hf ω
  have hAω := lhsClosing_integrable_mul_slice hA hfm hf ω
  have hDω := lhsClosing_integrable_mul_slice hD hfm hf ω
  have hTω : MeasureTheory.Integrable (fun y : Homogenization.Vec d => t⁻¹ *
      ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    (lhsClosing_integrable_mul_slice (hS.sub hA) hfm hf ω).const_mul t⁻¹
  have hstep : (∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω)) -
      ∫ y, θ y * f ((-y) +ᵥ ω)
      = ∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω) := by
    rw [← MeasureTheory.integral_sub hSω hAω]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hstep' : t⁻¹ * (∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))
      = ∫ y, t⁻¹ * ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)) := by
    simpa only [smul_eq_mul] using (MeasureTheory.integral_const_mul (t⁻¹)
      (fun y : Homogenization.Vec d => (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))
      (μ := MeasureTheory.volume)).symm
  calc t⁻¹ * (smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - smearScalar θ f ω) -
        smearGrad θ f ω i
      = t⁻¹ * ((∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω)) -
          ∫ y, θ y * f ((-y) +ᵥ ω)) - smearGrad θ f ω i := by
        rw [smearScalar_vadd_basisVec, smearScalar]
    _ = t⁻¹ * (∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)) -
          smearGrad θ f ω i := by
        rw [hstep]
    _ = (∫ y, t⁻¹ * ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))) -
          smearGrad θ f ω i := by
        rw [hstep']
    _ = ∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω) := by
        simp only [smearGrad]
        rw [← MeasureTheory.integral_sub hTω hDω]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by
          unfold lhsClosing_kernelDifferenceQuotient
          ring)

theorem lhsClosing_abs_differenceQuotient_smearScalar_le
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ)
    (ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    |t⁻¹ * (smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - smearScalar θ f ω) -
        smearGrad θ f ω i| ≤ Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| := by
  rw [lhsClosing_differenceQuotient_smearScalar_eq_integral hθ hθc hfm hf i t ω]
  have hkdq : MeasureTheory.Integrable (fun y : Homogenization.Vec d => lhsClosing_kernelDifferenceQuotient θ i t y)
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := lhsClosing_integrable_kernelDifferenceQuotient hθ hθc i t
  calc |∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)|
      = ‖∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| * |f ((-y) +ᵥ ω)| :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [Real.norm_eq_abs, abs_mul])
    _ ≤ ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| * Cf := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hkdq.abs.mul_const Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
    _ = (∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) * Cf := MeasureTheory.integral_mul_const _ _
    _ = Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| := mul_comm _ _

theorem lhsClosing_eLpNorm_differenceQuotient_smearScalar_le {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ) :
    MeasureTheory.eLpNorm (fun ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d => t⁻¹ * (smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω)
        - smearScalar θ f ω) - smearGrad θ f ω i) 2 P.toMeasure
      ≤ ENNReal.ofReal (Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) := by
  refine (MeasureTheory.eLpNorm_le_of_ae_bound (p := 2) (μ := P.toMeasure)
    (C := Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) ?_ ?_).trans_eq ?_
  · have hS : MeasureTheory.StronglyMeasurable (smearScalar θ f) := by
      have hjoint : MeasureTheory.StronglyMeasurable
          (fun p : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d × Homogenization.Vec d =>
            θ p.2 * f ((-p.2) +ᵥ p.1)) :=
        ((hθ.continuous.measurable.comp measurable_snd).mul
          (hfm.comp (SuperdiffusionCLT.Probability.Stationary.measurable_negVadd_shellSeq
            (d := d)))).stronglyMeasurable
      exact hjoint.integral_prod_right' (ν := (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
    have hshift : Measurable (fun ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
        t • Homogenization.basisVec i +ᵥ ω) :=
      (SuperdiffusionCLT.Section3.Terms.measurable_vadd_shellSeq (d := d)).comp
        (measurable_id.prodMk measurable_const)
    exact (((hS.comp_measurable hshift).sub hS).const_mul t⁻¹ |>.aestronglyMeasurable).sub
      (SuperdiffusionCLT.Probability.Stationary.aestronglyMeasurable_smearGrad_apply (P := P) hθ hfm i)
  · filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact lhsClosing_abs_differenceQuotient_smearScalar_le hθ hθc hfm hf i t ω
  · simp only [MeasureTheory.measure_univ, ENNReal.one_rpow, one_mul]

theorem lhsClosing_tendsto_eLpNorm_differenceQuotient_smearScalar {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) :
    Filter.Tendsto (fun t : ℝ => MeasureTheory.eLpNorm (fun ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d =>
        t⁻¹ * (smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - smearScalar θ f ω)
          - smearGrad θ f ω i) 2 P.toMeasure) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hI : Filter.Tendsto (fun t : ℝ => ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := lhsClosing_tendsto_integral_abs_kernelDifferenceQuotient hθ hθc i
  have hub : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (Cf *
      ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hI.const_mul Cf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Filter.Eventually.of_forall fun t => zero_le)
    (Filter.Eventually.of_forall fun t =>
      lhsClosing_eLpNorm_differenceQuotient_smearScalar_le (P := P) hθ hθc hfm hf i t)

/-- A bounded measurable field smeared against a C¹ compact kernel has the stated gradient. -/
theorem lhsClosing_smearScalar_hasHorizontalGradient {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}
    [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) P.toMeasure]
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    HasHorizontalGradient (μ := P.toMeasure)
      ((memLp_smearScalar (P := P) hθ hθc hfm hf).toLp (smearScalar θ f))
      ((memLp_smearGrad (P := P) hθ hθc hfm hf).toLp
        (fun ω => Homogenization.HilbertVec.ofVec (smearGrad θ f ω))) := by
  classical
  intro i
  have hFc : MeasureTheory.MemLp (fun ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d => smearGrad θ f ω i) 2 P.toMeasure :=
    memLp_smearGrad_apply (P := P) hθ hθc hfm hf i
  have hcoord : vectorL2Coord (μ := P.toMeasure) i
      ((memLp_smearGrad (P := P) hθ hθc hfm hf).toLp
        (fun ω => Homogenization.HilbertVec.ofVec (smearGrad θ f ω)))
      = hFc.toLp (fun ω => smearGrad θ f ω i) := by
    rw [MeasureTheory.Lp.ext_iff]
    filter_upwards [vectorL2Coord_toLp (P := P) i (smearGrad θ f)
        (memLp_smearGrad (P := P) hθ hθc hfm hf), MeasureTheory.MemLp.coeFn_toLp hFc] with ω h1 h2
    rw [h1, h2]
  rw [hcoord]
  refine (hasDerivAt_iff_tendsto_slope_zero (f := fun t : ℝ =>
      koopman (μ := P.toMeasure) (t • Homogenization.basisVec i)
        ((memLp_smearScalar (P := P) hθ hθc hfm hf).toLp (smearScalar θ f)))
    (f' := hFc.toLp (fun ω => smearGrad θ f ω i))).mpr ?_
  refine MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
    (fun ω : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d => smearGrad θ f ω i) hFc ?_
  refine Filter.Tendsto.congr' ?_
    (lhsClosing_tendsto_eLpNorm_differenceQuotient_smearScalar (P := P) hθ hθc hfm hf i)
  filter_upwards with t
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [differenceQuotient_class_coeFn (P := P) t i
      (memLp_smearScalar (P := P) hθ hθc hfm hf)] with ω h1
  simp only [Pi.sub_apply, zero_add, zero_smul, koopman_zero, h1]


variable {P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)}

variable [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) P.toMeasure]
theorem lhsClosing_scalar_joint
    {κ : Homogenization.Vec d → ℝ} (hκ : Continuous κ) (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hgm : MeasureTheory.StronglyMeasurable g) (hg : MeasureTheory.Integrable g P.toMeasure) :
    MeasureTheory.Integrable (fun p : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d × Homogenization.Vec d => f p.1 * (κ p.2 * g (p.2 +ᵥ p.1)))
      (P.toMeasure.prod MeasureTheory.volume) := by
  refine (integrable_prod_weighted_comp_vadd (P := P) hκ hκi hgm hg).bdd_mul (c := Cf) ?_ ?_
  · exact (hfm.comp measurable_fst).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hf p.1

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) P.toMeasure] in
theorem lhsClosing_scalar_joint_back
    {κ : Homogenization.Vec d → ℝ} (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hg : MeasureTheory.Integrable g P.toMeasure) :
    MeasureTheory.Integrable (fun p : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d × Homogenization.Vec d => (g p.1 * κ p.2) * f ((-p.2) +ᵥ p.1))
      (P.toMeasure.prod MeasureTheory.volume) := by
  refine (hg.mul_prod hκi).mul_bdd (c := Cf) ?_ ?_
  · exact (hfm.comp measurable_negVadd_shellSeq).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hf _

theorem lhsClosing_scalar_transfer
    {κ : Homogenization.Vec d → ℝ} (hκ : Continuous κ) (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hgm : MeasureTheory.StronglyMeasurable g) (hg : MeasureTheory.Integrable g P.toMeasure) :
    (∫ ω, f ω * (∫ y, κ y * g (y +ᵥ ω)) ∂P.toMeasure) =
      ∫ ω, g ω * (∫ y, κ y * f ((-y) +ᵥ ω)) ∂P.toMeasure := by
  have hj := lhsClosing_scalar_joint (P := P) hκ hκi hfm hf hgm hg
  have hb := lhsClosing_scalar_joint_back (P := P) hκi hfm hf hg
  calc
    _ = ∫ ω, ∫ y, f ω * (κ y * g (y +ᵥ ω)) ∂MeasureTheory.volume ∂P.toMeasure := by
      simp only [MeasureTheory.integral_const_mul]
    _ = ∫ y, ∫ ω, f ω * (κ y * g (y +ᵥ ω)) ∂P.toMeasure :=
      MeasureTheory.integral_integral_swap hj
    _ = ∫ y, ∫ ω, (g ω * κ y) * f ((-y) +ᵥ ω) ∂P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [← SuperdiffusionCLT.Section3.Terms.integral_comp_vadd_shellSeq
        (fun ω => (g ω * κ y) * f ((-y) +ᵥ ω)) y]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      simp only [neg_vadd_vadd]
      ring
    _ = ∫ ω, ∫ y, (g ω * κ y) * f ((-y) +ᵥ ω) ∂MeasureTheory.volume ∂P.toMeasure :=
      (MeasureTheory.integral_integral_swap hb).symm
    _ = _ := by simp only [mul_assoc, MeasureTheory.integral_const_mul]

/-- Fubini and translation invariance transfer the spatial pairing to the smeared gradient. -/
theorem lhsClosing_spatial_pairing_transfer
    {G : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d} {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hGm : MeasureTheory.StronglyMeasurable (vecField G)) (hG : MeasureTheory.MemLp (vecField G) 2 P.toMeasure)
    (hθc : ∀ i, Continuous (coordKernel θ i))
    (hθi : ∀ i, MeasureTheory.Integrable (coordKernel θ i) MeasureTheory.volume)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    (∫ ω, f ω * orbitDivergenceField G θ ω ∂P.toMeasure) =
      ∫ ω, Homogenization.vecDot (smearGrad θ f ω) (G ω) ∂P.toMeasure := by
  have hg : ∀ i, MeasureTheory.Integrable (fun ω => G ω i) P.toMeasure := fun i =>
    (hG.eval_piLp i).integrable (by norm_num)
  have hgm : ∀ i, MeasureTheory.StronglyMeasurable (fun ω => G ω i) := fun i =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).continuous.comp_stronglyMeasurable hGm
  have hj := fun i => lhsClosing_scalar_joint (P := P) (hθc i) (hθi i) hfm hf (hgm i) (hg i)
  have hb := fun i => lhsClosing_scalar_joint_back (P := P) (hθi i) hfm hf (hg i)
  have hleft : ∀ i, MeasureTheory.Integrable (fun ω => f ω * ∫ y, coordKernel θ i y * G (y +ᵥ ω) i) P.toMeasure := by
    intro i
    simpa only [MeasureTheory.integral_const_mul] using (hj i).integral_prod_left
  have hright : ∀ i, MeasureTheory.Integrable (fun ω => G ω i * smearGrad θ f ω i) P.toMeasure := by
    intro i
    simpa only [mul_assoc, MeasureTheory.integral_const_mul, smearGrad, coordKernel] using (hb i).integral_prod_left
  have ha : ∀ᵐ ω ∂P.toMeasure, ∀ i,
      MeasureTheory.Integrable (fun y => coordKernel θ i y * G (y +ᵥ ω) i) MeasureTheory.volume :=
    Filter.eventually_all.mpr fun i =>
      (integrable_prod_weighted_comp_vadd (P := P) (hθc i) (hθi i) (hgm i) (hg i)).prod_right_ae
  calc
    _ = ∫ ω, ∑ i, f ω * (∫ y, coordKernel θ i y * G (y +ᵥ ω) i) ∂P.toMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ha] with ω hω
      rw [orbitDivergenceField]
      simp_rw [vecDot_euclideanGradient_eq_sum]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hω i), Finset.mul_sum]
    _ = ∑ i, ∫ ω, f ω * (∫ y, coordKernel θ i y * G (y +ᵥ ω) i) ∂P.toMeasure :=
      MeasureTheory.integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, ∫ ω, G ω i * smearGrad θ f ω i ∂P.toMeasure := by
      apply Finset.sum_congr rfl
      intro i _
      exact lhsClosing_scalar_transfer (P := P) (hθc i) (hθi i) hfm hf (hgm i) (hg i)
    _ = ∫ ω, ∑ i, G ω i * smearGrad θ f ω i ∂P.toMeasure :=
      (MeasureTheory.integral_finsetSum _ (fun i _ => hright i)).symm
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
/-- Solenoidal classes annihilate the horizontal gradient of a bounded smear. -/
theorem lhsClosing_smear_pairing_zero
    {G : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d}
    (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2 P.toMeasure)
    (hGsol : hG.toLp _ ∈ stationarySolenoidalSubspace (μ := P.toMeasure) (d := d))
    {θ : Homogenization.Vec d → ℝ} {f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    (∫ ω, Homogenization.vecDot (smearGrad θ f ω) (G ω) ∂P.toMeasure) = 0 := by
  have hh := lhsClosing_smearScalar_hasHorizontalGradient (P := P) hθ hθc hfm hf
  have hz := (Submodule.mem_orthogonal _ _).mp hGsol _
    ((Submodule.le_topologicalClosure _) ⟨_, hh⟩)
  rw [MeasureTheory.L2.inner_def] at hz
  convert hz using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp hG,
    MeasureTheory.MemLp.coeFn_toLp (memLp_smearGrad (P := P) hθ hθc hfm hf)] with ω h1 h2
  rw [h1, h2]
  simp only [Homogenization.HilbertVec.inner_def, Homogenization.HilbertVec.toVec_ofVec]

theorem lhsClosing_action_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d × Homogenization.Vec d => p.2 +ᵥ p.1)
      (P.toMeasure.prod MeasureTheory.volume) P.toMeasure := by
  have hm : Measurable (fun p : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d × Homogenization.Vec d => p.2 +ᵥ p.1) :=
    (measurable_vadd (M := Homogenization.Vec d) (α := SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)).comp measurable_swap
  refine ⟨hm, MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hz => ?_⟩
  rw [MeasureTheory.Measure.map_apply hm hs,
    MeasureTheory.Measure.prod_apply_symm (hs.preimage hm)]
  have heq : ∀ y : Homogenization.Vec d,
      P.toMeasure ((fun ω => y +ᵥ ω) ⁻¹' s) = 0 := fun y => by
    rw [MeasureTheory.VAddInvariantMeasure.measure_preimage_vadd y hs, hz]
  simp only [Set.preimage, Set.mem_ofPred_eq] at heq ⊢
  simp only [heq, MeasureTheory.lintegral_zero]

/-- Changing a stationary field on a null set preserves its spatial divergence tests. -/
theorem lhsClosing_orbitDivergence_congr
    {G H : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d}
    (h : G =ᵐ[P.toMeasure] H) (θ : Homogenization.Vec d → ℝ) :
    orbitDivergenceField G θ =ᵐ[P.toMeasure] orbitDivergenceField H θ := by
  have hh := (lhsClosing_action_quasiMeasurePreserving (P := P)).ae_eq_comp h
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hh] with ω hω
  exact MeasureTheory.integral_congr_ae (hω.mono fun y hy => congrArg
    (fun v => Homogenization.vecDot v (Homogenization.euclideanGradient θ y)) hy)

theorem lhsClosing_divFree_strong
    {G : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d}
    (hGm : MeasureTheory.StronglyMeasurable (vecField G))
    (hG : MeasureTheory.MemLp (vecField G) 2 P.toMeasure)
    (hGsol : hG.toLp _ ∈ stationarySolenoidalSubspace (μ := P.toMeasure) (d := d))
    {θ : Homogenization.Vec d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) :
    orbitDivergenceField G θ =ᵐ[P.toMeasure] 0 := by
  have hc := fun i => continuous_coordFderiv hθ i
  have hi := fun i => integrable_coordFderiv hθ hθc i
  have hΨ := memLp_orbitDivergenceField (P := P) hGm hG hc hi
  apply MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ _
    exact (hΨ.integrable (by norm_num)).integrableOn
  · intro s hs _
    let f : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ := s.indicator (fun _ => 1)
    have hfm : Measurable f := measurable_const.indicator hs
    have hf : ∀ ω, |f ω| ≤ (1 : ℝ) := by
      intro ω
      by_cases hω : ω ∈ s <;> simp [f, hω]
    have hz := lhsClosing_smear_pairing_zero hG hGsol hθ hθc hfm hf
    rw [← lhsClosing_spatial_pairing_transfer hGm hG hc hi hfm hf] at hz
    rw [← MeasureTheory.integral_indicator hs]
    convert hz using 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ s <;> simp [f, hω]

/-- Every stationary solenoidal L² class has almost-everywhere divergence-free realizations. -/
theorem lhsClosing_divFreeStep : divFreeStep (d := d) P := by
  intro G hG hGsol θ hθ hθc
  let K := hG.aestronglyMeasurable.mk (fun ω => Homogenization.HilbertVec.ofVec (G ω))
  let H : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d := fun ω => (K ω).toVec
  have heq : vecField G =ᵐ[P.toMeasure] vecField H :=
    hG.aestronglyMeasurable.ae_eq_mk
  have hHm : MeasureTheory.StronglyMeasurable (vecField H) :=
    hG.aestronglyMeasurable.stronglyMeasurable_mk
  have hH : MeasureTheory.MemLp (vecField H) 2 P.toMeasure := hG.ae_eq heq
  have hc := hG.toLp_congr hH heq
  have hHsol : hH.toLp _ ∈ stationarySolenoidalSubspace (μ := P.toMeasure) (d := d) :=
    hc ▸ hGsol
  have hz := lhsClosing_divFree_strong hHm hH hHsol hθ hθc
  have hv : G =ᵐ[P.toMeasure] H := heq.mono fun ω hω => congrArg Homogenization.HilbertVec.toVec hω
  exact (lhsClosing_orbitDivergence_congr hv θ).trans hz

/-- The first left-hand-side estimate, with exactly the dimension and data binders of the
statement. -/
theorem lhs_term1_closed
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P), SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          ∀ (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P), SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ (cStar K : ℝ), SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K hPrefix hJ2 hJ3 →
          ∀ (S : SuperdiffusionCLT.Section3.Setup.ScaleSelection), SuperdiffusionCLT.Section3.Setup.ScalesOrdering S →
          ∀ (e : Homogenization.Vec d), Homogenization.vecNormSq e = 1 →
            Homogenization.Book.Ch02.vecNorm e = 1 →
            ∀ (p : Homogenization.Vec d), p = SuperdiffusionCLT.Section3.Setup.testVector nu S.LPrime P S.n e →
            ∀ (F : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Homogenization.Vec d → Homogenization.Vec d),
              (∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d, F omega = fun x =>
                Homogenization.matVecMul
                  (SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.LPrime x -
                    SuperdiffusionCLT.Frozen.Section2.streamCutoff
                      omega S.ellPrime x) p) →
              ∀ (w : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                  Homogenization.H10Function
                    (Homogenization.openCubeSet
                      (Homogenization.originCube d (S.m : ℤ)))),
                (∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                  SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse (Homogenization.originCube d (S.m : ℤ)) (F omega)
                    (w omega)) →
                |(∫⁻ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                      SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm (Homogenization.originCube d (S.m : ℤ)) 2
                        (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                  ℝ≥0∞).toReal -
                  cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * Homogenization.vecNormSq p| ≤
                (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * Homogenization.vecNormSq p
 :=
  lhs_term1_of_divFreeStep d hd (fun _ _ => lhsClosing_divFreeStep)
    (fun M => lhsClosing_countableTestGradientsDense (Homogenization.originCube d M))


end SuperdiffusionCLT.Probability.Stationary
