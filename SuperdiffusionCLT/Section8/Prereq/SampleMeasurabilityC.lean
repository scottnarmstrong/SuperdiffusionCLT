/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.SampleMeasurabilityB
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.Minimal

/-!
# The analytic minimal resolvent is measurable in the sample

The value of the continuous representative of a cube resolvent at an interior point is the limit
of the pairings of its `L²` class with normalized indicators of shrinking balls.  Each pairing is a
measurable function of the sample by `SampleMeasurabilityB.lean`, so the cube resolvent is
measurable on every set of samples on which the field is continuous and skew, and so is the
supremum over cubes, the analytic minimal resolvent.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.ZeroTraceSobolev
open scoped RealInnerProductSpace

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

/-- Averages of a function continuous at `x` over small balls tend to its value at `x`. -/
theorem sampleMeas_tendsto_ballAverage {h : Vec d → ℝ} {x : Vec d} {r0 : ℝ} (hr0 : 0 < r0)
    (hint : IntegrableOn h (Metric.ball x r0)) (hc : ContinuousAt h x) :
    Tendsto (fun k : ℕ => (volume.real (Metric.ball x (r0 / ((k : ℝ) + 1))))⁻¹ *
      ∫ y in Metric.ball x (r0 / ((k : ℝ) + 1)), h y) atTop (𝓝 (h x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (r0 / δ)
  refine ⟨N, fun k hk => ?_⟩
  set r : ℝ := r0 / ((k : ℝ) + 1) with hr
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hrpos : 0 < r := by positivity
  have hrδ : r < δ := by
    rw [hr, div_lt_iff₀ hk1]
    have h1 : r0 / δ < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := Nat.cast_le.2 hk
      linarith only [hN, this]
    rw [div_lt_iff₀ hδ] at h1
    linarith only [h1]
  have hrr0 : r ≤ r0 := by
    rw [hr, div_le_iff₀ hk1]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith only [hr0, this]
  have hsub : Metric.ball x r ⊆ Metric.ball x r0 := Metric.ball_subset_ball hrr0
  have hvpos : 0 < volume.real (Metric.ball x r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume x hrpos).ne' (measure_ball_lt_top).ne
  have hint' : IntegrableOn h (Metric.ball x r) := hint.mono_set hsub
  have hconst : ∫ y in Metric.ball x r, h x = volume.real (Metric.ball x r) * h x := by
    rw [setIntegral_const, smul_eq_mul]
  have hdiff : ∫ y in Metric.ball x r, (h y - h x) =
      (∫ y in Metric.ball x r, h y) - volume.real (Metric.ball x r) * h x := by
    rw [integral_sub hint' (integrableOn_const (by exact measure_ball_lt_top.ne)), hconst]
  have hbound : ‖∫ y in Metric.ball x r, (h y - h x)‖ ≤ (ε / 2) * volume.real (Metric.ball x r) := by
    refine norm_setIntegral_le_of_norm_le_const (C := ε / 2) measure_ball_lt_top ?_
    intro y hy
    have := hδh (lt_trans (by simpa [Metric.mem_ball] using hy) hrδ)
    rw [Real.dist_eq] at this
    simpa only [Real.norm_eq_abs] using this.le
  rw [Real.dist_eq]
  have e1 : ((volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, h y) - h x =
      (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, (h y - h x) := by
    rw [hdiff]; field_simp
  rw [e1, abs_mul, abs_of_pos (inv_pos.2 hvpos)]
  calc (volume.real (Metric.ball x r))⁻¹ * |∫ y in Metric.ball x r, (h y - h x)|
      ≤ (volume.real (Metric.ball x r))⁻¹ * ((ε / 2) * volume.real (Metric.ball x r)) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hbound)
          (inv_pos.2 hvpos).le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith only [hε]

/-- The normalized indicator of a ball, as a function on a domain. -/
def sampleMeas_ballFn (U : Set (Vec d)) (x : Vec d) (r : ℝ) : U → ℝ := fun y =>
  (volume.real (Metric.ball x r))⁻¹ * (Metric.ball x r).indicator (fun _ => (1 : ℝ)) y.1

theorem sampleMeas_measurable_ballFn (U : Set (Vec d)) (x : Vec d) (r : ℝ) :
    Measurable (sampleMeas_ballFn U x r) :=
  measurable_const.mul ((measurable_const.indicator Metric.isOpen_ball.measurableSet).comp
    measurable_subtype_coe)

theorem sampleMeas_abs_ballFn_le (U : Set (Vec d)) (x : Vec d) (r : ℝ) (y : U) :
    |sampleMeas_ballFn U x r y| ≤ (volume.real (Metric.ball x r))⁻¹ := by
  unfold sampleMeas_ballFn
  rw [abs_mul]
  have h0 : 0 ≤ (volume.real (Metric.ball x r))⁻¹ := inv_nonneg.2 measureReal_nonneg
  rw [abs_of_nonneg h0]
  refine mul_le_of_le_one_right h0 ?_
  by_cases hy : y.1 ∈ Metric.ball x r <;> simp [hy]

/-- The `L²` class of the normalized ball indicator. -/
def sampleMeas_ballL2 (hU : IsOpenBoundedConvexDomain U) (x : Vec d) (r : ℝ) : ScalarL2 U :=
  boundedMeasurableToScalarL2 hU (sampleMeas_measurable_ballFn U x r)
    (sampleMeas_abs_ballFn_le U x r)

/-- The pairing of an `L²` class with the normalized ball indicator is the ball average of any
representative. -/
theorem sampleMeas_inner_ballL2 (hU : IsOpenBoundedConvexDomain U) {x : Vec d} {r : ℝ}
    (hBU : Metric.ball x r ⊆ U) (u : ScalarL2 U) {h : Vec d → ℝ}
    (hh : h =ᵐ[volumeMeasureOn U] u) :
    inner ℝ (sampleMeas_ballL2 hU x r) u =
      (volume.real (Metric.ball x r))⁻¹ * ∫ y in Metric.ball x r, h y := by
  rw [MeasureTheory.L2.inner_def]
  have hae : ∀ᵐ y ∂volumeMeasureOn U,
      inner ℝ ((sampleMeas_ballL2 hU x r : ScalarL2 U) y) (u y) =
        (Metric.ball x r).indicator (fun y => (volume.real (Metric.ball x r))⁻¹ * h y) y := by
    filter_upwards [boundedMeasurableToScalarL2_coeFn hU (sampleMeas_measurable_ballFn U x r)
      (sampleMeas_abs_ballFn_le U x r), hh,
      (ae_restrict_mem hU.isOpen.measurableSet : ∀ᵐ y ∂volumeMeasureOn U, y ∈ U)]
      with y h1 h2 hyU
    have h1' : (sampleMeas_ballL2 hU x r : ScalarL2 U) y = (volume.real (Metric.ball x r))⁻¹ *
        (Metric.ball x r).indicator (fun _ => (1 : ℝ)) y := by
      have : (sampleMeas_ballL2 hU x r : ScalarL2 U) y = domainExtension
          (sampleMeas_ballFn U x r) y := h1
      rw [this, domainExtension_of_mem hyU]
      rfl
    rw [h1', ← h2]
    by_cases hy : y ∈ Metric.ball x r
    · simp [hy, mul_comm]
    · simp [hy]
  rw [integral_congr_ae hae, integral_indicator Metric.isOpen_ball.measurableSet]
  simp only [volumeMeasureOn]
  rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet,
    Set.inter_eq_left.2 hBU, integral_const_mul]

/-- **The cube resolvent value is the limit of ball-average functionals.** -/
theorem sampleMeas_cubeValue_tendsto [NeZero d] (a : CoeffField d)
    (hU : IsOpenBoundedConvexDomain U) {nu Lam : ℝ} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lam U a)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U) (hd : 2 ≤ d)
    (mu : MarkovProcess.Semigroup.PositiveShift) {f : U → ℝ} (hfmeas : Measurable f) {D : ℝ}
    (hfD : ∀ y, |f y| ≤ D) {x : Vec d} (hx : x ∈ U) {r0 : ℝ} (hr0 : 0 < r0)
    (hcl : Metric.closedBall x r0 ⊆ U) :
    Tendsto (fun k : ℕ =>
      sampleMeas_theta (mu : ℝ) nu mu.property hnu (boundedMeasurableToScalarL2 hU hfmeas hfD)
        (sampleMeas_ballL2 hU x (r0 / ((k : ℝ) + 1))) a) atTop
      (𝓝 (SuperdiffusionCLT.Section8.DivergenceForm.continuousCoeffBoundedResolvent a hU hnu
        hnu hEll hsymm hcont hd mu hfmeas hfD x)) := by
  set h := continuousCoeffBoundedResolvent a hU hnu hnu hEll hsymm hcont hd mu hfmeas hfD with hh
  have hhc : ContinuousOn h U := continuousOn_continuousCoeffBoundedResolvent a hU hnu hnu hEll
    hsymm hcont hd mu hfmeas hfD
  have hhae := continuousCoeffBoundedResolvent_ae a hU hnu hnu hEll hsymm hcont hd mu hfmeas hfD
  have hint : IntegrableOn h (Metric.ball x r0) :=
    ((hhc.mono hcl).integrableOn_compact (isCompact_closedBall x r0)).mono_set
      Metric.ball_subset_closedBall
  have hlim := sampleMeas_tendsto_ballAverage hr0 hint
    ((hhc.continuousAt (hU.isOpen.mem_nhds hx)))
  refine hlim.congr fun k => ?_
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hrle : r0 / ((k : ℝ) + 1) ≤ r0 := by
    rw [div_le_iff₀ hk1]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith only [hr0, this]
  have hBU : Metric.ball x (r0 / ((k : ℝ) + 1)) ⊆ U :=
    (Metric.ball_subset_ball hrle).trans (Metric.ball_subset_closedBall.trans hcl)
  rw [sampleMeas_theta_eq mu.property hnu _ _ hEll]
  exact (sampleMeas_inner_ballL2 hU hBU _ hhae).symm

theorem sampleMeas_theta_congr {α ν ν' : ℝ} (hα : 0 < α) (hν : 0 < ν) (hν' : 0 < ν')
    (f ψ : ScalarL2 U) (hn : ν' = ν) {c c' : CoeffField d} (hc : c' = c) :
    sampleMeas_theta α ν' hα hν' f ψ c' = sampleMeas_theta α ν hα hν f ψ c := by
  subst hn hc
  rfl

theorem sampleMeas_wholeSpaceCube_subset_closedBall (m : ℕ) :
    DivergenceForm.wholeSpaceCube d m ⊆ Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ m) := by
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs, abs_le]
  have := DivergenceForm.mem_wholeSpaceCube_iff.1 hx i
  constructor <;> linarith only [this.1, this.2]

/-- **The cube resolvent is measurable in the sample** on any set `G` of samples on which the
field is continuous and skew and the analytic datum is the one of the field. -/
theorem sampleMeas_measurable_cubeResolvent [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (G : Set Ω) {ν : ℝ} (hν : 0 < ν) (K : Ω → Vec d → Mat d)
    (hK : Measurable fun q : Vec d × Ω => K q.2 q.1)
    (hgood : ∀ ω ∈ G, Continuous (K ω) ∧ ∀ y, matTranspose (K ω y) = -K ω y)
    (A : Ω → DivergenceForm.WholeSpaceAnalyticData d)
    (hA : ∀ ω ∈ G, (A ω).a = (fun y => ν • (1 : Mat d) + K ω y) ∧ (A ω).nu = ν)
    (mu : MarkovProcess.Semigroup.PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (m : ℕ) (x : Vec d) :
    Measurable (fun ω : G => (A ω).analyticCubeResolvent mu f hf hfD m x) := by
  by_cases hx : x ∈ DivergenceForm.wholeSpaceCube d m
  swap
  · have : (fun ω : G => (A ω).analyticCubeResolvent mu f hf hfD m x) = fun _ => 0 := by
      funext ω
      simp only [DivergenceForm.WholeSpaceAnalyticData.analyticCubeResolvent, hx, ↓reduceDIte]
    rw [this]
    exact measurable_const
  have hU := DivergenceForm.isOpenBoundedConvexDomain_wholeSpaceCube d m
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU.isOpen x hx
  have hcl : Metric.closedBall x (ε / 2) ⊆ DivergenceForm.wholeSpaceCube d m :=
    (Metric.closedBall_subset_ball (by linarith only [hε])).trans hεU
  set g := boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe) (fun y => hfD y)
    with hg
  set θ : ℕ → G → ℝ := fun k ω => sampleMeas_theta (mu : ℝ) ν mu.property hν g
    (sampleMeas_ballL2 hU x (ε / 2 / ((k : ℝ) + 1))) (fun y => ν • (1 : Mat d) + K ω y) with hθ
  have hθm : ∀ k, Measurable (θ k) := fun k =>
    sampleMeas_measurable_theta G (sampleMeas_wholeSpaceCube_subset_closedBall m)
      hU.isOpen.measurableSet mu.property hν g _ K hK hgood
  refine measurable_of_tendsto_metrizable hθm ?_
  rw [tendsto_pi_nhds]
  intro ω
  obtain ⟨hω1, hω2⟩ := hA ω ω.2
  have hL3 := sampleMeas_cubeValue_tendsto (A ω).a hU (A ω).hnu ((A ω).cubeEllipticity m)
    (A ω).hsymm ((A ω).skewContinuousOnCube m) (A ω).hd mu (hf.comp measurable_subtype_coe)
    (fun y => hfD y) hx (by positivity) hcl
  have hval : (A ω).analyticCubeResolvent mu f hf hfD m x =
      DivergenceForm.continuousCoeffBoundedResolvent (A ω).a hU (A ω).hnu (A ω).hnu
        ((A ω).cubeEllipticity m) (A ω).hsymm ((A ω).skewContinuousOnCube m) (A ω).hd mu
        (hf.comp measurable_subtype_coe) (fun y => hfD y) x := by
    simp only [DivergenceForm.WholeSpaceAnalyticData.analyticCubeResolvent, hx, ↓reduceDIte]
  rw [hval]
  refine hL3.congr fun k => ?_
  exact sampleMeas_theta_congr mu.property hν (A ω).hnu _ _ hω2 hω1

/-- **The analytic minimal resolvent is measurable in the sample.** -/
theorem sampleMeas_measurable_minimalResolvent [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    (G : Set Ω) {ν : ℝ} (hν : 0 < ν) (K : Ω → Vec d → Mat d)
    (hK : Measurable fun q : Vec d × Ω => K q.2 q.1)
    (hgood : ∀ ω ∈ G, Continuous (K ω) ∧ ∀ y, matTranspose (K ω y) = -K ω y)
    (A : Ω → DivergenceForm.WholeSpaceAnalyticData d)
    (hA : ∀ ω ∈ G, (A ω).a = (fun y => ν • (1 : Mat d) + K ω y) ∧ (A ω).nu = ν)
    (mu : MarkovProcess.Semigroup.PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {D : ℝ}
    (hfD : ∀ x, |f x| ≤ D) (x : Vec d) :
    Measurable (fun ω : G => (A ω).analyticMinimalResolvent mu f hf hfD x) := by
  unfold DivergenceForm.WholeSpaceAnalyticData.analyticMinimalResolvent
  refine Measurable.iSup fun m => ?_
  unfold DivergenceForm.WholeSpaceAnalyticData.analyticCubeResolventENN
  exact ENNReal.measurable_ofReal.comp
    (sampleMeas_measurable_cubeResolvent G hν K hK hgood A hA mu hf hfD m x)

end

end SuperdiffusionCLT.Section8
