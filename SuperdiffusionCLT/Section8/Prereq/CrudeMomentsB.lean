/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Process.Kernel.ResolventTailMoments

/-!
# Displacement tails with a centre-dependent resolvent tail

The displacement tail `measure_compl_ball_le_of_hasResolventTail` asks for one profile at every
point.  The excessive-function comparison needs much less: a tail at the starting point, and at
the points at distance at least `10 r` from it only that the normalized potential of the ball of
radius `2 r` is at most one half.  This file proves the displacement tail under exactly these two
hypotheses, so that the profile at the starting point may carry the growth of the coefficient
there, while the far points need no uniformity.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

open MarkovProcess

namespace SuperdiffusionCLT.Section8

open SuperdiffusionCLT.Section8.Process
open MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.PositiveC0ContractiveResolvent

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]

/-- At a live point the compactified resolvent of the assembled cutoff is one minus the
normalized resolvent of the cutoff. -/
private theorem crudeMom_mul_onePointResolvent_assemble_coe (R : PositiveC0ContractiveResolvent X)
    (mu : PositiveShift) (psi : C₀(X, ℝ)) (y : X) :
    (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu
        (onePointAssemble (-psi) 1) (y : OnePoint X) =
      1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y := by
  have hmu : (mu : ℝ) ≠ 0 := mu.property.ne'
  have h := congrArg (fun w : C₀(OnePoint X, ℝ) ↦ w (y : OnePoint X))
    (R.onePointResolvent_operator mu (onePointAssemble (-psi) 1))
  simp only [onePointAssemble_coe, onePointAssemble_infty, onePointRemainder_assemble,
    map_neg, ZeroAtInftyContinuousMap.neg_apply] at h
  rw [h]
  field_simp
  ring

/-- At the added point the compactified resolvent of the assembled cutoff carries the full
weight. -/
private theorem crudeMom_mul_onePointResolvent_assemble_infty (R : PositiveC0ContractiveResolvent X)
    (mu : PositiveShift) (psi : C₀(X, ℝ)) :
    (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu
        (onePointAssemble (-psi) 1) OnePoint.infty = 1 := by
  have hmu : (mu : ℝ) ≠ 0 := mu.property.ne'
  have h := congrArg (fun w : C₀(OnePoint X, ℝ) ↦ w OnePoint.infty)
    (R.onePointResolvent_operator mu (onePointAssemble (-psi) 1))
  simp only [onePointAssemble_infty] at h
  rw [h]
  field_simp

/-- **Displacement tails from a tail at the starting point and a far smallness condition.**  Let
the kernel semigroup of a positive `C₀` contractive resolvent be conservative, let `mu t = 1`,
let the normalized `mu`-potential of the complement of the ball of radius `r` about `x` be at
most `phi`, and let the normalized `mu`-potential of the ball of radius `2 r` about `x` be at
most one half from every point at distance at least `10 r` from `x`.  Then the transition law
at time `t` leaves the ball of radius `11 r` about `x` with probability at most `2 e phi`. -/
theorem crudeMom_measure_compl_ball_le (R : PositiveC0ContractiveResolvent X)
    (hcons : R.kernelSemigroup.IsConservative) {mu : PositiveShift} {t : ℝ≥0}
    (ht : (mu : ℝ) * (t : ℝ) = 1) (x : X) {r : ℝ} (hr : 0 < r) {phi : ℝ} (hphi : 0 ≤ phi)
    (hcentre : ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r)ᶜ ≤
      ENNReal.ofReal phi)
    (hfarE : ∀ y : X, 10 * r ≤ dist y x →
      ENNReal.ofReal (mu : ℝ) *
        R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball x (2 * r)) ≤
      ENNReal.ofReal (1 / 2)) :
    R.kernelSemigroup t x (Metric.ball x (11 * r))ᶜ ≤
      ENNReal.ofReal (2 * Real.exp 1 * phi) := by
  have hmu : (0 : ℝ) < (mu : ℝ) := mu.property
  have hr2 : r < 2 * r := by linarith only [hr]
  have hr1011 : 10 * r < 11 * r := by linarith only [hr]
  obtain ⟨psi, hpsi⟩ : ∃ psi : C₀(X, ℝ), ∀ z, psi z = radialCutoff x r (2 * r) z :=
    ⟨radialCutoffC0 x r (2 * r) hr2, fun _ ↦ rfl⟩
  obtain ⟨chi, hchi⟩ : ∃ chi : C₀(X, ℝ), ∀ z, chi z = radialCutoff x (10 * r) (11 * r) z :=
    ⟨radialCutoffC0 x (10 * r) (11 * r) hr1011, fun _ ↦ rfl⟩
  have hpsi0 : ∀ z, 0 ≤ psi z := fun z ↦ by
    rw [hpsi z]; exact radialCutoff_nonneg x r (2 * r) z
  have hpsi1 : ∀ z, psi z ≤ 1 := fun z ↦ by
    rw [hpsi z]; exact radialCutoff_le_one x r (2 * r) z
  have hpsi_one : ∀ z, dist z x ≤ r → psi z = 1 := fun z hz ↦ by
    rw [hpsi z]; exact radialCutoff_eq_one hr2 hz
  have hpsi_zero : ∀ z, 2 * r ≤ dist z x → psi z = 0 := fun z hz ↦ by
    rw [hpsi z]; exact radialCutoff_eq_zero hr2 hz
  have hchi0 : ∀ z, 0 ≤ chi z := fun z ↦ by
    rw [hchi z]; exact radialCutoff_nonneg x (10 * r) (11 * r) z
  have hchi1 : ∀ z, chi z ≤ 1 := fun z ↦ by
    rw [hchi z]; exact radialCutoff_le_one x (10 * r) (11 * r) z
  have hchi_one : ∀ z, dist z x ≤ 10 * r → chi z = 1 := fun z hz ↦ by
    rw [hchi z]; exact radialCutoff_eq_one hr1011 hz
  have hchi_zero : ∀ z, 11 * r ≤ dist z x → chi z = 0 := fun z hz ↦ by
    rw [hchi z]; exact radialCutoff_eq_zero hr1011 hz
  -- the compactified observables
  obtain ⟨ghat, hghat_coe, hghat_infty, hres_coe, hres_infty⟩ :
      ∃ ghat : C₀(OnePoint X, ℝ),
        (∀ z : X, ghat (z : OnePoint X) = 1 - psi z) ∧ ghat OnePoint.infty = 1 ∧
        (∀ y : X, (mu : ℝ) *
            R.onePointResolvent.toContractiveResolvent.operator mu ghat (y : OnePoint X) =
            1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y) ∧
        (mu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator mu ghat
            OnePoint.infty = 1 := by
    refine ⟨onePointAssemble (-psi) 1, fun z ↦ ?_, onePointAssemble_infty _ _,
      crudeMom_mul_onePointResolvent_assemble_coe R mu psi,
      crudeMom_mul_onePointResolvent_assemble_infty R mu psi⟩
    rw [onePointAssemble_coe, ZeroAtInftyContinuousMap.neg_apply]
    ring
  obtain ⟨fhat, hfhat_coe, hfhat_infty⟩ :
      ∃ fhat : C₀(OnePoint X, ℝ),
        (∀ z : X, fhat (z : OnePoint X) = 1 - chi z) ∧ fhat OnePoint.infty = 1 := by
    refine ⟨onePointAssemble (-chi) 1, fun z ↦ ?_, onePointAssemble_infty _ _⟩
    rw [onePointAssemble_coe, ZeroAtInftyContinuousMap.neg_apply]
    ring
  have hghat_nonneg : ∀ z, 0 ≤ ghat z := by
    intro z
    induction z using OnePoint.rec with
    | infty => rw [hghat_infty]; norm_num
    | coe y => rw [hghat_coe]; linarith only [hpsi1 y]
  -- the smallness away from the starting point
  have hfar : ∀ y : X, 10 * r ≤ dist y x →
      (mu : ℝ) * R.toContractiveResolvent.operator mu psi y ≤ 1 / 2 := by
    intro y hy
    have hball : MeasurableSet (Metric.ball x (2 * r)) := Metric.isOpen_ball.measurableSet
    have hle : ∀ z, ENNReal.ofReal (psi z) ≤ (Metric.ball x (2 * r)).indicator 1 z := by
      intro z
      by_cases hz : z ∈ Metric.ball x (2 * r)
      · rw [Set.indicator_of_mem hz, Pi.one_apply]
        exact ENNReal.ofReal_le_one.mpr (hpsi1 z)
      · rw [Set.indicator_of_notMem hz]
        have hz' : 2 * r ≤ dist z x := by
          simp only [Metric.mem_ball, not_lt] at hz
          exact hz
        rw [hpsi_zero z hz', ENNReal.ofReal_zero]
    have hpot : R.kernelSemigroup.kernelResolvent (mu : ℝ) ((Metric.ball x (2 * r)).indicator 1) y
        = R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball x (2 * r)) := by
      rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
        (measurable_one.indicator hball) y, lintegral_indicator_one hball]
    have hkey : ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi y) ≤
        ENNReal.ofReal (1 / 2) := by
      rw [ENNReal.ofReal_mul mu.property.le,
        ← R.kernelResolvent_ofReal_eq_operator mu psi hpsi0 y]
      calc ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun z ↦ ENNReal.ofReal (psi z)) y
          ≤ ENNReal.ofReal (mu : ℝ) *
              R.kernelSemigroup.kernelResolvent (mu : ℝ)
                ((Metric.ball x (2 * r)).indicator 1) y := by
            gcongr
            exact R.kernelSemigroup.kernelResolvent_mono _ hle y
        _ = ENNReal.ofReal (mu : ℝ) *
              R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball x (2 * r)) := by
            rw [hpot]
        _ ≤ ENNReal.ofReal (1 / 2) := hfarE y hy
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hkey
  -- the lower bound at the starting point, where conservativity is used
  have hball_meas : MeasurableSet (Metric.ball x r) := Metric.isOpen_ball.measurableSet
  have hpotconv : R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) =
      R.kernelSemigroup.kernelResolvent (mu : ℝ) ((Metric.ball x r).indicator 1) x := by
    rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ)
      (measurable_one.indicator hball_meas) x, lintegral_indicator_one hball_meas]
  have hindle : ∀ z, (Metric.ball x r).indicator 1 z ≤ ENNReal.ofReal (psi z) := by
    intro z
    by_cases hz : z ∈ Metric.ball x r
    · rw [Set.indicator_of_mem hz, Pi.one_apply,
        hpsi_one z (Metric.mem_ball.mp hz).le, ENNReal.ofReal_one]
    · rw [Set.indicator_of_notMem hz]
      exact zero_le
  have hpotball : ENNReal.ofReal (mu : ℝ) *
      R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) ≤
      ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi x) := by
    rw [hpotconv, ENNReal.ofReal_mul hmu.le,
      ← R.kernelResolvent_ofReal_eq_operator mu psi hpsi0 x]
    gcongr
    exact R.kernelSemigroup.kernelResolvent_mono _ hindle x
  have hunit : ENNReal.ofReal (mu : ℝ) *
      R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ = 1 := by
    have hconv : R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ =
        R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun _ ↦ 1) x := by
      rw [← R.kernelSemigroup.lintegral_resolventPotential (mu : ℝ) measurable_const x,
        lintegral_one]
    rw [hconv]
    exact hcons.ofReal_mul_kernelResolvent_one hmu x
  have hcentreE : (1 : ℝ≥0∞) ≤
      ENNReal.ofReal ((mu : ℝ) * R.toContractiveResolvent.operator mu psi x) +
        ENNReal.ofReal phi := by
    calc (1 : ℝ≥0∞)
        = ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x Set.univ := hunit.symm
      _ = ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r) +
          ENNReal.ofReal (mu : ℝ) *
            R.kernelSemigroup.resolventPotential (mu : ℝ) x (Metric.ball x r)ᶜ := by
          rw [← mul_add, measure_add_measure_compl hball_meas]
      _ ≤ _ := add_le_add hpotball hcentre
  have hcentreR : 1 ≤ (mu : ℝ) * R.toContractiveResolvent.operator mu psi x + phi := by
    rw [← ENNReal.ofReal_add (mul_nonneg hmu.le (R.isPositive mu psi hpsi0 x)) hphi]
      at hcentreE
    exact ENNReal.one_le_ofReal.mp hcentreE
  -- the excessive function dominating the compactified test observable
  have hval : ∀ w : OnePoint X,
      ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) w =
        2 * ((mu : ℝ) *
          R.onePointResolvent.toContractiveResolvent.operator mu ghat w) := by
    intro w
    rw [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul, mul_assoc]
  have hfv : ∀ z : OnePoint X, fhat z ≤
      ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) z := by
    intro z
    rw [hval z]
    induction z using OnePoint.rec with
    | infty =>
        rw [hfhat_infty, hres_infty]
        norm_num
    | coe y =>
        have hnn : 0 ≤ 1 - (mu : ℝ) * R.toContractiveResolvent.operator mu psi y := by
          rw [← hres_coe y]
          exact mul_nonneg hmu.le
            (R.onePointResolvent.isPositive mu ghat hghat_nonneg (y : OnePoint X))
        rw [hfhat_coe, hres_coe y]
        by_cases hy : dist y x ≤ 10 * r
        · rw [hchi_one y hy]
          linarith only [hnn]
        · replace hy := not_le.mp hy
          have hb := hfar y hy.le
          linarith only [hchi0 y, hb]
  have hexcess : ∀ nu : PositiveShift, (mu : ℝ) < (nu : ℝ) → ∀ z : OnePoint X,
      (nu : ℝ) * R.onePointResolvent.toContractiveResolvent.operator nu
          ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat) z ≤
        (nu : ℝ) / ((nu : ℝ) - (mu : ℝ)) *
          ((2 * (mu : ℝ)) •
            R.onePointResolvent.toContractiveResolvent.operator mu ghat) z :=
    fun nu hnu z ↦
      SuperdiffusionCLT.Section8.Process.PositiveC0ContractiveResolvent.mul_operator_smul_operator_le
        R.onePointResolvent mu hghat_nonneg (by linarith only [hmu]) nu hnu z
  have hcomp := R.onePointResolvent.integral_kernelSemigroup_le_exp_mul (mu : ℝ)
    ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat)
    hexcess fhat hfv t (x : OnePoint X)
  rw [ht] at hcomp
  have hvx : ((2 * (mu : ℝ)) • R.onePointResolvent.toContractiveResolvent.operator mu ghat)
      (x : OnePoint X) ≤ 2 * phi := by
    rw [hval, hres_coe x]
    linarith only [hcentreR]
  have hsg : R.onePointResolvent.kernelSemigroup = R.onePointKernelSemigroup := rfl
  rw [hsg] at hcomp
  have hfinal : ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X) ≤
      2 * Real.exp 1 * phi := by
    calc ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X)
        ≤ Real.exp 1 * ((2 * (mu : ℝ)) •
            R.onePointResolvent.toContractiveResolvent.operator mu ghat)
              (x : OnePoint X) := hcomp
      _ ≤ Real.exp 1 * (2 * phi) :=
          mul_le_mul_of_nonneg_left hvx (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 * phi := by ring
  -- transport the estimate back to the live space
  have : IsProbabilityMeasure (R.kernelSemigroup t x) := ⟨hcons t x⟩
  have hlaw : R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) := by
    rw [R.onePointKernelSemigroup_apply_coe t x, hcons t x, tsub_self, zero_smul, add_zero]
  have hmap : ∫ w, fhat w ∂R.onePointKernelSemigroup t (x : OnePoint X) =
      ∫ z, (1 - chi z) ∂R.kernelSemigroup t x := by
    have hmeas : AEStronglyMeasurable (fun w : OnePoint X ↦ fhat w)
        ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) :=
      (map_continuous fhat).aestronglyMeasurable
    rw [hlaw, integral_map OnePoint.continuous_coe.measurable.aemeasurable hmeas]
    exact integral_congr_ae (Eventually.of_forall hfhat_coe)
  have hSmeas : MeasurableSet ((Metric.ball x (11 * r))ᶜ) :=
    Metric.isOpen_ball.measurableSet.compl
  have hlower : (R.kernelSemigroup t x ((Metric.ball x (11 * r))ᶜ)).toReal ≤
      ∫ z, (1 - chi z) ∂R.kernelSemigroup t x := by
    rw [← measureReal_def, ← integral_indicator_one hSmeas]
    refine integral_mono ((integrable_const (1 : ℝ)).indicator hSmeas)
      ((integrable_const (1 : ℝ)).sub (chi.toBCF.integrable _)) fun z ↦ ?_
    by_cases hz : z ∈ (Metric.ball x (11 * r))ᶜ
    · have hz' : 11 * r ≤ dist z x := by
        simp only [Set.mem_compl_iff, Metric.mem_ball, not_lt] at hz
        exact hz
      rw [Set.indicator_of_mem hz, Pi.one_apply, hchi_zero z hz']
      norm_num
    · rw [Set.indicator_of_notMem hz]
      linarith only [hchi1 z]
  rw [← ENNReal.ofReal_toReal (measure_ne_top (R.kernelSemigroup t x) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← hmap] at hlower
  exact le_trans hlower hfinal

end SuperdiffusionCLT.Section8

end
