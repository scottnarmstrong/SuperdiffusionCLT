/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import MarkovProcess.Path.ExitTimeShift
public import SuperdiffusionCLT.Section8.Process.Trajectory.ExitTimeChaining

/-!
# One restart step between nested exit times

If `U₁ ⊆ U₂` are open and `closure U₁ ⊆ U₂`, a path started at `x ∈ U₁` exits `U₁` before `U₂`, at
a point of `closure U₁`, and the exit time from `U₂` is the exit time from `U₁` plus the exit time
from `U₂` of the restarted path.  The strong Markov property turns this into the comparison

`E^x[e^{-lam T_{U₂}}] ≤ M · E^x[e^{-lam T_{U₁}}]`

whenever `E^y[e^{-lam T_{U₂}}] ≤ M` on `closure U₁`.

* `exitEst_exitTime_mono`, `exitEst_shift_add_le`: path-level facts;
* `exitEst_lintegral_step`: the comparison.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

open MarkovProcess

namespace SuperdiffusionCLT.Section8.Process

noncomputable section

section PathFacts

variable {alpha : Type*} [PseudoMetricSpace alpha]

/-- Enlarging the open set postpones the exit. -/
theorem exitEst_exitTime_mono {U₁ U₂ : Set alpha} (h : U₁ ⊆ U₂) (omega : ContinuousPath alpha) :
    ContinuousPath.exitTime U₁ omega ≤ ContinuousPath.exitTime U₂ omega := by
  rw [MarkovProcess.ContinuousPath.le_exitTime_iff]
  intro v hv
  exact MarkovProcess.ContinuousPath.exitTime_le_of_notMem U₁ omega v fun h1 => hv (h h1)

/-- The exit time splits at any time not after it. -/
theorem exitEst_shift_add_le (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) ≤ ContinuousPath.exitTime U omega) :
    (t : ℝ≥0∞) + ContinuousPath.exitTime U (ContinuousPath.shift t omega) ≤
      ContinuousPath.exitTime U omega := by
  rw [add_comm, MarkovProcess.ContinuousPath.le_exitTime_iff]
  intro v hv
  have hle : ContinuousPath.exitTime U omega ≤ v :=
    MarkovProcess.ContinuousPath.exitTime_le_of_notMem U omega v hv
  have htv : t ≤ v := ENNReal.coe_le_coe.mp (ht.trans hle)
  have hbad : ContinuousPath.shift t omega (v - t) ∉ U := by
    rw [ContinuousPath.shift_apply, add_tsub_cancel_of_le htv]
    exact hv
  calc ContinuousPath.exitTime U (ContinuousPath.shift t omega) + (t : ℝ≥0∞) ≤
        ((v - t : NNReal) : ℝ≥0∞) + t :=
        add_le_add
          (MarkovProcess.ContinuousPath.exitTime_le_of_notMem U (ContinuousPath.shift t omega)
            (v - t) hbad) le_rfl
    _ = v := by rw [← ENNReal.coe_add, tsub_add_cancel_of_le htv]

end PathFacts

section Step

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha] [LocallyCompactSpace alpha]

open MarkovProcess.SubMarkovKernelSemigroup

/-- **One restart between nested exit times.**  If `E^y[e^{-lam T_{U₂}}] ≤ M` on `closure U₁`,
then `E^x[e^{-lam T_{U₂}}] ≤ M E^x[e^{-lam T_{U₁}}]` for `x ∈ U₁`, where `closure U₁ ⊆ U₂`. -/
theorem exitEst_lintegral_step (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U₁ U₂ : Set alpha) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hcl : closure U₁ ⊆ U₂)
    (lam : ℝ) (hlam : 0 ≤ lam) (M : ℝ≥0∞) (hMtop : M ≠ ⊤)
    (hM : ∀ y ∈ closure U₁,
      ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam (ContinuousPath.exitTime U₂) eta
        ∂(IsConservative.continuousProcess P hP y) ≤ M)
    (x : alpha) (hx : x ∈ U₁) :
    ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam (ContinuousPath.exitTime U₂) eta
        ∂(IsConservative.continuousProcess P hP x) ≤
      M * ∫⁻ eta, ContinuousPath.discountedStoppingWeight lam (ContinuousPath.exitTime U₁) eta
        ∂(IsConservative.continuousProcess P hP x) := by
  let Q : Kernel alpha (MarkovProcess.ContinuousPath alpha) :=
    IsConservative.continuousProcess P hP
  let σ : MarkovProcess.ContinuousPath alpha → ℝ≥0∞ := ContinuousPath.exitTime U₁
  let W : MarkovProcess.ContinuousPath alpha → ℝ≥0∞ :=
    ContinuousPath.discountedStoppingWeight lam σ
  let F : MarkovProcess.ContinuousPath alpha → ℝ≥0∞ :=
    ContinuousPath.discountedStoppingWeight lam (ContinuousPath.exitTime U₂)
  let S : Set (MarkovProcess.ContinuousPath alpha) := {omega | σ omega < ⊤}
  let Y : MarkovProcess.ContinuousPath alpha → MarkovProcess.ContinuousPath alpha :=
    fun omega ↦ ContinuousPath.shift ((σ omega).untopD 0) omega
  have hσ : IsStoppingTime (ContinuousPath.canonicalFiltration (alpha := alpha)) σ :=
    ContinuousPath.isStoppingTime_exitTime U₁ hU₁
  have hS : MeasurableSet[hσ.measurableSpace] S :=
    StoppingTime.measurableSet_stoppingTime_lt_top hσ
  have hW : Measurable[hσ.measurableSpace] W :=
    ContinuousPath.measurable_discountedStoppingWeight_stopped σ hσ lam
  have hF : Measurable F :=
    ContinuousPath.measurable_discountedStoppingWeight _
      (ContinuousPath.isStoppingTime_exitTime U₂ hU₂) lam
  have hY : Measurable Y := ContinuousPath.measurable_shift_untopD_stoppingTime σ hσ
  have hRestart :
      ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega ∂Q x =
        ∫⁻ omega, W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((σ omega).untopD 0))) omega ∂Q x := by
    apply StoppingTime.lintegral_mul_indicator_of_restrict_map
      (mu := Q x)
      (kappa := Kernel.comap Q (fun omega ↦ omega ((σ omega).untopD 0))
        (ContinuousPath.measurable_eval_untopD_stoppingTime σ hσ))
      (Y := Y) (m := hσ.measurableSpace) (S := S) (F := F) (W := W)
    · exact hY
    · exact hσ.measurableSpace_le
    · exact hS
    · intro A hA
      exact hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK x σ hσ A hA
    · exact hF
    · exact hW
  have hzero : ∀ᵐ omega ∂Q x, omega 0 = x := IsConservative.ae_eval_zero_eq hP hK x
  -- pointwise comparison
  have hpoint : ∀ omega : MarkovProcess.ContinuousPath alpha,
      F omega ≤ W omega * S.indicator (fun omega ↦ F (Y omega)) omega := by
    intro omega
    by_cases hs : omega ∈ S
    · rw [Set.indicator_of_mem hs]
      have hσfin : σ omega ≠ ⊤ := ne_of_lt hs
      have hle : σ omega ≤ ContinuousPath.exitTime U₂ omega :=
        exitEst_exitTime_mono (fun y hy => hcl (subset_closure hy)) omega
      by_cases h2 : ContinuousPath.exitTime U₂ omega = ⊤
      · have : F omega = 0 := by
          simp [F, ContinuousPath.discountedStoppingWeight, h2]
        rw [this]; exact zero_le
      · have hcoe : (((σ omega).untopD 0 : NNReal) : ℝ≥0∞) = σ omega := by
          exact ENNReal.coe_toNNReal hσfin
        have hsplit := exitEst_shift_add_le U₂ omega ((σ omega).untopD 0) (hcoe ▸ hle)
        rw [hcoe] at hsplit
        have hYfin : ContinuousPath.exitTime U₂ (Y omega) ≠ ⊤ := by
          intro h
          have : ContinuousPath.exitTime U₂ (ContinuousPath.shift ((σ omega).untopD 0) omega) = ⊤ := h
          rw [this, add_top] at hsplit
          exact h2 (top_le_iff.mp hsplit)
        have hWmem : omega ∈ ({omega | σ omega < ⊤} : Set _) := hs
        have hFmem : omega ∈ ({omega | ContinuousPath.exitTime U₂ omega < ⊤} : Set _) :=
          lt_top_iff_ne_top.2 h2
        have hYmem : Y omega ∈ ({omega | ContinuousPath.exitTime U₂ omega < ⊤} : Set _) :=
          lt_top_iff_ne_top.2 hYfin
        simp only [F, W, ContinuousPath.discountedStoppingWeight]
        rw [Set.indicator_of_mem hFmem, Set.indicator_of_mem hWmem, Set.indicator_of_mem hYmem,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hreal := ENNReal.toReal_mono h2 hsplit
        rw [ENNReal.toReal_add hσfin hYfin] at hreal
        nlinarith only [hreal, hlam]
    · rw [Set.indicator_of_notMem hs, mul_zero]
      have hs' : σ omega = ⊤ := by
        by_contra hne; exact hs (lt_top_iff_ne_top.2 hne)
      have : ContinuousPath.exitTime U₂ omega = ⊤ :=
        top_le_iff.mp (hs' ▸ exitEst_exitTime_mono (fun y hy => hcl (subset_closure hy)) omega)
      simp [F, ContinuousPath.discountedStoppingWeight, this]
  have hbound : ∀ᵐ omega ∂Q x,
      W omega * S.indicator
          (fun omega ↦ ∫⁻ eta, F eta ∂Q (omega ((σ omega).untopD 0))) omega ≤ M * W omega := by
    filter_upwards [hzero] with omega h0
    by_cases hs : omega ∈ S
    · rw [Set.indicator_of_mem hs]
      have hfr := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier U₁ hU₁ omega
        (h0 ▸ hx) (ne_of_lt hs)
      have hcl' : omega ((σ omega).untopD 0) ∈ closure U₁ := hfr.1
      rw [mul_comm]
      exact mul_le_mul_left (hM _ hcl') _
    · rw [Set.indicator_of_notMem hs, mul_zero]; exact zero_le
  calc ∫⁻ omega, F omega ∂Q x ≤ ∫⁻ omega, W omega * S.indicator (fun omega ↦ F (Y omega)) omega
        ∂Q x := lintegral_mono hpoint
    _ = _ := hRestart
    _ ≤ ∫⁻ omega, M * W omega ∂Q x := lintegral_mono_ae hbound
    _ = M * ∫⁻ omega, W omega ∂Q x := lintegral_const_mul' _ _ hMtop

end Step

end

end SuperdiffusionCLT.Section8.Process
