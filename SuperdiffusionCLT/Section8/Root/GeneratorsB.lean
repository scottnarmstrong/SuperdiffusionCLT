/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.Generators
public import SuperdiffusionCLT.Section8.DivergenceForm.Regularity.CaccioppoliPlain
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeSchauderFreezing

/-!
# Local energy bounds and the `H¹` limit of the Dirichlet solutions

* `gen_caccioppoli_ball`: a homogeneous weak solution on `B_s` bounded by `δ` has Dirichlet energy
  on `B_{s/2}` at most `C δ²`.
-/

@[expose] public section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section8.DivergenceForm

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

/-- **Caccioppoli on a ball.** -/
theorem gen_caccioppoli_ball [NeZero d] {a : CoeffField d} {lam Lam s : ℝ} (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (euclidBall (d := d) s) a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : H1Function (euclidBall (d := d) s)) (δ : ℝ),
      IsWeakSolutionOn a (euclidBall (d := d) s) D 0 0 →
      (∀ᵐ x ∂volume.restrict (euclidBall (d := d) s), |D.toFun x| ≤ δ) →
      ∫ x in euclidBall (d := d) (s / 2), vecNormSq (D.grad x) ≤ C * δ ^ 2 := by
  have hcvx := gen_cvx (d := d) hs
  have h0 : (0 : Vec d) ∈ euclidBall (d := d) s := by
    show vecNormSq (0 : Vec d) < s ^ 2
    simp [vecNormSq, vecDot]
    positivity
  have hlam : 0 < lam := (hEll.2 0 h0).1
  have hfin : volume (euclidBall (d := d) s) ≠ ⊤ := volume_euclidBall_ne_top hs
  set K : Set (Vec d) := {x | vecNormSq x ≤ (s / 2) ^ 2} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_vecNormSq
      continuous_const) ?_
    refine (Metric.isBounded_ball (x := (0 : Vec d)) (r := s)).subset ?_
    refine fun x hx => euclidBall_subset_ball hs ?_
    have h1 : vecNormSq x ≤ (s / 2) ^ 2 := hx
    show vecNormSq x < s ^ 2
    nlinarith only [h1, hs]
  have hKU : K ⊆ euclidBall (d := d) s := by
    intro x hx
    have h1 : vecNormSq x ≤ (s / 2) ^ 2 := hx
    show vecNormSq x < s ^ 2
    nlinarith only [h1, hs]
  obtain ⟨η, hη, hηb, hη1, hηs⟩ := exists_contDiff_one_on_compact_tsupport_subset hKc hKU hcvx.1
  have hηc : HasCompactSupport η :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport η)
      (hcvx.2.1.isBounded.subset hηs)
  -- gradient bound
  have hηnot : ∀ x, x ∉ tsupport η → fderiv ℝ η x = 0 := fun x hx => by
    have h := notMem_tsupport_iff_eventuallyEq.1 hx
    rw [h.fderiv_eq]
    simp
  have hdη : Continuous fun x => vecNormSq (fun i => (fderiv ℝ η x) (basisVec i)) := by
    have hc : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by simp)
    unfold vecNormSq vecDot
    exact continuous_finsetSum _ fun i _ => (hc.clm_apply continuous_const).mul
      (hc.clm_apply continuous_const)
  obtain ⟨C₀, hC₀⟩ := hηc.exists_bound_of_continuousOn hdη.continuousOn
  set Cη : ℝ := max C₀ 0 with hCηdef
  have hCη0 : 0 ≤ Cη := le_max_right _ _
  have hCη : ∀ x, vecNormSq (fun i => (fderiv ℝ η x) (basisVec i)) ≤ Cη := fun x => by
    by_cases hx : x ∈ tsupport η
    · exact (le_trans (le_abs_self _) (hC₀ x hx)).trans (le_max_left _ _) |>.trans (le_refl _)
    · have : fderiv ℝ η x = 0 := hηnot x hx
      simp only [this, zero_apply]
      have : vecNormSq (fun _ : Fin d => (0 : ℝ)) = 0 := by simp [vecNormSq, vecDot]
      rw [this]
      exact hCη0
  refine ⟨2 / lam * (2 * Lam ^ 2 / lam * (Cη * (volume (euclidBall (d := d) s)).toReal)), ?_, ?_⟩
  · positivity
  intro D δ hD hδ
  have hsol : IsScalarForcedWeakSolution a (euclidBall (d := d) s) (fun _ => (0 : ℝ)) D := by
    refine ⟨MemLp.zero', fun v => ?_⟩
    have := hD v
    simpa [vecDot] using this
  have hcacc := cutoff_energy_absorbed_plain hsol hcvx hEll η hη hηc hηs
  simp only [zero_mul, integral_zero, zero_add] at hcacc
  set I1 : ℝ := ∫ x in euclidBall (d := d) s, η x ^ 2 * vecNormSq (D.grad x) with hI1def
  set I2 : ℝ := ∫ x in euclidBall (d := d) s, D.toFun x ^ 2 *
    vecNormSq (fun i => (fderiv ℝ η x) (basisVec i)) with hI2def
  have hη2 : ∀ x, η x ^ 2 ≤ 1 := fun x => by
    have := hηb x
    nlinarith only [this.1, this.2]
  have hgrad_int := SuperdiffusionCLT.Section8.Common.Estimates.Schauder.integrableOn_vecNormSq_grad D
  have hint : IntegrableOn (fun x => η x ^ 2 * vecNormSq (D.grad x)) (euclidBall (d := d) s) := by
    refine hgrad_int.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact ((hη.continuous.pow 2).aestronglyMeasurable).mul hgrad_int.1
    · have h0 : 0 ≤ vecNormSq (D.grad x) := vecNormSq_nonneg _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
      exact mul_le_of_le_one_left h0 (hη2 x)
  have hI2 : I2 ≤ δ ^ 2 * Cη * (volume (euclidBall (d := d) s)).toReal := by
    have h1 : I2 ≤ ∫ x in euclidBall (d := d) s, δ ^ 2 * Cη := by
      have hfm : IsFiniteMeasure (volume.restrict (euclidBall (d := d) s)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfin⟩
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
        (integrable_const (δ ^ 2 * Cη)) ?_
      · exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
      · filter_upwards [hδ] with x hx
        have h2 : D.toFun x ^ 2 ≤ δ ^ 2 := by
          have := pow_le_pow_left₀ (abs_nonneg _) hx 2
          rwa [sq_abs] at this
        exact mul_le_mul h2 (hCη x) (vecNormSq_nonneg _) (sq_nonneg _)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at h1
    linarith only [h1, mul_comm (volume (euclidBall (d := d) s)).toReal (δ ^ 2 * Cη)]
  have hI1 : ∫ x in euclidBall (d := d) (s / 2), vecNormSq (D.grad x) ≤ I1 := by
    have e : ∫ x in euclidBall (d := d) (s / 2), vecNormSq (D.grad x) =
        ∫ x in euclidBall (d := d) (s / 2), η x ^ 2 * vecNormSq (D.grad x) := by
      refine setIntegral_congr_fun (isOpen_euclidBall _).measurableSet fun x hx => ?_
      have hxK : x ∈ K := by
        have : vecNormSq x < (s / 2) ^ 2 := hx
        exact le_of_lt this
      have : η x = 1 := by simpa using hη1 hxK
      simp [this]
    rw [e]
    refine setIntegral_mono_set hint (Filter.Eventually.of_forall fun x => ?_) ?_
    · exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    · exact (euclidBall_mono (by linarith only [hs]) (by linarith only [hs])).eventuallyLE
  have hcl : 0 < 2 / lam := by positivity
  have h3 : I1 ≤ 2 / lam * (2 * Lam ^ 2 / lam * I2) := by
    have : lam / 2 * I1 ≤ 2 * Lam ^ 2 / lam * I2 := hcacc
    have h4 := mul_le_mul_of_nonneg_left this hcl.le
    have e : 2 / lam * (lam / 2 * I1) = I1 := by field_simp
    linarith only [h4, e]
  have hpos : 0 ≤ 2 / lam * (2 * Lam ^ 2 / lam) := by positivity
  calc ∫ x in euclidBall (d := d) (s / 2), vecNormSq (D.grad x) ≤ I1 := hI1
    _ ≤ 2 / lam * (2 * Lam ^ 2 / lam * I2) := h3
    _ ≤ 2 / lam * (2 * Lam ^ 2 / lam * (δ ^ 2 * Cη * (volume (euclidBall (d := d) s)).toReal)) := by
        gcongr
    _ = _ := by ring

end SuperdiffusionCLT.Section8
