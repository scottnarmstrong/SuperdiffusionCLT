/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pC
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import SuperdiffusionCLT.Section8.Prereq.BallBoundary

/-!
# Integration by parts of a `C¹` vector field against `H¹₀`

For a bounded open convex `U`, a `C¹` vector field `B` with compact support and `φ ∈ H¹₀(U)`,
`∫_U B·∇φ = -∫_U (∇·B) φ`.  A `C¹` field on the whole space gives the same identity on `U` after
cutting it off outside a ball containing `U` (`ballBdry_ibp_of_contDiff`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Filter Topology
open SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem ballBdry_continuous_div {B : Vec d → Vec d} (hB : ∀ i, ContDiff ℝ 1 (fun x => B x i)) :
    Continuous (ballBdry_div B) := by
  unfold ballBdry_div
  refine continuous_finsetSum _ fun i _ => ?_
  simpa using ((hB i).continuous_fderiv (by simp)).clm_apply continuous_const

/-- Integration by parts of a compactly supported `C¹` field against `H¹₀`. -/
theorem ballBdry_ibp {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {B : Vec d → Vec d} (hB : ∀ i, ContDiff ℝ 1 (fun x => B x i))
    (hBc : ∀ i, HasCompactSupport (fun x => B x i)) (φ : H10Function U) :
    ∫ x in U, vecDot (B x) (φ.toH1Function.grad x) =
      -∫ x in U, ballBdry_div B x * φ.toH1Function.toFun x := by
  have : IsFiniteMeasure (volume.restrict U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hBb : ∀ i, ∃ M : ℝ, ∀ x, |B x i| ≤ M := fun i => by
    obtain ⟨M, hM⟩ := (hB i).continuous.bounded_above_of_compact_support (hBc i)
    exact ⟨M, fun x => by simpa using hM x⟩
  have hDc : ∀ i, Continuous (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) := fun i => by
    simpa using ((hB i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDb : ∀ i, ∃ M : ℝ, ∀ x, |fderiv ℝ (fun y => B y i) x (basisVec i)| ≤ M := fun i => by
    have hk : HasCompactSupport (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) := by
      simpa using (hBc i).fderiv_apply (𝕜 := ℝ) (basisVec i)
    obtain ⟨M, hM⟩ := (hDc i).bounded_above_of_compact_support hk
    exact ⟨M, fun x => by simpa using hM x⟩
  choose Mb hMb using hBb
  choose Md hMd using hDb
  let one : H1Function U := H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
    (f := fun _ : Vec d => (1 : ℝ)) contDiff_const
  have hone : ∀ x, one.toFun x = 1 := fun x => rfl
  have hone' : ∀ x i, one.grad x i = 0 := fun x i => by
    change fderiv ℝ (fun _ : Vec d => (1 : ℝ)) x (basisVec i) = 0
    simp
  have hBL2 : ∀ i, MemLp (fun x => B x i) 2 (volume.restrict U) := fun i =>
    ((hB i).continuous.memLp_of_hasCompactSupport (hBc i)).restrict U
  have hDL2 : ∀ i, MemLp (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) 2
      (volume.restrict U) := fun i => by
    have hk : HasCompactSupport (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) := by
      simpa using (hBc i).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact ((hDc i).memLp_of_hasCompactSupport hk).restrict U
  have hdivL2 : MemLp (ballBdry_div B) 2 (volume.restrict U) := by
    unfold ballBdry_div
    exact memLp_finsetSum (s := Finset.univ)
      (f := fun i x => fderiv ℝ (fun y => B y i) x (basisVec i)) fun i _ => hDL2 i
  have hsmooth : ∀ n, ∫ x in U, vecDot (B x) (hcGrad (φ.approx n) x) =
      -∫ x in U, ballBdry_div B x * φ.approx n x := by
    intro n
    have hφs := φ.approx_smooth n
    have hφc := φ.approx_hasCompactSupport n
    have hφU := φ.approx_support_subset n
    have hLipEx : ∀ i, ∃ K : NNReal, LipschitzWith K (fun x => B x i) := fun i =>
      ((hB i).lipschitzWith_of_hasCompactSupport (hBc i) (by simp))
    choose Kl hLip using hLipEx
    have hper : ∀ i, ∫ x in U, (B x i * one.toFun x) * fderiv ℝ (φ.approx n) x (basisVec i) =
        -∫ x in U, (B x i * one.grad x i + one.toFun x *
          fderiv ℝ (fun y => B y i) x (basisVec i)) * φ.approx n x := fun i =>
      integral_mul_partial_product hU.isOpen one (hLip i) (hMb i) hφs hφc hφU i
    have h1 : ∀ i, Integrable (fun x => (B x i * one.toFun x) *
        fderiv ℝ (φ.approx n) x (basisVec i)) (volume.restrict U) := fun i => by
      have := (hBL2 i).integrable_mul (memLp_hcGrad_apply hφs hφc U i)
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [hone, hcGrad]
    have h2 : ∀ i, Integrable (fun x => (fderiv ℝ (fun y => B y i) x (basisVec i)) *
        φ.approx n x) (volume.restrict U) := fun i =>
      (hDL2 i).integrable_mul (flatW2p_memLp_two_of_continuous hφs.continuous hφc)
    have e1 : ∫ x in U, vecDot (B x) (hcGrad (φ.approx n) x) =
        ∑ i, ∫ x in U, (B x i * one.toFun x) * fderiv ℝ (φ.approx n) x (basisVec i) := by
      rw [← integral_finsetSum _ (fun i _ => h1 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [vecDot, hcGrad, hone, mul_one]
    have e2 : ∫ x in U, ballBdry_div B x * φ.approx n x =
        ∑ i, ∫ x in U, (fderiv ℝ (fun y => B y i) x (basisVec i)) * φ.approx n x := by
      rw [← integral_finsetSum _ (fun i _ => h2 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [ballBdry_div, Finset.sum_mul]
    rw [e1, e2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hper i]
    simp only [hone, hone', mul_zero, zero_add, one_mul]
  have hAL2 : ∀ i, MemLp (fun x => B x i) 2 (volume.restrict U) := hBL2
  have hl := hc_tendsto_integral_vecDot (A := B) hAL2 φ
  have hr := (hc_tendsto_integral_mul hdivL2 φ).neg
  exact tendsto_nhds_unique (hl.congr fun n => hsmooth n) hr

/-- Integration by parts of a `C¹` field on the whole space against `H¹₀(U)`, for `U` inside a
closed ball. -/
theorem ballBdry_ibp_of_contDiff {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {G : Vec d → Vec d} (hG : ∀ i, ContDiff ℝ 1 (fun x => G x i)) {x₀ : Vec d} {R : ℝ}
    (hR : 0 ≤ R) (hUR : U ⊆ Metric.closedBall x₀ R) (φ : H10Function U) :
    ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) =
      -∫ x in U, ballBdry_div G x * φ.toH1Function.toFun x := by
  let χ : ContDiffBump x₀ := ⟨R + 1, R + 2, by linarith only [hR], by linarith only⟩
  let B : Vec d → Vec d := fun x i => χ x * G x i
  have hBd : ∀ i, ContDiff ℝ 1 (fun x => B x i) := fun i =>
    (χ.contDiff (n := 1)).mul (hG i)
  have hBc : ∀ i, HasCompactSupport (fun x => B x i) := fun i =>
    χ.hasCompactSupport.mul_right
  have hnhds : ∀ x ∈ U, B =ᶠ[nhds x] G := fun x hx => by
    have hx' : x ∈ Metric.closedBall x₀ R := hUR hx
    have hmem : Metric.ball x 1 ∈ nhds x := Metric.ball_mem_nhds x one_pos
    filter_upwards [hmem] with y hy
    have hy' : y ∈ Metric.closedBall x₀ (R + 1) := by
      rw [Metric.mem_closedBall] at hx' ⊢
      rw [Metric.mem_ball] at hy
      linarith only [dist_triangle y x x₀, hx', hy]
    ext i
    simp only [B, χ.one_of_mem_closedBall hy', one_mul]
  have hdiv : ∀ x ∈ U, ballBdry_div B x = ballBdry_div G x := fun x hx => by
    unfold ballBdry_div
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (fun y => B y i) =ᶠ[nhds x] fun y => G y i := (hnhds x hx).mono fun y hy => by
      simp [hy]
    rw [this.fderiv_eq]
  have h := ballBdry_ibp hU hBd hBc φ
  have hms : MeasurableSet U := hU.isOpen.measurableSet
  have e1 : ∫ x in U, vecDot (B x) (φ.toH1Function.grad x) =
      ∫ x in U, vecDot (G x) (φ.toH1Function.grad x) :=
    setIntegral_congr_fun hms fun x hx => by rw [(hnhds x hx).self_of_nhds]
  have e2 : ∫ x in U, ballBdry_div B x * φ.toH1Function.toFun x =
      ∫ x in U, ballBdry_div G x * φ.toH1Function.toFun x :=
    setIntegral_congr_fun hms fun x hx => by rw [hdiv x hx]
  rw [e1, e2] at h
  exact h

end SuperdiffusionCLT.Section8
