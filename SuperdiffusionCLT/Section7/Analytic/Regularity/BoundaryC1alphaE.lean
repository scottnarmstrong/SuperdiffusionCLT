/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryC1alphaD
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal NNReal

/-!
# Integration by parts of an `H¹` function against an `H¹₀` test function

For `v ∈ H¹(U)`, a smooth compactly supported vector field `B` and `ψ ∈ H¹₀(U)`,
`∫_U v B·∇ψ = -∫_U (∇v·B + v ∇·B) ψ`.  This is the product rule used to put cutoff equations into
scalar form.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The divergence of a smooth vector field. -/
noncomputable def r3c_div (B : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∑ i, fderiv ℝ (fun y => B y i) x (basisVec i)

theorem r3c_memLp_bdd_mul {U : Set (Vec d)} {a f : Vec d → ℝ} (ha : Continuous a)
    {M : ℝ} (hM : ∀ x, |a x| ≤ M) (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun x => a x * f x) 2 (volume.restrict U) := by
  refine hf.of_le_mul (c := M) (ha.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

theorem r3c_integral_mul_vec_h10 {U : Set (Vec d)} (hU : IsOpen U) (v : H1Function U)
    {B : Vec d → Vec d} (hB : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => B x i))
    (hBc : ∀ i, HasCompactSupport (fun x => B x i)) (ψ : H10Function U) :
    ∫ x in U, vecDot (v.toFun x • B x) (ψ.toH1Function.grad x) =
      -∫ x in U, (vecDot (v.grad x) (B x) + v.toFun x * r3c_div B x) * ψ.toH1Function.toFun x := by
  -- bounded smooth coefficients
  have hBb : ∀ i, ∃ M : ℝ, ∀ x, |B x i| ≤ M := fun i => by
    obtain ⟨M, hM⟩ := (hB i).continuous.bounded_above_of_compact_support (hBc i)
    exact ⟨M, fun x => by simpa using hM x⟩
  have hDb : ∀ i, ∃ M : ℝ, ∀ x, |fderiv ℝ (fun y => B y i) x (basisVec i)| ≤ M := fun i => by
    have hc : Continuous (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) := by
      simpa using ((hB i).continuous_fderiv (by simp)).clm_apply continuous_const
    have hk : HasCompactSupport (fun x => fderiv ℝ (fun y => B y i) x (basisVec i)) := by
      simpa using (hBc i).fderiv_apply (𝕜 := ℝ) (basisVec i)
    obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hk
    exact ⟨M, fun x => by simpa using hM x⟩
  choose Mb hMb using hBb
  choose Md hMd using hDb
  have hvL2 : MemLp v.toFun 2 (volume.restrict U) := v.memL2
  have hgL2 : ∀ i, MemLp (fun x => v.grad x i) 2 (volume.restrict U) := fun i => v.grad_memL2 i
  have hBv : ∀ i, MemLp (fun x => B x i * v.toFun x) 2 (volume.restrict U) := fun i =>
    r3c_memLp_bdd_mul (hB i).continuous (hMb i) hvL2
  have hG2 : ∀ i, MemLp (fun x => B x i * v.grad x i + v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i))
      2 (volume.restrict U) := fun i =>
    (r3c_memLp_bdd_mul (hB i).continuous (hMb i) (hgL2 i)).add
      (by
        have := r3c_memLp_bdd_mul (U := U) (a := fun x => fderiv ℝ (fun y => B y i) x (basisVec i))
          (by simpa using ((hB i).continuous_fderiv (by simp)).clm_apply continuous_const) (hMd i) hvL2
        simpa only [mul_comm] using this)
  -- the scalar `a = ∇v·B + v div B`
  set a : Vec d → ℝ := fun x => vecDot (v.grad x) (B x) + v.toFun x * r3c_div B x with ha
  have hae : ∀ x, a x = ∑ i, (B x i * v.grad x i +
      v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) := by
    intro x
    simp only [ha, vecDot, r3c_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have haL2 : MemLp a 2 (volume.restrict U) := by
    have : a = fun x => ∑ i, (B x i * v.grad x i +
        v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) := funext hae
    rw [this]
    exact memLp_finsetSum (s := Finset.univ) (f := fun i x => B x i * v.grad x i + v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) fun i _ => hG2 i
  have hAL2 : ∀ i, MemLp (fun x => (v.toFun x • B x) i) 2 (volume.restrict U) := fun i => by
    simpa [mul_comm] using hBv i
  -- identity for smooth test functions
  have hsmooth : ∀ n, ∫ x in U, vecDot (v.toFun x • B x) (hcGrad (ψ.approx n) x) =
      -∫ x in U, a x * ψ.approx n x := by
    intro n
    have hφs := ψ.approx_smooth n
    have hφc := ψ.approx_hasCompactSupport n
    have hφU := ψ.approx_support_subset n
    have hLipEx : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (fun x => B x i) := fun i =>
      ((hB i).of_le (by simp : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).lipschitzWith_of_hasCompactSupport
        (hBc i) (by simp)
    choose Kl hLip using hLipEx
    have hper : ∀ i, ∫ x in U, (B x i * v.toFun x) * fderiv ℝ (ψ.approx n) x (basisVec i) =
        -∫ x in U, (B x i * v.grad x i + v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) *
          ψ.approx n x := fun i =>
      integral_mul_partial_product hU v (hLip i) (hMb i) hφs hφc hφU i
    have h1 : ∀ i, Integrable (fun x => (B x i * v.toFun x) * fderiv ℝ (ψ.approx n) x (basisVec i))
        (volume.restrict U) := fun i =>
      (hBv i).integrable_mul (memLp_hcGrad_apply hφs hφc U i)
    have h2 : ∀ i, Integrable (fun x => (B x i * v.grad x i +
        v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) * ψ.approx n x) (volume.restrict U) :=
      fun i => (hG2 i).integrable_mul (flatW2p_memLp_two_of_continuous hφs.continuous hφc)
    have e1 : ∫ x in U, vecDot (v.toFun x • B x) (hcGrad (ψ.approx n) x) =
        ∑ i, ∫ x in U, (B x i * v.toFun x) * fderiv ℝ (ψ.approx n) x (basisVec i) := by
      rw [← integral_finsetSum _ (fun i _ => h1 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [vecDot, hcGrad, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∫ x in U, a x * ψ.approx n x = ∑ i, ∫ x in U, (B x i * v.grad x i +
        v.toFun x * fderiv ℝ (fun y => B y i) x (basisVec i)) * ψ.approx n x := by
      rw [← integral_finsetSum _ (fun i _ => h2 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show a x * ψ.approx n x = _
      rw [hae x, Finset.sum_mul]
    rw [e1, e2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hper i
  have hl := hc_tendsto_integral_vecDot hAL2 ψ
  have hr := (hc_tendsto_integral_mul haL2 ψ).neg
  exact tendsto_nhds_unique (hl.congr fun n => hsmooth n) hr

end SuperdiffusionCLT.Section7
