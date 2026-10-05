/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorW2pB
public import SuperdiffusionCLT.Section7.Analytic.Defs

/-!
# The skew-structured equation as a Laplace equation with a divergence-free drift

For `a = ν Id + K`, `K` skew with `C²` entries, the weak equation `-∇·(a∇z) = f` on a bounded open
set is the weak Laplace equation `-Δ z = (f - c·∇z)/ν`, `c_i = ∑ⱼ ∂ⱼ aᵢⱼ`, and also
`-Δ z = f/ν - ∇·((z/ν) c)`.  The first is the strong-form drift equation, the second the
divergence-form equation with flux `(z/ν) c`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intW2p_matVecMul_one (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

theorem intW2p_memLp_mul_bdd {U : Set (Vec d)} {b f : Vec d → ℝ}
    (hb : AEStronglyMeasurable b (volume.restrict U)) {M : ℝ} (hM : ∀ x ∈ U, |b x| ≤ M)
    (hU : MeasurableSet U) (hf : MemLp f 2 (volume.restrict U)) :
    MemLp (fun x ↦ b x * f x) 2 (volume.restrict U) := by
  refine hf.of_le_mul (c := M) (hb.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _)

theorem intW2p_drift_bound {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    {U : Set (Vec d)} (hb : Bornology.IsBounded U) :
    ∃ M : ℝ, ∀ x ∈ U, ∀ i, |intW2p_drift a x i| ≤ M := by
  have hc : Continuous fun x ↦ intW2p_drift a x :=
    continuous_pi fun i ↦ (intW2p_drift_contDiff ha i).continuous
  obtain ⟨M, hM⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun x hx i ↦ ?_⟩
  have h1 := hM x (subset_closure hx)
  have h2 : |intW2p_drift a x i| ≤ ‖intW2p_drift a x‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (intW2p_drift a x) i
  exact h2.trans h1

theorem intW2p_memLp_drift_dot {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U) (z : H1Function U) :
    MemLp (fun x ↦ vecDot (intW2p_drift a x) (z.grad x)) 2 (volume.restrict U) := by
  obtain ⟨M, hM⟩ := intW2p_drift_bound ha hb
  unfold vecDot
  refine memLp_finsetSum _ fun i _ ↦ ?_
  exact intW2p_memLp_mul_bdd (b := fun x ↦ intW2p_drift a x i)
    (intW2p_drift_contDiff ha i).continuous.aestronglyMeasurable (fun x hx ↦ hM x hx i)
    hU.measurableSet (z.grad_memL2 i)

theorem intW2p_memLp_flux {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j)
    {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U) (z : H1Function U) (nu : ℝ)
    (i : Fin d) :
    MemLp (fun x ↦ z.grad x i - z.toFun x / nu * intW2p_drift a x i) 2 (volume.restrict U) := by
  obtain ⟨M, hM⟩ := intW2p_drift_bound ha hb
  refine (z.grad_memL2 i).sub ?_
  have := intW2p_memLp_mul_bdd (b := fun x ↦ intW2p_drift a x i)
    (intW2p_drift_contDiff ha i).continuous.aestronglyMeasurable (fun x hx ↦ hM x hx i)
    hU.measurableSet (MeasureTheory.MemLp.const_mul z.memL2 (1 / nu))
  refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
  simp only
  ring

/-- **The strong-form drift equation.**  `-Δ z = (f - c·∇z)/ν` weakly, tested against `H¹₀(U)`. -/
theorem intW2p_laplace_scalar {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {f : Vec d → ℝ} {z : H1Function U}
    (hz : SuperdiffusionCLT.Section8.DivergenceForm.IsScalarForcedWeakSolution a U f z) :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d)) U z
      (fun x ↦ (f x - vecDot (intW2p_drift a x) (z.grad x)) / nu) (fun _ ↦ 0) := by
  intro v
  have hf : MemLp f 2 (volume.restrict U) := hz.1
  have hDz := intW2p_memLp_drift_dot ha hU hb z
  have hs : MemLp (fun x ↦ (vecDot (intW2p_drift a x) (z.grad x) - f x) / nu) 2
      (volume.restrict U) := by
    have := MeasureTheory.MemLp.const_mul (hDz.sub hf) (1 / nu)
    refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.sub_apply]
    ring
  have key : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) +
        ∫ x in U, (vecDot (intW2p_drift a x) (z.grad x) - f x) / nu * φ x = 0 := by
    intro φ hφ hc hsub
    have e := hz.2 (H10Function.ofContDiff hU hφ hc hsub)
    have e2 := intW2p_smooth_scalar hU hsk ha z hφ hc hsub
    have e3 : (∫ x in U, vecDot (matVecMul (a x) (z.grad x))
        (fun i ↦ fderiv ℝ φ x (basisVec i))) = ∫ x in U, f x * φ x := e
    have hi1 := intW2p_integrable_mul hDz (hφ.continuous) hc
    have hi2 := intW2p_integrable_mul hf (hφ.continuous) hc
    have e4 : ∫ x in U, (vecDot (intW2p_drift a x) (z.grad x) - f x) / nu * φ x =
        (1 / nu) * ((∫ x in U, vecDot (intW2p_drift a x) (z.grad x) * φ x) -
          ∫ x in U, f x * φ x) := by
      rw [← integral_sub hi1 hi2, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    rw [e4]
    have hne : nu ≠ 0 := hnu.ne'
    field_simp
    linarith only [e, e2, e3]
  have hmain := intW2p_h10_of_smooth (W := z.grad) (s := fun x ↦
    (vecDot (intW2p_drift a x) (z.grad x) - f x) / nu) z.grad_memL2 hs key v
  have h0 : ∀ x, vecDot ((0 : Vec d)) (v.toH1Function.grad x) = 0 := fun x ↦ by simp [vecDot]
  simp only [intW2p_matVecMul_one, h0, integral_zero, add_zero]
  have : ∫ x in U, (f x - vecDot (intW2p_drift a x) (z.grad x)) / nu * v.toH1Function.toFun x =
      -∫ x in U, (vecDot (intW2p_drift a x) (z.grad x) - f x) / nu * v.toH1Function.toFun x := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [this]
  linarith only [hmain]

theorem intW2p_integrable_vecDot {U : Set (Vec d)} {X Y : Vec d → Vec d}
    (hX : ∀ i, MemLp (fun x ↦ X x i) 2 (volume.restrict U))
    (hY : ∀ i, MemLp (fun x ↦ Y x i) 2 (volume.restrict U)) :
    Integrable (fun x ↦ vecDot (X x) (Y x)) (volume.restrict U) := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ ↦ (hX i).integrable_mul (hY i)

/-- **The divergence-form drift equation.**  `-Δ z = f/ν - ∇·((z/ν) c)` weakly, tested against
`H¹₀(U)`: the flux `(z/ν) c` is bounded when `z` is. -/
theorem intW2p_laplace_flux {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {a : CoeffField d} {nu : ℝ} (hnu : 0 < nu)
    (hsk : ∀ y i j, a y i j + a y j i = if i = j then 2 * nu else 0)
    (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {f : Vec d → ℝ} {z : H1Function U}
    (hz : SuperdiffusionCLT.Section8.DivergenceForm.IsScalarForcedWeakSolution a U f z) :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn (fun _ ↦ (1 : Mat d)) U z
      (fun x ↦ f x / nu) (fun x ↦ (z.toFun x / nu) • intW2p_drift a x) := by
  intro v
  have hf : MemLp f 2 (volume.restrict U) := hz.1
  have hW := intW2p_memLp_flux ha hU hb z nu
  have hs : MemLp (fun x ↦ -(f x / nu)) 2 (volume.restrict U) := by
    have := MeasureTheory.MemLp.const_mul hf (-(1 / nu))
    refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  have hFl : ∀ i, MemLp (fun x ↦ (z.toFun x / nu * intW2p_drift a x i)) 2 (volume.restrict U) :=
    fun i ↦ by
      have := (z.grad_memL2 i).sub (hW i)
      refine this.ae_eq (Eventually.of_forall fun x ↦ ?_)
      simp only [Pi.sub_apply]
      ring
  have key : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x in U, vecDot (fun i ↦ z.grad x i - z.toFun x / nu * intW2p_drift a x i)
        (fun i ↦ fderiv ℝ φ x (basisVec i))) + ∫ x in U, -(f x / nu) * φ x = 0 := by
    intro φ hφ hc hsub
    have e := hz.2 (H10Function.ofContDiff hU hφ hc hsub)
    have e2 := intW2p_smooth_flux hU hsk ha z hφ hc hsub
    have e3 : (∫ x in U, vecDot (matVecMul (a x) (z.grad x))
        (fun i ↦ fderiv ℝ φ x (basisVec i))) = ∫ x in U, f x * φ x := e
    have hD : Continuous fun x ↦ vecDot (intW2p_drift a x)
        (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
      unfold vecDot
      exact continuous_finsetSum _ fun i _ ↦ ((intW2p_drift_contDiff ha i).continuous).mul
        (intW2p_d1_smooth hφ i).continuous
    have hDcs : HasCompactSupport fun x ↦ vecDot (intW2p_drift a x)
        (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
      unfold vecDot
      exact intW2p_cs_sum Finset.univ fun i _ ↦ (intW2p_d1_cs hc i).mul_left
    have hi1 := intW2p_integrable_mul z.memL2 hD hDcs
    have hi2 := intW2p_integrable_mul hf hφ.continuous hc
    have hgz : ∀ i, MemLp (fun x ↦ z.grad x i) 2 (volume.restrict U) := z.grad_memL2
    have hi3 : Integrable (fun x ↦ vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i)))
        (volume.restrict U) := by
      unfold vecDot
      exact integrable_finsetSum _ fun i _ ↦ intW2p_integrable_mul (hgz i)
        (intW2p_d1_smooth hφ i).continuous (intW2p_d1_cs hc i)
    have e4 : (∫ x in U, vecDot (fun i ↦ z.grad x i - z.toFun x / nu * intW2p_drift a x i)
        (fun i ↦ fderiv ℝ φ x (basisVec i))) =
        (∫ x in U, vecDot (z.grad x) (fun i ↦ fderiv ℝ φ x (basisVec i))) -
          (1 / nu) * ∫ x in U, z.toFun x * vecDot (intW2p_drift a x)
            (fun i ↦ fderiv ℝ φ x (basisVec i)) := by
      rw [← integral_const_mul, ← integral_sub hi3 (hi1.const_mul _)]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only [vecDot, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    have e5 : ∫ x in U, -(f x / nu) * φ x = -((1 / nu) * ∫ x in U, f x * φ x) := by
      rw [← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      simp only
      ring
    rw [e4, e5]
    have hne : nu ≠ 0 := hnu.ne'
    field_simp
    linarith only [e, e2, e3]
  have hmain := intW2p_h10_of_smooth (W := fun x i ↦ z.grad x i - z.toFun x / nu * intW2p_drift a x i)
    (s := fun x ↦ -(f x / nu)) hW hs key v
  have hflux : ∀ x, vecDot (fun i ↦ z.grad x i - z.toFun x / nu * intW2p_drift a x i)
      (v.toH1Function.grad x) = vecDot (z.grad x) (v.toH1Function.grad x) -
        vecDot ((z.toFun x / nu) • intW2p_drift a x) (v.toH1Function.grad x) := fun x ↦ by
    simp only [vecDot, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hI1 := intW2p_integrable_vecDot (U := U) (X := z.grad) (Y := v.toH1Function.grad)
    z.grad_memL2 v.toH1Function.grad_memL2
  have hI2 := intW2p_integrable_vecDot (U := U) (X := fun x ↦ (z.toFun x / nu) • intW2p_drift a x)
    (Y := v.toH1Function.grad) (fun i ↦ by simpa only [Pi.smul_apply, smul_eq_mul] using hFl i)
    v.toH1Function.grad_memL2
  simp only [hflux] at hmain
  rw [integral_sub hI1 hI2] at hmain
  simp only [intW2p_matVecMul_one]
  have e6 : ∫ x in U, -(f x / nu) * v.toH1Function.toFun x =
      -∫ x in U, f x / nu * v.toH1Function.toFun x := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  rw [e6] at hmain
  linarith only [hmain]

end SuperdiffusionCLT.Section8
