/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.CubePerturb
public import SuperdiffusionCLT.Section7.Analytic.CZ.CubeScalarData
public import SuperdiffusionCLT.Sobolev.DirichletW2pDivergence

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}`: the perturbation term

For a smooth coefficient field `A` with `A - 1` small and `∇A` of size `K` on a cube, the
divergence datum `(A - 1) ∇v` of a function `v` with a weak Hessian has a weak Jacobian, computed by
the product rule, and the Jacobian is bounded by the Hessian of `v` and the gradient of `v`.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem flatW2p_memLp_two_of_continuous {U : Set (Vec d)} {f : Vec d → ℝ} (hc : Continuous f)
    (hs : HasCompactSupport f) : MemLp f 2 (volume.restrict U) :=
  (hc.memLp_of_hasCompactSupport hs).restrict U

/-- Product rule for a weak partial derivative against a smooth multiplier. -/
theorem flatW2p_weakPartial_mul {U : Set (Vec d)} {j : Fin d} {a v g : Vec d → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hv : MemLp v 2 (volume.restrict U))
    (hg : MemLp g 2 (volume.restrict U)) (hw : HasWeakPartialDerivOn U j v g) :
    HasWeakPartialDerivOn U j (fun x => a x * v x)
      (fun x => a x * g x + v x * fderiv ℝ a x (basisVec j)) := by
  intro φ hφ hφc hφU
  have haφ : ContDiff ℝ (⊤ : ℕ∞) (fun x => a x * φ x) := ha.mul hφ
  have hcs : HasCompactSupport (fun x => a x * φ x) :=
    hφc.mono (Function.support_mul_subset_right _ _)
  have hsub : tsupport (fun x => a x * φ x) ⊆ U := (tsupport_mul_subset_right).trans hφU
  have h0 := hw (fun x => a x * φ x) haφ hcs hsub
  have hder : ∀ x, fderiv ℝ (fun y => a y * φ y) x (basisVec j) =
      a x * fderiv ℝ φ x (basisVec j) + fderiv ℝ a x (basisVec j) * φ x := by
    intro x
    have h1 : DifferentiableAt ℝ a x := (ha.differentiable (by norm_num)) x
    have h2 : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)) x
    rw [fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hc1 : Continuous (fun x => fderiv ℝ φ x (basisVec j)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hc2 : Continuous (fun x => fderiv ℝ a x (basisVec j)) :=
    (ha.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs1 : HasCompactSupport (fun x => fderiv ℝ φ x (basisVec j)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hT1 : MemLp (fun x => a x * fderiv ℝ φ x (basisVec j)) 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous (ha.continuous.mul hc1)
      (hcs1.mono (Function.support_mul_subset_right _ _))
  have hT2 : MemLp (fun x => fderiv ℝ a x (basisVec j) * φ x) 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous (hc2.mul hφ.continuous)
      (hφc.mono (Function.support_mul_subset_right _ _))
  have hT3 : MemLp (fun x => a x * φ x) 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous haφ.continuous hcs
  have i1 : Integrable (fun x => v x * (a x * fderiv ℝ φ x (basisVec j))) (volume.restrict U) :=
    hv.integrable_mul hT1
  have i2 : Integrable (fun x => v x * (fderiv ℝ a x (basisVec j) * φ x)) (volume.restrict U) :=
    hv.integrable_mul hT2
  have i3 : Integrable (fun x => g x * (a x * φ x)) (volume.restrict U) :=
    hg.integrable_mul hT3
  simp only [hder] at h0
  have e1 : (∫ x in U, v x * (a x * fderiv ℝ φ x (basisVec j) +
      fderiv ℝ a x (basisVec j) * φ x)) =
      (∫ x in U, v x * (a x * fderiv ℝ φ x (basisVec j))) +
        ∫ x in U, v x * (fderiv ℝ a x (basisVec j) * φ x) := by
    simp_rw [mul_add]
    exact integral_add i1 i2
  have e2 : (fun x => a x * v x * fderiv ℝ φ x (basisVec j)) =
      fun x => v x * (a x * fderiv ℝ φ x (basisVec j)) := by
    funext x; ring
  have e3 : (fun x => (a x * g x + v x * fderiv ℝ a x (basisVec j)) * φ x) =
      fun x => g x * (a x * φ x) + v x * (fderiv ℝ a x (basisVec j) * φ x) := by
    funext x; ring
  rw [e2, e3, integral_add i3 i2]
  linarith only [h0, e1]

/-- Sum of two weak partial derivatives. -/
theorem flatW2p_weakPartial_add {U : Set (Vec d)} {j : Fin d} {u₁ u₂ g₁ g₂ : Vec d → ℝ}
    (hu₁ : MemLp u₁ 2 (volume.restrict U)) (hu₂ : MemLp u₂ 2 (volume.restrict U))
    (hg₁ : MemLp g₁ 2 (volume.restrict U)) (hg₂ : MemLp g₂ 2 (volume.restrict U))
    (h₁ : HasWeakPartialDerivOn U j u₁ g₁) (h₂ : HasWeakPartialDerivOn U j u₂ g₂) :
    HasWeakPartialDerivOn U j (fun x => u₁ x + u₂ x) (fun x => g₁ x + g₂ x) := by
  intro φ hφ hφc hφU
  have hc1 : Continuous (fun x => fderiv ℝ φ x (basisVec j)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hD : MemLp (fun x => fderiv ℝ φ x (basisVec j)) 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous hc1 (hφc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hφ2 : MemLp φ 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous hφ.continuous hφc
  have e1 := h₁ φ hφ hφc hφU
  have e2 := h₂ φ hφ hφc hφU
  simp_rw [add_mul]
  have j1 : Integrable (fun x => u₁ x * fderiv ℝ φ x (basisVec j)) (volume.restrict U) :=
    hu₁.integrable_mul hD
  have j2 : Integrable (fun x => u₂ x * fderiv ℝ φ x (basisVec j)) (volume.restrict U) :=
    hu₂.integrable_mul hD
  have j3 : Integrable (fun x => g₁ x * φ x) (volume.restrict U) := hg₁.integrable_mul hφ2
  have j4 : Integrable (fun x => g₂ x * φ x) (volume.restrict U) := hg₂.integrable_mul hφ2
  rw [integral_add j1 j2, integral_add j3 j4]
  linarith only [e1, e2]

/-- A finite sum of weak partial derivatives. -/
theorem flatW2p_weakPartial_sum {U : Set (Vec d)} {j : Fin d} {ι : Type*} (s : Finset ι)
    {u g : ι → Vec d → ℝ} (hu : ∀ i ∈ s, MemLp (u i) 2 (volume.restrict U))
    (hg : ∀ i ∈ s, MemLp (g i) 2 (volume.restrict U))
    (hw : ∀ i ∈ s, HasWeakPartialDerivOn U j (u i) (g i)) :
    HasWeakPartialDerivOn U j (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, g i x) := by
  intro φ hφ hφc hφU
  have hc1 : Continuous (fun x => fderiv ℝ φ x (basisVec j)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hD : MemLp (fun x => fderiv ℝ φ x (basisVec j)) 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous hc1 (hφc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have hφ2 : MemLp φ 2 (volume.restrict U) :=
    flatW2p_memLp_two_of_continuous hφ.continuous hφc
  simp_rw [Finset.sum_mul]
  have j1 : ∀ i ∈ s, Integrable (fun x => u i x * fderiv ℝ φ x (basisVec j))
      (volume.restrict U) := fun i hi => (hu i hi).integrable_mul hD
  have j2 : ∀ i ∈ s, Integrable (fun x => g i x * φ x) (volume.restrict U) :=
    fun i hi => (hg i hi).integrable_mul hφ2
  rw [integral_finsetSum s j1, integral_finsetSum s j2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i hi => hw i hi φ hφ hφc hφU)

/-- Negation of a weak partial derivative. -/
theorem flatW2p_weakPartial_neg {U : Set (Vec d)} {j : Fin d} {u g : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U j u g) :
    HasWeakPartialDerivOn U j (fun x => -u x) (fun x => -g x) := by
  intro φ hφ hφc hφU
  have e := h φ hφ hφc hφU
  simp only [neg_mul, integral_neg]
  rw [e]

/-- A bounded continuous multiplier keeps `L²`. -/
theorem flatW2p_memLp_mul_bdd {U : Set (Vec d)} (hU : MeasurableSet U) {a f : Vec d → ℝ}
    {c : ℝ} (ha : Continuous a) (hb : ∀ x ∈ U, |a x| ≤ c)
    (hf : MemLp f 2 (volume.restrict U)) : MemLp (fun x => a x * f x) 2 (volume.restrict U) := by
  refine (hf.const_mul c).mono (ha.aestronglyMeasurable.mul hf.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((hb x hx).trans (le_abs_self c)) (abs_nonneg _)

/-- The weak Jacobian of the perturbation datum `(A - 1) ∇v`: the product rule. -/
noncomputable def flatPertJac (A : CoeffField d) (g : Vec d → Vec d)
    (h : Fin d → Fin d → Vec d → ℝ) : Fin d → Vec d → Vec d :=
  fun i x k => ∑ l, ((A x i l - (1 : Mat d) i l) * h l k x +
    g x l * fderiv ℝ (fun y => A y i l) x (basisVec k))

theorem flatW2p_hasWeakJacobian_pert {U : Set (Vec d)} (hU : MeasurableSet U) {A : CoeffField d}
    {ε K : ℝ} (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (hAε : ∀ x ∈ U, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    (hAK : ∀ x ∈ U, ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    {u : H1Function U} (H : HasWeakHessianOn U u) :
    HasWeakJacobianOn U (pert A u.grad) (flatPertJac A u.grad H.hess) := by
  intro i k
  have hacd : ∀ l, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i l - (1 : Mat d) i l) :=
    fun l => (hA i l).sub contDiff_const
  have hfd : ∀ l x, fderiv ℝ (fun y => A y i l - (1 : Mat d) i l) x =
      fderiv ℝ (fun y => A y i l) x := fun l x => fderiv_sub_const _
  have hdc : ∀ l, Continuous (fun x => fderiv ℝ (fun y => A y i l) x (basisVec k)) :=
    fun l => ((hA i l).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have key : ∀ l ∈ (Finset.univ : Finset (Fin d)), HasWeakPartialDerivOn U k
      (fun x => (A x i l - (1 : Mat d) i l) * u.grad x l)
      (fun x => (A x i l - (1 : Mat d) i l) * H.hess l k x +
        u.grad x l * fderiv ℝ (fun y => A y i l) x (basisVec k)) := by
    intro l _
    have := flatW2p_weakPartial_mul (hacd l) (u.gradMemL2 l) (H.hess_memL2 l k)
      (H.weak_second l k)
    simpa only [hfd] using this
  have hm1 : ∀ l ∈ (Finset.univ : Finset (Fin d)),
      MemLp (fun x => (A x i l - (1 : Mat d) i l) * u.grad x l) 2 (volume.restrict U) :=
    fun l _ => flatW2p_memLp_mul_bdd hU (c := ε) ((hacd l).continuous)
      (fun x hx => hAε x hx i l) (u.gradMemL2 l)
  have hm2 : ∀ l ∈ (Finset.univ : Finset (Fin d)),
      MemLp (fun x => (A x i l - (1 : Mat d) i l) * H.hess l k x +
        u.grad x l * fderiv ℝ (fun y => A y i l) x (basisVec k)) 2 (volume.restrict U) := by
    intro l _
    refine (flatW2p_memLp_mul_bdd hU (c := ε) ((hacd l).continuous)
      (fun x hx => hAε x hx i l) (H.hess_memL2 l k)).add ?_
    have := flatW2p_memLp_mul_bdd hU (c := K) (hdc l)
      (fun x hx => hAK x hx i l k) (u.gradMemL2 l)
    simpa only [mul_comm] using this
  have := flatW2p_weakPartial_sum Finset.univ hm1 hm2 key
  simpa only [pert, matVecMul, flatPertJac, Matrix.sub_apply] using this

/-- The Frobenius norm of a matrix is at most the sum of the absolute values of its entries. -/
theorem flatW2p_norm_ofMat_le (M : Mat d) :
    ‖HilbertMat.ofMat M‖ ≤ ∑ i, ∑ j, |M i j| := by
  set S : ℝ := ∑ i, ∑ j, |M i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hle : ∀ i j, |M i j| ≤ S := fun i j =>
    (Finset.single_le_sum (f := fun j => |M i j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, |M i j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i))
  have hsq : ‖HilbertMat.ofMat M‖ ^ 2 = ∑ i, ∑ j, M i j * M i j := by
    rw [← real_inner_self_eq_norm_sq, HilbertMat.inner_def]
  have h2 : ∑ i, ∑ j, M i j * M i j ≤ S * S := by
    calc ∑ i, ∑ j, M i j * M i j = ∑ i, ∑ j, |M i j| * |M i j| := by
          simp_rw [← abs_mul_abs_self (M _ _)]
      _ ≤ ∑ i, ∑ j, |M i j| * S := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hle i j) (abs_nonneg _)
      _ = S * S := by
          simp_rw [← Finset.sum_mul]
          rw [← hS]
  by_contra hlt
  have hlt := not_le.mp hlt
  nlinarith only [hlt, hS0, hsq, h2, norm_nonneg (HilbertMat.ofMat M)]

theorem flatW2p_norm_jac_le {A : CoeffField d} {ε K : ℝ} {g : Vec d → Vec d}
    {h : Fin d → Fin d → Vec d → ℝ} {x : Vec d}
    (hε : ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    (hK : ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) :
    ‖jacobianHilbertMat (flatPertJac A g h) x‖ ≤
      (d : ℝ) ^ 3 * (ε * ‖HilbertMat.ofMat (fun i j => h i j x)‖ + K * ‖g x‖) := by
  have hh : ∀ i j, |h i j x| ≤ ‖HilbertMat.ofMat (fun a b => h a b x)‖ := by
    intro i j
    have := abs_hess_le_norm (fun x => HilbertMat.ofMat (fun a b => h a b x)) i j x
    simpa using this
  have hg : ∀ l, |g x l| ≤ ‖g x‖ := fun l => by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (g x) l
  have hentry : ∀ i k, |flatPertJac A g h i x k| ≤
      d * (ε * ‖HilbertMat.ofMat (fun a b => h a b x)‖ + K * ‖g x‖) := by
    intro i k
    calc |flatPertJac A g h i x k| ≤ ∑ l, |((A x i l - (1 : Mat d) i l) * h l k x +
          g x l * fderiv ℝ (fun y => A y i l) x (basisVec k))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _l : Fin d, (ε * ‖HilbertMat.ofMat (fun a b => h a b x)‖ + K * ‖g x‖) := by
          refine Finset.sum_le_sum fun l _ => ?_
          refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [abs_mul]
            exact mul_le_mul (hε i l) (hh l k) (abs_nonneg _)
              (le_trans (abs_nonneg _) (hε i l))
          · rw [abs_mul, mul_comm]
            exact mul_le_mul (hK i l k) (hg l) (abs_nonneg _) (le_trans (abs_nonneg _) (hK i l k))
      _ = d * (ε * ‖HilbertMat.ofMat (fun a b => h a b x)‖ + K * ‖g x‖) := by
          simp [Finset.sum_const, Finset.card_univ]
          ring
  calc ‖jacobianHilbertMat (flatPertJac A g h) x‖
      ≤ ∑ i, ∑ k, |flatPertJac A g h i x k| := by
        have := flatW2p_norm_ofMat_le (fun i k => flatPertJac A g h i x k)
        simpa [jacobianHilbertMat] using this
    _ ≤ ∑ _i : Fin d, ∑ _k : Fin d,
          ((d : ℝ) * (ε * ‖HilbertMat.ofMat (fun a b => h a b x)‖ + K * ‖g x‖)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => hentry i k
    _ = (d : ℝ) ^ 3 * (ε * ‖HilbertMat.ofMat (fun i j => h i j x)‖ + K * ‖g x‖) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

end SuperdiffusionCLT.Section7
