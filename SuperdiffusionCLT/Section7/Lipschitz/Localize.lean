/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB
public import SuperdiffusionCLT.Section7.Analytic.Defs
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.Truncation
public import Homogenization.Sobolev.H1.LocalizedZeroTrace

/-!
# Localization of the Poisson equation by a cutoff

If `-Δφ = F` weakly in `V` and `φ` has localized zero trace in a window `B`, then for a smooth
cutoff `χ` with compact support in `B` the product `χφ` lies in `H¹₀(V)` and solves
`-Δ(χφ) = F'` with `F' = χF - 2∇χ·∇φ - φΔχ`; the datum is scalar and equals `F` where `χ = 1`.
-/

@[expose] public section

open Homogenization MeasureTheory

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem lip_localize_memLp_mul {μ : Measure (Vec d)} [IsFiniteMeasureOnCompacts μ]
    {b f : Vec d → ℝ} (hb : Continuous b) (hbc : HasCompactSupport b)
    (hf : MemLp f 2 μ) : MemLp (fun x => b x * f x) 2 μ := by
  have hb' : MemLp b ⊤ μ := hb.memLp_of_hasCompactSupport hbc
  exact hb'.mul hf

theorem lip_localize_matVec_one (v : Vec d) : matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

theorem lip_localize_vecDot_zero (v : Vec d) : vecDot (0 : Vec d) v = 0 := by
  simp [vecDot]

/-- **C2f — localization of the Poisson equation by a cutoff**: the product with a cutoff
supported in the window of the localized zero trace is an `H¹₀` solution; the right-hand side is
unchanged where the cutoff is `1`. -/
theorem lip_localize (d : ℕ) [NeZero d] {V B : Set (Vec d)} (hV : IsOpen V)
    (hVb : IsBoundedDomain V) (φ : H1Function V) (F : Vec d → ℝ) (hF : MemScalarL2 V F)
    (hφ : IsWeakSolutionOn (fun _ => (1 : Mat d)) V φ F (fun _ => 0))
    (hz : LocalizedZeroTraceFunctionOn V B φ.toFun)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχB : tsupport χ ⊆ B) :
    ∃ (φ' : H10Function V) (F' : Vec d → ℝ), MemScalarL2 V F' ∧
      (∀ x, φ'.toH1Function.toFun x = χ x * φ.toFun x) ∧
      (∀ x, (∀ᶠ y in nhds x, χ y = 1) → F' x = F x) ∧
      IsWeakSolutionOn (fun _ => (1 : Mat d)) V φ'.toH1Function F' (fun _ => 0) := by
  classical
  have _ := hVb
  let D : Fin d → Vec d → ℝ := fun i x => fderiv ℝ χ x (basisVec i)
  have hD : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (D i) := fun i =>
    (hχ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc : ∀ i, HasCompactSupport (D i) := fun i => hχc.fderiv_apply ℝ (basisVec i)
  let c : Fin d → Vec d → ℝ := fun i x => fderiv ℝ (D i) x (basisVec i)
  have hcC : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i) := fun i =>
    ((hD i).fderiv_right (by simp)).clm_apply contDiff_const
  have hcc : ∀ i, HasCompactSupport (c i) := fun i => (hDc i).fderiv_apply ℝ (basisVec i)
  obtain ⟨φ', hφ'⟩ := hz χ hχ hχc hχB
  let F' : Vec d → ℝ := fun x =>
    χ x * F x - 2 * ∑ i, D i x * φ.grad x i - ∑ i, c i x * φ.toFun x
  have hmul : ∀ {b f : Vec d → ℝ}, Continuous b → HasCompactSupport b →
      MemLp f 2 (volume.restrict V) → MemLp (fun x => b x * f x) 2 (volume.restrict V) :=
    fun hb hbc hf => lip_localize_memLp_mul hb hbc hf
  have hint : ∀ {f g : Vec d → ℝ}, MemLp f 2 (volume.restrict V) → MemLp g 2 (volume.restrict V) →
      Integrable (fun x => f x * g x) (volume.restrict V) := fun hf hg => hf.integrable_mul hg
  have hF'L2 : MemScalarL2 V F' := by
    have h1 : MemLp (fun x => χ x * F x) 2 (volume.restrict V) := hmul hχ.continuous hχc hF
    have h2 : MemLp (fun x => ∑ i, D i x * φ.grad x i) 2 (volume.restrict V) :=
      memLp_finsetSum _ fun i _ => hmul (hD i).continuous (hDc i) (φ.gradMemL2 i)
    have h3 : MemLp (fun x => ∑ i, c i x * φ.toFun x) 2 (volume.restrict V) :=
      memLp_finsetSum _ fun i _ => hmul (hcC i).continuous (hcc i) φ.memL2
    exact (h1.sub (h2.const_mul 2)).sub h3
  refine ⟨φ', F', hF'L2, fun x => congrFun hφ' x, ?_, ?_⟩
  · intro x hx
    have hD0 : ∀ i, D i x = 0 := fun i => by
      have h1 : χ =ᶠ[nhds x] fun _ => (1 : ℝ) := hx
      simp only [D]
      rw [h1.fderiv_eq]
      simp
    have hc0 : ∀ i, c i x = 0 := fun i => by
      have h1 : ∀ᶠ y in nhds x, χ =ᶠ[nhds y] fun _ => (1 : ℝ) := hx.eventually_nhds
      have h2 : D i =ᶠ[nhds x] fun _ => (0 : ℝ) := h1.mono fun y hy => by
        simp only [D]
        rw [hy.fderiv_eq]
        simp
      simp only [c]
      rw [h2.fderiv_eq]
      simp
    simp only [F', hD0, hc0]
    simp [hx.self_of_nhds]
  · intro ψ
    let u : H1Function V := φ.mulContDiffHasCompactSupport hχ hχc
    have hu : u.toFun = fun x => χ x * φ.toFun x := by simp [u]
    have hug : ∀ x i, u.grad x i = χ x * φ.grad x i + φ.toFun x * D i x := fun x i => by
      simp [u, D]
    have e1 : φ'.toH1Function.toFun = u.toFun := by rw [hφ', hu]
    have hae : ∀ i, (fun x => φ'.toH1Function.grad x i) =ᵐ[volume.restrict V]
        (fun x => u.grad x i) := fun i => by
      have h := φ'.toH1Function.hasWeakPartialDerivOn i
      rw [e1] at h
      exact HasWeakPartialDerivOn.ae_eq hV
        (locallyIntegrableOn_of_memL2On (φ'.toH1Function.gradMemL2 i))
        (locallyIntegrableOn_of_memL2On (u.gradMemL2 i)) h (u.hasWeakPartialDerivOn i)
    have hall : ∀ᵐ x ∂volume.restrict V, ∀ i,
        φ'.toH1Function.grad x i = χ x * φ.grad x i + φ.toFun x * D i x := by
      rw [ae_all_iff]
      intro i
      filter_upwards [hae i] with x hx
      rw [hx, hug]
    let ψχ : H10Function V := ψ.mulContDiffHasCompactSupport hχ hχc
    have hψχf : ψχ.toH1Function.toFun = fun x => χ x * ψ.toH1Function.toFun x := by
      simp [ψχ]
    have hψχg : ∀ x i, ψχ.toH1Function.grad x i =
        χ x * ψ.toH1Function.grad x i + ψ.toH1Function.toFun x * D i x := fun x i => by
      show (ψ.toH1Function.mulContDiffHasCompactSupport hχ hχc).grad x i = _
      simp [D]
    have hE1 := hφ ψχ
    simp only [lip_localize_matVec_one, lip_localize_vecDot_zero, integral_zero, add_zero] at hE1
    have I1 : ∀ i, Integrable (fun x => χ x * φ.grad x i * ψ.toH1Function.grad x i)
        (volume.restrict V) := fun i =>
      hint (hmul hχ.continuous hχc (φ.gradMemL2 i)) (ψ.toH1Function.gradMemL2 i)
    have I2 : ∀ i, Integrable (fun x => D i x * φ.toFun x * ψ.toH1Function.grad x i)
        (volume.restrict V) := fun i =>
      hint (hmul (hD i).continuous (hDc i) φ.memL2) (ψ.toH1Function.gradMemL2 i)
    have I3 : ∀ i, Integrable (fun x => D i x * φ.grad x i * ψ.toH1Function.toFun x)
        (volume.restrict V) := fun i =>
      hint (hmul (hD i).continuous (hDc i) (φ.gradMemL2 i)) ψ.toH1Function.memL2
    have I4 : ∀ i, Integrable (fun x => c i x * φ.toFun x * ψ.toH1Function.toFun x)
        (volume.restrict V) := fun i =>
      hint (hmul (hcC i).continuous (hcc i) φ.memL2) ψ.toH1Function.memL2
    have I5 : Integrable (fun x => χ x * F x * ψ.toH1Function.toFun x) (volume.restrict V) :=
      hint (hmul hχ.continuous hχc hF) ψ.toH1Function.memL2
    -- the test identity
    have hT : (∑ i, ∫ x in V, χ x * φ.grad x i * ψ.toH1Function.grad x i) +
        (∑ i, ∫ x in V, D i x * φ.grad x i * ψ.toH1Function.toFun x) =
        ∫ x in V, χ x * F x * ψ.toH1Function.toFun x := by
      rw [← Finset.sum_add_distrib]
      have h1 : ∫ x in V, vecDot (φ.grad x) (ψχ.toH1Function.grad x) =
          ∑ i, ∫ x in V, (χ x * φ.grad x i * ψ.toH1Function.grad x i +
            D i x * φ.grad x i * ψ.toH1Function.toFun x) := by
        refine Eq.trans ?_ (integral_finsetSum _ fun i _ => (I1 i).add (I3 i))
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [vecDot, hψχg]
        refine Finset.sum_congr rfl fun i _ => by ring
      have h2 : ∫ x in V, F x * ψχ.toH1Function.toFun x =
          ∫ x in V, χ x * F x * ψ.toH1Function.toFun x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hψχf]; ring
      rw [h1, h2] at hE1
      rw [← hE1]
      exact Finset.sum_congr rfl fun i _ => (integral_add (I1 i) (I3 i)).symm
    -- integration by parts
    have hP : ∀ i, ∫ x in V, D i x * φ.toFun x * ψ.toH1Function.grad x i =
        -((∫ x in V, D i x * φ.grad x i * ψ.toH1Function.toFun x) +
          ∫ x in V, c i x * φ.toFun x * ψ.toH1Function.toFun x) := fun i => by
      let w : H1Function V := φ.mulContDiffHasCompactSupport (hD i) (hDc i)
      have h := rc_ibp w ψ i
      have hw : ∀ x, w.grad x i = D i x * φ.grad x i + φ.toFun x * c i x := fun x => by
        simp [w, c]
      have hwf : w.toFun = fun x => D i x * φ.toFun x := by simp [w]
      rw [hwf] at h
      have h' : ∫ x in V, w.grad x i * ψ.toH1Function.toFun x =
          (∫ x in V, D i x * φ.grad x i * ψ.toH1Function.toFun x) +
            ∫ x in V, c i x * φ.toFun x * ψ.toH1Function.toFun x := by
        rw [← integral_add (I3 i) (I4 i)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hw]; ring
      rw [← h', h]
      simp
    have hG : ∫ x in V, vecDot (matVecMul (1 : Mat d) (φ'.toH1Function.grad x))
        (ψ.toH1Function.grad x) =
        (∑ i, ∫ x in V, χ x * φ.grad x i * ψ.toH1Function.grad x i) +
          ∑ i, ∫ x in V, D i x * φ.toFun x * ψ.toH1Function.grad x i := by
      rw [← Finset.sum_add_distrib]
      refine Eq.trans ?_ (Finset.sum_congr rfl fun i _ => (integral_add (I1 i) (I2 i)))
      refine Eq.trans ?_ (integral_finsetSum _ fun i _ => (I1 i).add (I2 i))
      refine integral_congr_ae ?_
      filter_upwards [hall] with x hx
      simp only [lip_localize_matVec_one, vecDot, hx]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hR : ∫ x in V, F' x * ψ.toH1Function.toFun x =
        (∫ x in V, χ x * F x * ψ.toH1Function.toFun x) -
          2 * (∑ i, ∫ x in V, D i x * φ.grad x i * ψ.toH1Function.toFun x) -
          ∑ i, ∫ x in V, c i x * φ.toFun x * ψ.toH1Function.toFun x := by
      have hf : (fun x => F' x * ψ.toH1Function.toFun x) = fun x =>
          χ x * F x * ψ.toH1Function.toFun x -
            2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x -
            ∑ i, c i x * φ.toFun x * ψ.toH1Function.toFun x := by
        funext x
        show (χ x * F x - 2 * ∑ i, D i x * φ.grad x i - ∑ i, c i x * φ.toFun x) *
          ψ.toH1Function.toFun x = _
        rw [sub_mul, sub_mul, mul_assoc 2, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      have hS3 : Integrable (fun x => ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x)
          (volume.restrict V) := integrable_finsetSum _ fun i _ => I3 i
      have hS4 : Integrable (fun x => ∑ i, c i x * φ.toFun x * ψ.toH1Function.toFun x)
          (volume.restrict V) := integrable_finsetSum _ fun i _ => I4 i
      have hS3' : Integrable (fun x => 2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x)
          (volume.restrict V) := hS3.const_mul 2
      have j1 : ∫ x in V, (χ x * F x * ψ.toH1Function.toFun x -
          2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x) =
          (∫ x in V, χ x * F x * ψ.toH1Function.toFun x) -
            ∫ x in V, 2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x :=
        integral_sub I5 hS3'
      have j2 : ∫ x in V, (χ x * F x * ψ.toH1Function.toFun x -
          2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x -
          ∑ i, c i x * φ.toFun x * ψ.toH1Function.toFun x) =
          (∫ x in V, (χ x * F x * ψ.toH1Function.toFun x -
            2 * ∑ i, D i x * φ.grad x i * ψ.toH1Function.toFun x)) -
            ∫ x in V, ∑ i, c i x * φ.toFun x * ψ.toH1Function.toFun x :=
        integral_sub (I5.sub hS3') hS4
      rw [hf, j2, j1, integral_const_mul,
        integral_finsetSum _ fun i _ => I3 i, integral_finsetSum _ fun i _ => I4 i]
    have hS : (∑ i, ∫ x in V, D i x * φ.toFun x * ψ.toH1Function.grad x i) =
        -((∑ i, ∫ x in V, D i x * φ.grad x i * ψ.toH1Function.toFun x) +
          ∑ i, ∫ x in V, c i x * φ.toFun x * ψ.toH1Function.toFun x) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => hP i
    simp only [lip_localize_vecDot_zero, integral_zero, add_zero]
    rw [hG, hR]
    linarith only [hT, hS]

/-- Witness: the hypotheses of `lip_localize` hold on the unit disc for the zero function and the
zero cutoff. -/
example : ∃ (φ' : H10Function (Metric.ball (0 : Vec 2) 1)) (F' : Vec 2 → ℝ),
    MemScalarL2 (Metric.ball (0 : Vec 2) 1) F' ∧
      (∀ x, φ'.toH1Function.toFun x = (0 : Vec 2 → ℝ) x *
        (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun x) ∧
      (∀ x, (∀ᶠ y in nhds x, (0 : Vec 2 → ℝ) y = 1) → F' x = (0 : Vec 2 → ℝ) x) ∧
      IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Metric.ball (0 : Vec 2) 1) φ'.toH1Function F'
        (fun _ => 0) := by
  refine lip_localize 2 (B := Set.univ) Metric.isOpen_ball
    (Homogenization.Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball) 0 0
    MemLp.zero ?_ (localizedZeroTraceFunctionOn_of_h10_any 0) 0 contDiff_const
    (HasCompactSupport.zero) (Set.subset_univ _)
  intro ψ
  simp [lip_localize_matVec_one, lip_localize_vecDot_zero]

end SuperdiffusionCLT.Section7
