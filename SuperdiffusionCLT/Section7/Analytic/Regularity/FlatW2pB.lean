/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.FlatW2p

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Flat `W^{2,p}`: one Neumann step

The weak Hessian of a function with a weak Hessian in `L̲^p`, perturbed by `(A - 1) ∇·`, and the
estimate of one step of the Neumann iteration: the response to the datum `(A - 1) ∇v` has a weak
Hessian in `L̲^p`, with a bound in terms of the Hessian and the gradient of `v`.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

/-- The Hessian of a weak-Hessian witness as a `HilbertMat`-valued field. -/
abbrev flatHessMat {U : Set (Vec d)} {u : H1Function U} (H : HasWeakHessianOn U u) :
    Vec d → HilbertMat d :=
  fun x => HilbertMat.ofMat (fun i j => H.hess i j x)

theorem flatW2p_toReal_le {C a b : ℝ≥0∞} (hC : C ≠ ⊤) (hb : b ≠ ⊤) (h : a ≤ C * b) :
    a.toReal ≤ C.toReal * b.toReal := by
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hb) h
  rwa [ENNReal.toReal_mul] at this

theorem flatW2p_aesm_jac (Q : TriadicCube d) {A : CoeffField d}
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) {g : Vec d → Vec d}
    {h : Fin d → Fin d → Vec d → ℝ} (hg : AEStronglyMeasurable g (normalizedCubeMeasure Q))
    (hh : ∀ i j, AEStronglyMeasurable (h i j) (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (jacobianHilbertMat (flatPertJac A g h)) (normalizedCubeMeasure Q) := by
  have hentry : ∀ i k, AEStronglyMeasurable (fun x => flatPertJac A g h i x k)
      (normalizedCubeMeasure Q) := by
    intro i k
    refine (Finset.univ : Finset (Fin d)).aestronglyMeasurable_fun_sum fun l _ => ?_
    have c1 : Continuous (fun x => A x i l - (1 : Mat d) i l) :=
      ((hA i l).continuous).sub continuous_const
    have c2 : Continuous (fun x => fderiv ℝ (fun y => A y i l) x (basisVec k)) :=
      ((hA i l).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have g1 : AEStronglyMeasurable (fun x => g x l) (normalizedCubeMeasure Q) :=
      (continuous_apply l).comp_aestronglyMeasurable hg
    exact (c1.aestronglyMeasurable.mul (hh l k)).add (g1.mul c2.aestronglyMeasurable)
  have hmat' : AEStronglyMeasurable
      (fun x => (fun i k => flatPertJac A g h i x k : Fin d → Fin d → ℝ))
      (normalizedCubeMeasure Q) :=
    AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i =>
      aemeasurable_pi_iff.2 fun k => (hentry i k).aemeasurable)
  have hmat : AEStronglyMeasurable (fun x => (fun i k => flatPertJac A g h i x k : Mat d))
      (normalizedCubeMeasure Q) := hmat'
  exact (HilbertMat.continuousLinearEquivMat d).symm.continuous.comp_aestronglyMeasurable hmat

theorem flatW2p_jac_memLp_norm_le [NeZero d] (Q : TriadicCube d) {A : CoeffField d} {ε K : ℝ}
    (hε0 : 0 ≤ ε) (hK0 : 0 ≤ K) (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (hAε : ∀ x ∈ openCubeSet Q, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    (hAK : ∀ x ∈ openCubeSet Q, ∀ i j k, |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K)
    {q : ℝ≥0∞} (hq : 1 ≤ q) {g : Vec d → Vec d} {h : Fin d → Fin d → Vec d → ℝ}
    (hg : MemLp g q (normalizedCubeMeasure Q))
    (hH : MemLp (fun x => HilbertMat.ofMat (fun i j => h i j x)) q (normalizedCubeMeasure Q)) :
    MemLp (jacobianHilbertMat (flatPertJac A g h)) q (normalizedCubeMeasure Q) ∧
      cubeLpNorm Q q (jacobianHilbertMat (flatPertJac A g h)) ≤
        (d : ℝ) ^ 3 * ε * cubeLpNorm Q q (fun x => HilbertMat.ofMat (fun i j => h i j x)) +
          (d : ℝ) ^ 3 * K * cubeLpNorm Q q g := by
  have hhm : ∀ i j, AEStronglyMeasurable (h i j) (normalizedCubeMeasure Q) := by
    intro i j
    have := (HilbertMat.entryL i j).continuous.comp_aestronglyMeasurable hH.aestronglyMeasurable
    simpa [Function.comp_def] using this
  have hJm := flatW2p_aesm_jac Q hA hg.aestronglyMeasurable hhm
  have hd0 : (0 : ℝ) ≤ (d : ℝ) ^ 3 := by positivity
  set c₁ : ℝ := (d : ℝ) ^ 3 * ε with hc₁
  set c₂ : ℝ := (d : ℝ) ^ 3 * K with hc₂
  have hc₁0 : 0 ≤ c₁ := by positivity
  have hc₂0 : 0 ≤ c₂ := by positivity
  set Φ₁ : Vec d → ℝ := fun x => c₁ * ‖HilbertMat.ofMat (fun i j => h i j x)‖ with hΦ₁def
  set Φ₂ : Vec d → ℝ := fun x => c₂ * ‖g x‖ with hΦ₂def
  have hΦ₁ : MemLp Φ₁ q (normalizedCubeMeasure Q) := hH.norm.const_mul c₁
  have hΦ₂ : MemLp Φ₂ q (normalizedCubeMeasure Q) := hg.norm.const_mul c₂
  have hbd : ∀ᵐ x ∂(normalizedCubeMeasure Q),
      ‖jacobianHilbertMat (flatPertJac A g h) x‖ ≤ ‖(Φ₁ + Φ₂) x‖ := by
    filter_upwards [ae_mem_openCubeSet Q] with x hx
    have := flatW2p_norm_jac_le (g := g) (h := h) (hAε x hx) (hAK x hx)
    have hnn : 0 ≤ (Φ₁ + Φ₂) x := by simp only [Pi.add_apply, hΦ₁def, hΦ₂def]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc _ ≤ _ := this
      _ = (Φ₁ + Φ₂) x := by simp only [Pi.add_apply, hΦ₁def, hΦ₂def, hc₁, hc₂]; ring
  have hmem := (hΦ₁.add hΦ₂).mono hJm hbd
  refine ⟨hmem, ?_⟩
  have h1 : eLpNorm (jacobianHilbertMat (flatPertJac A g h)) q (normalizedCubeMeasure Q) ≤
      eLpNorm Φ₁ q (normalizedCubeMeasure Q) + eLpNorm Φ₂ q (normalizedCubeMeasure Q) :=
    (eLpNorm_mono_ae hJm hbd).trans
      (eLpNorm_add_le hq)
  have e1 : eLpNorm Φ₁ q (normalizedCubeMeasure Q) = ENNReal.ofReal c₁ *
      eLpNorm (fun x => HilbertMat.ofMat (fun i j => h i j x)) q (normalizedCubeMeasure Q) := by
    have : Φ₁ = c₁ • fun x => ‖HilbertMat.ofMat (fun i j => h i j x)‖ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc₁0]
    congr 1
    exact eLpNorm_norm _ hH.aestronglyMeasurable
  have e2 : eLpNorm Φ₂ q (normalizedCubeMeasure Q) = ENNReal.ofReal c₂ *
      eLpNorm g q (normalizedCubeMeasure Q) := by
    have : Φ₂ = c₂ • fun x => ‖g x‖ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc₂0]
    congr 1
    exact eLpNorm_norm _ hg.aestronglyMeasurable
  rw [e1, e2] at h1
  have hfin : ENNReal.ofReal c₁ * eLpNorm (fun x => HilbertMat.ofMat (fun i j => h i j x)) q
        (normalizedCubeMeasure Q) + ENNReal.ofReal c₂ * eLpNorm g q (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_lt_top.ne,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_lt_top.ne⟩
  have h2 := ENNReal.toReal_mono hfin h1
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hH.eLpNorm_lt_top.ne)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_lt_top.ne), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁0, ENNReal.toReal_ofReal hc₂0] at h2
  exact h2

/-- The step estimate for the Neumann iteration (response to `(A - 1) ∇v`), with constants
depending only on `d` and `p`. -/
theorem flatW2p_step_exists [NeZero d] (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ Cg Ch : ℝ, 0 < Cg ∧ 0 < Ch ∧
      ∀ (m : ℤ) (A : CoeffField d) (ε K : ℝ), 0 ≤ ε → 0 ≤ K →
        (∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j)) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε) →
        (∀ x ∈ openCubeSet (originCube d m), ∀ i j k,
          |fderiv ℝ (fun y => A y i j) x (basisVec k)| ≤ K) →
        ∀ (v : H10Function (openCubeSet (originCube d m)))
          (Hv : HasWeakHessianOn (openCubeSet (originCube d m)) v.toH1Function),
          MemLp v.toH1Function.grad p (normalizedCubeMeasure (originCube d m)) →
          MemLp (flatHessMat Hv) p (normalizedCubeMeasure (originCube d m)) →
          ∃ (y : H10Function (openCubeSet (originCube d m)))
            (Hy : HasWeakHessianOn (openCubeSet (originCube d m)) y.toH1Function),
            CubeDirichletDivergenceProblem (originCube d m) y (pert A v.toH1Function.grad) ∧
            MemLp y.toH1Function.grad p (normalizedCubeMeasure (originCube d m)) ∧
            MemLp (flatHessMat Hy) p (normalizedCubeMeasure (originCube d m)) ∧
            cubeLpNorm (originCube d m) p y.toH1Function.grad ≤
              Cg * ((d : ℝ) * ε * cubeLpNorm (originCube d m) p v.toH1Function.grad) ∧
            cubeLpNorm (originCube d m) p (flatHessMat Hy) ≤
              Ch * ((d : ℝ) ^ 3 * ε * cubeLpNorm (originCube d m) p (flatHessMat Hv) +
                (d : ℝ) ^ 3 * K * cubeLpNorm (originCube d m) p v.toH1Function.grad) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
  obtain ⟨Cg, hCg0, hCg⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  obtain ⟨C, hCtop, hC⟩ := Sobolev.exists_cubeDirichletResponseHessianLpEstimate hd p hp1 hpt
  refine ⟨Cg, C.toReal + 1, hCg0, by positivity, ?_⟩
  intro m A ε K hε0 hK0 hA hAε hAK v Hv hvg hvH
  have : IsFiniteMeasure (normalizedCubeMeasure (originCube d m)) := inferInstance
  have hAm : ∀ i j, AEStronglyMeasurable (fun x => A x i j) (volume.restrict (openCubeSet (originCube d m))) :=
    fun i j => (hA i j).continuous.aestronglyMeasurable
  obtain ⟨hPp, hPn⟩ := memLp_pert_and_norm_le (originCube d m) hAm hε0 hAε hvg
  have hP2' : MemLp (pert A v.toH1Function.grad) 2 (normalizedCubeMeasure (originCube d m)) :=
    hPp.mono_exponent hp2
  obtain ⟨y, hy⟩ := exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure hP2'
  have hresp : Section3.ResponseFields.IsCubeDirichletResponse (originCube d m) (pert A v.toH1Function.grad) y :=
    hy
  have hgy := hCg (originCube d m) _ hPp y (isZeroTrace_one_iff.2 hy)
  have hJ := flatW2p_jac_memLp_norm_le (originCube d m) hε0 hK0 hA hAε hAK (le_trans (by norm_num) hp2)
    hvg hvH
  have hJ2 : MemLp (jacobianHilbertMat (flatPertJac A v.toH1Function.grad Hv.hess)) 2
      (normalizedCubeMeasure (originCube d m)) := hJ.1.mono_exponent hp2
  have hweak := flatW2p_hasWeakJacobian_pert (measurableSet_openCubeSet (originCube d m)) hA hAε hAK Hv
  obtain ⟨Hy, hHymem, hHybd⟩ := hC m (pert A v.toH1Function.grad)
    (flatPertJac A v.toH1Function.grad Hv.hess) hP2' hweak hJ2 hJ.1 y hresp
  refine ⟨y, Hy, hy, hgy.1, hHymem, ?_, ?_⟩
  · calc cubeLpNorm (originCube d m) p y.toH1Function.grad
        ≤ Cg * cubeLpNorm (originCube d m) p (pert A v.toH1Function.grad) := hgy.2
      _ ≤ Cg * ((d : ℝ) * ε * cubeLpNorm (originCube d m) p v.toH1Function.grad) :=
          mul_le_mul_of_nonneg_left hPn hCg0.le
  · have h1 := flatW2p_toReal_le hCtop.ne hJ.1.eLpNorm_lt_top.ne hHybd
    have h2 : cubeLpNorm (originCube d m) p (flatHessMat Hy) ≤
        C.toReal * cubeLpNorm (originCube d m) p (jacobianHilbertMat
          (flatPertJac A v.toH1Function.grad Hv.hess)) := h1
    have h3 := hJ.2
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    have hn : 0 ≤ cubeLpNorm (originCube d m) p (jacobianHilbertMat
          (flatPertJac A v.toH1Function.grad Hv.hess)) := ENNReal.toReal_nonneg
    calc cubeLpNorm (originCube d m) p (flatHessMat Hy)
        ≤ C.toReal * cubeLpNorm (originCube d m) p (jacobianHilbertMat
          (flatPertJac A v.toH1Function.grad Hv.hess)) := h2
      _ ≤ (C.toReal + 1) * cubeLpNorm (originCube d m) p (jacobianHilbertMat
          (flatPertJac A v.toH1Function.grad Hv.hess)) := by nlinarith only [hn]
      _ ≤ (C.toReal + 1) * ((d : ℝ) ^ 3 * ε * cubeLpNorm (originCube d m) p (flatHessMat Hv) +
            (d : ℝ) ^ 3 * K * cubeLpNorm (originCube d m) p v.toH1Function.grad) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The initial step of the Neumann iteration: the response to the datum `G`. -/
theorem flatW2p_init_exists [NeZero d] (hd : 2 ≤ d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ Cg Ch : ℝ, 0 < Cg ∧ 0 < Ch ∧
      ∀ (m : ℤ) (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
        MemLp G p (normalizedCubeMeasure (originCube d m)) →
        HasWeakJacobianOn (openCubeSet (originCube d m)) G DG →
        MemLp (jacobianHilbertMat DG) p (normalizedCubeMeasure (originCube d m)) →
          ∃ (y : H10Function (openCubeSet (originCube d m)))
            (Hy : HasWeakHessianOn (openCubeSet (originCube d m)) y.toH1Function),
            CubeDirichletDivergenceProblem (originCube d m) y G ∧
            MemLp y.toH1Function.grad p (normalizedCubeMeasure (originCube d m)) ∧
            MemLp (flatHessMat Hy) p (normalizedCubeMeasure (originCube d m)) ∧
            cubeLpNorm (originCube d m) p y.toH1Function.grad ≤
              Cg * cubeLpNorm (originCube d m) p G ∧
            cubeLpNorm (originCube d m) p (flatHessMat Hy) ≤
              Ch * cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) := by
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
  obtain ⟨Cg, hCg0, hCg⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  obtain ⟨C, hCtop, hC⟩ := Sobolev.exists_cubeDirichletResponseHessianLpEstimate hd p hp1 hpt
  refine ⟨Cg, C.toReal + 1, hCg0, by positivity, ?_⟩
  intro m G DG hGp hweak hJp
  have : IsFiniteMeasure (normalizedCubeMeasure (originCube d m)) := inferInstance
  have hG2 : MemLp G 2 (normalizedCubeMeasure (originCube d m)) := hGp.mono_exponent hp2
  have hJ2 : MemLp (jacobianHilbertMat DG) 2 (normalizedCubeMeasure (originCube d m)) := hJp.mono_exponent hp2
  obtain ⟨y, hy⟩ := exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure hG2
  have hresp : Section3.ResponseFields.IsCubeDirichletResponse (originCube d m) G y := hy
  have hgy := hCg (originCube d m) _ hGp y (isZeroTrace_one_iff.2 hy)
  obtain ⟨Hy, hHymem, hHybd⟩ := hC m G DG hG2 hweak hJ2 hJp y hresp
  refine ⟨y, Hy, hy, hgy.1, hHymem, hgy.2, ?_⟩
  have h1 := flatW2p_toReal_le hCtop.ne hJp.eLpNorm_lt_top.ne hHybd
  have h2 : cubeLpNorm (originCube d m) p (flatHessMat Hy) ≤
      C.toReal * cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) := h1
  have hn : 0 ≤ cubeLpNorm (originCube d m) p (jacobianHilbertMat DG) := ENNReal.toReal_nonneg
  have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  nlinarith only [h2, hn, hC0]

end SuperdiffusionCLT.Section7
