/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pC

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Half cube: the base step

The zero-trace response on the half cube to a flux with a weak Jacobian in `L̲^p` has a weak Hessian
in `L̲^p` up to the flat face (`hc_base_div`).  The Hessian estimate uses only the scalar divergence
of the flux, so the jump of the tangential flux components across the flat face is harmless.  The
gradient estimate holds for fluxes in `L̲^p` with no Jacobian (`hc_grad_estimate`).  The remaining
lemmas port the perturbation bookkeeping of the cube to the half cube.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem hc_exists_div [NeZero d] (e : Fin d) (m : ℤ) {G : Vec d → Vec d}
    (hG2 : MemLp G 2 (volume.restrict (flatHalfCube e m))) :
    ∃ y : H10Function (flatHalfCube e m), HalfDivProblem e m y G := by
  obtain ⟨y, hy⟩ := exists_h10_weak_solution (a := fun _ => (1 : Mat d)) (f := fun _ => (0 : ℝ))
    (g := fun x => -G x) (isOpen_flatHalfCube e m) (isBoundedDomain_flatHalfCube e m)
    (flatHalfCube_nonempty e m)
    (Section5.isEllipticFieldOn_one (measurableSet_flatHalfCube e m)) MemLp.zero hG2.neg
  refine ⟨y, fun φ => ?_⟩
  have := hy φ
  simpa [matVecMul_one_left, vecDot_neg_left, integral_neg] using this


theorem hc_toReal_le {C a b : ℝ≥0∞} (hb : b ≠ ⊤) (h : a ≤ C * b) (hC : C ≠ ⊤) :
    a.toReal ≤ C.toReal * b.toReal := by
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hb) h
  rwa [ENNReal.toReal_mul] at this

/-- The base step on the half cube: the zero-trace response to a flux `G` with a weak Jacobian in
`L̲^p`, built by odd reflection to the whole cube. -/
theorem hc_base_div (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ Cg Ch : ℝ, 0 < Cg ∧ 0 < Ch ∧
      ∀ (m : ℤ) (G : Vec d → Vec d) (DG : Fin d → Vec d → Vec d),
        MemLp G p (flatHalfMeasure e m) →
        HasWeakJacobianOn (flatHalfCube e m) G DG →
        MemLp (jacobianHilbertMat DG) p (flatHalfMeasure e m) →
        ∃ (y : H10Function (flatHalfCube e m))
          (Hy : HasWeakHessianOn (flatHalfCube e m) y.toH1Function),
          HalfDivProblem e m y G ∧
          MemLp y.toH1Function.grad p (flatHalfMeasure e m) ∧
          MemLp (flatHessMat Hy) p (flatHalfMeasure e m) ∧
          flatHalfNorm e m p y.toH1Function.grad ≤ Cg * flatHalfNorm e m p G ∧
          flatHalfNorm e m p (flatHessMat Hy) ≤
            Ch * flatHalfNorm e m p (jacobianHilbertMat DG) := by
  have : NeZero d := ⟨by omega⟩
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1.le).ne'
  have hpt' : p ≠ ⊤ := hpt.ne
  obtain ⟨Cg, hCg0, hCg⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  obtain ⟨Ch, hChtop, hCh⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d
      (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  refine ⟨2 * Cg, 2 * d * Ch.toReal + 1, by positivity, by positivity, ?_⟩
  intro m G DG hGp hweak hJp
  have hG2 : MemLp G 2 (flatHalfMeasure e m) := hGp.mono_exponent hp2
  have hJ2 : MemLp (jacobianHilbertMat DG) 2 (flatHalfMeasure e m) := hJp.mono_exponent hp2
  have hG2v : MemLp G 2 (volume.restrict (flatHalfCube e m)) :=
    (memLp_flatHalfMeasure_iff e m).1 hG2
  have hJ2v : MemLp (jacobianHilbertMat DG) 2 (volume.restrict (flatHalfCube e m)) :=
    (memLp_flatHalfMeasure_iff e m).1 hJ2
  have hGcomp : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict (flatHalfCube e m)) :=
    hc_memLp_comp hG2v
  have hDGcomp : ∀ i, GradMemL2On (flatHalfCube e m) (DG i) := fun i j =>
    hc_memLp_entry hJ2v i j
  obtain ⟨y, hy⟩ := hc_exists_div e m hG2v
  have hf2 : MemLp (weakDivergence DG) 2 (volume.restrict (flatHalfCube e m)) :=
    memLp_weakDivergence hJ2v
  have hscal : ∀ φ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (y.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, weakDivergence DG x * φ.toH1Function.toFun x := by
    intro φ
    rw [hy φ, setIntegral_vecDot_zeroTrace_grad_eq_neg hGcomp hDGcomp hweak φ, neg_neg]
  have F2 := hc_extend_div e m hGcomp hy
  have F3 := hc_extend_poisson e m hf2 hscal
  have hGt : MemLp (hcExtVec e G) p (normalizedCubeMeasure (originCube d m)) :=
    memLp_hcExtVec_normalized e m hp0 hpt' hGp
  obtain ⟨hgm, hgb⟩ := hCg (originCube d m) (hcExtVec e G) hGt (hcOddH10 y)
    (isZeroTrace_one_iff.2 F2)
  have hfp : MemLp (weakDivergence DG) p (flatHalfMeasure e m) := memLp_weakDivergence hJp
  have hFt : MemLp (hcExt (-1) e (weakDivergence DG)) p (normalizedCubeMeasure (originCube d m)) :=
    memLp_hcExt_normalized e m (by simp) hp0 hpt' hfp
  have hFt2 : MemLp (hcExt (-1) e (weakDivergence DG)) 2 (normalizedCubeMeasure (originCube d m)) :=
    hFt.mono_exponent hp2
  obtain ⟨Hψ, hHm, hHb⟩ := hCh m _ hFt2 hFt (hcOddH10 y) F3
  have hyg : eLpNorm y.toH1Function.grad p (flatHalfMeasure e m) =
      eLpNorm (hcOddH10 y).toH1Function.grad p (flatHalfMeasure e m) :=
    eLpNorm_flatHalf_congr e m (fun x hx => by
      funext i
      show y.toH1Function.grad x i = hcExtVec e y.toH1Function.grad x i
      simp only [hcExtVec, hcExt_of_pos hx.2]) p
  have hhess : flatHessMat (hcRestrictHessian e m y Hψ) = flatHessMat Hψ := rfl
  have hgm' : MemLp y.toH1Function.grad p (flatHalfMeasure e m) := by
    rw [memLp_iff, hyg]
    exact lt_of_le_of_lt (eLpNorm_flatHalf_le_cube e m _ p) hgm.eLpNorm_lt_top
  have hHm' : MemLp (flatHessMat (hcRestrictHessian e m y Hψ)) p (flatHalfMeasure e m) := by
    rw [memLp_iff, hhess]
    exact lt_of_le_of_lt (eLpNorm_flatHalf_le_cube e m _ p) hHm.eLpNorm_lt_top
  refine ⟨y, hcRestrictHessian e m y Hψ, hy, hgm', hHm', ?_, ?_⟩
  · have h1 : flatHalfNorm e m p y.toH1Function.grad ≤
        cubeLpNorm (originCube d m) p (hcOddH10 y).toH1Function.grad := by
      unfold flatHalfNorm cubeLpNorm
      rw [hyg]
      exact ENNReal.toReal_mono hgm.eLpNorm_lt_top.ne (eLpNorm_flatHalf_le_cube e m _ p)
    have h2 : cubeLpNorm (originCube d m) p (hcExtVec e G) ≤ 2 * flatHalfNorm e m p G := by
      unfold cubeLpNorm flatHalfNorm
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hGp.eLpNorm_lt_top.ne)
        (eLpNorm_hcExtVec_le e m hGp.aestronglyMeasurable hp1.le hpt')
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
    have hn : 0 ≤ cubeLpNorm (originCube d m) p (hcExtVec e G) := ENNReal.toReal_nonneg
    calc flatHalfNorm e m p y.toH1Function.grad ≤ Cg * cubeLpNorm (originCube d m) p (hcExtVec e G) :=
          h1.trans hgb
      _ ≤ Cg * (2 * flatHalfNorm e m p G) := mul_le_mul_of_nonneg_left h2 hCg0.le
      _ = 2 * Cg * flatHalfNorm e m p G := by ring
  · have h1 : flatHalfNorm e m p (flatHessMat (hcRestrictHessian e m y Hψ)) ≤
        cubeLpNorm (originCube d m) p (flatHessMat Hψ) := by
      unfold flatHalfNorm cubeLpNorm
      rw [hhess]
      exact ENNReal.toReal_mono hHm.eLpNorm_lt_top.ne (eLpNorm_flatHalf_le_cube e m _ p)
    have h2 : cubeLpNorm (originCube d m) p (flatHessMat Hψ) ≤
        Ch.toReal * cubeLpNorm (originCube d m) p (hcExt (-1) e (weakDivergence DG)) :=
      hc_toReal_le hFt.eLpNorm_lt_top.ne hHb hChtop.ne
    have h3 : cubeLpNorm (originCube d m) p (hcExt (-1) e (weakDivergence DG)) ≤
        2 * flatHalfNorm e m p (weakDivergence DG) := by
      unfold cubeLpNorm flatHalfNorm
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfp.eLpNorm_lt_top.ne)
        (eLpNorm_hcExt_le e m (σ := -1) (by simp) hfp.aestronglyMeasurable hp1.le hpt')
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
    have h4 : flatHalfNorm e m p (weakDivergence DG) ≤
        d * flatHalfNorm e m p (jacobianHilbertMat DG) := by
      unfold flatHalfNorm
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) hJp.eLpNorm_lt_top.ne)
        (hc_eLpNorm_weakDivergence_le hJp)
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
    have hC : 0 ≤ Ch.toReal := ENNReal.toReal_nonneg
    have hJn : 0 ≤ flatHalfNorm e m p (jacobianHilbertMat DG) := ENNReal.toReal_nonneg
    calc flatHalfNorm e m p (flatHessMat (hcRestrictHessian e m y Hψ))
        ≤ Ch.toReal * (2 * (d * flatHalfNorm e m p (jacobianHilbertMat DG))) :=
          h1.trans (h2.trans (mul_le_mul_of_nonneg_left (h3.trans
            (mul_le_mul_of_nonneg_left h4 (by norm_num))) hC))
      _ = (2 * d * Ch.toReal) * flatHalfNorm e m p (jacobianHilbertMat DG) := by ring
      _ ≤ (2 * d * Ch.toReal + 1) * flatHalfNorm e m p (jacobianHilbertMat DG) := by
          nlinarith only [hJn]

theorem hc_gradL2 (e : Fin d) (m : ℤ) (w : H10Function (flatHalfCube e m)) :
    MemLp w.toH1Function.grad 2 (flatHalfMeasure e m) :=
  (memLp_flatHalfMeasure_iff e m).2 w.toH1Function.grad_memVectorL2

theorem hc_integrable_vecDot_mu (e : Fin d) (m : ℤ) {F G : Vec d → Vec d}
    (hF : MemLp F 2 (flatHalfMeasure e m)) (hG : MemLp G 2 (flatHalfMeasure e m)) :
    Integrable (fun x => vecDot (F x) (G x)) (volume.restrict (flatHalfCube e m)) :=
  integrableOn_vecDot_of_memVectorL2 ((memLp_flatHalfMeasure_iff e m).1 hF)
    ((memLp_flatHalfMeasure_iff e m).1 hG)

/-- The gradient estimate on the half cube, by odd reflection. -/
theorem hc_grad_estimate (hd : 2 ≤ d) (e : Fin d) {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hpt : p < ⊤) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ (m : ℤ) (h : Vec d → Vec d), MemLp h p (flatHalfMeasure e m) →
      ∀ y : H10Function (flatHalfCube e m), HalfDivProblem e m y h →
        MemLp y.toH1Function.grad p (flatHalfMeasure e m) ∧
          flatHalfNorm e m p y.toH1Function.grad ≤ Cg * flatHalfNorm e m p h := by
  have : NeZero d := ⟨by omega⟩
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp2
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1.le).ne'
  have hpt' : p ≠ ⊤ := hpt.ne
  obtain ⟨Cg, hCg0, hCg⟩ := CubeCalderonZygmund.exists_cubeDirichletDivergence_cz d
    (⟨p, hp1, hpt⟩ : FiniteLpExponent)
  refine ⟨2 * Cg, by positivity, ?_⟩
  intro m h hhp y hy
  have hh2v : MemLp h 2 (volume.restrict (flatHalfCube e m)) :=
    (memLp_flatHalfMeasure_iff e m).1 (hhp.mono_exponent hp2)
  have F2 := hc_extend_div e m (hc_memLp_comp hh2v) hy
  have hGt : MemLp (hcExtVec e h) p (normalizedCubeMeasure (originCube d m)) :=
    memLp_hcExtVec_normalized e m hp0 hpt' hhp
  obtain ⟨hgm, hgb⟩ := hCg (originCube d m) (hcExtVec e h) hGt (hcOddH10 y)
    (isZeroTrace_one_iff.2 F2)
  have hyg : eLpNorm y.toH1Function.grad p (flatHalfMeasure e m) =
      eLpNorm (hcOddH10 y).toH1Function.grad p (flatHalfMeasure e m) :=
    eLpNorm_flatHalf_congr e m (fun x hx => by
      funext i
      show y.toH1Function.grad x i = hcExtVec e y.toH1Function.grad x i
      simp only [hcExtVec, hcExt_of_pos hx.2]) p
  refine ⟨?_, ?_⟩
  · rw [memLp_iff, hyg]
    exact lt_of_le_of_lt (eLpNorm_flatHalf_le_cube e m _ p) hgm.eLpNorm_lt_top
  · have h1 : flatHalfNorm e m p y.toH1Function.grad ≤
        cubeLpNorm (originCube d m) p (hcOddH10 y).toH1Function.grad := by
      unfold flatHalfNorm cubeLpNorm
      rw [hyg]
      exact ENNReal.toReal_mono hgm.eLpNorm_lt_top.ne (eLpNorm_flatHalf_le_cube e m _ p)
    have h2 : cubeLpNorm (originCube d m) p (hcExtVec e h) ≤ 2 * flatHalfNorm e m p h := by
      unfold cubeLpNorm flatHalfNorm
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hhp.eLpNorm_lt_top.ne)
        (eLpNorm_hcExtVec_le e m hhp.aestronglyMeasurable hp1.le hpt')
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofNat] at this
    calc flatHalfNorm e m p y.toH1Function.grad ≤ Cg * cubeLpNorm (originCube d m) p (hcExtVec e h) :=
          h1.trans hgb
      _ ≤ Cg * (2 * flatHalfNorm e m p h) := mul_le_mul_of_nonneg_left h2 hCg0.le
      _ = 2 * Cg * flatHalfNorm e m p h := by ring

theorem hc_aesm_pert {μ : Measure (Vec d)} {A : CoeffField d}
    (hA : ∀ i j, Continuous (fun x => A x i j)) {F : Vec d → Vec d}
    (hF : AEStronglyMeasurable F μ) : AEStronglyMeasurable (pert A F) μ := by
  refine AEMeasurable.aestronglyMeasurable (aemeasurable_pi_iff.2 fun i => ?_)
  simp only [pert, matVecMul]
  refine (Finset.univ.aestronglyMeasurable_fun_sum fun j _ => ?_).aemeasurable
  refine AEStronglyMeasurable.mul ?_ ?_
  · have h2 : AEStronglyMeasurable (fun x => A x i j - (1 : Mat d) i j) μ :=
      (hA i j).aestronglyMeasurable.sub aestronglyMeasurable_const
    simpa only [Matrix.sub_apply] using h2
  · exact (continuous_apply j).comp_aestronglyMeasurable hF

theorem hc_ae_mem (e : Fin d) (m : ℤ) : ∀ᵐ x ∂(flatHalfMeasure e m), x ∈ flatHalfCube e m :=
  ae_restrict_mem (measurableSet_flatHalfCube e m)

theorem hc_memLp_pert_and_norm_le [NeZero d] (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hA : ∀ i j, Continuous (fun x => A x i j)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {q : ℝ≥0∞} {F : Vec d → Vec d} (hF : MemLp F q (flatHalfMeasure e m)) :
    MemLp (pert A F) q (flatHalfMeasure e m) ∧
      flatHalfNorm e m q (pert A F) ≤ d * ε * flatHalfNorm e m q F := by
  have hnorm : ∀ᵐ x ∂(flatHalfMeasure e m),
      ‖pert A F x‖ ≤ ‖((d : ℝ) * ε) • F x‖ := by
    filter_upwards [hc_ae_mem e m] with x hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_matVecMul_sub_one_le (hε x hx) (F x)
  have hm := hc_aesm_pert hA hF.aestronglyMeasurable
  have hmem : MemLp (pert A F) q (flatHalfMeasure e m) :=
    (hF.const_smul ((d : ℝ) * ε)).mono hm hnorm
  refine ⟨hmem, ?_⟩
  have h0 : 0 ≤ (d : ℝ) * ε := by positivity
  rw [flatHalfNorm, flatHalfNorm, ← smul_eq_mul]
  have h1 : eLpNorm (pert A F) q (flatHalfMeasure e m) ≤
      ENNReal.ofReal ((d : ℝ) * ε) * eLpNorm F q (flatHalfMeasure e m) := by
    calc eLpNorm (pert A F) q (flatHalfMeasure e m)
        ≤ eLpNorm (((d : ℝ) * ε) • F) q (flatHalfMeasure e m) := eLpNorm_mono_ae hm hnorm
      _ = _ := by
        rw [eLpNorm_const_smul, Real.enorm_eq_ofReal h0]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF.eLpNorm_lt_top.ne) h1
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal h0] at h2

theorem hc_grad_sub {U : Set (Vec d)} (u v : H10Function U) :
    (u - v).toH1Function.grad = fun x => u.toH1Function.grad x - v.toH1Function.grad x := by
  change (u.toH1Function - v.toH1Function).grad = _
  rw [H1Function.sub_grad]

theorem hc_problem_add {e : Fin d} {m : ℤ} {w₁ w₂ : H10Function (flatHalfCube e m)}
    {h₁ h₂ : Vec d → Vec d} (h₁2 : MemLp h₁ 2 (flatHalfMeasure e m))
    (h₂2 : MemLp h₂ 2 (flatHalfMeasure e m))
    (H₁ : HalfDivProblem e m w₁ h₁) (H₂ : HalfDivProblem e m w₂ h₂) :
    HalfDivProblem e m (w₁ + w₂) (fun x => h₁ x + h₂ x) := by
  intro φ
  have hφ := hc_gradL2 e m φ
  have a1 := H₁ φ
  have a2 := H₂ φ
  have hg : (w₁ + w₂).toH1Function.grad =
      fun x => w₁.toH1Function.grad x + w₂.toH1Function.grad x := rfl
  rw [hg]
  simp only [vecDot_add_left]
  rw [integral_add (hc_integrable_vecDot_mu e m (hc_gradL2 e m w₁) hφ)
      (hc_integrable_vecDot_mu e m (hc_gradL2 e m w₂) hφ),
    integral_add (hc_integrable_vecDot_mu e m h₁2 hφ) (hc_integrable_vecDot_mu e m h₂2 hφ)]
  linarith only [a1, a2]

theorem hc_problem_sub {e : Fin d} {m : ℤ} {w₁ w₂ : H10Function (flatHalfCube e m)}
    {h₁ h₂ : Vec d → Vec d} (h₁2 : MemLp h₁ 2 (flatHalfMeasure e m))
    (h₂2 : MemLp h₂ 2 (flatHalfMeasure e m))
    (H₁ : HalfDivProblem e m w₁ h₁) (H₂ : HalfDivProblem e m w₂ h₂) :
    HalfDivProblem e m (w₁ - w₂) (fun x => h₁ x - h₂ x) := by
  intro φ
  have hφ := hc_gradL2 e m φ
  have a1 := H₁ φ
  have a2 := H₂ φ
  rw [hc_grad_sub]
  simp only [vecDot_sub_left']
  rw [integral_sub (hc_integrable_vecDot_mu e m (hc_gradL2 e m w₁) hφ)
      (hc_integrable_vecDot_mu e m (hc_gradL2 e m w₂) hφ),
    integral_sub (hc_integrable_vecDot_mu e m h₁2 hφ) (hc_integrable_vecDot_mu e m h₂2 hφ)]
  linarith only [a1, a2]

theorem hc_problem_of_A [NeZero d] (e : Fin d) (m : ℤ) {A : CoeffField d}
    (hA : ∀ i j, Continuous (fun x => A x i j)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ x ∈ flatHalfCube e m, ∀ i j, |A x i j - (1 : Mat d) i j| ≤ ε)
    {G : Vec d → Vec d} (hG2 : MemLp G 2 (flatHalfMeasure e m))
    {w : H10Function (flatHalfCube e m)}
    (hw : IsZeroTraceDirichletRhsWeakSolution A (flatHalfCube e m) w (fun x => -G x)) :
    HalfDivProblem e m w (fun x => G x + pert A w.toH1Function.grad x) := by
  intro φ
  have hφ := hc_gradL2 e m φ
  have hP := (hc_memLp_pert_and_norm_le e m hA hε0 hε (hc_gradL2 e m w)).1
  have eq : ∀ x, vecDot (matVecMul (A x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) =
      vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) +
        vecDot (pert A w.toH1Function.grad x) (φ.toH1Function.grad x) := by
    intro x
    rw [matVecMul_eq_add_pert (A x), vecDot_add_left]
    rfl
  have h := hw φ
  simp only [eq, vecDot_neg_left] at h
  rw [integral_add (hc_integrable_vecDot_mu e m (hc_gradL2 e m w) hφ)
    (hc_integrable_vecDot_mu e m hP hφ), integral_neg] at h
  simp only [vecDot_add_left]
  rw [integral_add (hc_integrable_vecDot_mu e m hG2 hφ) (hc_integrable_vecDot_mu e m hP hφ)]
  linarith only [h]

end SuperdiffusionCLT.Section7
