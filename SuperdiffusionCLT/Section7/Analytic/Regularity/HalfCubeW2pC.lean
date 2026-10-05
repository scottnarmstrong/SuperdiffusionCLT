/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Regularity.HalfCubeW2pB

@[expose] public section

open Homogenization MeasureTheory Filter Topology
open scoped ENNReal

/-!
# Half cube: the reflected problem

If `y ∈ H¹₀(D)` solves a weak problem on the half cube, its odd extension solves the reflected
problem on the cube, with the flux datum extended by the parity `hcExtVec` and the scalar datum
extended oddly (`hc_reflected_identity`, `hc_extend_div`, `hc_extend_poisson`).  The weak Hessian of
the extension restricts to the half cube.
-/

namespace SuperdiffusionCLT.Section7

open SuperdiffusionCLT.Sobolev

variable {d : ℕ}

theorem hc_tendsto_integral_vecDot {U : Set (Vec d)} {A : Vec d → Vec d}
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict U)) (φ : H10Function U) :
    Tendsto (fun n => ∫ x in U, vecDot (A x) (hcGrad (φ.approx n) x)) atTop
      (𝓝 (∫ x in U, vecDot (A x) (φ.toH1Function.grad x))) := by
  have hi : ∀ i, Tendsto (fun n => ∫ x in U, hcGrad (φ.approx n) x i * A x i) atTop
      (𝓝 (∫ x in U, φ.toH1Function.grad x i * A x i)) := fun i =>
    tendsto_setIntegral_mul_of_tendsto_eLpNorm_two (hA i)
      (fun n => memLp_hcGrad_apply (φ.approx_smooth n) (φ.approx_hasCompactSupport n) U i)
      (φ.toH1Function.gradMemL2 i) (φ.tendsto_approx_grad i)
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ => hi i
  have e1 : ∀ n, (∫ x in U, vecDot (A x) (hcGrad (φ.approx n) x)) =
      ∑ i, ∫ x in U, hcGrad (φ.approx n) x i * A x i := by
    intro n
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [vecDot]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro i _
      exact (memLp_hcGrad_apply (φ.approx_smooth n) (φ.approx_hasCompactSupport n) U i).integrable_mul
        (hA i)
  have e2 : (∫ x in U, vecDot (A x) (φ.toH1Function.grad x)) =
      ∑ i, ∫ x in U, φ.toH1Function.grad x i * A x i := by
    rw [← integral_finsetSum]
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [vecDot]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · intro i _
      exact ((φ.toH1Function.gradMemL2 i).integrable_mul (hA i))
  simp_rw [e1, e2]
  exact hsum

theorem hc_tendsto_integral_mul {U : Set (Vec d)} {a : Vec d → ℝ}
    (ha : MemLp a 2 (volume.restrict U)) (φ : H10Function U) :
    Tendsto (fun n => ∫ x in U, a x * φ.approx n x) atTop
      (𝓝 (∫ x in U, a x * φ.toH1Function.toFun x)) := by
  have := tendsto_setIntegral_mul_of_tendsto_eLpNorm_two ha
    (fun n => flatW2p_memLp_two_of_continuous (φ.approx_smooth n).continuous
      (φ.approx_hasCompactSupport n)) φ.toH1Function.memL2 φ.tendsto_approx
  simpa only [mul_comm] using this


theorem tsupport_hcOddApprox_subset_cube {e : Fin d} {m : ℤ} {φ : Vec d → ℝ}
    (hs : tsupport φ ⊆ openCubeSet (originCube d m)) :
    tsupport (hcOddApprox e φ) ⊆ openCubeSet (originCube d m) := by
  have h1 : tsupport (fun x => φ (hcFlip e x)) ⊆ openCubeSet (originCube d m) := by
    intro x hx
    have := tsupport_comp_hcFlip_subset e φ hx
    exact (hcFlip_mem_openCubeSet_iff e m x).1 (hs this)
  refine (tsupport_sub _ _).trans (Set.union_subset hs ?_)
  simpa [tsupport_neg] using h1

theorem hcGrad_hcOddApprox {e : Fin d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d)
    (i : Fin d) :
    hcGrad (hcOddApprox e φ) x i = hcGrad φ x i - hcGrad (fun y => φ (hcFlip e y)) x i := by
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fun y => φ (hcFlip e y)) :=
    (hc_contDiff_comp_hcFlip hφ e).differentiable (by norm_num)
  unfold hcGrad hcOddApprox
  rw [fderiv_fun_sub (hd1 x) (hd2 x)]
  rfl

theorem hcGrad_comp_hcFlip {e : Fin d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Vec d)
    (i : Fin d) :
    hcGrad (fun y => φ (hcFlip e y)) x i = -hcSgn e i * hcGrad φ (hcFlip e x) i :=
  fderiv_comp_hcFlip (hφ.differentiable (by norm_num)) e x i

theorem hc_vecDot_flip {e : Fin d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (K : Vec d → Vec d) {x : Vec d} (hx : 0 < x e) :
    vecDot (hcExtVec e K (hcFlip e x)) (hcGrad φ (hcFlip e x)) =
      -vecDot (K x) (hcGrad (fun y => φ (hcFlip e y)) x) := by
  unfold vecDot
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcGrad_comp_hcFlip hφ x i]
  unfold hcExtVec
  rw [hcExt_comp_flip hx]
  ring


theorem hc_reflected_smooth (e : Fin d) (m : ℤ) {K : Vec d → Vec d} {f : Vec d → ℝ}
    (hK : ∀ i, MemLp (fun x => K x i) 2 (volume.restrict (flatHalfCube e m)))
    (hf : MemLp f 2 (volume.restrict (flatHalfCube e m)))
    (hid : ∀ χ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (K x) (χ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, f x * χ.toH1Function.toFun x)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ openCubeSet (originCube d m)) :
    (∫ x in openCubeSet (originCube d m), vecDot (hcExtVec e K x) (hcGrad φ x)) =
      ∫ x in openCubeSet (originCube d m), hcExt (-1) e f x * φ x := by
  set D := flatHalfCube e m with hD
  have hφf : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (hcFlip e y)) := hc_contDiff_comp_hcFlip hφ e
  have hφfc : HasCompactSupport (fun y => φ (hcFlip e y)) := hc_hasCompactSupport_comp_hcFlip hc e
  have hψ := hφ.sub hφf
  have hψc := hc.sub hφfc
  -- vector side
  have hAQ : ∀ i, MemLp (fun x => hcExtVec e K x i) 2
      (volume.restrict (openCubeSet (originCube d m))) := fun i =>
    memLp_hcExt_volume e m (hcSgn_abs e i) (hK i)
  have hint : Integrable (fun x => vecDot (hcExtVec e K x) (hcGrad φ x))
      (volume.restrict (openCubeSet (originCube d m))) := by
    unfold vecDot
    exact integrable_finsetSum _ fun i _ =>
      (hAQ i).integrable_mul (memLp_hcGrad_apply hφ hc _ i)
  rw [hc_integral_openCubeSet_split e m hint]
  have hI1 : Integrable (fun x => vecDot (K x) (hcGrad φ x)) (volume.restrict D) :=
    hc_integrable_vecDot_grad hK hφ hc
  have hI2 : Integrable (fun x => vecDot (K x) (hcGrad (fun y => φ (hcFlip e y)) x))
      (volume.restrict D) := hc_integrable_vecDot_grad hK hφf hφfc
  have e1 : (∫ x in D, vecDot (hcExtVec e K x) (hcGrad φ x)) =
      ∫ x in D, vecDot (K x) (hcGrad φ x) := by
    refine setIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx => ?_
    simp only [vecDot, hcExtVec, hcExt_of_pos hx.2]
  have e2 : (∫ x in D, vecDot (hcExtVec e K (hcFlip e x)) (hcGrad φ (hcFlip e x))) =
      -∫ x in D, vecDot (K x) (hcGrad (fun y => φ (hcFlip e y)) x) := by
    rw [← integral_neg]
    exact setIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx =>
      hc_vecDot_flip hφ K hx.2
  rw [e1, e2]
  have hvec : (∫ x in D, vecDot (K x) (hcGrad φ x)) +
      -(∫ x in D, vecDot (K x) (hcGrad (fun y => φ (hcFlip e y)) x)) =
      ∫ x in D, vecDot (K x) (hcGrad (hcOddApprox e φ) x) := by
    rw [← sub_eq_add_neg, ← integral_sub hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot, hcGrad_hcOddApprox hφ, mul_sub, Finset.sum_sub_distrib]
  rw [hvec]
  -- scalar side
  have hfQ : MemLp (hcExt (-1) e f) 2 (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_hcExt_volume e m (by simp) hf
  have hφ2 : MemLp φ 2 (volume.restrict (openCubeSet (originCube d m))) :=
    flatW2p_memLp_two_of_continuous hφ.continuous hc
  have hint2 : Integrable (fun x => hcExt (-1) e f x * φ x)
      (volume.restrict (openCubeSet (originCube d m))) := hfQ.integrable_mul hφ2
  rw [hc_integral_openCubeSet_split e m hint2]
  have hJ1 : Integrable (fun x => f x * φ x) (volume.restrict D) :=
    hf.integrable_mul (flatW2p_memLp_two_of_continuous hφ.continuous hc)
  have hJ2 : Integrable (fun x => f x * φ (hcFlip e x)) (volume.restrict D) :=
    hf.integrable_mul (flatW2p_memLp_two_of_continuous hφf.continuous hφfc)
  have f1 : (∫ x in D, hcExt (-1) e f x * φ x) = ∫ x in D, f x * φ x := by
    refine setIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx => ?_
    simp only [hcExt_of_pos hx.2]
  have f2 : (∫ x in D, hcExt (-1) e f (hcFlip e x) * φ (hcFlip e x)) =
      -∫ x in D, f x * φ (hcFlip e x) := by
    rw [← integral_neg]
    refine setIntegral_congr_fun (measurableSet_flatHalfCube e m) fun x hx => ?_
    simp only [hcExt_comp_flip hx.2]
    ring
  rw [f1, f2, ← sub_eq_add_neg, ← integral_sub hJ1 hJ2]
  have hψ0 : ∀ x : Vec d, x e = 0 → hcOddApprox e φ x = 0 := fun x hx => by
    simp [hcOddApprox, hcFlip_zero_of_mem hx]
  have := hc_tail_identity e m hK hf hid (ψ := hcOddApprox e φ) hψ hψc
    (tsupport_hcOddApprox_subset_cube hs) hψ0
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hcOddApprox]
  ring


/-- **The reflected identity.** If `∫_D K·∇χ = ∫_D f χ` for all `χ ∈ H¹₀(D)`, then with the
parities `hcExtVec` for the vector field and `hcExt (-1)` (odd) for the scalar, the same identity
holds on the whole cube against all `H¹₀(cube)` test functions. -/
theorem hc_reflected_identity (e : Fin d) (m : ℤ) {K : Vec d → Vec d} {f : Vec d → ℝ}
    (hK : ∀ i, MemLp (fun x => K x i) 2 (volume.restrict (flatHalfCube e m)))
    (hf : MemLp f 2 (volume.restrict (flatHalfCube e m)))
    (hid : ∀ χ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (K x) (χ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, f x * χ.toH1Function.toFun x)
    (φ : H10Function (openCubeSet (originCube d m))) :
    (∫ x in openCubeSet (originCube d m), vecDot (hcExtVec e K x) (φ.toH1Function.grad x)) =
      ∫ x in openCubeSet (originCube d m), hcExt (-1) e f x * φ.toH1Function.toFun x := by
  have hAQ : ∀ i, MemLp (fun x => hcExtVec e K x i) 2
      (volume.restrict (openCubeSet (originCube d m))) := fun i =>
    memLp_hcExt_volume e m (hcSgn_abs e i) (hK i)
  have hfQ : MemLp (hcExt (-1) e f) 2 (volume.restrict (openCubeSet (originCube d m))) :=
    memLp_hcExt_volume e m (by simp) hf
  have h1 := hc_tendsto_integral_vecDot hAQ φ
  have h2 := hc_tendsto_integral_mul hfQ φ
  have h3 : ∀ n, (∫ x in openCubeSet (originCube d m), vecDot (hcExtVec e K x) (hcGrad (φ.approx n) x)) =
      ∫ x in openCubeSet (originCube d m), hcExt (-1) e f x * φ.approx n x := fun n =>
    hc_reflected_smooth e m hK hf hid (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
  simp_rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

theorem flatHalfMeasure_const_ne (d : ℕ) (m : ℤ) :
    ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ 0 ∧
      ENNReal.ofReal (cubeVolume (originCube d m))⁻¹ ≠ ⊤ := by
  have hv : (0 : ℝ) < cubeVolume (originCube d m) := cubeVolume_pos _
  exact ⟨by simpa using hv, ENNReal.ofReal_ne_top⟩

theorem memLp_flatHalfMeasure_iff (e : Fin d) (m : ℤ) {E : Type*} [NormedAddCommGroup E]
    {F : Vec d → E} {p : ℝ≥0∞} :
    MemLp F p (flatHalfMeasure e m) ↔ MemLp F p (volume.restrict (flatHalfCube e m)) := by
  obtain ⟨h1, h2⟩ := flatHalfMeasure_const_ne d m
  constructor
  · intro h
    refine MemLp.of_measure_le_smul (c := (ENNReal.ofReal (cubeVolume (originCube d m))⁻¹)⁻¹)
      (by simpa using h1) ?_ h
    rw [flatHalfMeasure_eq, smul_smul, ENNReal.inv_mul_cancel h1 h2, one_smul]
  · intro h
    refine MemLp.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume (originCube d m))⁻¹) h2 ?_ h
    rw [flatHalfMeasure_eq]


/-- Normalized `L^p` norm on the half cube. -/
noncomputable def flatHalfNorm {E : Type*} [NormedAddCommGroup E] (e : Fin d) (m : ℤ) (p : ℝ≥0∞)
    (F : Vec d → E) : ℝ :=
  (eLpNorm F p (flatHalfMeasure e m)).toReal

/-- The weak zero-trace formulation of `-Δ y = ∇·h` on the half cube. -/
def HalfDivProblem (e : Fin d) (m : ℤ) (y : H10Function (flatHalfCube e m)) (h : Vec d → Vec d) :
    Prop :=
  ∀ φ : H10Function (flatHalfCube e m),
    ∫ x in flatHalfCube e m, vecDot (y.toH1Function.grad x) (φ.toH1Function.grad x) =
      -∫ x in flatHalfCube e m, vecDot (h x) (φ.toH1Function.grad x)

theorem hc_integrable_vecDot {U : Set (Vec d)} {A B : Vec d → Vec d}
    (hA : ∀ i, MemLp (fun x => A x i) 2 (volume.restrict U))
    (hB : ∀ i, MemLp (fun x => B x i) 2 (volume.restrict U)) :
    Integrable (fun x => vecDot (A x) (B x)) (volume.restrict U) := by
  unfold vecDot
  exact integrable_finsetSum _ fun i _ => (hA i).integrable_mul (hB i)

theorem hcExtVec_add (e : Fin d) (A B : Vec d → Vec d) :
    hcExtVec e (fun x => A x + B x) = fun x => hcExtVec e A x + hcExtVec e B x := by
  funext x i
  simp only [hcExtVec, hcExt, Pi.add_apply]
  split_ifs <;> ring

theorem hc_extend_div (e : Fin d) (m : ℤ) {y : H10Function (flatHalfCube e m)} {G : Vec d → Vec d}
    (hG : ∀ i, MemLp (fun x => G x i) 2 (volume.restrict (flatHalfCube e m)))
    (hy : HalfDivProblem e m y G) :
    CubeDirichletDivergenceProblem (originCube d m) (hcOddH10 y) (hcExtVec e G) := by
  intro φ
  have hK : ∀ i, MemLp (fun x => y.toH1Function.grad x i + G x i) 2
      (volume.restrict (flatHalfCube e m)) := fun i => (y.toH1Function.gradMemL2 i).add (hG i)
  have hid : ∀ χ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (y.toH1Function.grad x + G x) (χ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, (fun _ => (0 : ℝ)) x * χ.toH1Function.toFun x := by
    intro χ
    simp only [zero_mul, integral_zero]
    simp only [vecDot_add_left]
    rw [integral_add (hc_integrable_vecDot y.toH1Function.gradMemL2 χ.toH1Function.gradMemL2)
      (hc_integrable_vecDot hG χ.toH1Function.gradMemL2)]
    linarith only [hy χ]
  have h := hc_reflected_identity e m (K := fun x => y.toH1Function.grad x + G x) (f := fun _ => 0)
    hK MemLp.zero hid φ
  have hz : hcExt (-1) e (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
    funext x; simp [hcExt]
  rw [hcExtVec_add, hz] at h
  simp only [zero_mul, integral_zero, vecDot_add_left] at h
  have hA1 : ∀ i, MemLp (fun x => hcExtVec e y.toH1Function.grad x i) 2
      (volume.restrict (openCubeSet (originCube d m))) := fun i =>
    memLp_hcExt_volume e m (hcSgn_abs e i) (y.toH1Function.gradMemL2 i)
  have hA2 : ∀ i, MemLp (fun x => hcExtVec e G x i) 2
      (volume.restrict (openCubeSet (originCube d m))) := fun i =>
    memLp_hcExt_volume e m (hcSgn_abs e i) (hG i)
  have hφ := φ.toH1Function.gradMemL2
  rw [integral_add (hc_integrable_vecDot hA1 hφ) (hc_integrable_vecDot hA2 hφ)] at h
  show ∫ x in openCubeSet (originCube d m), vecDot (hcExtVec e y.toH1Function.grad x)
      (φ.toH1Function.grad x) = -∫ x in openCubeSet (originCube d m), vecDot (hcExtVec e G x)
      (φ.toH1Function.grad x)
  linarith only [h]

theorem hc_extend_poisson (e : Fin d) (m : ℤ) {y : H10Function (flatHalfCube e m)} {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (flatHalfCube e m)))
    (hy : ∀ φ : H10Function (flatHalfCube e m),
      ∫ x in flatHalfCube e m, vecDot (y.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in flatHalfCube e m, f x * φ.toH1Function.toFun x) :
    CubeDirichletWeakPoissonProblem (originCube d m) (hcOddH10 y) (hcExt (-1) e f) := by
  intro φ
  exact hc_reflected_identity e m y.toH1Function.gradMemL2 hf hy φ

theorem hc_hasWeakPartialDerivOn_congr_fun {U : Set (Vec d)} (hU : MeasurableSet U) {j : Fin d}
    {u u' g : Vec d → ℝ} (h : ∀ x ∈ U, u x = u' x) (hw : HasWeakPartialDerivOn U j u g) :
    HasWeakPartialDerivOn U j u' g := by
  intro φ hφ hc hs
  have := hw φ hφ hc hs
  rw [← this]
  exact setIntegral_congr_fun hU fun x hx => by rw [h x hx]

/-- The weak Hessian of the odd extension restricts to a weak Hessian on the half cube. -/
def hcRestrictHessian (e : Fin d) (m : ℤ) (y : H10Function (flatHalfCube e m))
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) (hcOddH10 y).toH1Function) :
    HasWeakHessianOn (flatHalfCube e m) y.toH1Function where
  hess := H.hess
  hess_memL2 := fun i j => by
    have := H.hess_memL2 i j
    unfold MemScalarL2 volumeMeasureOn at this ⊢
    exact this.mono_measure (Measure.restrict_mono (flatHalfCube_subset e m) le_rfl)
  weak_second := fun i j => by
    have h1 := (H.weak_second i j).restrict (isOpen_flatHalfCube e m) (flatHalfCube_subset e m)
    refine hc_hasWeakPartialDerivOn_congr_fun (measurableSet_flatHalfCube e m) (fun x hx => ?_) h1
    show hcExtVec e y.toH1Function.grad x i = y.toH1Function.grad x i
    simp only [hcExtVec, hcExt_of_pos hx.2]


instance isFiniteMeasure_flatHalfMeasure (e : Fin d) (m : ℤ) :
    IsFiniteMeasure (flatHalfMeasure e m) := by
  unfold flatHalfMeasure
  have : IsFiniteMeasure (normalizedCubeMeasure (originCube d m)) := inferInstance
  infer_instance

theorem flatHalfMeasure_le (e : Fin d) (m : ℤ) :
    flatHalfMeasure e m ≤ normalizedCubeMeasure (originCube d m) :=
  Measure.restrict_le_self

theorem eLpNorm_flatHalf_le_cube {E : Type*} [NormedAddCommGroup E] (e : Fin d) (m : ℤ)
    (F : Vec d → E) (p : ℝ≥0∞) :
    eLpNorm F p (flatHalfMeasure e m) ≤ eLpNorm F p (normalizedCubeMeasure (originCube d m)) :=
  eLpNorm_mono_measure F (flatHalfMeasure_le e m)

theorem eLpNorm_flatHalf_congr {E : Type*} [NormedAddCommGroup E] (e : Fin d) (m : ℤ)
    {F F' : Vec d → E} (h : ∀ x ∈ flatHalfCube e m, F x = F' x) (p : ℝ≥0∞) :
    eLpNorm F p (flatHalfMeasure e m) = eLpNorm F' p (flatHalfMeasure e m) := by
  refine eLpNorm_congr_ae ?_
  unfold flatHalfMeasure
  exact ae_restrict_of_forall_mem (measurableSet_flatHalfCube e m) h

theorem hc_two_rpow_le_two {q : ℝ} (hq : 1 ≤ q) : (2 : ℝ≥0∞) ^ (1 / q) ≤ 2 := by
  calc (2 : ℝ≥0∞) ^ (1 / q) ≤ 2 ^ (1 : ℝ) :=
        ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [div_le_one (by linarith only [hq])]; exact hq)
    _ = 2 := ENNReal.rpow_one _

theorem eLpNorm_hcExtVec_le (e : Fin d) (m : ℤ) {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable G (flatHalfMeasure e m)) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (hcExtVec e G) p (normalizedCubeMeasure (originCube d m)) ≤
      2 * eLpNorm G p (flatHalfMeasure e m) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  rw [eLpNorm_hcExtVec_normalized e m hG hp0 hpt]
  refine mul_le_mul_left (hc_two_rpow_le_two ?_) _
  have := ENNReal.toReal_mono hpt hp1
  simpa using this

theorem eLpNorm_hcExt_le (e : Fin d) (m : ℤ) {σ : ℝ} (hσ : |σ| = 1) {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F (flatHalfMeasure e m)) {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (hcExt σ e F) p (normalizedCubeMeasure (originCube d m)) ≤
      2 * eLpNorm F p (flatHalfMeasure e m) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le one_pos hp1).ne'
  rw [eLpNorm_hcExt_normalized e m hσ hF hp0 hpt]
  refine mul_le_mul_left (hc_two_rpow_le_two ?_) _
  have := ENNReal.toReal_mono hpt hp1
  simpa using this

theorem hc_eLpNorm_weakDivergence_le {μ : Measure (Vec d)} {DG : Fin d → Vec d → Vec d}
    {p : ℝ≥0∞} (hJ : MemLp (jacobianHilbertMat DG) p μ) :
    eLpNorm (weakDivergence DG) p μ ≤
      (d : ℝ≥0∞) * eLpNorm (jacobianHilbertMat DG) p μ := by
  have h : eLpNorm (weakDivergence DG) p μ ≤ eLpNorm (((d : ℝ)) • jacobianHilbertMat DG) p μ := by
    refine eLpNorm_mono_ae (memLp_weakDivergence hJ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    simpa [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) by positivity)] using abs_weakDivergence_le DG x
  refine h.trans ?_
  rw [eLpNorm_const_smul]
  simp


theorem hc_memLp_comp {μ : Measure (Vec d)} {q : ℝ≥0∞} {G : Vec d → Vec d} (hG : MemLp G q μ)
    (i : Fin d) : MemLp (fun x => G x i) q μ := by
  have := (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).comp_memLp' hG
  simpa [Function.comp_def] using this

theorem hc_memLp_entry {μ : Measure (Vec d)} {q : ℝ≥0∞} {DG : Fin d → Vec d → Vec d}
    (hJ : MemLp (jacobianHilbertMat DG) q μ) (i j : Fin d) : MemLp (fun x => DG i x j) q μ := by
  have := (HilbertMat.entryL i j).comp_memLp' hJ
  simpa [Function.comp_def, jacobianHilbertMat] using this

theorem flatHalfCube_nonempty (e : Fin d) (m : ℤ) : (flatHalfCube e m).Nonempty := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  refine ⟨fun _ => (3 : ℝ) ^ m / 4, ?_, ?_⟩
  · rw [hc_mem_openCubeSet_originCube_iff]
    intro i
    constructor <;> linarith only [h3]
  · simp only [Set.mem_ofPred_eq]; linarith only [h3]

theorem isBoundedDomain_flatHalfCube (e : Fin d) (m : ℤ) : IsBoundedDomain (flatHalfCube e m) :=
  ((isBounded_openCubeSet (originCube d m)).subset (flatHalfCube_subset e m)).isBoundedDomain

end SuperdiffusionCLT.Section7
