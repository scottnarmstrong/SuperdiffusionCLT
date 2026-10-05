/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion
public import SuperdiffusionCLT.Section8.DivergenceForm.ScalarWeakSolution
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.Cubes

/-!
# Classical solutions of divergence-form equations are weak solutions

If the coefficient `a` has `C¹` entries and `u` is `C²`, then on a bounded open convex domain `U`
the restriction of `u` is an `H¹(U)` weak solution of `-∇·(a∇u) = -(divForm 1 a u)`.  The proof
integrates by parts against smooth compactly supported tests and passes to `H¹₀` tests along their
smooth approximants, using Cauchy–Schwarz on `U`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open SuperdiffusionCLT.Section8.DivergenceForm

namespace SuperdiffusionCLT.Section8

variable {d : ℕ} {U : Set (Vec d)}

/-- Cauchy–Schwarz for the integral of a product of two `L²` functions. -/
theorem domId_abs_integral_mul_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [Lp.norm_toLp, Lp.norm_toLp] at h
  rw [L2.inner_def] at h
  have : ∫ x, inner ℝ ((hf.toLp f) x) ((hg.toLp g) x) ∂μ = ∫ x, f x * g x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  rwa [this] at h

theorem domId_tendsto_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h q : α → ℝ} {p : ℕ → α → ℝ}
    (hh : MemLp h 2 μ) (hp : ∀ n, MemLp (p n) 2 μ) (hq : MemLp q 2 μ)
    (hlim : Tendsto (fun n ↦ eLpNorm (fun x ↦ p n x - q x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, h x * p n x ∂μ) atTop (𝓝 (∫ x, h x * q x ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n ↦ (eLpNorm h 2 μ).toReal * (eLpNorm (fun x ↦ p n x - q x) 2 μ).toReal)
      atTop (𝓝 ((eLpNorm h 2 μ).toReal * 0)) :=
    ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim).const_mul _
  rw [mul_zero] at hb
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hb
  have h1 : Integrable (fun x ↦ h x * p n x) μ := hh.integrable_mul (hp n)
  have h2 : Integrable (fun x ↦ h x * q x) μ := hh.integrable_mul hq
  have h3 : ∫ x, h x * p n x ∂μ - ∫ x, h x * q x ∂μ = ∫ x, h x * (p n x - q x) ∂μ := by
    rw [← integral_sub h1 h2]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [mul_sub]
  rw [h3, Real.norm_eq_abs]
  exact domId_abs_integral_mul_le hh ((hp n).sub hq)

theorem domId_ibp_coord {F φ : Vec d → ℝ} (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin d) :
    ∫ x, F x * fderiv ℝ φ x (Pi.single i 1) =
      -∫ x, fderiv ℝ F x (Pi.single i 1) * φ x := by
  have hFc : Continuous F := hF.continuous
  have hFd : Continuous fun x ↦ fderiv ℝ F x (Pi.single i 1) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hφc : Continuous φ := hφ.continuous
  have hφd : Continuous fun x ↦ fderiv ℝ φ x (Pi.single i 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcd : HasCompactSupport fun x ↦ fderiv ℝ φ x (Pi.single i 1) :=
    hc.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_ ?_ ?_
  · exact (hFd.mul hφc).integrable_of_hasCompactSupport (hc.mul_left)
  · exact (hFc.mul hφd).integrable_of_hasCompactSupport (hcd.mul_left)
  · exact (hFc.mul hφc).integrable_of_hasCompactSupport (hc.mul_left)
  · exact fun x _ ↦ (hF.differentiable one_ne_zero) x
  · exact fun x _ ↦ (hφ.differentiable (by simp)) x
/-- A continuous function is in `L²` of a bounded convex domain. -/
theorem domId_memLp_of_continuous (hU : IsOpenBoundedConvexDomain U) {g : Vec d → ℝ}
    (hg : Continuous g) : MemLp g 2 (volumeMeasureOn U) := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hK : IsCompact (closure U) := hU.isBoundedDomain.isBounded.isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hU.isOpen.measurableSet]
  exact Eventually.of_forall fun x hx ↦ hC x (subset_closure hx)

/-- The coordinate flux `F_i = ∑ⱼ aᵢⱼ ∂ⱼ u`. -/
noncomputable def domId_flux (a : CoeffField d) (u : Vec d → ℝ) (i : Fin d) (y : Vec d) : ℝ :=
  ∑ j : Fin d, a y i j * fderiv ℝ u y (Pi.single j 1)

theorem domId_flux_contDiff {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ a y i j)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin d) : ContDiff ℝ 1 (domId_flux a u i) := by
  unfold domId_flux
  refine ContDiff.sum fun j _ ↦ (ha i j).mul ?_
  have h1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  exact h1.clm_apply contDiff_const

theorem domId_divForm_eq {a : CoeffField d} (u : Vec d → ℝ) (x : Vec d) :
    divForm 1 a u x = ∑ i : Fin d, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) := by
  unfold divForm domId_flux
  rw [one_mul]

theorem domId_divForm_continuous {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ a y i j)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (divForm 1 (a) u) := by
  have : divForm 1 a u = fun x ↦ ∑ i : Fin d, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) :=
    funext (domId_divForm_eq u)
  rw [this]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  exact ((domId_flux_contDiff ha hu i).continuous_fderiv one_ne_zero).clm_apply continuous_const


theorem domId_setIntegral_test {φ : Vec d → ℝ} (hφ : ∀ x, x ∉ U → φ x = 0) (h : Vec d → ℝ) :
    ∫ x in U, h x * φ x = ∫ x, h x * φ x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
  rw [hφ x hx, mul_zero]

/-- **Classical solutions are weak solutions.**  If `a` is `C¹` and `u` is `C²`, then `u` is an
`H¹(U)` weak solution of `-∇·(a∇u) = -(∇·(a∇u))` on a bounded open convex domain. -/
theorem domId_weak_of_classical (hU : IsOpenBoundedConvexDomain U) {a : CoeffField d}
    (ha : ∀ i j, ContDiff ℝ 1 fun y ↦ a y i j) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) :
    IsScalarForcedWeakSolution a U (fun x ↦ -(divForm 1 a u x))
      (H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hu.of_le (by norm_num))) := by
  classical
  have hLc := domId_divForm_continuous ha hu
  refine ⟨(domId_memLp_of_continuous hU hLc).neg, fun v ↦ ?_⟩
  have hF := domId_flux_contDiff ha hu
  have hDc : ∀ i, Continuous fun x ↦ fderiv ℝ (domId_flux a u i) x (Pi.single i 1) :=
    fun i ↦ ((hF i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFmem : ∀ i, MemLp (domId_flux a u i) 2 (volumeMeasureOn U) :=
    fun i ↦ domId_memLp_of_continuous hU (hF i).continuous
  have hDmem : ∀ i, MemLp (fun x ↦ fderiv ℝ (domId_flux a u i) x (Pi.single i 1)) 2
      (volumeMeasureOn U) := fun i ↦ domId_memLp_of_continuous hU (hDc i)
  have hphi : ∀ n, MemLp (v.approx n) 2 (volumeMeasureOn U) := fun n ↦
    ((v.approx_smooth n).continuous.memLp_of_hasCompactSupport (v.approx_hasCompactSupport n)).restrict U
  have hphid : ∀ n i, MemLp (fun x ↦ fderiv ℝ (v.approx n) x (Pi.single i 1)) 2
      (volumeMeasureOn U) := fun n i ↦ by
    have hc : Continuous fun x ↦ fderiv ℝ (v.approx n) x (Pi.single i 1) :=
      ((v.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport
      ((v.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (Pi.single i 1))).restrict U
  have hA : ∀ i, Tendsto (fun n ↦ ∫ x in U, domId_flux a u i x *
      fderiv ℝ (v.approx n) x (Pi.single i 1)) atTop
      (𝓝 (∫ x in U, domId_flux a u i x * v.toH1Function.grad x i)) := fun i ↦
    domId_tendsto_integral_mul (hFmem i) (fun n ↦ hphid n i) (v.toH1Function.gradMemL2 i)
      (v.tendsto_approx_grad i)
  have hB : ∀ i, Tendsto (fun n ↦ ∫ x in U, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) *
      v.approx n x) atTop
      (𝓝 (∫ x in U, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) * v.toH1Function.toFun x)) :=
    fun i ↦ domId_tendsto_integral_mul (hDmem i) hphi v.toH1Function.memL2 v.tendsto_approx
  have hAB : ∀ i n, ∫ x in U, domId_flux a u i x * fderiv ℝ (v.approx n) x (Pi.single i 1) =
      -∫ x in U, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) * v.approx n x := fun i n ↦ by
    have hz : ∀ x, x ∉ U → v.approx n x = 0 := fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hx (v.approx_support_subset n h)
    have hz' : ∀ x, x ∉ U → fderiv ℝ (v.approx n) x (Pi.single i 1) = 0 := fun x hx ↦ by
      rw [fderiv_of_notMem_tsupport ℝ fun h ↦ hx (v.approx_support_subset n h)]
      rfl
    rw [domId_setIntegral_test hz, setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx ↦ by rw [hz' x hx, mul_zero])]
    exact domId_ibp_coord (hF i) (v.approx_smooth n) (v.approx_hasCompactSupport n) i
  have hlim : ∀ i, ∫ x in U, domId_flux a u i x * v.toH1Function.grad x i =
      -∫ x in U, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) * v.toH1Function.toFun x :=
    fun i ↦ tendsto_nhds_unique (hA i) (((hB i).neg).congr fun n ↦ (hAB i n).symm)
  have hpair : ∀ x, vecDot (matVecMul (a x)
      ((H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hu.of_le (by norm_num))).grad x))
      (v.toH1Function.grad x) = ∑ i, domId_flux a u i x * v.toH1Function.grad x i := fun x ↦ by
    unfold vecDot matVecMul domId_flux
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rfl
  calc
    ∫ x in U, vecDot (matVecMul (a x)
        ((H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU (hu.of_le (by norm_num))).grad x))
        (v.toH1Function.grad x) ∂volume
        = ∫ x in U, ∑ i, domId_flux a u i x * v.toH1Function.grad x i ∂volume := by
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      exact hpair x
    _ = ∑ i, ∫ x in U, domId_flux a u i x * v.toH1Function.grad x i ∂volume :=
      integral_finsetSum _ fun i _ ↦ (hFmem i).integrable_mul (v.toH1Function.gradMemL2 i)
    _ = ∑ i, -∫ x in U, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) *
        v.toH1Function.toFun x ∂volume := Finset.sum_congr rfl fun i _ ↦ hlim i
    _ = -∫ x in U, ∑ i, fderiv ℝ (domId_flux a u i) x (Pi.single i 1) *
        v.toH1Function.toFun x ∂volume := by
      rw [Finset.sum_neg_distrib]
      congr 1
      exact (integral_finsetSum _ fun i _ ↦
        (hDmem i).integrable_mul v.toH1Function.memL2).symm
    _ = ∫ x in U, (-(divForm 1 a u x)) * v.toH1Function.toFun x ∂volume := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
      dsimp only
      rw [domId_divForm_eq, ← Finset.sum_mul, neg_mul]

end SuperdiffusionCLT.Section8
