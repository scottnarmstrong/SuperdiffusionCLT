/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.RealizationAbstract
public import SuperdiffusionCLT.Probability.LHSTerm1Closing

/-!
# Stationary potential realization for jointly measurable actions

Section 3 of the paper (stationary potential realization).
Bounded measurable orbit averages have horizontal gradients. Fubini transfers
solenoidal orthogonality to spatial divergence tests, and indicator functions
show that each test vanishes almost everywhere. Countable spatial test density
then yields the weak equation for every H¹₀ test on each cube.

The final theorem has no separability or strong-continuity hypothesis on L²,
and imposes no topology on the probability space.
-/

@[expose] public section

open scoped Topology ENNReal InnerProductSpace
noncomputable section
namespace SuperdiffusionCLT.Probability.Stationary
universe u
variable {d : ℕ} {Ω : Type u} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
  [MeasureTheory.IsProbabilityMeasure μ] [AddAction (Homogenization.Vec d) Ω]
  [MeasurableVAdd₂ (Homogenization.Vec d) Ω] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ]

theorem realizationAbstractClose_measurable_negVAdd :
    Measurable (fun p : Ω × Homogenization.Vec d => (-p.2) +ᵥ p.1) :=
  (measurable_neg.comp measurable_snd).vadd measurable_fst

def realizationAbstractClose_vecField (G : Ω → Homogenization.Vec d) : Ω → Homogenization.HilbertVec d :=
  fun ω => Homogenization.HilbertVec.ofVec (G ω)

def realizationAbstractClose_orbitDivergenceField (G : Ω → Homogenization.Vec d) (θ : Homogenization.Vec d → ℝ)
    (ω : Ω) : ℝ := ∫ x, Homogenization.vecDot (G (x +ᵥ ω)) (Homogenization.euclideanGradient θ x)

omit [MeasureTheory.IsProbabilityMeasure μ] in
theorem realizationAbstractClose_integral_comp_vadd (g : Ω → ℝ) (x : Homogenization.Vec d) :
    ∫ ω, g (x +ᵥ ω) ∂μ = ∫ ω, g ω ∂μ :=
  (measurePreserving_const_vadd (μ := μ) x).integral_comp'
    (f := MeasurableEquiv.vadd x) g

def realizationAbstractClose_smearScalar (θ : Homogenization.Vec d → ℝ) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  ∫ y, θ y * f ((-y) +ᵥ ω)

def realizationAbstractClose_smearGrad (θ : Homogenization.Vec d → ℝ) (f : Ω → ℝ) (ω : Ω) : Homogenization.Vec d :=
  fun i => ∫ y, fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)

omit [MeasurableSpace Ω] [MeasurableVAdd₂ (Homogenization.Vec d) Ω] in
theorem realizationAbstractClose_smearScalar_vadd_basisVec (θ : Homogenization.Vec d → ℝ) (f : Ω → ℝ) (ω : Ω)
    (t : ℝ) (i : Fin d) :
    realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) =
      ∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω) := by
  have hshift : ∀ y : Homogenization.Vec d, (-y) +ᵥ (t • Homogenization.basisVec i +ᵥ ω) =
      (t • Homogenization.basisVec i - y) +ᵥ ω := by
    intro y
    rw [vadd_vadd, sub_eq_neg_add, add_comm]
  have hpt : (∫ y, θ y * f ((-y) +ᵥ (t • Homogenization.basisVec i +ᵥ ω))) =
      ∫ y, θ y * f ((t • Homogenization.basisVec i - y) +ᵥ ω) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with y
    rw [hshift y]
  rw [realizationAbstractClose_smearScalar, hpt]
  have htrans := MeasureTheory.integral_add_right_eq_self (μ := (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
    (f := fun y : Homogenization.Vec d => θ y * f ((t • Homogenization.basisVec i - y) +ᵥ ω))
    (t • Homogenization.basisVec i)
  rw [← htrans]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  have harg : t • Homogenization.basisVec i - (y + t • Homogenization.basisVec i) = -y := by
    abel
  rw [harg]

omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_aestronglyMeasurable_smearScalar
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ}
    (hθm : Measurable θ) (hfm : Measurable f) :
    MeasureTheory.AEStronglyMeasurable (realizationAbstractClose_smearScalar θ f) μ := by
  have hjoint : MeasureTheory.StronglyMeasurable (fun p : Ω × Homogenization.Vec d => θ p.2 * f ((-p.2) +ᵥ p.1)) :=
    ((hθm.comp measurable_snd).mul
      (hfm.comp (realizationAbstractClose_measurable_negVAdd (d := d)))).stronglyMeasurable
  have h := hjoint.integral_prod_right' (ν := (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
  exact h.aestronglyMeasurable

omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_measurable_smearScalar
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ}
    (hθm : Measurable θ) (hfm : Measurable f) :
    Measurable (realizationAbstractClose_smearScalar θ f) := by
  have hjoint : MeasureTheory.StronglyMeasurable (fun p : Ω × Homogenization.Vec d => θ p.2 * f ((-p.2) +ᵥ p.1)) :=
    ((hθm.comp measurable_snd).mul
      (hfm.comp (realizationAbstractClose_measurable_negVAdd (d := d)))).stronglyMeasurable
  exact (hjoint.integral_prod_right' (ν := (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))).measurable

omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_aestronglyMeasurable_smearGrad_apply
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ}
    (hθ : ContDiff ℝ 1 θ) (hfm : Measurable f) (i : Fin d) :
    MeasureTheory.AEStronglyMeasurable (fun ω => realizationAbstractClose_smearGrad θ f ω i) μ := by
  have hdθm : Measurable (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hjoint : MeasureTheory.StronglyMeasurable
      (fun p : Ω × Homogenization.Vec d =>
        fderiv ℝ θ p.2 (Homogenization.basisVec i) * f ((-p.2) +ᵥ p.1)) :=
    ((hdθm.comp measurable_snd).mul
      (hfm.comp (realizationAbstractClose_measurable_negVAdd (d := d)))).stronglyMeasurable
  have h := hjoint.integral_prod_right' (ν := (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
  simpa only [realizationAbstractClose_smearGrad] using h.aestronglyMeasurable

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_memLp_smearScalar
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    MeasureTheory.MemLp (realizationAbstractClose_smearScalar θ f) 2 μ := by
  have hθi : MeasureTheory.Integrable θ (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    hθ.continuous.integrable_of_hasCompactSupport hθc
  refine MeasureTheory.MemLp.of_bound (realizationAbstractClose_aestronglyMeasurable_smearScalar (μ := μ) hθ.continuous.measurable hfm)
    (Cf * ∫ y, |θ y|) ?_
  filter_upwards with ω
  calc ‖realizationAbstractClose_smearScalar θ f ω‖ = ‖∫ y, θ y * f ((-y) +ᵥ ω)‖ := by
        rw [realizationAbstractClose_smearScalar]
    _ ≤ ∫ y, ‖θ y * f ((-y) +ᵥ ω)‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y, Cf * |θ y| := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hθi.abs.const_mul Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul]
          calc |θ y| * |f ((-y) +ᵥ ω)| ≤ |θ y| * Cf :=
                mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
            _ = Cf * |θ y| := mul_comm _ _
    _ = Cf * ∫ y, |θ y| := MeasureTheory.integral_const_mul _ _

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_memLp_smearGrad_apply
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) :
    MeasureTheory.MemLp (fun ω => realizationAbstractClose_smearGrad θ f ω i) 2 μ := by
  have hdθc : HasCompactSupport (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    hθc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i)
  have hdθcont : Continuous (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i)) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdθi : MeasureTheory.Integrable (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    hdθcont.integrable_of_hasCompactSupport hdθc
  refine MeasureTheory.MemLp.of_bound (realizationAbstractClose_aestronglyMeasurable_smearGrad_apply (μ := μ) hθ hfm i)
    (Cf * ∫ y, |fderiv ℝ θ y (Homogenization.basisVec i)|) ?_
  filter_upwards with ω
  calc ‖realizationAbstractClose_smearGrad θ f ω i‖ =
        ‖∫ y, fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)‖ := by
        rw [realizationAbstractClose_smearGrad]
    _ ≤ ∫ y, ‖fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ y, Cf * |fderiv ℝ θ y (Homogenization.basisVec i)| := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hdθi.abs.const_mul Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          rw [Real.norm_eq_abs, abs_mul]
          calc |fderiv ℝ θ y (Homogenization.basisVec i)| * |f ((-y) +ᵥ ω)| ≤
                |fderiv ℝ θ y (Homogenization.basisVec i)| * Cf :=
                mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
            _ = Cf * |fderiv ℝ θ y (Homogenization.basisVec i)| := mul_comm _ _
    _ = Cf * ∫ y, |fderiv ℝ θ y (Homogenization.basisVec i)| := MeasureTheory.integral_const_mul _ _

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_memLp_smearGrad
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (realizationAbstractClose_smearGrad θ f ω)) 2 μ := by
  classical
  refine MeasureTheory.MemLp.of_eval_piLp (fun i => ?_)
  have h := realizationAbstractClose_memLp_smearGrad_apply (μ := μ) hθ hθc hfm hf i
  have hfun : (fun ω : Ω => Homogenization.HilbertVec.ofVec (realizationAbstractClose_smearGrad θ f ω) i) =
      fun ω : Ω => realizationAbstractClose_smearGrad θ f ω i := by
    funext ω
    exact PiLp.toLp_apply 2 (fun _ : Fin d => ℝ) (realizationAbstractClose_smearGrad θ f ω) i
  rwa [hfun]

theorem realizationAbstractClose_integrable_mul_slice {g : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hg : MeasureTheory.Integrable g (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)))
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (ω : Ω) :
    MeasureTheory.Integrable (fun y : Homogenization.Vec d => g y * f ((-y) +ᵥ ω)) (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := by
  refine MeasureTheory.Integrable.congr (f := fun y : Homogenization.Vec d => f ((-y) +ᵥ ω) * g y) ?_
    (Filter.Eventually.of_forall fun y => mul_comm _ _)
  refine hg.bdd_mul (c := Cf) (f := fun y : Homogenization.Vec d => f ((-y) +ᵥ ω)) ?_ ?_
  · exact (hfm.comp ((realizationAbstractClose_measurable_negVAdd (d := d)).comp
      ((measurable_const : Measurable (fun _ : Homogenization.Vec d => ω)).prodMk measurable_id))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hf _

theorem realizationAbstractClose_differenceQuotient_smearScalar_eq_integral
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ) (ω : Ω) :
    t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - realizationAbstractClose_smearScalar θ f ω) -
        realizationAbstractClose_smearGrad θ f ω i
      = ∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω) := by
  have hS : MeasureTheory.Integrable (fun y : Homogenization.Vec d => θ (y + t • Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    (hθ.continuous.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (lhsClosing_hasCompactSupport_shift hθc (t • Homogenization.basisVec i))
  have hA : MeasureTheory.Integrable θ (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    hθ.continuous.integrable_of_hasCompactSupport hθc
  have hD : MeasureTheory.Integrable (fun y : Homogenization.Vec d => fderiv ℝ θ y (Homogenization.basisVec i))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hθc.fderiv_apply (𝕜 := ℝ) (Homogenization.basisVec i))
  have hSω := realizationAbstractClose_integrable_mul_slice hS hfm hf ω
  have hAω := realizationAbstractClose_integrable_mul_slice hA hfm hf ω
  have hDω := realizationAbstractClose_integrable_mul_slice hD hfm hf ω
  have hTω : MeasureTheory.Integrable (fun y : Homogenization.Vec d => t⁻¹ *
      ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)))
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) :=
    (realizationAbstractClose_integrable_mul_slice (hS.sub hA) hfm hf ω).const_mul t⁻¹
  have hstep : (∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω)) -
      ∫ y, θ y * f ((-y) +ᵥ ω)
      = ∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω) := by
    rw [← MeasureTheory.integral_sub hSω hAω]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  have hstep' : t⁻¹ * (∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))
      = ∫ y, t⁻¹ * ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)) := by
    simpa only [smul_eq_mul] using (MeasureTheory.integral_const_mul (t⁻¹)
      (fun y : Homogenization.Vec d => (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))
      (μ := MeasureTheory.volume)).symm
  calc t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - realizationAbstractClose_smearScalar θ f ω) -
        realizationAbstractClose_smearGrad θ f ω i
      = t⁻¹ * ((∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω)) -
          ∫ y, θ y * f ((-y) +ᵥ ω)) - realizationAbstractClose_smearGrad θ f ω i := by
        rw [realizationAbstractClose_smearScalar_vadd_basisVec, realizationAbstractClose_smearScalar]
    _ = t⁻¹ * (∫ y, (θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω)) -
          realizationAbstractClose_smearGrad θ f ω i := by
        rw [hstep]
    _ = (∫ y, t⁻¹ * ((θ (y + t • Homogenization.basisVec i) - θ y) * f ((-y) +ᵥ ω))) -
          realizationAbstractClose_smearGrad θ f ω i := by
        rw [hstep']
    _ = ∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω) := by
        simp only [realizationAbstractClose_smearGrad]
        rw [← MeasureTheory.integral_sub hTω hDω]
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by
          unfold lhsClosing_kernelDifferenceQuotient
          ring)

theorem realizationAbstractClose_abs_differenceQuotient_smearScalar_le
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ)
    (ω : Ω) :
    |t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - realizationAbstractClose_smearScalar θ f ω) -
        realizationAbstractClose_smearGrad θ f ω i| ≤ Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| := by
  rw [realizationAbstractClose_differenceQuotient_smearScalar_eq_integral hθ hθc hfm hf i t ω]
  have hkdq : MeasureTheory.Integrable (fun y : Homogenization.Vec d => lhsClosing_kernelDifferenceQuotient θ i t y)
      (MeasureTheory.volume : MeasureTheory.Measure (Homogenization.Vec d)) := lhsClosing_integrable_kernelDifferenceQuotient hθ hθc i t
  calc |∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)|
      = ‖∫ y, lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖lhsClosing_kernelDifferenceQuotient θ i t y * f ((-y) +ᵥ ω)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| * |f ((-y) +ᵥ ω)| :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [Real.norm_eq_abs, abs_mul])
    _ ≤ ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| * Cf := by
        refine MeasureTheory.integral_mono_of_nonneg ?_ (hkdq.abs.mul_const Cf) ?_
        · filter_upwards with y; positivity
        · filter_upwards with y
          exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
    _ = (∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) * Cf := MeasureTheory.integral_mul_const _ _
    _ = Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y| := mul_comm _ _

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_eLpNorm_differenceQuotient_smearScalar_le
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) (t : ℝ) :
    MeasureTheory.eLpNorm (fun ω : Ω => t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω)
        - realizationAbstractClose_smearScalar θ f ω) - realizationAbstractClose_smearGrad θ f ω i) 2 μ
      ≤ ENNReal.ofReal (Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) := by
  have hSm := realizationAbstractClose_measurable_smearScalar hθ.continuous.measurable hfm
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun ω : Ω => t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω)
        - realizationAbstractClose_smearScalar θ f ω) - realizationAbstractClose_smearGrad θ f ω i) μ :=
    (((hSm.comp (measurable_const_vadd _)).sub hSm).const_mul _).aestronglyMeasurable.sub
      (realizationAbstractClose_aestronglyMeasurable_smearGrad_apply (μ := μ) hθ hfm i)
  refine (MeasureTheory.eLpNorm_le_of_ae_bound (p := 2) (μ := μ)
    (C := Cf * ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|) hmeas ?_).trans_eq ?_
  · filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact realizationAbstractClose_abs_differenceQuotient_smearScalar_le hθ hθc hfm hf i t ω
  · simp only [MeasureTheory.measure_univ, ENNReal.one_rpow, one_mul]

omit [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_tendsto_eLpNorm_differenceQuotient_smearScalar
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) (i : Fin d) :
    Filter.Tendsto (fun t : ℝ => MeasureTheory.eLpNorm (fun ω : Ω =>
        t⁻¹ * (realizationAbstractClose_smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) - realizationAbstractClose_smearScalar θ f ω)
          - realizationAbstractClose_smearGrad θ f ω i) 2 μ) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have hI : Filter.Tendsto (fun t : ℝ => ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := lhsClosing_tendsto_integral_abs_kernelDifferenceQuotient hθ hθc i
  have hub : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (Cf *
      ∫ y, |lhsClosing_kernelDifferenceQuotient θ i t y|)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hI.const_mul Cf)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hub
    (Filter.Eventually.of_forall fun t => zero_le)
    (Filter.Eventually.of_forall fun t =>
      realizationAbstractClose_eLpNorm_differenceQuotient_smearScalar_le (μ := μ) hθ hθc hfm hf i t)

theorem realizationAbstractClose_smearScalar_hasHorizontalGradient

    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    HasHorizontalGradient (μ := μ)
      ((realizationAbstractClose_memLp_smearScalar (μ := μ) hθ hθc hfm hf).toLp (realizationAbstractClose_smearScalar θ f))
      ((realizationAbstractClose_memLp_smearGrad (μ := μ) hθ hθc hfm hf).toLp
        (fun ω => Homogenization.HilbertVec.ofVec (realizationAbstractClose_smearGrad θ f ω))) := by
  classical
  intro i
  have hFc : MeasureTheory.MemLp (fun ω : Ω => realizationAbstractClose_smearGrad θ f ω i) 2 μ :=
    realizationAbstractClose_memLp_smearGrad_apply (μ := μ) hθ hθc hfm hf i
  have hcoord : vectorL2Coord (μ := μ) i
      ((realizationAbstractClose_memLp_smearGrad (μ := μ) hθ hθc hfm hf).toLp
        (fun ω => Homogenization.HilbertVec.ofVec (realizationAbstractClose_smearGrad θ f ω)))
      = hFc.toLp (fun ω => realizationAbstractClose_smearGrad θ f ω i) := by
    rw [MeasureTheory.Lp.ext_iff]
    filter_upwards [realizationAbstract_vectorL2Coord_toLp (μ := μ) i (realizationAbstractClose_smearGrad θ f)
        (realizationAbstractClose_memLp_smearGrad (μ := μ) hθ hθc hfm hf), MeasureTheory.MemLp.coeFn_toLp hFc] with ω h1 h2
    rw [h1, h2]
  rw [hcoord]
  refine (hasDerivAt_iff_tendsto_slope_zero (f := fun t : ℝ =>
      koopman (μ := μ) (t • Homogenization.basisVec i)
        ((realizationAbstractClose_memLp_smearScalar (μ := μ) hθ hθc hfm hf).toLp (realizationAbstractClose_smearScalar θ f)))
    (f' := hFc.toLp (fun ω => realizationAbstractClose_smearGrad θ f ω i))).mpr ?_
  refine MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
    (fun ω : Ω => realizationAbstractClose_smearGrad θ f ω i) hFc ?_
  refine Filter.Tendsto.congr' ?_
    (realizationAbstractClose_tendsto_eLpNorm_differenceQuotient_smearScalar (μ := μ) hθ hθc hfm hf i)
  filter_upwards with t
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [realizationAbstract_differenceQuotient_class_coeFn (μ := μ) t i
      (realizationAbstractClose_memLp_smearScalar (μ := μ) hθ hθc hfm hf)] with ω h1
  simp only [Pi.sub_apply, zero_add, zero_smul, koopman_zero, h1]

theorem realizationAbstractClose_integrable_prod_weighted_comp_vadd

    {ρ : Homogenization.Vec d → ℝ} (hρm : Continuous ρ) (hρ : MeasureTheory.Integrable ρ MeasureTheory.volume)
    {g : Ω → ℝ} (hgm : MeasureTheory.StronglyMeasurable g) (hg : MeasureTheory.Integrable g μ) :
    MeasureTheory.Integrable (fun q : Ω × Homogenization.Vec d => ρ q.2 * g (q.2 +ᵥ q.1))
      (μ.prod MeasureTheory.volume) := by
  have hmeas : Measurable fun q : Ω × Homogenization.Vec d => q.2 +ᵥ q.1 :=
    (measurable_vadd (M := Homogenization.Vec d) (α := Ω)).comp measurable_swap
  have hjm : MeasureTheory.StronglyMeasurable fun q : Ω × Homogenization.Vec d => ρ q.2 * g (q.2 +ᵥ q.1) :=
    ((hρm.measurable.comp measurable_snd).stronglyMeasurable).mul
      (hgm.comp_measurable hmeas)
  refine (MeasureTheory.integrable_prod_iff' hjm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y =>
      ((measurePreserving_const_vadd (μ := μ) (Ω := Ω) y).integrable_comp_of_integrable
        hg).const_mul (ρ y)
  · have hval : ∀ y : Homogenization.Vec d,
        (∫ ω, ‖ρ y * g (y +ᵥ ω)‖ ∂μ) = |ρ y| * ∫ ω, ‖g ω‖ ∂μ := by
      intro y
      simp only [norm_mul, Real.norm_eq_abs]
      rw [MeasureTheory.integral_const_mul]
      exact congrArg (fun t => |ρ y| * t)
        (realizationAbstractClose_integral_comp_vadd
          (fun ω => |g ω|) y)
    refine (MeasureTheory.integrable_congr (Filter.Eventually.of_forall hval)).2 ?_
    exact hρ.abs.mul_const _

theorem realizationAbstractClose_scalar_joint
    {κ : Homogenization.Vec d → ℝ} (hκ : Continuous κ) (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : Ω → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hgm : MeasureTheory.StronglyMeasurable g) (hg : MeasureTheory.Integrable g μ) :
    MeasureTheory.Integrable (fun p : Ω × Homogenization.Vec d => f p.1 * (κ p.2 * g (p.2 +ᵥ p.1)))
      (μ.prod MeasureTheory.volume) := by
  refine (realizationAbstractClose_integrable_prod_weighted_comp_vadd (μ := μ) hκ hκi hgm hg).bdd_mul (c := Cf) ?_ ?_
  · exact (hfm.comp measurable_fst).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hf p.1

omit [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.VAddInvariantMeasure (Homogenization.Vec d) Ω μ] in
theorem realizationAbstractClose_scalar_joint_back
    {κ : Homogenization.Vec d → ℝ} (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : Ω → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hg : MeasureTheory.Integrable g μ) :
    MeasureTheory.Integrable (fun p : Ω × Homogenization.Vec d => (g p.1 * κ p.2) * f ((-p.2) +ᵥ p.1))
      (μ.prod MeasureTheory.volume) := by
  refine (hg.mul_prod hκi).mul_bdd (c := Cf) ?_ ?_
  · exact (hfm.comp realizationAbstractClose_measurable_negVAdd).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hf _

theorem realizationAbstractClose_scalar_transfer
    {κ : Homogenization.Vec d → ℝ} (hκ : Continuous κ) (hκi : MeasureTheory.Integrable κ MeasureTheory.volume)
    {f g : Ω → ℝ} {Cf : ℝ} (hfm : Measurable f)
    (hf : ∀ ω, |f ω| ≤ Cf) (hgm : MeasureTheory.StronglyMeasurable g) (hg : MeasureTheory.Integrable g μ) :
    (∫ ω, f ω * (∫ y, κ y * g (y +ᵥ ω)) ∂μ) =
      ∫ ω, g ω * (∫ y, κ y * f ((-y) +ᵥ ω)) ∂μ := by
  have hj := realizationAbstractClose_scalar_joint (μ := μ) hκ hκi hfm hf hgm hg
  have hb := realizationAbstractClose_scalar_joint_back (μ := μ) hκi hfm hf hg
  calc
    _ = ∫ ω, ∫ y, f ω * (κ y * g (y +ᵥ ω)) ∂MeasureTheory.volume ∂μ := by
      simp only [MeasureTheory.integral_const_mul]
    _ = ∫ y, ∫ ω, f ω * (κ y * g (y +ᵥ ω)) ∂μ :=
      MeasureTheory.integral_integral_swap hj
    _ = ∫ y, ∫ ω, (g ω * κ y) * f ((-y) +ᵥ ω) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [← realizationAbstractClose_integral_comp_vadd
        (fun ω => (g ω * κ y) * f ((-y) +ᵥ ω)) y]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      simp only [neg_vadd_vadd]
      ring
    _ = ∫ ω, ∫ y, (g ω * κ y) * f ((-y) +ᵥ ω) ∂MeasureTheory.volume ∂μ :=
      (MeasureTheory.integral_integral_swap hb).symm
    _ = _ := by simp only [mul_assoc, MeasureTheory.integral_const_mul]

theorem realizationAbstractClose_spatial_pairing_transfer
    {G : Ω → Homogenization.Vec d} {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hGm : MeasureTheory.StronglyMeasurable (realizationAbstractClose_vecField G)) (hG : MeasureTheory.MemLp (realizationAbstractClose_vecField G) 2 μ)
    (hθc : ∀ i, Continuous (coordKernel θ i))
    (hθi : ∀ i, MeasureTheory.Integrable (coordKernel θ i) MeasureTheory.volume)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    (∫ ω, f ω * realizationAbstractClose_orbitDivergenceField G θ ω ∂μ) =
      ∫ ω, Homogenization.vecDot (realizationAbstractClose_smearGrad θ f ω) (G ω) ∂μ := by
  have hg : ∀ i, MeasureTheory.Integrable (fun ω => G ω i) μ := fun i =>
    (hG.eval_piLp i).integrable (by norm_num)
  have hgm : ∀ i, MeasureTheory.StronglyMeasurable (fun ω => G ω i) := fun i =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).continuous.comp_stronglyMeasurable hGm
  have hj := fun i => realizationAbstractClose_scalar_joint (μ := μ) (hθc i) (hθi i) hfm hf (hgm i) (hg i)
  have hb := fun i => realizationAbstractClose_scalar_joint_back (μ := μ) (hθi i) hfm hf (hg i)
  have hleft : ∀ i, MeasureTheory.Integrable (fun ω => f ω * ∫ y, coordKernel θ i y * G (y +ᵥ ω) i) μ := by
    intro i
    simpa only [MeasureTheory.integral_const_mul] using (hj i).integral_prod_left
  have hright : ∀ i, MeasureTheory.Integrable (fun ω => G ω i * realizationAbstractClose_smearGrad θ f ω i) μ := by
    intro i
    simpa only [mul_assoc, MeasureTheory.integral_const_mul, realizationAbstractClose_smearGrad, coordKernel] using (hb i).integral_prod_left
  have ha : ∀ᵐ ω ∂μ, ∀ i,
      MeasureTheory.Integrable (fun y => coordKernel θ i y * G (y +ᵥ ω) i) MeasureTheory.volume :=
    Filter.eventually_all.mpr fun i =>
      (realizationAbstractClose_integrable_prod_weighted_comp_vadd (μ := μ) (hθc i) (hθi i) (hgm i) (hg i)).prod_right_ae
  calc
    _ = ∫ ω, ∑ i, f ω * (∫ y, coordKernel θ i y * G (y +ᵥ ω) i) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [ha] with ω hω
      rw [realizationAbstractClose_orbitDivergenceField]
      simp_rw [vecDot_euclideanGradient_eq_sum]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ => hω i), Finset.mul_sum]
    _ = ∑ i, ∫ ω, f ω * (∫ y, coordKernel θ i y * G (y +ᵥ ω) i) ∂μ :=
      MeasureTheory.integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i, ∫ ω, G ω i * realizationAbstractClose_smearGrad θ f ω i ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact realizationAbstractClose_scalar_transfer (μ := μ) (hθc i) (hθi i) hfm hf (hgm i) (hg i)
    _ = ∫ ω, ∑ i, G ω i * realizationAbstractClose_smearGrad θ f ω i ∂μ :=
      (MeasureTheory.integral_finsetSum _ (fun i _ => hright i)).symm
    _ = _ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with ω
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem realizationAbstractClose_smear_pairing_zero
    {G : Ω → Homogenization.Vec d}
    (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2 μ)
    (hGsol : hG.toLp _ ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {θ : Homogenization.Vec d → ℝ} {f : Ω → ℝ} {Cf : ℝ}
    (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hfm : Measurable f) (hf : ∀ ω, |f ω| ≤ Cf) :
    (∫ ω, Homogenization.vecDot (realizationAbstractClose_smearGrad θ f ω) (G ω) ∂μ) = 0 := by
  have hh := realizationAbstractClose_smearScalar_hasHorizontalGradient (μ := μ) hθ hθc hfm hf
  have hz := (Submodule.mem_orthogonal _ _).mp hGsol _
    ((Submodule.le_topologicalClosure _) ⟨_, hh⟩)
  rw [MeasureTheory.L2.inner_def] at hz
  convert hz using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.MemLp.coeFn_toLp hG,
    MeasureTheory.MemLp.coeFn_toLp (realizationAbstractClose_memLp_smearGrad (μ := μ) hθ hθc hfm hf)] with ω h1 h2
  rw [h1, h2]
  simp only [Homogenization.HilbertVec.inner_def, Homogenization.HilbertVec.toVec_ofVec]

theorem realizationAbstractClose_action_quasiMeasurePreserving :
    MeasureTheory.Measure.QuasiMeasurePreserving
      (fun p : Ω × Homogenization.Vec d => p.2 +ᵥ p.1)
      (μ.prod MeasureTheory.volume) μ := by
  have hm : Measurable (fun p : Ω × Homogenization.Vec d => p.2 +ᵥ p.1) :=
    (measurable_vadd (M := Homogenization.Vec d) (α := Ω)).comp measurable_swap
  refine ⟨hm, MeasureTheory.Measure.AbsolutelyContinuous.mk fun s hs hz => ?_⟩
  rw [MeasureTheory.Measure.map_apply hm hs,
    MeasureTheory.Measure.prod_apply_symm (hs.preimage hm)]
  have heq : ∀ y : Homogenization.Vec d,
      μ ((fun ω => y +ᵥ ω) ⁻¹' s) = 0 := fun y => by
    rw [MeasureTheory.VAddInvariantMeasure.measure_preimage_vadd y hs, hz]
  simp only [Set.preimage, Set.mem_ofPred_eq] at heq ⊢
  simp only [heq, MeasureTheory.lintegral_zero]

theorem realizationAbstractClose_orbitDivergence_congr
    {G H : Ω → Homogenization.Vec d}
    (h : G =ᵐ[μ] H) (θ : Homogenization.Vec d → ℝ) :
    realizationAbstractClose_orbitDivergenceField G θ =ᵐ[μ] realizationAbstractClose_orbitDivergenceField H θ := by
  have hh := (realizationAbstractClose_action_quasiMeasurePreserving (d := d) (μ := μ)).ae_eq_comp h
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hh] with ω hω
  exact MeasureTheory.integral_congr_ae (hω.mono fun y hy => congrArg
    (fun v => Homogenization.vecDot v (Homogenization.euclideanGradient θ y)) hy)

theorem realizationAbstractClose_integrable_orbitDivergence
    {G : Ω → Homogenization.Vec d} {θ : Homogenization.Vec d → ℝ}
    (hGm : MeasureTheory.StronglyMeasurable (realizationAbstractClose_vecField G))
    (hG : MeasureTheory.MemLp (realizationAbstractClose_vecField G) 2 μ)
    (hθc : ∀ i, Continuous (coordKernel θ i))
    (hθi : ∀ i, MeasureTheory.Integrable (coordKernel θ i) MeasureTheory.volume) :
    MeasureTheory.Integrable (realizationAbstractClose_orbitDivergenceField G θ) μ := by
  have hj : ∀ i, MeasureTheory.Integrable (fun p : Ω × Homogenization.Vec d =>
      coordKernel θ i p.2 * G (p.2 +ᵥ p.1) i) (μ.prod MeasureTheory.volume) := fun i =>
    realizationAbstractClose_integrable_prod_weighted_comp_vadd (hθc i) (hθi i)
      ((PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin d => ℝ) i).continuous.comp_stronglyMeasurable hGm)
      ((hG.eval_piLp i).integrable (by norm_num))
  have ha := MeasureTheory.ae_all_iff.mpr (fun i => (hj i).prod_right_ae)
  refine (MeasureTheory.integrable_finsetSum Finset.univ
    (fun i _ => (hj i).integral_prod_left)).congr ?_
  filter_upwards [ha] with ω hω
  simp only [realizationAbstractClose_orbitDivergenceField, vecDot_euclideanGradient_eq_sum]
  exact (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hω i)).symm

theorem realizationAbstractClose_divFree_strong
    {G : Ω → Homogenization.Vec d}
    (hGm : MeasureTheory.StronglyMeasurable (realizationAbstractClose_vecField G))
    (hG : MeasureTheory.MemLp (realizationAbstractClose_vecField G) 2 μ)
    (hGsol : hG.toLp _ ∈ stationarySolenoidalSubspace (μ := μ) (d := d))
    {θ : Homogenization.Vec d → ℝ} (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) :
    realizationAbstractClose_orbitDivergenceField G θ =ᵐ[μ] 0 := by
  have hc := fun i => continuous_coordFderiv hθ i
  have hi := fun i => integrable_coordFderiv hθ hθc i
  have hΨ := realizationAbstractClose_integrable_orbitDivergence (μ := μ) hGm hG hc hi
  apply MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ _
    exact hΨ.integrableOn
  · intro s hs _
    let f : Ω → ℝ := s.indicator (fun _ => 1)
    have hfm : Measurable f := measurable_const.indicator hs
    have hf : ∀ ω, |f ω| ≤ (1 : ℝ) := by
      intro ω
      by_cases hω : ω ∈ s <;> simp [f, hω]
    have hz := realizationAbstractClose_smear_pairing_zero hG hGsol hθ hθc hfm hf
    rw [← realizationAbstractClose_spatial_pairing_transfer hGm hG hc hi hfm hf] at hz
    rw [← MeasureTheory.integral_indicator hs]
    convert hz using 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with ω
    by_cases hω : ω ∈ s <;> simp [f, hω]

theorem realizationAbstractClose_divFreeStep :
    ∀ (G : Ω → Homogenization.Vec d) (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (G ω)) 2 μ),
      hG.toLp _ ∈ stationarySolenoidalSubspace (μ := μ) (d := d) →
      ∀ θ : Homogenization.Vec d → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ →
      ∀ᵐ ω ∂μ, ∫ x, Homogenization.vecDot (G (x +ᵥ ω)) (Homogenization.euclideanGradient θ x) = 0 := by
  intro G hG hGsol θ hθ hθc
  let K := hG.aestronglyMeasurable.mk (fun ω => Homogenization.HilbertVec.ofVec (G ω))
  let H : Ω → Homogenization.Vec d := fun ω => (K ω).toVec
  have heq : realizationAbstractClose_vecField G =ᵐ[μ] realizationAbstractClose_vecField H :=
    hG.aestronglyMeasurable.ae_eq_mk
  have hHm : MeasureTheory.StronglyMeasurable (realizationAbstractClose_vecField H) :=
    hG.aestronglyMeasurable.stronglyMeasurable_mk
  have hH : MeasureTheory.MemLp (realizationAbstractClose_vecField H) 2 μ := hG.ae_eq heq
  have hc := hG.toLp_congr hH heq
  have hHsol : hH.toLp _ ∈ stationarySolenoidalSubspace (μ := μ) (d := d) :=
    hc ▸ hGsol
  have hz := realizationAbstractClose_divFree_strong hHm hH hHsol hθ hθc
  have hv : G =ᵐ[μ] H := heq.mono fun ω hω => congrArg Homogenization.HilbertVec.toVec hω
  exact (realizationAbstractClose_orbitDivergence_congr hv θ).trans hz

/-- Joint measurability gives the abstract stationary-potential realization on each cube. -/
theorem realizationAbstractClose_exists_realization
    (M : ℕ) (F : Ω → Homogenization.Vec d → Homogenization.Vec d) (gradHatW : Ω → Homogenization.Vec d)
    (hcocycle : ∀ ω x y, F (x +ᵥ ω) y = F ω (y + x))
    (hF : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (F ω 0)) 2 μ)
    (hG : MeasureTheory.MemLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) 2 μ)
    (hproj : hG.toLp (fun ω => Homogenization.HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := μ)
        (hF.toLp (fun ω => Homogenization.HilbertVec.ofVec (F ω 0)))) :
    ∃ uReal : Ω → Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))),
      (∀ᵐ ω ∂μ, (uReal ω).grad =ᵐ[Homogenization.volumeMeasureOn (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)))]
        fun x => gradHatW (x +ᵥ ω)) ∧
      (∀ᵐ ω ∂μ, ∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ))),
        ∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot ((uReal ω).grad x) (φ.toH1Function.grad x) =
          -∫ x in Homogenization.openCubeSet (Homogenization.originCube d (M : ℤ)), Homogenization.vecDot (F ω x) (φ.toH1Function.grad x)) :=
  realizationAbstract_exists_realization_of_divFreeStep M
    realizationAbstractClose_divFreeStep (lhsClosing_countableTestGradientsDense _)
    hcocycle hF hG hproj

end SuperdiffusionCLT.Probability.Stationary
end
