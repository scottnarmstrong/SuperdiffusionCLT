/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatKernel
public import MarkovProcess.Feller.Resolvent
public import MarkovProcess.Trajectory.Dynkin

/-!
# The `d`-dimensional heat semigroup on `Vec d`

The transition semigroup of `d`-dimensional Brownian motion, assembled from the transition
kernels of `SuperdiffusionCLT.Section8.Brownian.HeatKernel`.  It is conservative, Feller,
and satisfies the intrinsic Kolmogorov moment criterion with exponents `p = 4` and `q = 2`, so
the existence-and-uniqueness theorem of `MarkovProcess.Main` applies to it.

The metric on `Vec d = Fin d → ℝ` is the coordinatewise supremum metric, so the displacement
`‖z‖` appearing in the moment bound is the supremum of the coordinate displacements; the fourth
moment of that supremum is bounded by `d` times the fourth moment of one standard normal.

Main results:

* `heatSemigroup`, `heatSemigroup_apply`: the semigroup and its transition measures.
* `isConservative_heatSemigroup`: no mass is lost.
* `kernelIntegral_heatSemigroup`: the scaling representation of the transition operator.
* `mapsC0_heatSemigroup`, `hasContinuousC0Orbits_heatSemigroup`,
  `isFellerKernelSemigroup_heatSemigroup`: the Feller property.
* `gaussianVecFourthMoment`, `hasKolmogorovMoments_heatSemigroup`: the intrinsic Kolmogorov
  moment bound with `p = 4`, `q = 2`.
* `kolmogorovRegular_heatSemigroup`: Kolmogorov regularity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Definition

variable {d : ℕ}

/-- **The `d`-dimensional heat semigroup.**  Its transition measure at time `t` from `x` is the
product of the real Gaussian laws with means the coordinates of `x` and common variance `t`. -/
def heatSemigroup (d : ℕ) : SubMarkovKernelSemigroup (Vec d) where
  kernel := heatKernel d
  measurable_kernel := measurable_heatKernelJoint d
  kernel_zero := heatKernel_zero d
  kernel_add s t := (heatKernel_comp s t).symm
  isSubMarkovKernel _ := IsSubMarkovKernel.of_isMarkovKernel _

@[simp]
theorem heatSemigroup_apply (t : ℝ≥0) (x : Vec d) :
    heatSemigroup d t x = Measure.pi fun i ↦ gaussianReal (x i) t :=
  heatKernel_apply t x

theorem heatSemigroup_apply_eq_map (t : ℝ≥0) (x : Vec d) :
    heatSemigroup d t x = (stdGaussian d).map fun z ↦ x + Real.sqrt t • z :=
  heatKernel_apply_eq_map t x

/-- The heat semigroup is conservative: every transition measure has total mass one. -/
theorem isConservative_heatSemigroup (d : ℕ) : (heatSemigroup d).IsConservative := by
  intro t x
  rw [heatSemigroup_apply]
  exact measure_univ

end Definition

section Feller

variable {d : ℕ}

private theorem measurable_add_smul (t : ℝ≥0) (x : Vec d) :
    Measurable fun z : Vec d ↦ x + Real.sqrt t • z := by
  refine Measurable.of_eval fun i ↦ ?_
  exact measurable_const.add (measurable_const.mul (measurable_pi_apply i))

/-- **The scaling representation of the heat semigroup.**  Integrating a `C₀` function against
the transition measure at time `t` from `x` is integrating its translate
`z ↦ f (x + √t • z)` against the standard Gaussian vector. -/
theorem kernelIntegral_heatSemigroup (t : ℝ≥0) (f : C₀(Vec d, ℝ)) (x : Vec d) :
    kernelIntegral (heatSemigroup d t) f x =
      ∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian d) := by
  rw [kernelIntegral, heatSemigroup_apply_eq_map]
  exact integral_map (φ := fun z : Vec d ↦ x + Real.sqrt t • z) (f := fun y : Vec d ↦ f y)
    (measurable_add_smul t x).aemeasurable f.continuous.aestronglyMeasurable

/-- A `C₀` function is bounded by its norm. -/
theorem norm_apply_le_norm_c0 (f : C₀(Vec d, ℝ)) (x : Vec d) : ‖f x‖ ≤ ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact f.toBCF.norm_coe_le_norm x

private theorem integrable_c0_comp (f : C₀(Vec d, ℝ)) (t : ℝ≥0) (x : Vec d) :
    Integrable (fun z ↦ f (x + Real.sqrt t • z)) (stdGaussian d) := by
  refine Integrable.mono' (integrable_const ‖f‖) ?_ (Filter.Eventually.of_forall fun z ↦ ?_)
  · exact (f.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact norm_apply_le_norm_c0 f _

/-- The cocompact filter of `Vec d` is countably generated: on a proper metric space it is the
filter of complements of bounded sets, which is the comap of `atTop` along the norm. -/
theorem isCountablyGenerated_cocompact (d : ℕ) :
    (Filter.cocompact (Vec d)).IsCountablyGenerated := by
  rw [← Metric.cobounded_eq_cocompact, ← comap_norm_atTop]
  infer_instance

/-- The heat semigroup maps `C₀` into itself. -/
theorem mapsC0_heatSemigroup (d : ℕ) : (heatSemigroup d).MapsC0 := by
  intro t f
  have hrep : kernelIntegral (heatSemigroup d t) f =
      fun x ↦ ∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian d) :=
    funext (kernelIntegral_heatSemigroup t f)
  rw [hrep]
  refine ⟨?_, ?_⟩
  · refine continuous_of_dominated (F := fun (x z : Vec d) ↦ f (x + Real.sqrt t • z))
      (bound := fun _ ↦ ‖f‖) ?_ ?_ (integrable_const (μ := stdGaussian d) ‖f‖) ?_
    · exact fun x ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable
    · exact fun _ ↦ Filter.Eventually.of_forall fun _ ↦ norm_apply_le_norm_c0 f _
    · exact Filter.Eventually.of_forall fun _ ↦ f.continuous.comp (by fun_prop)
  · have := isCountablyGenerated_cocompact d
    refine Filter.tendsto_iff_seq_tendsto.mpr fun u hu ↦ ?_
    have hlim : Filter.Tendsto
        (fun n ↦ ∫ z, f (u n + Real.sqrt t • z) ∂(stdGaussian d)) atTop
        (nhds (∫ _z : Vec d, (0 : ℝ) ∂(stdGaussian d))) := by
      refine tendsto_integral_of_dominated_convergence
        (F := fun (n : ℕ) (z : Vec d) ↦ f (u n + Real.sqrt t • z)) (fun _ ↦ ‖f‖)
        (fun _ ↦ (f.continuous.comp (by fun_prop)).aestronglyMeasurable)
        (integrable_const (μ := stdGaussian d) ‖f‖)
        (fun _ ↦ Filter.Eventually.of_forall fun _ ↦ norm_apply_le_norm_c0 f _)
        (Filter.Eventually.of_forall fun z ↦ ?_)
      have htranslate : Filter.Tendsto (fun y : Vec d ↦ y + Real.sqrt t • z)
          (Filter.cocompact (Vec d)) (Filter.cocompact (Vec d)) :=
        CocompactMapClass.cocompact_tendsto
          ((Homeomorph.addRight (Real.sqrt (t : ℝ) • z)).toCocompactMap)
      exact f.zero_at_infty'.comp (htranslate.comp hu)
    rw [integral_zero] at hlim
    exact hlim

/-- A finite measure on `Vec d` puts arbitrarily little mass far from the origin. -/
theorem exists_measure_norm_ge_lt (nu : Measure (Vec d)) [IsFiniteMeasure nu] {eps : ℝ}
    (heps : 0 < eps) : ∃ R : ℝ, 0 < R ∧ (nu {z : Vec d | R ≤ ‖z‖}).toReal < eps := by
  have hmeasA : ∀ n : ℕ, NullMeasurableSet {z : Vec d | (n : ℝ) ≤ ‖z‖} nu := fun n ↦
    ((isClosed_le continuous_const continuous_norm).measurableSet).nullMeasurableSet
  have hanti : Antitone fun n : ℕ ↦ {z : Vec d | (n : ℝ) ≤ ‖z‖} := by
    intro n m hnm z hz
    simp only [Set.mem_ofPred_eq] at hz ⊢
    exact le_trans (Nat.cast_le.mpr hnm) hz
  have hempty : (⋂ n : ℕ, {z : Vec d | (n : ℝ) ≤ ‖z‖}) = (∅ : Set (Vec d)) := by
    refine Set.eq_empty_of_forall_notMem fun z hz ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
    exact absurd (Set.mem_iInter.mp hz n) (not_le.mpr hn)
  have htend := tendsto_measure_iInter_atTop hmeasA hanti ⟨0, measure_ne_top nu _⟩
  rw [hempty, measure_empty] at htend
  have hev : ∀ᶠ n : ℕ in atTop, nu {z : Vec d | (n : ℝ) ≤ ‖z‖} < ENNReal.ofReal eps :=
    htend.eventually_lt_const (by simpa using heps)
  obtain ⟨n, hn⟩ := (hev.and (Filter.eventually_gt_atTop 0)).exists
  exact ⟨(n : ℝ), by exact_mod_cast hn.2, ENNReal.toReal_lt_of_lt_ofReal hn.1⟩

/-- The `C₀` orbit displacement of the heat semigroup is uniformly small over short times: for
every `ε > 0` there is a `δ > 0` such that the transition operator moves a `C₀` function by at
most `ε` in the uniform norm over every time shorter than `δ`. -/
theorem exists_norm_c0Operator_sub_le_heatSemigroup (f : C₀(Vec d, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ≥0, (h : ℝ) < delta →
      ‖(heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) h f - f‖ ≤ eps := by
  obtain ⟨delta0, hdelta0, huc⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (eps / 2) (half_pos heps)
  obtain ⟨R, hR, hRmeas⟩ := exists_measure_norm_ge_lt (stdGaussian d)
    (eps := eps / (4 * (‖f‖ + 1))) (by positivity)
  set S : Set (Vec d) := {z : Vec d | R ≤ ‖z‖} with hS
  have hSmeas : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  set bound : Vec d → ℝ := fun z ↦ eps / 2 + 2 * ‖f‖ * S.indicator (fun _ ↦ (1 : ℝ)) z with hbound
  have hindInt : Integrable (S.indicator fun _ ↦ (1 : ℝ)) (stdGaussian d) :=
    (integrable_indicator_iff hSmeas).mpr (integrableOn_const (measure_ne_top _ _))
  have hboundInt : Integrable bound (stdGaussian d) :=
    (integrable_const (μ := stdGaussian d) (eps / 2)).add (hindInt.const_mul _)
  have hboundIntegral : ∫ z, bound z ∂(stdGaussian d) ≤ eps := by
    rw [hbound, integral_add (integrable_const (μ := stdGaussian d) (eps / 2))
      (hindInt.const_mul _), integral_const, MeasureTheory.integral_const_mul,
      integral_indicator_const (1 : ℝ) hSmeas]
    have hkey : 2 * ‖f‖ * ((stdGaussian d).real S) ≤ eps / 2 := by
      have hpos : (0 : ℝ) ≤ (stdGaussian d).real S := measureReal_nonneg
      calc 2 * ‖f‖ * ((stdGaussian d).real S)
          ≤ 2 * (‖f‖ + 1) * (eps / (4 * (‖f‖ + 1))) := by
            refine mul_le_mul ?_ (le_of_lt hRmeas) hpos (by positivity)
            exact mul_le_mul_of_nonneg_left (by linarith only []) (by norm_num)
        _ = eps / 2 := by field_simp; ring
    rw [probReal_univ]
    simp only [smul_eq_mul, mul_one]
    linarith only [hkey]
  refine ⟨(delta0 / R) ^ 2, by positivity, fun h hh ↦ ?_⟩
  have hsqrt : Real.sqrt h * R < delta0 := by
    have h1 : Real.sqrt h < delta0 / R := by
      have hlt := Real.sqrt_lt_sqrt h.coe_nonneg hh
      rwa [Real.sqrt_sq (by positivity)] at hlt
    calc Real.sqrt h * R < delta0 / R * R := mul_lt_mul_of_pos_right h1 hR
      _ = delta0 := div_mul_cancel₀ delta0 (ne_of_gt hR)
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (le_of_lt heps)).2 fun x ↦ ?_
  show ‖(heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) h f x - f x‖ ≤ eps
  rw [SubMarkovKernelSemigroup.c0Operator_apply, kernelIntegral_heatSemigroup]
  have hsub : (∫ z, f (x + Real.sqrt h • z) ∂(stdGaussian d)) - f x =
      ∫ z, (f (x + Real.sqrt h • z) - f x) ∂(stdGaussian d) := by
    rw [integral_sub (integrable_c0_comp f h x) (integrable_const (f x)), integral_const,
      probReal_univ, one_smul]
  rw [hsub]
  refine le_trans (norm_integral_le_of_norm_le hboundInt
    (Filter.Eventually.of_forall fun z ↦ ?_)) hboundIntegral
  by_cases hz : z ∈ S
  · have h1 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ 2 * ‖f‖ := by
      calc ‖f (x + Real.sqrt h • z) - f x‖ ≤ ‖f (x + Real.sqrt h • z)‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add (norm_apply_le_norm_c0 f _) (norm_apply_le_norm_c0 f _)
        _ = 2 * ‖f‖ := by ring
    rw [hbound]
    simp only [Set.indicator_of_mem hz, mul_one]
    linarith only [h1, heps]
  · have hdist : dist (x + Real.sqrt h • z) x < delta0 := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      have hzR : ‖z‖ < R := lt_of_not_ge (by simpa only [hS, Set.mem_ofPred_eq] using hz)
      calc Real.sqrt h * ‖z‖ ≤ Real.sqrt h * R :=
            mul_le_mul_of_nonneg_left (le_of_lt hzR) (Real.sqrt_nonneg _)
        _ < delta0 := hsqrt
    have h2 : ‖f (x + Real.sqrt h • z) - f x‖ ≤ eps / 2 := by
      rw [← dist_eq_norm]
      exact le_of_lt (huc hdist)
    rw [hbound]
    simp only [Set.indicator_of_notMem hz, mul_zero, add_zero]
    exact h2

/-- The `C₀` orbits of the heat semigroup are continuous in time. -/
theorem hasContinuousC0Orbits_heatSemigroup (d : ℕ) :
    (heatSemigroup d).HasContinuousC0Orbits (mapsC0_heatSemigroup d) := by
  intro f
  rw [Metric.continuous_iff]
  intro b eps heps
  obtain ⟨delta, hdelta, hkey⟩ :=
    exists_norm_c0Operator_sub_le_heatSemigroup f (half_pos heps)
  refine ⟨delta, hdelta, fun a hab ↦ ?_⟩
  have hcontraction : ∀ c e : ℝ≥0, c ≤ e → (e : ℝ) - (c : ℝ) < delta →
      dist ((heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) e f)
        ((heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) c f) ≤ eps / 2 := by
    intro c e hce hlt
    have hcoe : ((e - c : ℝ≥0) : ℝ) < delta := by
      rw [NNReal.coe_sub hce]
      exact hlt
    have hop : (heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) e f =
        (heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) c
          ((heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) (e - c) f) := by
      conv_lhs => rw [← add_tsub_cancel_of_le hce]
      rw [SubMarkovKernelSemigroup.c0Operator_add]
      rfl
    rw [dist_eq_norm, hop, ← map_sub]
    calc ‖(heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) c
            ((heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) (e - c) f - f)‖
        ≤ ‖(heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) c‖ *
            ‖(heatSemigroup d).c0Operator (mapsC0_heatSemigroup d) (e - c) f - f‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (eps / 2) :=
          mul_le_mul (SubMarkovKernelSemigroup.norm_c0Operator_le _ _ c) (hkey _ hcoe)
            (norm_nonneg _) zero_le_one
      _ = eps / 2 := one_mul _
  have habs : |(a : ℝ) - (b : ℝ)| < delta := by
    rw [← NNReal.dist_eq]
    exact hab
  rcases le_total b a with hba | hab'
  · have hcb : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    have hstep := hcontraction b a hba (by
      rw [abs_of_nonneg (by linarith only [hcb])] at habs
      exact habs)
    linarith only [hstep, heps]
  · have hcb : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab'
    have hstep := hcontraction a b hab' (by
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hcb])] at habs
      exact habs)
    rw [dist_comm]
    linarith only [hstep, heps]

/-- **The `d`-dimensional heat semigroup is a Feller semigroup.** -/
theorem isFellerKernelSemigroup_heatSemigroup (d : ℕ) :
    (heatSemigroup d).IsFellerKernelSemigroup :=
  ⟨mapsC0_heatSemigroup d, hasContinuousC0Orbits_heatSemigroup d⟩

end Feller

section Moments

variable {d : ℕ}

/-- On `Vec d` the norm is the supremum of the coordinate norms, so its fourth power is at most
the sum of the fourth powers of the coordinates. -/
theorem enorm_pow_le_sum_enorm_pow (z : Vec d) :
    ‖z‖ₑ ^ (4 : ℕ) ≤ ∑ i, ‖z i‖ₑ ^ (4 : ℕ) := by
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin d)) with hemp | hne
  · have hnn : ‖z‖₊ = 0 := by
      rw [show ‖z‖₊ = Finset.univ.sup fun i ↦ ‖z i‖₊ from rfl, hemp, Finset.sup_empty]
      rfl
    have hzero : ‖z‖ₑ = 0 := by
      rw [show ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞) from rfl, hnn, ENNReal.coe_zero]
    rw [hzero]
    simp
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun j ↦ ‖z j‖₊
    have hcoord : ‖z‖ₑ = ‖z i‖ₑ := by
      rw [show ‖z‖ₑ = (‖z‖₊ : ℝ≥0∞) from rfl,
        show ‖z‖₊ = Finset.univ.sup fun j ↦ ‖z j‖₊ from rfl, hi]
      rfl
    rw [hcoord]
    exact Finset.single_le_sum (f := fun j ↦ ‖z j‖ₑ ^ (4 : ℕ)) (fun _ _ ↦ zero_le)
      (Finset.mem_univ i)

/-- The fourth absolute moment of one coordinate of the standard Gaussian vector equals the
fourth absolute moment of a standard normal, the coordinate evaluation being measure preserving
from the product law to its factor. -/
theorem lintegral_enorm_pow_eval_stdGaussian (d : ℕ) (i : Fin d) :
    ∫⁻ z, ‖z i‖ₑ ^ (4 : ℕ) ∂(stdGaussian d) = ∫⁻ u, ‖u‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) := by
  rw [stdGaussian]
  exact (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1)
    i).lintegral_comp (f := fun u : ℝ ↦ ‖u‖ₑ ^ (4 : ℕ)) (by fun_prop)

/-- **The fourth moment of the standard Gaussian vector is at most `d` times the fourth moment
of one standard normal.** -/
theorem lintegral_enorm_pow_stdGaussian_le (d : ℕ) :
    ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian d)
      ≤ (d : ℝ≥0∞) * ∫⁻ u, ‖u‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) := by
  calc ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian d)
      ≤ ∫⁻ z, ∑ i, ‖z i‖ₑ ^ (4 : ℕ) ∂(stdGaussian d) :=
        lintegral_mono enorm_pow_le_sum_enorm_pow
    _ = ∑ i : Fin d, ∫⁻ z, ‖z i‖ₑ ^ (4 : ℕ) ∂(stdGaussian d) :=
        lintegral_finsetSum _ fun i _ ↦
          (by fun_prop : Measurable fun z : Vec d ↦ ‖z i‖ₑ ^ (4 : ℕ))
    _ = ∑ _i : Fin d, ∫⁻ u, ‖u‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) :=
        Finset.sum_congr rfl fun i _ ↦ lintegral_enorm_pow_eval_stdGaussian d i
    _ = (d : ℝ≥0∞) * ∫⁻ u, ‖u‖ₑ ^ (4 : ℕ) ∂(gaussianReal 0 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The fourth moment of the standard Gaussian vector is finite. -/
theorem lintegral_enorm_pow_stdGaussian_lt_top (d : ℕ) :
    ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian d) < ⊤ :=
  lt_of_le_of_lt (lintegral_enorm_pow_stdGaussian_le d)
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top d)
      MarkovProcess.lintegral_enorm_pow_gaussianReal_lt_top)

/-- The fourth moment of the standard Gaussian vector, as a nonnegative real number. -/
def gaussianVecFourthMoment (d : ℕ) : ℝ≥0 :=
  (∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian d)).toNNReal

@[simp]
theorem coe_gaussianVecFourthMoment (d : ℕ) :
    (gaussianVecFourthMoment d : ℝ≥0∞) = ∫⁻ z, ‖z‖ₑ ^ (4 : ℕ) ∂(stdGaussian d) :=
  ENNReal.coe_toNNReal (ne_of_lt (lintegral_enorm_pow_stdGaussian_lt_top d))

/-- The fourth moment of the standard Gaussian vector grows at most linearly in the dimension. -/
theorem gaussianVecFourthMoment_le (d : ℕ) :
    (gaussianVecFourthMoment d : ℝ≥0∞)
      ≤ (d : ℝ≥0∞) * (MarkovProcess.gaussianFourthMoment : ℝ≥0∞) := by
  rw [coe_gaussianVecFourthMoment, MarkovProcess.coe_gaussianFourthMoment]
  exact lintegral_enorm_pow_stdGaussian_le d

private theorem enorm_sqrt_sq (h : ℝ≥0) : ‖Real.sqrt (h : ℝ)‖ₑ ^ (2 : ℕ) = (h : ℝ≥0∞) := by
  rw [← enorm_pow, Real.sq_sqrt h.coe_nonneg, Real.enorm_of_nonneg h.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]

/-- **The `d`-dimensional heat semigroup satisfies the Kolmogorov moment criterion** with
exponents `p = 4` and `q = 2` and the fourth moment of the standard Gaussian vector as constant:
the fourth moment of the displacement over a time step `h` is exactly `h ^ 2` times that
constant. -/
theorem hasKolmogorovMoments_heatSemigroup (d : ℕ) :
    (heatSemigroup d).HasKolmogorovMoments 4 2 (gaussianVecFourthMoment d) := by
  refine ⟨by norm_num, by norm_num, fun h y ↦ ?_⟩
  have hmeasf : Measurable fun w : Vec d ↦ edist w y ^ (4 : ℝ) :=
    (measurable_edist_left (x := y)).pow_const 4
  rw [heatSemigroup_apply_eq_map, lintegral_map hmeasf (measurable_add_smul h y)]
  have hint : ∀ z : Vec d, edist (y + Real.sqrt (h : ℝ) • z) y ^ (4 : ℝ) =
      ‖Real.sqrt (h : ℝ)‖ₑ ^ (4 : ℕ) * ‖z‖ₑ ^ (4 : ℕ) := by
    intro z
    rw [ENNReal.rpow_ofNat, edist_eq_enorm_sub, add_sub_cancel_left, enorm_smul, mul_pow]
  simp_rw [hint]
  rw [lintegral_const_mul _ (by fun_prop), coe_gaussianVecFourthMoment, ENNReal.rpow_ofNat,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, enorm_sqrt_sq]
  exact le_of_eq (mul_comm _ _)

/-- The heat semigroup is Kolmogorov regular, by its moment bound. -/
theorem kolmogorovRegular_heatSemigroup (d : ℕ) :
    (heatSemigroup d).KolmogorovRegular (isConservative_heatSemigroup d) :=
  SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
    (isConservative_heatSemigroup d) (hasKolmogorovMoments_heatSemigroup d)

end Moments

end

end SuperdiffusionCLT.Section8.Brownian
