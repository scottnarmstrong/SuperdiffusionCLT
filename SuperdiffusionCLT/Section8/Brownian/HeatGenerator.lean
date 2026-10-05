/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatSemigroup
public import SuperdiffusionCLT.Section8.Brownian.TaylorGaussian

/-!
# Half the Laplacian generates the `d`-dimensional heat semigroup

Half the Laplacian is the infinitesimal generator of the heat semigroup on `Vec d`.  Writing
`heatKernel d t x` for the Gaussian law on `Vec d` with mean `x` and variance `t` in every
coordinate, and `x ↦ ∫ f d heatKernel d t x` for the Gaussian average of `f` at scale `t`, the
difference quotient `t⁻¹ (∫ f d heatKernel d t x - f x)` converges as `t → 0⁺` to half the
Laplacian of `f` at `x`, uniformly in the centre `x`.

The argument is the classical one, run in `d` variables.  The scaling representation
`heatKernel d t x = (stdGaussian d).map (fun z ↦ x + √t • z)` reduces every average to the
standard Gaussian vector, and the second-order Taylor estimate of `TaylorGaussian` splits the
increment into a first-order term whose Gaussian average vanishes, a second-order term whose
Gaussian average is `t` times half the Laplacian, and a remainder controlled by the modulus of
continuity of the second derivative on the bulk of the law and by a fourth moment on the tail.
Neither bound depends on `x`, whence the uniformity.

Main results:

* `vecLaplacian`: the trace of the second derivative on `Vec d`.
* `tendstoUniformly_gaussianAverage_sub_div`: the limit above, as a `TendstoUniformly`
  statement.
* `gaussianAverage`, `tendsto_gaussianAverage_sub_div`: the Gaussian average of a continuous
  function vanishing at infinity, and the same limit read in the `C₀` norm.
* `tendsto_differenceQuotient_heatSemigroup`, `mem_generatorDomain_heatSemigroup` and
  `generator_heatSemigroup`: twice continuously differentiable `C₀` functions whose second
  derivative vanishes at infinity lie in the generator domain of the `C₀` semigroup of the heat
  semigroup, and the generator is half the Laplacian there.

No partial differential equation is solved and the generator domain is not characterized, only
contained.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Filter Homogenization MeasureTheory ProbabilityTheory Topology
open MarkovProcess
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

section Laplacian

variable {d : ℕ}

/-- **The Laplacian on `Vec d`**: the trace of the second derivative, that is the sum of the
second derivatives along the coordinate directions. -/
def vecLaplacian (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, iteratedFDeriv ℝ 2 f x ![Pi.single i 1, Pi.single i 1]

/-- The Laplacian read through the derivative of the derivative. -/
theorem vecLaplacian_eq_sum_fderiv (f : Vec d → ℝ) (x : Vec d) :
    vecLaplacian f x = ∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1) := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  simp

/-- The `n`-th moment of the norm of the standard Gaussian vector. -/
def gaussianVecMoment (d n : ℕ) : ℝ := ∫ z : Vec d, ‖z‖ ^ n ∂(stdGaussian d)

theorem gaussianVecMoment_nonneg (d n : ℕ) : 0 ≤ gaussianVecMoment d n :=
  integral_nonneg fun z ↦ by positivity

/-- The scaling representation of the Gaussian average of a continuous function. -/
theorem integral_heatKernel_eq {f : Vec d → ℝ} (hf : Continuous f) (t : ℝ≥0) (x : Vec d) :
    ∫ y, f y ∂(heatKernel d t x) = ∫ z, f (x + Real.sqrt t • z) ∂(stdGaussian d) := by
  rw [heatKernel_apply_eq_map]
  exact integral_map (φ := fun z : Vec d ↦ x + Real.sqrt t • z) (f := fun y : Vec d ↦ f y)
    (by fun_prop) hf.aestronglyMeasurable

/-- The transition operator of the heat semigroup is the Gaussian average. -/
theorem kernelIntegral_heatSemigroup_eq (t : ℝ≥0) (f : Vec d → ℝ) (x : Vec d) :
    kernelIntegral (heatSemigroup d t) f x = ∫ y, f y ∂(heatKernel d t x) := rfl

end Laplacian

section Estimate

variable {d : ℕ}

/-- A pure-algebra step: away from the origin a constant is dominated by a quadratic. -/
private theorem le_mul_sq_div {M a b : ℝ} (hM : 0 ≤ M) (hb : 0 < b) (hab : b ≤ a) :
    M ≤ M * a ^ 2 / b ^ 2 := by
  have hsq : b ^ 2 ≤ a ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self hb.le hab
  rw [le_div_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left hsq hM

/-- **The quantitative estimate.**  If the second derivative of `f` is bounded by `M` in operator
norm and varies by at most `eps` over distances smaller than `delta`, then the Gaussian
difference quotient at scale `t` differs from half the Laplacian by at most a fixed multiple of
`eps` plus a term of order `t`, uniformly in the centre `x`. -/
private theorem abs_gaussianQuotient_sub_le {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    {bd M eps delta : ℝ} (hbd : ∀ y, |f y| ≤ bd)
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ M) (heps : 0 ≤ eps) (hdelta : 0 < delta)
    (hunif : ∀ u v : Vec d, ‖u - v‖ < delta →
      ‖iteratedFDeriv ℝ 2 f u - iteratedFDeriv ℝ 2 f v‖ ≤ eps)
    {t : ℝ≥0} (ht : 0 < (t : ℝ)) (x : Vec d) :
    |(t : ℝ)⁻¹ * (∫ y, f y ∂(heatKernel d t x) - f x) - vecLaplacian f x / 2| ≤
      eps * gaussianVecMoment d 2
        + 2 * M * (t : ℝ) * gaussianVecMoment d 4 / delta ^ 2 := by
  have htne : (t : ℝ) ≠ 0 := ht.ne'
  have hdne : delta ≠ 0 := hdelta.ne'
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  set sigma := Real.sqrt (t : ℝ) with hsigmadef
  have hsigmann : 0 ≤ sigma := Real.sqrt_nonneg _
  have hsigma2 : sigma ^ 2 = (t : ℝ) := Real.sq_sqrt t.coe_nonneg
  have hcont : Continuous f := hf.continuous
  have hchange : ∫ y, f y ∂(heatKernel d t x) = ∫ z, f (x + sigma • z) ∂(stdGaussian d) :=
    integral_heatKernel_eq hcont t x
  set E : Vec d → ℝ := fun z ↦
    f (x + sigma • z) - f x - fderiv ℝ f x (sigma • z)
      - iteratedFDeriv ℝ 2 f x ![sigma • z, sigma • z] / 2 with hEdef
  have hEeq : ∀ z : Vec d, E z = f (x + sigma • z) - f x - sigma * fderiv ℝ f x z
      - (t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z := by
    intro z
    have h1 : fderiv ℝ f x (sigma • z) = sigma * fderiv ℝ f x z := by
      rw [map_smul, smul_eq_mul]
    have hb : fderiv ℝ (fderiv ℝ f) x (sigma • z) (sigma • z)
        = sigma ^ 2 * fderiv ℝ (fderiv ℝ f) x z z := by
      rw [map_smul (fderiv ℝ (fderiv ℝ f) x) sigma z, smul_apply, map_smul,
        smul_eq_mul, smul_eq_mul]
      ring
    have h2 : iteratedFDeriv ℝ 2 f x ![sigma • z, sigma • z]
        = (t : ℝ) * fderiv ℝ (fderiv ℝ f) x z z := by
      rw [iteratedFDeriv_two_apply]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hb, hsigma2]
    rw [hEdef]
    simp only [h1, h2]
    ring
  have hshift : Integrable (fun z : Vec d ↦ f (x + sigma • z)) (stdGaussian d) := by
    refine Integrable.mono' (integrable_const bd)
      ((hcont.comp (by fun_prop)).aestronglyMeasurable) ?_
    filter_upwards with z
    simpa using hbd (x + sigma • z)
  have hlin : Integrable (fun z : Vec d ↦ sigma * fderiv ℝ f x z) (stdGaussian d) :=
    (integrable_clm_stdGaussian (fderiv ℝ f x)).const_mul sigma
  have hquad : Integrable
      (fun z : Vec d ↦ (t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z) (stdGaussian d) :=
    (integrable_bilin_stdGaussian (fderiv ℝ (fderiv ℝ f) x)).const_mul _
  have hEint : Integrable E (stdGaussian d) := by
    refine Integrable.congr (((hshift.sub (integrable_const (f x))).sub hlin).sub hquad) ?_
    filter_upwards with z
    exact (hEeq z).symm
  have hI1 : ∫ z : Vec d, sigma * fderiv ℝ f x z ∂(stdGaussian d) = 0 := by
    rw [integral_const_mul, integral_clm_stdGaussian, mul_zero]
  have hI2 : ∫ z : Vec d, (t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z ∂(stdGaussian d)
      = (t : ℝ) / 2 * vecLaplacian f x := by
    rw [integral_const_mul, integral_bilin_stdGaussian, vecLaplacian_eq_sum_fderiv]
  have hE : ∫ z, E z ∂(stdGaussian d)
      = (∫ z, f (x + sigma • z) ∂(stdGaussian d)) - f x - (t : ℝ) / 2 * vecLaplacian f x := by
    have e0 : ∫ z, E z ∂(stdGaussian d)
        = ∫ z : Vec d, (f (x + sigma • z) - f x - sigma * fderiv ℝ f x z
            - (t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z) ∂(stdGaussian d) :=
      integral_congr_ae (Filter.Eventually.of_forall hEeq)
    have e1 : ∫ z : Vec d, (f (x + sigma • z) - f x - sigma * fderiv ℝ f x z
          - (t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z) ∂(stdGaussian d)
        = (∫ z : Vec d, (f (x + sigma • z) - f x - sigma * fderiv ℝ f x z) ∂(stdGaussian d))
          - ∫ z : Vec d, ((t : ℝ) / 2 * fderiv ℝ (fderiv ℝ f) x z z) ∂(stdGaussian d) :=
      integral_sub ((hshift.sub (integrable_const (f x))).sub hlin) hquad
    have e2 : ∫ z : Vec d, (f (x + sigma • z) - f x - sigma * fderiv ℝ f x z) ∂(stdGaussian d)
        = (∫ z : Vec d, (f (x + sigma • z) - f x) ∂(stdGaussian d))
          - ∫ z : Vec d, (sigma * fderiv ℝ f x z) ∂(stdGaussian d) :=
      integral_sub (hshift.sub (integrable_const (f x))) hlin
    have e3 : ∫ z : Vec d, (f (x + sigma • z) - f x) ∂(stdGaussian d)
        = (∫ z, f (x + sigma • z) ∂(stdGaussian d)) - ∫ _z : Vec d, f x ∂(stdGaussian d) :=
      integral_sub hshift (integrable_const (f x))
    have e4 : ∫ _z : Vec d, f x ∂(stdGaussian d) = f x := by simp
    rw [e0, e1, e2, e3, e4, hI1, hI2]
    ring
  have hEbound : ∀ z : Vec d, |E z| ≤
      eps * (t : ℝ) * ‖z‖ ^ 2 + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * ‖z‖ ^ 4 := by
    intro z
    have hnorm : ‖sigma • z‖ = sigma * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsigmann]
    have hnormsq : ‖sigma • z‖ ^ 2 = (t : ℝ) * ‖z‖ ^ 2 := by
      rw [hnorm, mul_pow, hsigma2]
    have hCbound : ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ 2 f (x + s • (sigma • z)) - iteratedFDeriv ℝ 2 f x‖ ≤
          eps + 2 * M * ‖sigma • z‖ ^ 2 / delta ^ 2 := by
      intro s hs
      have hpos : 0 ≤ 2 * M * ‖sigma • z‖ ^ 2 / delta ^ 2 := by positivity
      rcases lt_or_ge ‖sigma • z‖ delta with hlt | hge
      · have hclose : ‖x + s • (sigma • z) - x‖ < delta := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
          calc s * ‖sigma • z‖ ≤ 1 * ‖sigma • z‖ :=
                mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
            _ = ‖sigma • z‖ := one_mul _
            _ < delta := hlt
        have := hunif _ _ hclose
        linarith only [this, hpos]
      · have habs : ‖iteratedFDeriv ℝ 2 f (x + s • (sigma • z)) - iteratedFDeriv ℝ 2 f x‖
            ≤ 2 * M := by
          calc ‖iteratedFDeriv ℝ 2 f (x + s • (sigma • z)) - iteratedFDeriv ℝ 2 f x‖
              ≤ ‖iteratedFDeriv ℝ 2 f (x + s • (sigma • z))‖ + ‖iteratedFDeriv ℝ 2 f x‖ :=
                norm_sub_le _ _
            _ ≤ M + M := add_le_add (hM _) (hM _)
            _ = 2 * M := by ring
        have hstep : 2 * M ≤ 2 * M * ‖sigma • z‖ ^ 2 / delta ^ 2 :=
          le_mul_sq_div (by linarith only [hMnn]) hdelta hge
        linarith only [habs, hstep, heps]
    have htaylor := abs_sub_taylor_two_le hf x (sigma • z) _ hCbound
    refine le_trans htaylor (le_of_eq ?_)
    rw [hnormsq]
    field_simp
  have hboundInt : Integrable
      (fun z : Vec d ↦ eps * (t : ℝ) * ‖z‖ ^ 2 + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * ‖z‖ ^ 4)
      (stdGaussian d) :=
    ((integrable_norm_pow_stdGaussian d 2).const_mul _).add
      ((integrable_norm_pow_stdGaussian d 4).const_mul _)
  have hIabs : |∫ z, E z ∂(stdGaussian d)| ≤
      eps * (t : ℝ) * gaussianVecMoment d 2
        + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * gaussianVecMoment d 4 := by
    calc |∫ z, E z ∂(stdGaussian d)| ≤ ∫ z, |E z| ∂(stdGaussian d) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z : Vec d,
            (eps * (t : ℝ) * ‖z‖ ^ 2 + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * ‖z‖ ^ 4)
            ∂(stdGaussian d) := integral_mono hEint.abs hboundInt hEbound
      _ = eps * (t : ℝ) * gaussianVecMoment d 2
            + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * gaussianVecMoment d 4 := by
          rw [integral_add ((integrable_norm_pow_stdGaussian d 2).const_mul _)
            ((integrable_norm_pow_stdGaussian d 4).const_mul _), integral_const_mul,
            integral_const_mul, gaussianVecMoment, gaussianVecMoment]
  have hkey : (t : ℝ)⁻¹ * (∫ y, f y ∂(heatKernel d t x) - f x) - vecLaplacian f x / 2
      = (t : ℝ)⁻¹ * ∫ z, E z ∂(stdGaussian d) := by
    rw [hchange, hE]
    field_simp
  rw [hkey, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht.le)]
  calc (t : ℝ)⁻¹ * |∫ z, E z ∂(stdGaussian d)|
      ≤ (t : ℝ)⁻¹ * (eps * (t : ℝ) * gaussianVecMoment d 2
          + 2 * M * (t : ℝ) ^ 2 / delta ^ 2 * gaussianVecMoment d 4) :=
        mul_le_mul_of_nonneg_left hIabs (inv_nonneg.mpr ht.le)
    _ = eps * gaussianVecMoment d 2
          + 2 * M * (t : ℝ) * gaussianVecMoment d 4 / delta ^ 2 := by
        field_simp

end Estimate

section Uniform

variable {d : ℕ}

/-- A continuous function vanishing at infinity is bounded and uniformly continuous. -/
private theorem exists_bound_modulus {G : Type*} [NormedAddCommGroup G] {g : Vec d → G}
    (hg : Continuous g) (hg0 : Tendsto g (cocompact (Vec d)) (𝓝 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ (∀ y, ‖g y‖ ≤ M) ∧
      ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
        ∀ u v : Vec d, ‖u - v‖ < delta → ‖g u - g v‖ ≤ eps := by
  set G0 : C₀(Vec d, G) := ⟨⟨g, hg⟩, hg0⟩ with hG0
  refine ⟨‖G0‖, norm_nonneg _, fun y ↦ ?_, fun eps heps ↦ ?_⟩
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact G0.toBCF.norm_coe_le_norm y
  · obtain ⟨delta, hdelta, hd⟩ := Metric.uniformContinuous_iff.mp
      (ZeroAtInftyContinuousMap.uniformContinuous G0) eps heps
    refine ⟨delta, hdelta, fun u v huv ↦ le_of_lt ?_⟩
    have hres := hd (a := u) (b := v) (by rwa [dist_eq_norm])
    rwa [dist_eq_norm] at hres

/-- **Half the Laplacian generates the Gaussian averages.**  For a twice continuously
differentiable `f` whose value and second derivative vanish at infinity, the difference quotient
of the Gaussian average of `f` at scale `t`, taken at the centre `x`, converges as `t → 0⁺` to
half the Laplacian of `f` at `x`, uniformly in `x`. -/
theorem tendstoUniformly_gaussianAverage_sub_div {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f)
    (hf0 : Tendsto f (cocompact (Vec d)) (𝓝 0))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 f) (cocompact (Vec d)) (𝓝 0)) :
    TendstoUniformly (fun (t : ℝ≥0) (x : Vec d) ↦
        (t : ℝ)⁻¹ * (∫ y, f y ∂(heatKernel d t x) - f x))
      (fun x ↦ vecLaplacian f x / 2) (𝓝[>] 0) := by
  obtain ⟨bd, -, hbd, -⟩ := exists_bound_modulus hf.continuous hf0
  obtain ⟨M, hMnn, hM, hmod⟩ :=
    exists_bound_modulus (hf.continuous_iteratedFDeriv (by norm_num)) hf2
  have hbd' : ∀ y, |f y| ≤ bd := fun y ↦ by simpa only [Real.norm_eq_abs] using hbd y
  rw [Metric.tendstoUniformly_iff]
  intro eps heps
  have hm2 : 0 ≤ gaussianVecMoment d 2 := gaussianVecMoment_nonneg d 2
  have hm4 : 0 ≤ gaussianVecMoment d 4 := gaussianVecMoment_nonneg d 4
  have hm2pos : 0 < gaussianVecMoment d 2 + 1 := by linarith only [hm2]
  set eps' : ℝ := eps / (2 * (gaussianVecMoment d 2 + 1)) with heps'def
  have heps'pos : 0 < eps' := div_pos heps (by linarith only [hm2pos])
  obtain ⟨delta, hdelta, hdelta'⟩ := hmod eps' heps'pos
  have hK : 0 < M * gaussianVecMoment d 4 + 1 := by positivity
  set T : ℝ := eps * delta ^ 2 / (4 * (M * gaussianVecMoment d 4 + 1)) with hTdef
  have hTpos : 0 < T := div_pos (mul_pos heps (pow_pos hdelta 2)) (by linarith only [hK])
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, (t : ℝ) < T := by
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ) < T} :=
      isOpen_lt NNReal.continuous_coe continuous_const
    have hmem : (0 : ℝ≥0) ∈ {t : ℝ≥0 | (t : ℝ) < T} := by simpa using hTpos
    exact mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)
  filter_upwards [hev, self_mem_nhdsWithin] with t htT htpos
  intro x
  have htpos' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr htpos
  have hmain := abs_gaussianQuotient_sub_le hf hbd' hM heps'pos.le hdelta hdelta' htpos' x
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt hmain ?_
  have hA : eps' * gaussianVecMoment d 2 ≤ eps / 2 := by
    have h1 : eps' * gaussianVecMoment d 2 ≤ eps' * (gaussianVecMoment d 2 + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) heps'pos.le
    have h2 : eps' * (gaussianVecMoment d 2 + 1) = eps / 2 := by
      rw [heps'def]
      field_simp
    linarith only [h1, h2]
  have hB : 2 * M * (t : ℝ) * gaussianVecMoment d 4 / delta ^ 2 < eps / 2 := by
    rw [div_lt_iff₀ (pow_pos hdelta 2)]
    have h1 : 2 * (M * gaussianVecMoment d 4) * (t : ℝ)
        ≤ 2 * (M * gaussianVecMoment d 4 + 1) * (t : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hK]) htpos'.le
    have h2 : 2 * (M * gaussianVecMoment d 4 + 1) * (t : ℝ)
        < 2 * (M * gaussianVecMoment d 4 + 1) * T :=
      mul_lt_mul_of_pos_left htT (by linarith only [hK])
    have h3 : 2 * (M * gaussianVecMoment d 4 + 1) * T = eps * delta ^ 2 / 2 := by
      rw [hTdef]
      field_simp
      ring
    linarith only [h1, h2, h3]
  linarith only [hA, hB]

end Uniform

section C0

variable {d : ℕ}

/-- **The Gaussian average of a `C₀` function.**  At scale `t` it is the integral of `f` against
the `d`-dimensional heat kernel started at `x`; at `t = 0` it is `f` itself. -/
def gaussianAverage (d : ℕ) (f : C₀(Vec d, ℝ)) (t : ℝ≥0) : C₀(Vec d, ℝ) :=
  (heatSemigroup d).c0KernelIntegral (mapsC0_heatSemigroup d) t f

@[simp]
theorem gaussianAverage_apply (f : C₀(Vec d, ℝ)) (t : ℝ≥0) (x : Vec d) :
    gaussianAverage d f t x = ∫ y, f y ∂(heatKernel d t x) := rfl

/-- **Half the Laplacian generates the Gaussian averages, in the `C₀` norm.**  If `f` is a `C₀`
function which is twice continuously differentiable, whose second derivative vanishes at
infinity, and whose Laplacian is the `C₀` function `g`, then the difference quotients of the
Gaussian averages of `f` converge in the `C₀` norm to `g / 2` as the scale tends to zero. -/
theorem tendsto_gaussianAverage_sub_div (f g : C₀(Vec d, ℝ)) (hf : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 (f : Vec d → ℝ)) (cocompact (Vec d)) (𝓝 0))
    (hg : ∀ x, g x = vecLaplacian (f : Vec d → ℝ) x) :
    Tendsto (fun t : ℝ≥0 ↦ (t : ℝ)⁻¹ • (gaussianAverage d f t - f)) (𝓝[>] 0)
      (𝓝 ((2 : ℝ)⁻¹ • g)) := by
  have huniform := tendstoUniformly_gaussianAverage_sub_div hf f.zero_at_infty' hf2
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  have hlim : (fun x : Vec d ↦ vecLaplacian (f : Vec d → ℝ) x / 2) = ⇑((2 : ℝ)⁻¹ • g) := by
    funext x
    rw [← hg x]
    simp [div_eq_inv_mul]
  have hfun : (fun t : ℝ≥0 ↦ ⇑((t : ℝ)⁻¹ • (gaussianAverage d f t - f)))
      = fun (t : ℝ≥0) (x : Vec d) ↦ (t : ℝ)⁻¹ * (∫ y, f y ∂(heatKernel d t x) - f x) := by
    funext t x
    simp
  rw [← hlim, hfun]
  exact huniform

/-- The `C₀` semigroup of the heat semigroup acts by Gaussian averages. -/
theorem c0Semigroup_heatSemigroup_apply (f : C₀(Vec d, ℝ)) (t : ℝ≥0) :
    (isFellerKernelSemigroup_heatSemigroup d).c0Semigroup t f = gaussianAverage d f t :=
  ZeroAtInftyContinuousMap.ext fun _ ↦ rfl

/-- The difference quotients of the heat semigroup converge, in the `C₀` norm, to half the
Laplacian. -/
theorem tendsto_differenceQuotient_heatSemigroup (f g : C₀(Vec d, ℝ))
    (hf : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 (f : Vec d → ℝ)) (cocompact (Vec d)) (𝓝 0))
    (hg : ∀ x, g x = vecLaplacian (f : Vec d → ℝ) x) :
    Tendsto (fun t : ℝ≥0 ↦
        (t : ℝ)⁻¹ • ((isFellerKernelSemigroup_heatSemigroup d).c0Semigroup t f - f))
      (𝓝[>] 0) (𝓝 ((2 : ℝ)⁻¹ • g)) := by
  simpa only [c0Semigroup_heatSemigroup_apply] using
    tendsto_gaussianAverage_sub_div f g hf hf2 hg

/-- **Twice continuously differentiable `C₀` functions with second derivative vanishing at
infinity lie in the generator domain of the `d`-dimensional heat semigroup.** -/
theorem mem_generatorDomain_heatSemigroup (f g : C₀(Vec d, ℝ))
    (hf : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 (f : Vec d → ℝ)) (cocompact (Vec d)) (𝓝 0))
    (hg : ∀ x, g x = vecLaplacian (f : Vec d → ℝ) x) :
    f ∈ (isFellerKernelSemigroup_heatSemigroup d).c0Semigroup.generatorDomain :=
  (isFellerKernelSemigroup_heatSemigroup d).c0Semigroup.mem_generatorDomain_of_tendsto
    (tendsto_differenceQuotient_heatSemigroup f g hf hf2 hg)

/-- **The generator of the `d`-dimensional heat semigroup is half the Laplacian**: on a twice
continuously differentiable `C₀` function `f` whose second derivative vanishes at infinity and
whose Laplacian is the `C₀` function `g`, the generator of the `C₀` semigroup of `d`-dimensional
Brownian motion is `g / 2`. -/
theorem generator_heatSemigroup (f g : C₀(Vec d, ℝ)) (hf : ContDiff ℝ 2 (f : Vec d → ℝ))
    (hf2 : Tendsto (iteratedFDeriv ℝ 2 (f : Vec d → ℝ)) (cocompact (Vec d)) (𝓝 0))
    (hg : ∀ x, g x = vecLaplacian (f : Vec d → ℝ) x) :
    (isFellerKernelSemigroup_heatSemigroup d).c0Semigroup.generator
      ⟨f, mem_generatorDomain_heatSemigroup f g hf hf2 hg⟩ = (2 : ℝ)⁻¹ • g :=
  (isFellerKernelSemigroup_heatSemigroup d).c0Semigroup.generator_mk_eq
    (tendsto_differenceQuotient_heatSemigroup f g hf hf2 hg)

end C0

end

end SuperdiffusionCLT.Section8.Brownian
