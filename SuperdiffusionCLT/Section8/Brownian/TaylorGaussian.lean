/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Brownian.HeatKernel
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.IntegrableExpMul

/-!
# A second-order Taylor estimate and the second moments of the standard Gaussian vector

Two analytic facts about the heat semigroup on `Vec d = Fin d → ℝ`, both stated in the
quantitative, centre-uniform form that an infinitesimal generator computation needs.

The first is a second-order Taylor estimate for a twice continuously differentiable function on
a real normed space, with the remainder controlled by the increment of the second derivative
along the segment joining the centre to the endpoint.  It is proved by restricting to that
segment and running the mean value inequality twice, so the constant is explicit and does not
depend on the centre.

The second is the pair of first and second moments of the standard Gaussian vector: coordinates
have mean zero, and the second moment of a pair of coordinates is `1` on the diagonal and `0`
off it.  These follow from the one-dimensional Gaussian moments through Fubini for a product of
functions of separate coordinates.  Their invariant consequence is the identity
`∫ z, B z z = ∑ i, B (e i) (e i)` for a continuous bilinear form `B`: the Gaussian average of a
quadratic form is its trace.

Main results:

* `abs_sub_taylor_two_le`: the second-order Taylor estimate with a modulus.
* `integrable_norm_pow_stdGaussian`: all polynomial moments of the standard Gaussian vector are
  finite.
* `integral_eval_stdGaussian`, `integral_eval_mul_eval_stdGaussian`: the first and second
  moments of the coordinates.
* `integrable_clm_stdGaussian`, `integrable_bilin_stdGaussian`: continuous linear and quadratic
  forms are Gaussian integrable.
* `integral_clm_stdGaussian`, `integral_bilin_stdGaussian`: the Gaussian average of a continuous
  linear form vanishes, and the Gaussian average of a continuous quadratic form is its trace.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Brownian

open Homogenization MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order Taylor estimate with a modulus.**  If the second derivative of `f` differs
from its value at `x` by at most `C` in operator norm everywhere on the segment from `x` to
`x + h`, then the second-order Taylor polynomial of `f` at `x` approximates `f (x + h)` to
within `C ‖h‖ ^ 2`. -/
theorem abs_sub_taylor_two_le {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x h : E) (C : ℝ)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 f (x + s • h) - iteratedFDeriv ℝ 2 f x‖ ≤ C) :
    |f (x + h) - f x - fderiv ℝ f x h - iteratedFDeriv ℝ 2 f x ![h, h] / 2| ≤ C * ‖h‖ ^ 2 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right le_rfl
  have hddf : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable (by simp)
  set D : E → ℝ := fun y ↦ iteratedFDeriv ℝ 2 f y ![h, h] with hDdef
  have hDeq : ∀ y : E, D y = fderiv ℝ (fderiv ℝ f) y h h := by
    intro y
    rw [hDdef]
    simpa using iteratedFDeriv_two_apply f y ![h, h]
  have hinner : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ x + s • h) h s := by
    intro s
    simpa using (((hasDerivAt_id s).smul_const h).const_add x)
  set F : ℝ → ℝ :=
    fun s ↦ f (x + s • h) - f x - s * fderiv ℝ f x h - s ^ 2 * (D x / 2) with hFdef
  set G : ℝ → ℝ := fun s ↦ fderiv ℝ f (x + s • h) h - fderiv ℝ f x h - s * D x with hGdef
  have hFderiv : ∀ s : ℝ, HasDerivAt F (G s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ ↦ f (x + s • h)) (fderiv ℝ f (x + s • h) h) s :=
      (hdf (x + s • h)).hasFDerivAt.comp_hasDerivAt s (hinner s)
    have h2 : HasDerivAt (fun s : ℝ ↦ s * fderiv ℝ f x h) (fderiv ℝ f x h) s := by
      simpa using (hasDerivAt_id s).mul_const (fderiv ℝ f x h)
    have h3 : HasDerivAt (fun s : ℝ ↦ s ^ 2 * (D x / 2)) (2 * s * (D x / 2)) s := by
      have hp : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
      exact hp.mul_const _
    have hsum := ((h1.sub_const (f x)).sub h2).sub h3
    convert hsum using 1
    rw [hGdef]
    ring
  have hGderiv : ∀ s : ℝ, HasDerivAt G (D (x + s • h) - D x) s := by
    intro s
    have hc : HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • h))
        (fderiv ℝ (fderiv ℝ f) (x + s • h) h) s :=
      (hddf (x + s • h)).hasFDerivAt.comp_hasDerivAt s (hinner s)
    have h1 := hc.clm_apply (hasDerivAt_const s h)
    have h2 : HasDerivAt (fun s : ℝ ↦ s * D x) (D x) s := by
      simpa using (hasDerivAt_id s).mul_const (D x)
    have hsum := (h1.sub_const (fderiv ℝ f x h)).sub h2
    convert hsum using 1
    rw [hDeq (x + s • h)]
    simp
  have hCnn : 0 ≤ C := by
    have h0 := hC 0 (by norm_num)
    simpa using h0
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) 1) := convex_Icc 0 1
  have hG0 : G 0 = 0 := by simp [hGdef]
  have hF0 : F 0 = 0 := by simp [hFdef]
  have hGbound : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖G s‖ ≤ C * ‖h‖ ^ 2 := by
    intro s hs
    have hkey : ‖G s - G 0‖ ≤ C * ‖h‖ ^ 2 * ‖s - 0‖ := by
      refine hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ ↦ (hGderiv u).hasDerivWithinAt) (fun u hu ↦ ?_) (by norm_num) hs
      have hsub : D (x + u • h) - D x
          = (iteratedFDeriv ℝ 2 f (x + u • h) - iteratedFDeriv ℝ 2 f x) ![h, h] := by
        rw [sub_apply]
      rw [hsub]
      refine le_trans (ContinuousMultilinearMap.le_opNorm _ _) ?_
      have hprod : ∏ i : Fin 2, ‖(![h, h] : Fin 2 → E) i‖ = ‖h‖ ^ 2 := by
        rw [Fin.prod_univ_two]
        simp [sq]
      rw [hprod]
      exact mul_le_mul_of_nonneg_right (hC u hu) (by positivity)
    rw [hG0, sub_zero] at hkey
    refine hkey.trans ?_
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1]
    have hnn : 0 ≤ C * ‖h‖ ^ 2 := by positivity
    calc C * ‖h‖ ^ 2 * s ≤ C * ‖h‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hs.2 hnn
      _ = C * ‖h‖ ^ 2 := mul_one _
  have hFbound : ‖F 1 - F 0‖ ≤ C * ‖h‖ ^ 2 * ‖(1 : ℝ) - 0‖ :=
    hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ ↦ (hFderiv u).hasDerivWithinAt) hGbound (by norm_num) (by norm_num)
  rw [hF0, sub_zero, Real.norm_eq_abs] at hFbound
  simp only [hFdef, one_smul, one_mul, one_pow] at hFbound
  calc |f (x + h) - f x - fderiv ℝ f x h - D x / 2|
      ≤ C * ‖h‖ ^ 2 * ‖(1 : ℝ) - 0‖ := by simpa using hFbound
    _ = C * ‖h‖ ^ 2 := by norm_num

end Taylor

section Moments

variable {d : ℕ}

/-- Every polynomial moment of a standard normal is finite. -/
theorem integrable_pow_gaussianReal (n : ℕ) :
    Integrable (fun u : ℝ ↦ u ^ n) (gaussianReal 0 1) :=
  integrable_pow_of_mem_interior_integrableExpSet (by simp) n

/-- Every polynomial moment of one coordinate of the standard Gaussian vector is finite. -/
theorem integrable_eval_pow_stdGaussian (d : ℕ) (i : Fin d) (n : ℕ) :
    Integrable (fun z : Vec d ↦ z i ^ n) (stdGaussian d) := by
  rw [stdGaussian]
  exact MeasureTheory.integrable_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (i := i)
    (f := fun u : ℝ ↦ u ^ n) (integrable_pow_gaussianReal n)

/-- A polynomial moment of one coordinate of the standard Gaussian vector is the corresponding
moment of a standard normal, the coordinate evaluation being measure preserving from the product
law to its factor. -/
theorem integral_eval_pow_stdGaussian (d : ℕ) (i : Fin d) (n : ℕ) :
    ∫ z : Vec d, z i ^ n ∂(stdGaussian d) = ∫ u : ℝ, u ^ n ∂(gaussianReal 0 1) := by
  rw [stdGaussian]
  exact MeasureTheory.integral_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (i := i)
    (f := fun u : ℝ ↦ u ^ n) (by fun_prop)

/-- On `Vec d` the norm is the supremum of the coordinate norms, so any of its powers is at most
one plus the sum of the corresponding powers of the coordinates.  The extra `1` covers the empty
index type, where the norm vanishes but the zeroth power does not. -/
theorem norm_pow_le_sum_abs_pow (n : ℕ) (z : Vec d) : ‖z‖ ^ n ≤ 1 + ∑ i, |z i| ^ n := by
  have hsum : (0 : ℝ) ≤ ∑ i, |z i| ^ n := Finset.sum_nonneg fun i _ ↦ by positivity
  rcases Finset.eq_empty_or_nonempty (Finset.univ : Finset (Fin d)) with hemp | hne
  · have hnn : ‖z‖₊ = 0 := by
      rw [show ‖z‖₊ = Finset.univ.sup fun i ↦ ‖z i‖₊ from rfl, hemp, Finset.sup_empty]
      rfl
    have hzero : ‖z‖ = 0 := by
      rw [show ‖z‖ = (‖z‖₊ : ℝ) from rfl, hnn, NNReal.coe_zero]
    have hone : (0 : ℝ) ^ n ≤ 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · rw [zero_pow hn.ne']
        norm_num
    rw [hzero]
    linarith only [hone, hsum]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun j ↦ ‖z j‖₊
    have hcoord : ‖z‖ = |z i| := by
      rw [show ‖z‖ = (‖z‖₊ : ℝ) from rfl,
        show ‖z‖₊ = Finset.univ.sup fun j ↦ ‖z j‖₊ from rfl, hi]
      rfl
    have hle : |z i| ^ n ≤ ∑ j, |z j| ^ n :=
      Finset.single_le_sum (f := fun j ↦ |z j| ^ n) (fun _ _ ↦ by positivity) (Finset.mem_univ i)
    rw [hcoord]
    linarith only [hle]

/-- **All polynomial moments of the standard Gaussian vector are finite.** -/
theorem integrable_norm_pow_stdGaussian (d : ℕ) (n : ℕ) :
    Integrable (fun z : Vec d ↦ ‖z‖ ^ n) (stdGaussian d) := by
  refine Integrable.mono' (g := fun z : Vec d ↦ 1 + ∑ i, |z i| ^ n)
    ((integrable_const 1).add (integrable_finsetSum _ fun i _ ↦ ?_)) (by fun_prop) ?_
  · simpa only [abs_pow] using (integrable_eval_pow_stdGaussian d i n).abs
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact norm_pow_le_sum_abs_pow n z

/-- A product of two coordinates of the standard Gaussian vector is integrable. -/
theorem integrable_eval_mul_eval_stdGaussian (d : ℕ) (i j : Fin d) :
    Integrable (fun z : Vec d ↦ z i * z j) (stdGaussian d) := by
  refine Integrable.mono' (integrable_norm_pow_stdGaussian d 2) (by fun_prop) ?_
  filter_upwards with z
  have hi : |z i| ≤ ‖z‖ := by simpa using norm_le_pi_norm z i
  have hj : |z j| ≤ ‖z‖ := by simpa using norm_le_pi_norm z j
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)

/-- **The coordinates of the standard Gaussian vector have mean zero.** -/
theorem integral_eval_stdGaussian (d : ℕ) (i : Fin d) : ∫ z : Vec d, z i ∂(stdGaussian d) = 0 := by
  simpa only [pow_one, integral_id_gaussianReal] using integral_eval_pow_stdGaussian d i 1

/-- **The coordinates of the standard Gaussian vector have variance one.** -/
theorem integral_eval_sq_stdGaussian (d : ℕ) (i : Fin d) :
    ∫ z : Vec d, z i ^ 2 ∂(stdGaussian d) = 1 := by
  have hvar : Var[fun u : ℝ ↦ u; gaussianReal 0 1] = ((1 : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal
  rw [variance_eq_integral (by fun_prop), integral_id_gaussianReal] at hvar
  rw [integral_eval_pow_stdGaussian d i 2]
  simpa using hvar

/-- Distinct coordinates of the standard Gaussian vector are uncorrelated. -/
theorem integral_eval_mul_eval_stdGaussian_of_ne (d : ℕ) {i j : Fin d} (hij : i ≠ j) :
    ∫ z : Vec d, z i * z j ∂(stdGaussian d) = 0 := by
  classical
  set g : Fin d → ℝ → ℝ := fun k u ↦ if k = i then u else if k = j then u else 1 with hg
  have hprod : ∀ z : Vec d, ∏ k, g k (z k) = z i * z j := by
    intro z
    have h1 : ∏ k ∈ ({i, j} : Finset (Fin d)), g k (z k) = ∏ k, g k (z k) := by
      refine Finset.prod_subset (Finset.subset_univ _) fun k _ hk ↦ ?_
      have hki : k ≠ i := fun hh ↦ hk (by simp [hh])
      have hkj : k ≠ j := fun hh ↦ hk (by simp [hh])
      simp [hg, hki, hkj]
    rw [← h1, Finset.prod_pair hij, hg]
    simp [hij.symm]
  calc ∫ z : Vec d, z i * z j ∂(stdGaussian d)
      = ∫ z : Vec d, ∏ k, g k (z k) ∂(stdGaussian d) := by simp_rw [hprod]
    _ = ∏ k : Fin d, ∫ u : ℝ, g k u ∂(gaussianReal 0 1) := by
        rw [stdGaussian]
        exact MeasureTheory.integral_fintype_prod_eq_prod (E := fun _ : Fin d ↦ ℝ)
          (μ := fun _ : Fin d ↦ gaussianReal 0 1) g
    _ = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
        simp [hg, integral_id_gaussianReal]

/-- **The second moments of the standard Gaussian vector**: the covariance of two coordinates is
one on the diagonal and zero off it. -/
theorem integral_eval_mul_eval_stdGaussian (d : ℕ) (i j : Fin d) :
    ∫ z : Vec d, z i * z j ∂(stdGaussian d) = if i = j then 1 else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · simpa only [ite_true, ← sq] using integral_eval_sq_stdGaussian d i
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hij)]
    exact integral_eval_mul_eval_stdGaussian_of_ne d hij

end Moments

section Forms

variable {d : ℕ}

/-- A continuous linear map on `Vec d` is determined by its values on the coordinate vectors. -/
theorem apply_eq_sum_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Vec d →L[ℝ] F) (z : Vec d) : L z = ∑ i, z i • L (Pi.single i 1) := by
  have hz : z = ∑ i, z i • (Pi.single i 1 : Vec d) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul]

/-- A continuous linear form is integrable against the standard Gaussian vector. -/
theorem integrable_clm_stdGaussian (L : Vec d →L[ℝ] ℝ) :
    Integrable (fun z : Vec d ↦ L z) (stdGaussian d) := by
  refine Integrable.mono' ((integrable_norm_pow_stdGaussian d 1).const_mul ‖L‖)
    L.continuous.aestronglyMeasurable ?_
  filter_upwards with z
  simpa only [pow_one] using L.le_opNorm z

/-- A continuous quadratic form is integrable against the standard Gaussian vector. -/
theorem integrable_bilin_stdGaussian (B : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) :
    Integrable (fun z : Vec d ↦ B z z) (stdGaussian d) := by
  have hcont : Continuous fun z : Vec d ↦ B z z :=
    isBoundedBilinearMap_apply.continuous.comp (B.continuous.prodMk continuous_id)
  refine Integrable.mono' ((integrable_norm_pow_stdGaussian d 2).const_mul ‖B‖)
    hcont.aestronglyMeasurable ?_
  filter_upwards with z
  calc ‖B z z‖ ≤ ‖B z‖ * ‖z‖ := (B z).le_opNorm z
    _ ≤ ‖B‖ * ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_right (B.le_opNorm z) (norm_nonneg z)
    _ = ‖B‖ * ‖z‖ ^ 2 := by ring

/-- **The Gaussian average of a continuous linear form vanishes.** -/
theorem integral_clm_stdGaussian (L : Vec d →L[ℝ] ℝ) : ∫ z, L z ∂(stdGaussian d) = 0 := by
  have hpoint : ∀ z : Vec d, L z = ∑ i, z i * L (Pi.single i 1) := by
    intro z
    simpa only [smul_eq_mul] using apply_eq_sum_smul L z
  calc ∫ z, L z ∂(stdGaussian d)
      = ∫ z : Vec d, ∑ i, z i * L (Pi.single i 1) ∂(stdGaussian d) :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin d, ∫ z : Vec d, z i * L (Pi.single i 1) ∂(stdGaussian d) :=
        integral_finsetSum _ fun i _ ↦ (integrable_eval_pow_stdGaussian d i 1).congr
          (by filter_upwards with z; rw [pow_one]) |>.mul_const _
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        rw [integral_mul_const, integral_eval_stdGaussian d i, zero_mul]

/-- **The Gaussian average of a continuous quadratic form is its trace.** -/
theorem integral_bilin_stdGaussian (B : Vec d →L[ℝ] Vec d →L[ℝ] ℝ) :
    ∫ z, B z z ∂(stdGaussian d) = ∑ i, B (Pi.single i 1) (Pi.single i 1) := by
  classical
  have hpoint : ∀ z : Vec d,
      B z z = ∑ i, ∑ j, z i * z j * B (Pi.single i 1) (Pi.single j 1) := by
    intro z
    have houter : B z z = ∑ i, z i * (B (Pi.single i 1) z) := by
      have h := apply_eq_sum_smul B z
      have happ : (B z) z = (∑ i, z i • B (Pi.single i 1)) z := by rw [h]
      rw [happ, sum_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [smul_apply, smul_eq_mul]
    rw [houter]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hinner : B (Pi.single i 1) z = ∑ j, z j * B (Pi.single i 1) (Pi.single j 1) := by
      simpa only [smul_eq_mul] using apply_eq_sum_smul (B (Pi.single i 1)) z
    rw [hinner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hint : ∀ i j : Fin d, Integrable
      (fun z : Vec d ↦ z i * z j * B (Pi.single i 1) (Pi.single j 1)) (stdGaussian d) :=
    fun i j ↦ (integrable_eval_mul_eval_stdGaussian d i j).mul_const _
  calc ∫ z, B z z ∂(stdGaussian d)
      = ∫ z : Vec d, ∑ i, ∑ j, z i * z j * B (Pi.single i 1) (Pi.single j 1)
          ∂(stdGaussian d) := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin d, ∑ j : Fin d,
          ∫ z : Vec d, z i * z j * B (Pi.single i 1) (Pi.single j 1) ∂(stdGaussian d) := by
        rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j]
        exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hint i j
    _ = ∑ i, B (Pi.single i 1) (Pi.single i 1) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hterm : ∀ j : Fin d,
            ∫ z : Vec d, z i * z j * B (Pi.single i 1) (Pi.single j 1) ∂(stdGaussian d)
              = (if i = j then 1 else 0) * B (Pi.single i 1) (Pi.single j 1) := by
          intro j
          rw [integral_mul_const, integral_eval_mul_eval_stdGaussian d i j]
        simp only [hterm, ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq Finset.univ i fun j ↦ B (Pi.single i 1) (Pi.single j 1)]
        simp

end Forms

end

end SuperdiffusionCLT.Section8.Brownian
