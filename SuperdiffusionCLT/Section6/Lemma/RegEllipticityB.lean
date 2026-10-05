/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxBridge
public import SuperdiffusionCLT.Section6.Lemma.RegEllipticity
public import Homogenization.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl

/-!
# `reg.ellipticity` from the homogenization error

For a field elliptic on a cube, `σ⁻¹ Λ_{1/4,1} + σ λ_{1/4,1}⁻¹ ≤ C(d) (𝓔² + 1)` where `𝓔` is
the homogenization error at exponent `1/9` against `σ Id`. The chain is the public
`q = 1 ≤ q = 2` comparison at half the exponent, the public bound of the ellipticities by the
error (`e.bound.Lambdas.by.Es`), and a comparison of the error between exponents. Also records
the summability of the scale series (so no `tsum` is read at its junk value).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization

noncomputable section

section ErrorComparison

variable {d : ℕ} [NeZero d]

/-- Comparison of geometric weights: for `s ≤ s'` the weight at `s'` is at most the inverse
discount at `s` times the weight at `s`. -/
theorem l5_geometricWeight_le {s s' q : ℝ} (hs : 0 < s) (hss : s ≤ s') (hq : 0 < q) (n : ℕ) :
    Book.Ch02.geometricWeight s' q n ≤
      (1 - (3 : ℝ) ^ (-s * q))⁻¹ * Book.Ch02.geometricWeight s q n := by
  have hsq : 0 < s * q := mul_pos hs hq
  have hc : 0 < 1 - (3 : ℝ) ^ (-s * q) := by
    have : (3 : ℝ) ^ (-s * q) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hsq])
    linarith only [this]
  have hc' : 1 - (3 : ℝ) ^ (-s' * q) ≤ 1 := by
    have : 0 ≤ (3 : ℝ) ^ (-s' * q) := Real.rpow_nonneg (by norm_num) _
    linarith only [this]
  have hpow : (3 : ℝ) ^ (-s' * q * (n : ℝ)) ≤ (3 : ℝ) ^ (-s * q * (n : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith only [mul_nonneg (mul_nonneg (sub_nonneg.mpr hss) hq.le) this]
  have hp0 : 0 ≤ (3 : ℝ) ^ (-s' * q * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  unfold Book.Ch02.geometricWeight Book.Ch02.geometricDiscount
  simp only [Real.rpow_eq_pow]
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
  calc (1 - (3 : ℝ) ^ (-s' * q)) * (3 : ℝ) ^ (-s' * q * (n : ℝ))
      ≤ 1 * (3 : ℝ) ^ (-s' * q * (n : ℝ)) := by gcongr
    _ ≤ _ := by rw [one_mul]; exact hpow

/-- The public homogenization error (`p = ∞`, `q = 2`) at the larger exponent `s'` is controlled
by the one at `s` (this is the "monotone in `s`" step: the discount normalisation costs the
constant `(1 - 3^{-2s})⁻¹`). -/
theorem l5_error_sq_le_of_le (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d)
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') :
    (Book.Ch02.HomogenizationErrorOnCube Q s' .infinity (.finite 2) a a0) ^ 2 ≤
      (1 - (3 : ℝ) ^ (-s * 2))⁻¹ *
        (Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0) ^ 2 := by
  have hs' : 0 < s' := lt_of_lt_of_le hs hss
  rw [Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0,
    Book.Ch02.homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs' a a0,
    ← tsum_mul_left]
  have hM : ∀ n : ℕ,
      0 ≤ Book.Ch02.maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (n : ℤ)) a a0 :=
    fun n => Book.Ch02.maxDescendantNormalizedBlockResponseAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) a a0
  refine Summable.tsum_le_tsum (fun n => ?_)
    (Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      Q a a0 hs')
    ((Book.Ch02.summable_geometricWeight_two_mul_maxDescendantNormalizedBlockResponseAtScale
      Q a a0 hs).mul_left _)
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (l5_geometricWeight_le hs hss two_pos n) (hM n)

end ErrorComparison

section Assembly

variable {d : ℕ} [NeZero d]

/-- **`reg.ellipticity` from the homogenization error, one cube.** For a field elliptic on the
cube `Q` and a scalar matrix `σ Id`, the weighted ellipticities `σ⁻¹ Λ_{1/4,1}` and
`σ λ_{1/4,1}⁻¹` are bounded by `C(d)` times `𝓔² + 1`, where `𝓔` is the homogenization error at
exponent `1/9` (`e.bound.Lambdas.by.Es` with `e.ellipticities.qone.by.qtwo` and monotonicity of
`𝓔` in `s`). -/
theorem regEllipticity_of_error (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a) (h0 : 0 < lam) (hle : lam ≤ Lam)
    {σ : ℝ} (hσ : 0 < σ) :
    σ⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a +
        σ * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤
      (4 * (d : ℝ) ^ 3 * ((1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ + 1)) *
        ((HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
            (MultiscaleExponent.finite 2) a (σ • (1 : Mat d))) ^ 2 + 1) := by
  set F := SuperdiffusionCLT.Section6.HarmonicApprox.paddedFamily Q hEll h0 hle with hF
  have hg : Book.Ch03.publicCoeffField Q F =ᵐ[volumeMeasureOn (cubeSet Q)] a :=
    SuperdiffusionCLT.Section6.HarmonicApprox.publicCoeffField_paddedFamily_ae_eq
      hEll h0 hle (subset_refl _)
  have hq4 : (0 : ℝ) < 1 / 4 := by norm_num
  have hq8 : (0 : ℝ) < 1 / 4 / 2 := by norm_num
  have hq9 : (0 : ℝ) < 1 / 9 := by norm_num
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- raw quantities equal those of the public representative
  have eL : LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (Book.Ch03.publicCoeffField Q F) =
      LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a :=
    l5_LambdaSq_congr_ae Q _ _ hg
  have el : lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (Book.Ch03.publicCoeffField Q F) =
      lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a :=
    l5_lambdaSq_congr_ae Q _ _ hg
  -- public upper and lower bounds
  have hU1 := Book.Ch03.sqrt_LambdaSq_publicCoeffField_finite_one_le_dim_mul_poincareUpperEllipticityFactor
    Q F hq4
  have hL1 := Book.Ch03.sqrt_lambdaSq_publicCoeffField_finite_one_inv_le_dim_mul_poincareLowerEllipticityFactor
    Q F hq4
  have hUpos : 0 ≤ Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F :=
    Book.Ch02.LambdaSq_nonneg Q F hq4 (by simp)
  have hLpos : 0 < Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F :=
    Book.Ch02.lambdaSq_pos Q F hq4 (by simp)
  have hrawU : LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a ≤
      (d : ℝ) ^ 2 * Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F := by
    rw [← eL]
    have h := (Real.sqrt_le_iff.mp hU1).2
    unfold Book.Ch03.poincareUpperEllipticityFactor at h
    rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow, mul_pow, Real.sq_sqrt hUpos] at h
    exact h
  have hrawL : (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤
      (d : ℝ) ^ 2 * (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ := by
    rw [← el]
    have h := (Real.sqrt_le_iff.mp hL1).2
    unfold Book.Ch03.poincareLowerEllipticityFactor at h
    rw [mul_pow] at h
    have hsq : (Real.rpow (Book.Ch02.lambdaSq Q (1 / 4)
        (Book.Ch02.MultiscaleExponent.finite 1) F) (-(1 / 2 : ℝ))) ^ 2 =
        (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹ := by
      rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
      norm_num [Real.rpow_neg_one]
    rw [hsq] at h
    exact h
  -- q = 1 to q = 2
  have hq12U := l5_LambdaSq_one_le_two_half Q F hq4
  have hq12L := l5_lambdaSq_one_inv_le_two_half Q F hq4
  -- the lemma 5.9 at s/2 = 1/8
  have h59U := Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
    Q F hq8 hσ
  have h59L := Book.Ch02.sigma_mul_lambdaSq_finite_two_inv_le_card_mul_homogenizationError_sq_add_one
    Q F hq8 hσ
  -- monotonicity of the error
  have hmono := l5_error_sq_le_of_le Q F (σ • (1 : Mat d)) hq9 (s' := 1 / 4 / 2)
    (by norm_num)
  have hE := SuperdiffusionCLT.Section6.HarmonicApprox.homogenizationErrorOnCube_eq_ch02
    hEll h0 hle (1 / 9) 2 (σ • (1 : Mat d))
  rw [hE]
  set E9 := Book.Ch02.HomogenizationErrorOnCube Q (1 / 9) Book.Ch02.MultiscaleExponent.infinity
    (Book.Ch02.MultiscaleExponent.finite 2) F (σ • (1 : Mat d)) with hE9
  set E8 := Book.Ch02.HomogenizationErrorOnCube Q (1 / 4 / 2) Book.Ch02.MultiscaleExponent.infinity
    (Book.Ch02.MultiscaleExponent.finite 2) F (σ • (1 : Mat d)) with hE8
  set K0 : ℝ := (1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ with hK0
  have hcard : (Fintype.card (Fin d) : ℝ) = d := by simp
  have hK0nn : 0 ≤ K0 := by
    have : (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact inv_nonneg.mpr (by linarith only [this])
  have hE8sq : E8 ^ 2 + 1 ≤ (K0 + 1) * (E9 ^ 2 + 1) := by
    have h9 : 0 ≤ E9 ^ 2 := sq_nonneg _
    nlinarith only [hmono, h9, hK0nn]
  have hd2 : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hup : σ⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a ≤
      (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) := by
    have hσi : 0 ≤ σ⁻¹ := inv_nonneg.mpr hσ.le
    rw [hcard] at h59U
    calc σ⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a
        ≤ σ⁻¹ * ((d : ℝ) ^ 2 *
            Book.Ch02.LambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F) :=
          mul_le_mul_of_nonneg_left hrawU hσi
      _ ≤ σ⁻¹ * ((d : ℝ) ^ 2 *
            Book.Ch02.LambdaSq Q (1 / 4 / 2) (Book.Ch02.MultiscaleExponent.finite 2) F) := by
          gcongr
      _ = (d : ℝ) ^ 2 * (σ⁻¹ *
            Book.Ch02.LambdaSq Q (1 / 4 / 2) (Book.Ch02.MultiscaleExponent.finite 2) F) := by
          ring
      _ ≤ (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) := by
          gcongr
  have hlo : σ * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤
      (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) := by
    rw [hcard] at h59L
    calc σ * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹
        ≤ σ * ((d : ℝ) ^ 2 *
            (Book.Ch02.lambdaSq Q (1 / 4) (Book.Ch02.MultiscaleExponent.finite 1) F)⁻¹) :=
          mul_le_mul_of_nonneg_left hrawL hσ.le
      _ ≤ σ * ((d : ℝ) ^ 2 *
            (Book.Ch02.lambdaSq Q (1 / 4 / 2) (Book.Ch02.MultiscaleExponent.finite 2) F)⁻¹) := by
          gcongr
      _ = (d : ℝ) ^ 2 * (σ *
            (Book.Ch02.lambdaSq Q (1 / 4 / 2) (Book.Ch02.MultiscaleExponent.finite 2) F)⁻¹) := by
          ring
      _ ≤ (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) := by
          gcongr
  calc σ⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a +
        σ * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹
      ≤ (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) + (d : ℝ) ^ 2 * (2 * d * (E8 ^ 2 + 1)) :=
        add_le_add hup hlo
    _ = 4 * (d : ℝ) ^ 3 * (E8 ^ 2 + 1) := by ring
    _ ≤ 4 * (d : ℝ) ^ 3 * ((K0 + 1) * (E9 ^ 2 + 1)) := by
        gcongr
    _ = _ := by ring

/-- **`reg.ellipticity`, dimensional constant.** The constant of `regEllipticity_of_error`
depends only on the dimension. -/
theorem regEllipticity_exists (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : TriadicCube d) {lam Lam : ℝ} {a : CoeffField d},
        IsEllipticFieldOn lam Lam (cubeSet Q) a → 0 < lam → lam ≤ Lam →
        ∀ {σ : ℝ}, 0 < σ →
          σ⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a +
              σ * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) a)⁻¹ ≤
            C * ((HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
                (MultiscaleExponent.finite 2) a (σ • (1 : Mat d))) ^ 2 + 1) := by
  refine ⟨4 * (d : ℝ) ^ 3 * ((1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ + 1), ?_,
    fun Q _ _ _ hEll h0 hle _ hσ => regEllipticity_of_error Q hEll h0 hle hσ⟩
  have hd : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hK0 : 0 ≤ (1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ := by
    have : (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    exact inv_nonneg.mpr (by linarith only [this])
  have h3 : (1 : ℝ) ≤ (d : ℝ) ^ 3 := one_le_pow₀ hd
  nlinarith only [h3, hK0]

/-! ## Summability of the scale sums for fields elliptic on the cube -/

/-! ## Satisfiability -/

omit [NeZero d] in
/-- The scalar field `Id` is elliptic on every cube, so the hypotheses of the results above are
met. -/
theorem regEllipticity_witness (Q : TriadicCube d) :
    IsEllipticFieldOn 1 1 (cubeSet Q) (constantCoeffField (1 : Mat d)) :=
  isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet Q)
    (by simpa using isEllipticMatrix_scalarMatrix (d := d) (sigma := 1) one_pos)

example (d : ℕ) [NeZero d] (Q : TriadicCube d) :
    (1 : ℝ)⁻¹ * LambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (constantCoeffField (1 : Mat d)) +
        1 * (lambdaSq Q (1 / 4) (MultiscaleExponent.finite 1) (constantCoeffField (1 : Mat d)))⁻¹ ≤
      (4 * (d : ℝ) ^ 3 * ((1 - (3 : ℝ) ^ (-(1 / 9 : ℝ) * 2))⁻¹ + 1)) *
        ((HomogenizationErrorOnCube Q (1 / 9) MultiscaleExponent.infinity
            (MultiscaleExponent.finite 2) (constantCoeffField (1 : Mat d)) ((1 : ℝ) • (1 : Mat d))) ^ 2 + 1) :=
  regEllipticity_of_error Q (regEllipticity_witness Q) one_pos le_rfl one_pos

end Assembly

end

end SuperdiffusionCLT.Section6
