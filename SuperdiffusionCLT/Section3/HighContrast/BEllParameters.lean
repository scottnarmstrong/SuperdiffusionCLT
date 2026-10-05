/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.HighContrast.ScaleTransport

/-!
# Parameters, monotonicity and the arithmetic choice of the cutoff index

The high-contrast step of the proof of `l.b.ell.homogenization` fixes the cutoff index
`k < n` with the two properties

`n - k >= C_0 log^2 (nu^{-1} k)` and `l - k <= C ((l - n) + log^2 (nu^{-1} l))`,

and it applies the entry theorem of `CoarseGraining` at the cutoff field's own
scales. This module supplies the dimensional inputs of that step.

## The canonical parameter record

The entry statements of `Section3/HighContrast/ScaleTransport.lean` consume a
`Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d`, while the printed
argument takes the constant `C_0 (d)` of [AK, Theorem 3.1] from `d`
alone. `canonicalParams` builds such a record from `2 <= d` by setting the
ellipticity exponents to `2 / 5` and the contrast exponent `xi` to `3 * d`.

## The contrast polynomial is monotone in the cutoff index

`cutoffContrastBound d xi nu m` bounds the initial-scale contrast of the
rebased cutoff law. It is a product of a factor depending on `nu` and `xi` and
`1 + (cutoffLargeCubeAmpConst d * (1 + m)) ^ 2`, so it is increasing in `m`
because the amplitude constant `cutoffLargeCubeAmpConst d` is a product of
square roots and of `gammaTriangleConst 2`, hence nonnegative for every `d`.
Monotonicity is what removes the manuscript's fixed point in `k`: the threshold
`log^2 (2 + poly(nu^{-1} k))` may be evaluated at `l` instead, exactly the
"with `C_0` enlarged if necessary, since `k <= l`" of the printed proof.

## The arithmetic choice of `k`

`exists_scaleSeparation` is the arithmetic of the printed proof: given `C` large
enough so that the hypothesis `C log^2 (nu^{-1} L) <= n` forces `n` off
the degenerate corner, the choice `k := n - ceil(C_0 log^2 (2 + poly(nu^{-1}
l))) - t_d` satisfies both inequalities. The `2 <= L` side condition excludes
`L = 0` (no admissible `l`) and `L = 1` (which forces `nu = 1`, `n = 0`, `l =
1`); that single corner is handled separately in the assembly.

## Main definitions and results

* `canonicalParams`: the parameter record of the entry theorem, from `d` alone.
* `cutoffContrastBound_mono`: the contrast polynomial is monotone in the cutoff
  index.
* `exists_scaleSeparation`: the arithmetic choice of `k` given `n`, `l`, `L`.
* `sigmaBarStarScalar_pos`: `shom_{m,*}(cu_n) > 0` with no analytic premise.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.HighContrast

open Homogenization MeasureTheory ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability

noncomputable section

/-! ## The canonical parameter record

The paper treats all dimensions `d >= 2` and takes the entry constant of
[AK, Theorem 3.1] (the printed lemma mentions only the constant `C_0 (d)`, with no
dimension condition). Here the entry theorem is stated for an arbitrary record of
`Book.Ch05.QuantitativeCoarseGrainedEllipticityParams`, so the assembly needs a
record determined by `d` alone. -/

/-- **The canonical parameter record of the high-contrast entry bound**: the
record of `Book.Ch05.QuantitativeCoarseGrainedEllipticityParams` with both
ellipticity exponents `2 / 5` and contrast exponent `3 * d`, built from the
chapter's standing dimension condition `d >= 2`. -/
noncomputable def canonicalParams (d : ℕ) (hd : 2 ≤ d) :
    Book.Ch05.QuantitativeCoarseGrainedEllipticityParams d where
  sUpper := 2 / 5
  sLower := 2 / 5
  xi := 3 * d
  two_le_dim := hd
  sUpper_nonneg := by norm_num
  sUpper_lt_one := by norm_num
  sLower_nonneg := by norm_num
  sLower_lt_one := by norm_num
  xi_gt_two_mul_dim := by
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
    push_cast
    linarith only [hd0]
  sum_lt_one := by norm_num
  dim_div_xi_lt_min := by
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) hd
    have h : ((d:ℝ)) / ((3 * d : ℕ) : ℝ) = 1 / 3 := by
      push_cast
      field_simp
    rw [h]
    norm_num

/-! ## Positivity of the dimensional constants

The amplitude `cutoffLargeCubeAmpConst d` of the envelope is a product
of nonnegative factors in every dimension, so the contrast polynomial is
monotone in the cutoff index without any probabilistic data. The only constant
whose positivity is not immediate is the `Gamma_sigma` independent-sum constant
at `sigma = 2`, which is the maximum of two positive constants. -/

private theorem gammaSigmaExpRegimeEndpointConst_two_nonneg :
    (0 : ℝ) ≤ IndependentSums.gammaSigmaExpRegimeEndpointConst 2 := by
  have heq : ¬ ((2 : ℝ) = 1) := by norm_num
  have hγ : (0 : ℝ) ≤ 8 * Real.exp 1 * Book.Ch04.gammaMomentConst 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg 1))
      (IndependentSums.gammaMomentConst_pos (by norm_num)).le
  rw [IndependentSums.gammaSigmaExpRegimeEndpointConst, ite_eq_right heq,
    IndependentSums.gammaSigmaExpRegimeConst]
  exact mul_nonneg (by norm_num) (le_max_of_le_left hγ)

private theorem gammaSigmaIndependentSumConst_two_nonneg :
    (0 : ℝ) ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 := by
  have hlt : ¬ ((2 : ℝ) < 1) := by norm_num
  rw [Book.Ch04.gammaSigmaIndependentSumConst, ite_eq_right hlt]
  exact gammaSigmaExpRegimeEndpointConst_two_nonneg

private theorem streamLinftyConst_nonneg (d : ℕ) : 0 ≤ streamLinftyConst d := by
  rw [streamLinftyConst]
  have htri : (0 : ℝ) ≤ IndependentSums.gammaTriangleConst 2 :=
    IndependentSums.gammaTriangleConst_pos.le
  have hbr : (0 : ℝ) ≤ Book.Ch04.gammaSigmaIndependentSumConst 2 +
      Real.sqrt ((d : ℝ)) / 2 :=
    add_nonneg gammaSigmaIndependentSumConst_two_nonneg
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
  exact mul_nonneg (mul_nonneg (pow_nonneg htri 2) (pow_nonneg (Nat.cast_nonneg _) 2)) hbr

private theorem largeCubeLinftyConst_nonneg (d : ℕ) : 0 ≤ largeCubeLinftyConst d := by
  rw [largeCubeLinftyConst]
  exact mul_nonneg (streamLinftyConst_nonneg d) (Real.sqrt_nonneg _)

private theorem shellZeroLargeCubeConst_nonneg (d : ℕ) : 0 ≤ shellZeroLargeCubeConst d :=
  Real.sqrt_nonneg _

private theorem cutoffLargeCubeAmpConst_nonneg (d : ℕ) : 0 ≤ cutoffLargeCubeAmpConst d := by
  rw [cutoffLargeCubeAmpConst]
  exact mul_nonneg
    (mul_nonneg IndependentSums.gammaTriangleConst_pos.le (Real.sqrt_nonneg _))
    (add_nonneg (shellZeroLargeCubeConst_nonneg d) (largeCubeLinftyConst_nonneg d))

private theorem three_mul_log_two_sq_ge_one : (1 : ℝ) ≤ 3 * Real.log 2 ^ (2 : ℕ) := by
  nlinarith only [Real.log_two_gt_d9]

/-! ## The arithmetic of the choice of `k`

The threshold `n - k >= C_0 log^2 (nu^{-1} k)` is printed in the paper; the
`2 + poly(·)` shape is not printed there — it is the entry theorem's
side condition `entryScaleLogSqConst xi C sigma * log^2 (2 + poly) <= j` of
`Section3/HighContrast/ScaleTransport.lean`, whose only printed counterpart is
the "contrast bounded by a dimensional polynomial in `nu^{-1} k`" of the
printed proof. By `cutoffContrastBound_mono` that threshold may be evaluated at `l`,
and the resulting `log (2 + poly(nu^{-1} l))` is at most a dimensional
constant plus `2 log (nu^{-1} l)`. The two private constants below record that
bookkeeping. -/

/-- The dimensional constant of the `log` comparison: `log (2 + poly(nu^{-1}
l)) <= scaleSeparationLogConst d xi + 2 log (nu^{-1} l)` for `nu <= 1` and
`2 <= l`, the shape into which the threshold `n - k >= C_0 log^2 (nu^{-1} k)`
is put once the polynomial factor of the contrast bound is unfolded. -/
private def scaleSeparationLogConst (d xi : ℕ) : ℝ :=
  Real.log 8 + Real.log (1 + Real.Gamma ((xi : ℝ) + 1)) + Real.log 3 +
    Real.log (1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) + 2 * Real.log 2

private theorem one_le_three_mul_log_sq {w : ℝ} (h : Real.log 2 ≤ w) :
    (1 : ℝ) ≤ 3 * w ^ (2 : ℕ) := by
  have h0 : (0 : ℝ) ≤ w := le_trans (Real.log_nonneg (by norm_num)) h
  have h1 : Real.log 2 ^ (2 : ℕ) ≤ w ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Real.log_nonneg (by norm_num)) h 2
  linarith only [three_mul_log_two_sq_ge_one, h1]

private theorem log_two_add_cutoffContrastBound_le (d xi : ℕ) {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) {l : ℕ} (hl2 : 2 ≤ l) :
    Real.log (2 + cutoffContrastBound d xi nu l) ≤
      scaleSeparationLogConst d xi + 2 * Real.log (nu⁻¹ * (l : ℝ)) := by
  have hA0 : (0 : ℝ) ≤ cutoffLargeCubeAmpConst d := cutoffLargeCubeAmpConst_nonneg d
  have hG : (0 : ℝ) ≤ Real.Gamma ((xi : ℝ) + 1) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  have hainv : (1 : ℝ) ≤ nu⁻¹ := one_le_inv_iff₀.mpr ⟨hnu, hnu1⟩
  have hainvp : (0 : ℝ) < nu⁻¹ := inv_pos.mpr hnu
  have hnu2 : (0 : ℝ) ≤ nu⁻¹ ^ (2 : ℕ) := by positivity
  have hnu12 : (1 : ℝ) ≤ nu⁻¹ ^ (2 : ℕ) := by
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 from zero_le_one) hainv 2
    linarith only [h]
  have hlR : (2 : ℝ) ≤ (l : ℝ) := Nat.cast_le.2 hl2
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := le_trans (by norm_num) hlR
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hl1
  have hw : Real.log (nu⁻¹ * (l : ℝ)) = Real.log nu⁻¹ + Real.log (l : ℝ) :=
    Real.log_mul (ne_of_gt hainvp) hl0.ne'
  -- the product bound for `2 + poly`
  have hfac : (1 : ℝ) ≤ (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) := by
    have h1 : (1 : ℝ) * (1 + Real.Gamma ((xi : ℝ) + 1)) ≤
        (1 + 2 * nu⁻¹ ^ (2 : ℕ)) * (1 + Real.Gamma ((xi : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hnu2))
        (by linarith only [hG] : (0 : ℝ) ≤ 1 + Real.Gamma ((xi : ℝ) + 1))
    linarith only [h1, hG]
  have hK1 : (2 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) := by
    linarith only [hfac]
  have hX1 : (1 : ℝ) ≤ 1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ) :=
    le_add_of_nonneg_right (sq_nonneg _)
  have h2kx : (2 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
      (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by
    have h1 : (1 : ℝ) * (4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ))) ≤
        (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) *
          (4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_right hX1 (by linarith only [hK1] :
        (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)))
    linarith only [h1, hK1]
  have hprod : (2 : ℝ) + cutoffContrastBound d xi nu l ≤
      8 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
        (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by
    calc (2 : ℝ) + cutoffContrastBound d xi nu l
        = 2 + 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
            (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by
          rw [cutoffContrastBound]
      _ ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
            (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) +
          4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
            (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by
          linarith only [h2kx]
      _ = 8 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
            (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by ring
  -- the log of the product splits into the four constants
  have hΓp : (0 : ℝ) < 1 + Real.Gamma ((xi : ℝ) + 1) := by linarith only [hG]
  have hνp : (0 : ℝ) < 1 + 2 * nu⁻¹ ^ (2 : ℕ) := by linarith only [hnu2]
  have hXp : (0 : ℝ) < 1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ) := by
    have hsq : (0 : ℝ) ≤ (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ) := sq_nonneg _
    linarith only [hsq]
  have h2 : Real.log (8 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) *
      (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ))) =
      Real.log 8 + Real.log (1 + Real.Gamma ((xi : ℝ) + 1)) +
        Real.log (1 + 2 * nu⁻¹ ^ (2 : ℕ)) +
        Real.log (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) := by
    rw [Real.log_mul
      (ne_of_gt (mul_pos (mul_pos (by norm_num) hΓp) hνp))
      (ne_of_gt hXp),
      Real.log_mul (ne_of_gt (mul_pos (by norm_num) hΓp)) (ne_of_gt hνp),
      Real.log_mul (ne_of_gt (by norm_num)) (ne_of_gt hΓp)]
  -- log (1 + 2 nu^{-2}) <= log 3 + 2 log (nu^{-1})
  have h3 : Real.log (1 + 2 * nu⁻¹ ^ (2 : ℕ)) ≤ Real.log 3 + 2 * Real.log nu⁻¹ := by
    have hle : 1 + 2 * nu⁻¹ ^ (2 : ℕ) ≤ 3 * nu⁻¹ ^ (2 : ℕ) := by linarith only [hnu12]
    have hν0 : (0 : ℝ) < nu⁻¹ ^ (2 : ℕ) := pow_pos hainvp 2
    calc Real.log (1 + 2 * nu⁻¹ ^ (2 : ℕ)) ≤ Real.log (3 * nu⁻¹ ^ (2 : ℕ)) :=
        Real.log_le_log (by linarith only [hνp]) hle
      _ = Real.log 3 + Real.log (nu⁻¹ ^ (2 : ℕ)) :=
          Real.log_mul (by norm_num) (ne_of_gt hν0)
      _ = Real.log 3 + 2 * Real.log nu⁻¹ := by rw [Real.log_pow nu⁻¹ 2]; norm_num
  -- log (1 + (A (1 + l))^2) <= log (1 + A^2) + 2 log (1 + l)
  have h1l : (1 : ℝ) ≤ 1 + (l : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg (l : ℕ))
  have e2 : (1 + (l : ℝ)) ^ (2 : ℕ) = 1 + 2 * (l : ℝ) + (l : ℝ) ^ (2 : ℕ) := by ring
  have h1lsq : (1 : ℝ) ≤ (1 + (l : ℝ)) ^ (2 : ℕ) := by
    linarith only [e2, sq_nonneg ((l : ℝ))]
  have h5 : Real.log (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) ≤
      Real.log (1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) + 2 * Real.log (1 + (l : ℝ)) := by
    have e1 : (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ) =
        cutoffLargeCubeAmpConst d ^ (2 : ℕ) * (1 + (l : ℝ)) ^ (2 : ℕ) := by rw [mul_pow]
    have hle : (1 : ℝ) + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ) ≤
        (1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) * (1 + (l : ℝ)) ^ (2 : ℕ) := by
      linarith only [e1, h1lsq]
    have hAp : (0 : ℝ) < 1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ) := by
      have hsq : (0 : ℝ) ≤ cutoffLargeCubeAmpConst d ^ (2 : ℕ) := sq_nonneg _
      linarith only [hsq]
    calc Real.log (1 + (cutoffLargeCubeAmpConst d * (1 + (l : ℝ))) ^ (2 : ℕ)) ≤
        Real.log ((1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) * (1 + (l : ℝ)) ^ (2 : ℕ)) :=
        Real.log_le_log (by linarith only [hXp]) hle
      _ = Real.log (1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) +
            Real.log ((1 + (l : ℝ)) ^ (2 : ℕ)) :=
          Real.log_mul (ne_of_gt hAp)
            (ne_of_gt (pow_pos (by linarith only [hlR] :
              (0 : ℝ) < 1 + (l : ℝ)) 2))
      _ = Real.log (1 + cutoffLargeCubeAmpConst d ^ (2 : ℕ)) +
            2 * Real.log (1 + (l : ℝ)) := by rw [Real.log_pow (1 + (l : ℝ)) 2]; norm_num
  -- log (1 + l) <= log 2 + log l
  have h6 : Real.log (1 + (l : ℝ)) ≤ Real.log 2 + Real.log (l : ℝ) := by
    have hle : 1 + (l : ℝ) ≤ 2 * (l : ℝ) := by linarith only [hlR]
    calc Real.log (1 + (l : ℝ)) ≤ Real.log (2 * (l : ℝ)) :=
        Real.log_le_log (by linarith only [h1l]) hle
      _ = Real.log 2 + Real.log (l : ℝ) :=
          Real.log_mul (by norm_num) hl0.ne'
  have hBpos : (0 : ℝ) < 2 + cutoffContrastBound d xi nu l := by
    linarith only [cutoffContrastBound_nonneg d xi nu l]
  rw [hw, scaleSeparationLogConst]
  linarith only [Real.log_le_log hBpos hprod, h2, h3, h5, h6]

/-! ## Monotonicity of the contrast polynomial -/

/-- **The contrast polynomial is monotone in the cutoff index.** This is the
"with `C_0` enlarged if necessary, since `k <= l`" of the printed proof: the
threshold `log^2 (2 + poly(nu^{-1} k))` may be evaluated at `l` instead of `k`, so no
fixed point in `k` remains. Both factors that depend on `nu` and `xi` are
identical on the two sides, and the remaining factor
`1 + (cutoffLargeCubeAmpConst d * (1 + m)) ^ 2` is increasing in `m` because
`cutoffLargeCubeAmpConst d` is a product of square roots and of
`gammaTriangleConst 2`, hence nonnegative in every dimension. -/
theorem cutoffContrastBound_mono (d xi : ℕ) {nu : ℝ} {m m' : ℕ}
    (h : m ≤ m') : cutoffContrastBound d xi nu m ≤ cutoffContrastBound d xi nu m' := by
  have hA : (0 : ℝ) ≤ cutoffLargeCubeAmpConst d := cutoffLargeCubeAmpConst_nonneg d
  have hm : (m : ℝ) ≤ (m' : ℝ) := Nat.cast_le.2 h
  have h1 : (1 : ℝ) + (m : ℝ) ≤ 1 + (m' : ℝ) := by linarith only [hm]
  have hstep : cutoffLargeCubeAmpConst d * (1 + (m : ℝ)) ≤
      cutoffLargeCubeAmpConst d * (1 + (m' : ℝ)) :=
    mul_le_mul_of_nonneg_left h1 hA
  have hsq : (cutoffLargeCubeAmpConst d * (1 + (m : ℝ))) ^ (2 : ℕ) ≤
      (cutoffLargeCubeAmpConst d * (1 + (m' : ℝ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀
      (show 0 ≤ cutoffLargeCubeAmpConst d * (1 + (m : ℝ)) from
        mul_nonneg hA (add_nonneg zero_le_one (Nat.cast_nonneg _))) hstep 2
  have hG : (0 : ℝ) ≤ Real.Gamma ((xi : ℝ) + 1) :=
    Real.Gamma_nonneg_of_nonneg (by positivity)
  have hnu2 : (0 : ℝ) ≤ nu⁻¹ ^ (2 : ℕ) := by positivity
  have hcoef : (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) * (1 + 2 * nu⁻¹ ^ (2 : ℕ)) := by
    have h1 : (0 : ℝ) ≤ 4 * (1 + Real.Gamma ((xi : ℝ) + 1)) :=
      mul_nonneg (by norm_num) (add_nonneg zero_le_one hG)
    exact mul_nonneg h1 (add_nonneg zero_le_one (mul_nonneg (by norm_num) hnu2))
  rw [cutoffContrastBound, cutoffContrastBound]
  exact mul_le_mul_of_nonneg_left (by linarith only [hsq]) hcoef

/-! ## The arithmetic choice of the cutoff index

This is the arithmetic of the printed proof:
for `C` large enough the hypothesis `C log^2 (nu^{-1} L) <= n` excludes
the degenerate corner `n = 0` (for `2 <= L` it forces `nu = L >= 2` there), and
with `Theta (nu, l) := C_0 log^2 (2 + poly(nu^{-1} l))` the choice
`k := n - ceil(Theta) - t_d` satisfies both printed inequalities. -/

/-- **The arithmetic choice of `k` given `n`, `l`, `L`**: there is a constant `C`
such that whenever `C log^2 (nu^{-1} L) <= n`, every pair `n < l <= L` with
`2 <= L` admits `k < n` with `C_0 log^2 (2 + poly(nu^{-1} k)) + t_d <= n - k`
and `l - k <= C ((l - n) + log^2 (nu^{-1} l))`. The side condition `2 <= L`
excludes `L = 0`, where no `l` is admissible, and `L = 1`, which forces
`nu = 1`, `n = 0`, `l = 1`; that single corner is handled separately. -/
theorem exists_scaleSeparation (d xi : ℕ) {C0 : ℝ} (hC0 : 0 < C0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 → ∀ n L : ℕ,
        C * Real.log (nu⁻¹ * (L : ℝ)) ^ 2 ≤ (n : ℝ) → ∀ l : ℕ, n < l → l ≤ L → 2 ≤ L →
          ∃ k : ℕ, k < n ∧
            C0 * Real.log (2 + cutoffContrastBound d xi nu k) ^ (2 : ℕ) + (triadicOffset d : ℝ)
                ≤ ((n - k : ℕ) : ℝ) ∧
            ((l - k : ℕ) : ℝ) ≤ C * (((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ 2) := by
  have ht0 : (0 : ℝ) ≤ (triadicOffset d : ℝ) := Nat.cast_nonneg _
  have hK1 : (0 : ℝ) ≤ 3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6 := by
    linarith only [sq_nonneg (scaleSeparationLogConst d xi)]
  have hcoefC : (0 : ℝ) ≤ 4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 :=
    mul_nonneg (by linarith only [hK1]) hC0.le
  refine ⟨4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
    3 * (triadicOffset d : ℝ), by linarith only [hcoefC, ht0], ?_⟩
  intro nu hnu hnu1 n L hnL l hnl hle hL2
  have hC1 : (1 : ℝ) ≤ 4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
      3 * (triadicOffset d : ℝ) := by linarith only [hcoefC, ht0]
  have hainv : (1 : ℝ) ≤ nu⁻¹ := one_le_inv_iff₀.mpr ⟨hnu, hnu1⟩
  have hainnn : (0 : ℝ) ≤ nu⁻¹ := le_trans zero_le_one hainv
  have h2L : (2 : ℝ) ≤ nu⁻¹ * (L : ℝ) := by
    have h1 : (1 : ℝ) * (L : ℝ) ≤ nu⁻¹ * (L : ℝ) :=
      mul_le_mul_of_nonneg_right hainv (Nat.cast_nonneg _)
    have h2 : (2 : ℝ) ≤ (1 : ℝ) * (L : ℝ) := by
      have hL : (2 : ℝ) ≤ (L : ℝ) := Nat.cast_le.2 hL2
      linarith only [hL]
    linarith only [h1, h2]
  -- the degenerate corner `n = 0` is impossible
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero] at hnL
    have hpos : (0 : ℝ) < Real.log (nu⁻¹ * (L : ℝ)) :=
      Real.log_pos (by linarith only [h2L] : (1 : ℝ) < nu⁻¹ * (L : ℝ))
    have hpowL : (0 : ℝ) < Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) := pow_pos hpos 2
    have hlow : (1 : ℝ) * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) ≤
        (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
          3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right hC1 hpowL.le
    have hcon : (0 : ℝ) < (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
        3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) := by
      linarith only [hlow, hpowL]
    exact absurd hnL (not_le.2 hcon)
  -- from here on `n >= 1`, so `l >= 2`
  have hl2 : (2 : ℕ) ≤ l := by omega
  have h2l : (2 : ℝ) ≤ nu⁻¹ * (l : ℝ) := by
    have h1 : (1 : ℝ) * (l : ℝ) ≤ nu⁻¹ * (l : ℝ) :=
      mul_le_mul_of_nonneg_right hainv (Nat.cast_nonneg _)
    have h2 : (2 : ℝ) ≤ (1 : ℝ) * (l : ℝ) := by
      have hl : (2 : ℝ) ≤ (l : ℝ) := Nat.cast_le.2 hl2
      linarith only [hl]
    linarith only [h1, h2]
  have hw0 : (0 : ℝ) ≤ Real.log (nu⁻¹ * (l : ℝ)) :=
    le_trans (Real.log_nonneg (by norm_num)) (Real.log_le_log (by norm_num) h2l)
  have hw1 : (1 : ℝ) ≤ 3 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) :=
    one_le_three_mul_log_sq (Real.log_le_log (by norm_num) h2l)
  have hwLle : Real.log (nu⁻¹ * (l : ℝ)) ≤ Real.log (nu⁻¹ * (L : ℝ)) := by
    refine Real.log_le_log (by linarith only [h2l]) ?_
    have h1 : ((l : ℕ) : ℝ) * nu⁻¹ ≤ (L : ℝ) * nu⁻¹ :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.2 hle) hainnn
    linarith only [h1]
  -- the threshold at `l` is at most a multiple of the square of its log
  have hsq4 : Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
      4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
        Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
    have hlog : Real.log (2 + cutoffContrastBound d xi nu l) ≤
        scaleSeparationLogConst d xi + 2 * Real.log (nu⁻¹ * (l : ℝ)) :=
      log_two_add_cutoffContrastBound_le d xi hnu hnu1 hl2
    have hx0 : (0 : ℝ) ≤ Real.log (2 + cutoffContrastBound d xi nu l) :=
      le_trans (Real.log_nonneg (by norm_num))
        (Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (by linarith only [cutoffContrastBound_nonneg d xi nu l] :
            (2 : ℝ) ≤ 2 + cutoffContrastBound d xi nu l))
    have ht : Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
        (scaleSeparationLogConst d xi + 2 * Real.log (nu⁻¹ * (l : ℝ))) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hx0 hlog 2
    have t1 : (scaleSeparationLogConst d xi + 2 * Real.log (nu⁻¹ * (l : ℝ))) ^ (2 : ℕ) =
        scaleSeparationLogConst d xi ^ (2 : ℕ) +
          4 * scaleSeparationLogConst d xi * Real.log (nu⁻¹ * (l : ℝ)) +
          4 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by ring
    have e : (scaleSeparationLogConst d xi - Real.log (nu⁻¹ * (l : ℝ))) ^ (2 : ℕ) =
        scaleSeparationLogConst d xi ^ (2 : ℕ) -
          2 * scaleSeparationLogConst d xi * Real.log (nu⁻¹ * (l : ℝ)) +
          Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by ring
    have hnon : (0 : ℝ) ≤ (scaleSeparationLogConst d xi -
          Real.log (nu⁻¹ * (l : ℝ))) ^ (2 : ℕ) := sq_nonneg _
    have e2 : (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
        (1 + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) =
        3 * scaleSeparationLogConst d xi ^ (2 : ℕ) +
          3 * scaleSeparationLogConst d xi ^ (2 : ℕ) *
            Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) +
          6 + 6 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by ring
    have hDw : (0 : ℝ) ≤ 3 * scaleSeparationLogConst d xi ^ (2 : ℕ) *
        Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
    have hstep1 : Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
        (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
          (1 + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) := by
      linarith only [ht, t1, e, hnon, e2, hDw]
    have hstep2 : (1 : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) ≤
        4 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
      linarith only [hw1]
    have hK1p : (0 : ℝ) ≤ 3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6 := hK1
    calc Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
        (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
          (1 + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) := hstep1
      _ ≤ (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
            (4 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hstep2 hK1p
      _ = 4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
            Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by ring
  have hΘle : C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
      4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 *
        Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
    calc C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
        C0 * (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) *
          Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsq4 hC0.le
      _ = 4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 *
            Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by ring
  have hΘpos : (0 : ℝ) < C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) := by
    have hlog2 : Real.log 2 ≤ Real.log (2 + cutoffContrastBound d xi nu l) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by linarith only [cutoffContrastBound_nonneg d xi nu l] :
          (2 : ℝ) ≤ 2 + cutoffContrastBound d xi nu l)
    have hpow : (0 : ℝ) < Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) :=
      pow_pos (lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2) 2
    exact mul_pos hC0 hpow
  have hceil : (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) ≤
      C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) + 1 :=
    (Nat.ceil_lt_add_one hΘpos.le).le
  have htw : (triadicOffset d : ℝ) ≤
      3 * (triadicOffset d : ℝ) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hw1 ht0
    linarith only [h]
  have hCw : (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) +
      (triadicOffset d : ℝ) ≤
      (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
        3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
    have h4 : (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
        3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) =
        4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 *
            Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) +
          3 * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) +
          3 * (triadicOffset d : ℝ) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
      ring
    linarith only [hceil, hΘle, htw, h4, hw1]
  have hCwL : (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) +
      (triadicOffset d : ℝ) ≤
      (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
        3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) := by
    have h2 : Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) ≤ Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hw0 hwLle 2
    have h3 : (0 : ℝ) ≤ 4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
        3 * (triadicOffset d : ℝ) := by linarith only [hcoefC, ht0]
    exact le_trans hCw (mul_le_mul_of_nonneg_left h2 h3)
  have hs : ⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
      triadicOffset d ≤ n := by
    have h1 : ((⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d : ℕ) : ℝ) =
        (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) +
          (triadicOffset d : ℝ) := Nat.cast_add _ _
    have h2 : ((⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d : ℕ) : ℝ) ≤
        (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
          3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (L : ℝ)) ^ (2 : ℕ) := by
      rw [h1]
      exact hCwL
    exact Nat.cast_le.mp (le_trans h2 hnL)
  refine ⟨n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
    triadicOffset d), ?_, ?_, ?_⟩
  · have hspos : 0 < ⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
      triadicOffset d := Nat.add_pos_left (Nat.ceil_pos.2 hΘpos) _
    omega
  · -- the first printed inequality, at the chosen `k`
    have hkl : n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d) ≤ l := by omega
    have hnk : n - (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d)) =
        ⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ + triadicOffset d := by
      omega
    have hBk : cutoffContrastBound d xi nu
        (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
          triadicOffset d)) ≤ cutoffContrastBound d xi nu l :=
      cutoffContrastBound_mono d xi hkl
    have hB0 : (0 : ℝ) ≤ cutoffContrastBound d xi nu
        (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
          triadicOffset d)) := cutoffContrastBound_nonneg d xi nu _
    have hlogk : Real.log (2 + cutoffContrastBound d xi nu
        (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
          triadicOffset d))) ≤ Real.log (2 + cutoffContrastBound d xi nu l) :=
      Real.log_le_log (by linarith only [hB0]) (add_le_add_right hBk 2)
    have hsqk : Real.log (2 + cutoffContrastBound d xi nu
        (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
          triadicOffset d))) ^ (2 : ℕ) ≤
        Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hB0])) hlogk 2
    calc C0 * Real.log (2 + cutoffContrastBound d xi nu
          (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
            triadicOffset d))) ^ (2 : ℕ) + (triadicOffset d : ℝ) ≤
        C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) + (triadicOffset d : ℝ) := by
          have h1 : C0 * Real.log (2 + cutoffContrastBound d xi nu
              (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
                triadicOffset d))) ^ (2 : ℕ) ≤
              C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hsqk hC0.le
          linarith only [h1]
      _ ≤ (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) +
          (triadicOffset d : ℝ) := by
          have hle : C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ) ≤
              (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) :=
            Nat.le_ceil _
          linarith only [hle]
      _ = ((n - (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
            triadicOffset d)) : ℕ) : ℝ) := by
          rw [hnk, Nat.cast_add]
  · -- the second printed inequality
    have hlk : l - (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d)) = (l - n) + (⌈C0 * Real.log (2 +
          cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ + triadicOffset d) := by
      omega
    have hcast : (((l - (n - (⌈C0 * Real.log (2 +
          cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ + triadicOffset d)) : ℕ) : ℝ)) =
        ((l - n : ℕ) : ℝ) + ((⌈C0 * Real.log (2 +
          cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ + triadicOffset d : ℕ) : ℝ) := by
      rw [hlk, Nat.cast_add]
    have hcast2 : (((⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
        triadicOffset d : ℕ) : ℝ)) =
        (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) +
          (triadicOffset d : ℝ) := Nat.cast_add _ _
    have hxn : ((l - n : ℕ) : ℝ) ≤ ((l - n : ℕ) : ℝ) *
        (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
          3 * (triadicOffset d : ℝ)) := by
      have h0 : (0 : ℝ) ≤ ((l - n : ℕ) : ℝ) := Nat.cast_nonneg _
      have h2 : ((l - n : ℕ) : ℝ) * 1 ≤ ((l - n : ℕ) : ℝ) *
          (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
            3 * (triadicOffset d : ℝ)) := mul_le_mul_of_nonneg_left hC1 h0
      linarith only [h2]
    calc ((l - (n - (⌈C0 * Real.log (2 + cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ +
          triadicOffset d)) : ℕ) : ℝ) =
        ((l - n : ℕ) : ℝ) + ((⌈C0 * Real.log (2 +
          cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ + triadicOffset d : ℕ) : ℝ) := hcast
      _ ≤ ((l - n : ℕ) : ℝ) + ((⌈C0 * Real.log (2 +
            cutoffContrastBound d xi nu l) ^ (2 : ℕ)⌉₊ : ℝ) + (triadicOffset d : ℝ)) := by
          rw [hcast2]
      _ ≤ ((l - n : ℕ) : ℝ) +
          (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
            3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
          linarith only [hCw]
      _ ≤ ((l - n : ℕ) : ℝ) * (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
            3 * (triadicOffset d : ℝ)) +
          (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
            3 * (triadicOffset d : ℝ)) * Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ) := by
          linarith only [hxn]
      _ = (4 * (3 * scaleSeparationLogConst d xi ^ (2 : ℕ) + 6) * C0 + 3 +
            3 * (triadicOffset d : ℝ)) *
          (((l - n : ℕ) : ℝ) + Real.log (nu⁻¹ * (l : ℝ)) ^ (2 : ℕ)) := by
          ring

/-! ## Positivity of the starred scalar

`shom_{m,*}(cu_n)` is the inverse of `shom_{m,*}^{-1}(cu_n)` (the
scalarization of `e.homs.defs.U.0`), and the latter is positive with no
analytic premise by `sigmaBarStarInvScalar_pos_cutoff` of
`Section2/Annealed/Integrability.lean`. -/

/-- **`shom_{m,*}(cu_n) > 0`** with no analytic premise: the annealed running
diffusivity of the cutoff field is the inverse of the positive scalar of
`shom_{m,*}^{-1}(cu_n)`, the positivity used to invert the lower-right block in
the block extraction. -/
theorem sigmaBarStarScalar_pos {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) (n : ℤ) :
    0 < sigmaBarStarScalar nu m P (cubeSet (originCube d n)) := by
  have h := sigmaBarStarInvScalar_pos_cutoff hnu m hPrefix hJ2 hJ3 hJ4 n
  rw [sigmaBarStarScalar_eq_inv hnu m hJ4 n h]
  exact inv_pos.2 h

end

end SuperdiffusionCLT.Section3.HighContrast