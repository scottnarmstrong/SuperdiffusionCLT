/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume
public import SuperdiffusionCLT.Section2.Annealed.Symmetry
public import Homogenization.Probability.IndependentSums.Triangle
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The global `ω_n : ℕ → ℝ` that the (P3') binder of [AK, Theorem 6.1] needs
(`akhc_weakerP3`: `(∀k,0<omegaSeq k) → Antitone omegaSeq → Tendsto omegaSeq atTop
(nhds 0) → ...`), built as the closed-form majorant of the per-`(j,n)`
amplitude (`ThetaLmP3Prime.lean`'s conclusion), which already depends only
on `n` (not `j`): `ω_n := gammaTriangleConst(1/3) · (Cmix·(L-n)_+^{1/2}·
S(n)⁻¹ + Cmix·(L-n)_+·S(n)⁻² + 3·Cmix·(max 1 n)^{-3000})`, `S(n) :=
sigmaBarStarScalar nu L P (cubeSet (originCube d n))`.

The one change from the raw amplitude is `(max 1 n)^{-3000}` in place
of `n^{-3000}`: at `n = 0`, `Real.rpow 0 (-3000) = 0` (mathlib's junk value
for a nonzero exponent at base `0`), which would make the term *jump up*
from `0` to `1` between `n = 0` and `n = 1` — breaking `Antitone` right at
the start. Since the per-`(j,n)` theorem is only ever invoked at
`n ≥ 1` (the window forces it), `(max 1 n)^{-3000} = n^{-3000}` on the whole
range that matters, so this is a change only at the otherwise-irrelevant
point `n = 0`, not a weakening of what that theorem already proved. -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.HomogBelow

open Homogenization MeasureTheory Filter

variable {d : ℕ} [NeZero d] (nu : ℝ) (hnu : 0 < nu) (L : ℕ) (Cmix : ℝ)
  (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
  (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
  (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P)
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- **`shom_{L,*}(cu_n)` is monotone increasing in `n`**: the reciprocal of
the antitone `sigmaBarStarInvSeq`. -/
theorem homogBelow_sigmaBarStarScalar_mono :
    Monotone (fun n : ℕ => SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) := by
  intro n1 n2 hn12
  dsimp only
  have hpos1 : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n1 :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n1
  have hpos2 : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n2 :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n2
  have hanti := SuperdiffusionCLT.Section2.Annealed.antitone_sigmaBarStarInvSeq
    hnu L hPrefix hJ2 hJ3 hJ4 hn12
  have heq1 : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ))) =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n1)⁻¹ :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n1 : ℤ) hpos1
  have heq2 : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ))) =
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n2)⁻¹ :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n2 : ℤ) hpos2
  rw [heq1, heq2]
  exact (inv_le_inv₀ hpos1 hpos2).2 hanti

/-- **The closed-form majorant `ω_n`**, matching the per-`(j,n)`
amplitude on `n ≥ 1`. -/
noncomputable def homogBelow_omegaSeq (n : ℕ) : ℝ :=
  Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
    (Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
        (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
            (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(1 : ℝ)) +
      (Cmix * ((L - n : ℕ) : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(2 : ℝ)) +
        3 * Cmix * (max 1 (n : ℝ)) ^ (-(3000 : ℝ))))

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- `S(n) > 0` at every scale `n`. -/
theorem homogBelow_sigmaBarStarScalar_pos (n : ℕ) :
    0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
      (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ))) := by
  have hpos : 0 < SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq nu L P n :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n
  rw [SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar_eq_inv hnu L hJ4 (n : ℤ) hpos]
  exact inv_pos.2 hpos

/-- Elementary: `Real.rpow` at a fixed negative exponent is antitone on the
positives. -/
private theorem homogBelow_rpow_neg_anti {a b y : ℝ} (ha : 0 < a) (hab : a ≤ b) (hy : 0 < y) :
    b ^ (-y) ≤ a ^ (-y) := by
  rw [Real.rpow_neg ha.le, Real.rpow_neg (ha.trans_le hab).le]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos (ha.trans_le hab) y)
    (Real.rpow_pos_of_pos ha y)).2 (Real.rpow_le_rpow ha.le hab hy.le)

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- **`ω_n > 0` for every `n`.** -/
theorem homogBelow_omegaSeq_pos (hCmix : 0 < Cmix) (n : ℕ) :
    0 < homogBelow_omegaSeq nu L Cmix P n := by
  have hSpos := homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 n
  have hgc2 : (2 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    Homogenization.IndependentSums.two_le_gammaGrowthConst _
  have hgcpos : 0 < Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    lt_of_lt_of_le (by norm_num) hgc2
  have hgtc : 0 < Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) := by
    unfold Homogenization.IndependentSums.gammaTriangleConst
    have h12 := Real.rpow_pos_of_pos hgcpos (12 : ℝ)
    linarith only [h12]
  have hmax1 : (0 : ℝ) < max 1 (n : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT3pos : 0 < 3 * Cmix * (max 1 (n : ℝ)) ^ (-(3000 : ℝ)) :=
    mul_pos (mul_pos (by norm_num) hCmix) (Real.rpow_pos_of_pos hmax1 _)
  have hT1nonneg : 0 ≤ Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg hCmix.le (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_pos_of_pos hSpos _).le
  have hT2nonneg : 0 ≤ Cmix * ((L - n : ℕ) : ℝ) *
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(2 : ℝ)) :=
    mul_nonneg (mul_nonneg hCmix.le (by positivity)) (Real.rpow_pos_of_pos hSpos _).le
  unfold homogBelow_omegaSeq
  have hsum_pos : 0 <
      Cmix * ((L - n : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(1 : ℝ)) +
        (Cmix * ((L - n : ℕ) : ℝ) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)))) ^ (-(2 : ℝ)) +
          3 * Cmix * (max 1 (n : ℝ)) ^ (-(3000 : ℝ))) := by
    linarith only [hT1nonneg, hT2nonneg, hT3pos]
  exact mul_pos hgtc hsum_pos

include hnu hPrefix hJ2 hJ3 hJ4 in
/-- **`ω_n` is antitone.** -/
theorem homogBelow_omegaSeq_antitone (hCmix : 0 < Cmix) :
    Antitone (homogBelow_omegaSeq nu L Cmix P) := by
  intro n1 n2 hn12
  have hgc2 : (2 : ℝ) ≤ Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    Homogenization.IndependentSums.two_le_gammaGrowthConst _
  have hgcpos : 0 < Homogenization.IndependentSums.gammaGrowthConst ((1 : ℝ) / 3) :=
    lt_of_lt_of_le (by norm_num) hgc2
  have hgtc_nonneg : 0 ≤ Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) := by
    unfold Homogenization.IndependentSums.gammaTriangleConst
    have h12 := (Real.rpow_pos_of_pos hgcpos (12 : ℝ)).le
    linarith only [h12]
  have hS1pos := homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 n1
  have hSle : SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ))) ≤
      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ))) :=
    homogBelow_sigmaBarStarScalar_mono nu hnu L P hPrefix hJ2 hJ3 hJ4 hn12
  have hLn_le : ((L - n2 : ℕ) : ℝ) ≤ ((L - n1 : ℕ) : ℝ) := by
    have : L - n2 ≤ L - n1 := by omega
    exact_mod_cast this
  have hLn2_nonneg : (0 : ℝ) ≤ ((L - n2 : ℕ) : ℝ) := by positivity
  have hSinv1_ge : (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(1 : ℝ)) ≤
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(1 : ℝ)) :=
    homogBelow_rpow_neg_anti hS1pos hSle (by norm_num)
  have hSinv2_ge : (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(2 : ℝ)) ≤
      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(2 : ℝ)) :=
    homogBelow_rpow_neg_anti hS1pos hSle (by norm_num)
  have hpow1half_le : ((L - n2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤ ((L - n1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hLn2_nonneg hLn_le (by norm_num)
  have hT1_le :
      Cmix * ((L - n2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(1 : ℝ)) ≤
        Cmix * ((L - n1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(1 : ℝ)) := by
    have hstep1 : Cmix * ((L - n2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≤
        Cmix * ((L - n1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hpow1half_le hCmix.le
    have hnonneg2 : (0 : ℝ) ≤ (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(1 : ℝ)) :=
      (Real.rpow_pos_of_pos
        (homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 n2) _).le
    exact mul_le_mul hstep1 hSinv1_ge hnonneg2
      (mul_nonneg hCmix.le (Real.rpow_nonneg (by positivity) _))
  have hT2_le :
      Cmix * ((L - n2 : ℕ) : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(2 : ℝ)) ≤
        Cmix * ((L - n1 : ℕ) : ℝ) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(2 : ℝ)) := by
    have hstep1 : Cmix * ((L - n2 : ℕ) : ℝ) ≤ Cmix * ((L - n1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hLn_le hCmix.le
    have hnonneg2 : (0 : ℝ) ≤ (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
        (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(2 : ℝ)) :=
      (Real.rpow_pos_of_pos
        (homogBelow_sigmaBarStarScalar_pos nu hnu L P hPrefix hJ2 hJ3 hJ4 n2) _).le
    exact mul_le_mul hstep1 hSinv2_ge hnonneg2 (mul_nonneg hCmix.le (by positivity))
  have hmax_le : max 1 (n1 : ℝ) ≤ max 1 (n2 : ℝ) := by
    have hcast : (n1 : ℝ) ≤ (n2 : ℝ) := by exact_mod_cast hn12
    exact max_le_max (le_refl 1) hcast
  have hmax1pos : (0 : ℝ) < max 1 (n1 : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hT3_le : 3 * Cmix * (max 1 (n2 : ℝ)) ^ (-(3000 : ℝ)) ≤
      3 * Cmix * (max 1 (n1 : ℝ)) ^ (-(3000 : ℝ)) :=
    mul_le_mul_of_nonneg_left (homogBelow_rpow_neg_anti hmax1pos hmax_le (by norm_num))
      (by positivity)
  unfold homogBelow_omegaSeq
  have hsum_le :
      Cmix * ((L - n2 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(1 : ℝ)) +
        (Cmix * ((L - n2 : ℕ) : ℝ) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (n2 : ℤ)))) ^ (-(2 : ℝ)) +
          3 * Cmix * (max 1 (n2 : ℝ)) ^ (-(3000 : ℝ))) ≤
      Cmix * ((L - n1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
              (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(1 : ℝ)) +
        (Cmix * ((L - n1 : ℕ) : ℝ) *
            (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarScalar nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (n1 : ℤ)))) ^ (-(2 : ℝ)) +
          3 * Cmix * (max 1 (n1 : ℝ)) ^ (-(3000 : ℝ))) := by
    linarith only [hT1_le, hT2_le, hT3_le]
  exact mul_le_mul_of_nonneg_left hsum_le hgtc_nonneg

/-- **`ω_n → 0`.** -/
theorem homogBelow_omegaSeq_tendsto_zero (hL1 : 1 ≤ L) :
    Filter.Tendsto (homogBelow_omegaSeq nu L Cmix P) Filter.atTop (nhds 0) := by
  have heq : (homogBelow_omegaSeq nu L Cmix P) =ᶠ[Filter.atTop]
      (fun n : ℕ => Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
        (3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)))) := by
    filter_upwards [Filter.eventually_ge_atTop L] with n hn
    show homogBelow_omegaSeq nu L Cmix P n = _
    unfold homogBelow_omegaSeq
    have hLn : (L - n : ℕ) = 0 := by omega
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
      have : 1 ≤ n := le_trans hL1 hn
      exact_mod_cast this
    have hmaxn : max 1 (n : ℝ) = (n : ℝ) := max_eq_right hn1
    rw [hLn, hmaxn]
    simp only [Nat.cast_zero]
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)]
    ring
  have h1 : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun x : ℝ => x ^ (-(3000 : ℝ))) Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3000)
  have h3 : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (-(3000 : ℝ))) Filter.atTop (nhds 0) :=
    h2.comp h1
  have h4 : Filter.Tendsto (fun n : ℕ => 3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ)))
      Filter.atTop (nhds (3 * Cmix * 0)) := h3.const_mul (3 * Cmix)
  have h5 : Filter.Tendsto (fun n : ℕ =>
        Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
          (3 * Cmix * (n : ℝ) ^ (-(3000 : ℝ))))
      Filter.atTop (nhds (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) *
        (3 * Cmix * 0))) :=
    h4.const_mul (Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3))
  have h6 : Homogenization.IndependentSums.gammaTriangleConst ((1 : ℝ) / 3) * (3 * Cmix * 0) =
      (0 : ℝ) := by ring
  rw [h6] at h5
  exact h5.congr' heq.symm

end SuperdiffusionCLT.Section4.HomogBelow
