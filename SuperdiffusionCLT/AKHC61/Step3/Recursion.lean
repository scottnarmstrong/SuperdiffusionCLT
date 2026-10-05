/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step3.AlgebraicComparison
public import SuperdiffusionCLT.AKHC61.Step3.VarianceAgain
public import SuperdiffusionCLT.AKHC61.Step2.JBoundSkeleton
public import SuperdiffusionCLT.AKHC61.WeakNorms.WeakNormSqF
public import Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.Recurrence

/-!
# Package E3: the Step 3 recursion (nodes 51, 52, 58)

Source: Step 3 of the proof of Theorem 6.1 of [AK]:
`e.induction.prime#Mnorm-bound`, `e.induction.prime#weaknorm-combination`,
`e.divcurl.conclusion.pre.applied` (external).

## Overview

The recursion is closed in `Step3/RecursionB.lean`, which imports this file. The key points are
to bound `EJ_k` by `O(F m) + O(F k - F m)` rather than by a fixed
constant, and to use a weighted AM-GM inequality with an optimized weight rather than the
naive `δ = 1`; with both, the coefficient on `F m` is driven to exactly the `1/4` budget
supplied by `B1`'s identity, with room to
spare. This file (`Recursion.lean`) carries the self-contained pieces that do not need `B2`'s
raw route-W bound at all: the real-number cores, the deterministic cross-scale identity, the
sharp `EJ` bounds, and the `θ`-producing IterationCore wrapper. `RecursionB.lean` carries the
final assembly (`akhcRec_dropBound_of_P2`), which does instantiate `B2`.

## Main results

* `akhcRec_half_sum_sub_le_product_drop`: the real-number core (mirrors CG's
  `half_sum_sub_le_product_drop`).
* `akhcRec_weighted_amgm`: weighted AM-GM `2√a√b ≤ a/δ + δb`, any `δ > 0` — the coordinator's
  key correction over a naive `δ = 1` bound.
* `akhcRec_sqrt_mul_sqrt_le_of_le`: `2√a√b ≤ 2√A√B` from `a ≤ A`, `b ≤ B`, with no sign
  hypotheses on `a, b` (`Real.sqrt` is unconditionally monotone).
* `akhcRec_crossScaleJ_sub_eq`: the deterministic identity for
  `EJ(cu_k, p_e(m), q_e(m)) − EJ(cu_m, p_e(m), q_e(m))`, any `k, m`, via B1's public formula
  `akhcJB_expectedJ_originCube_eq`.
* `akhcRec_expectedJ_atM_eq` / `akhcRec_expectedJ_atM_le_half_of_P2`: **`EJ(cu_m, p_e(m),
  q_e(m)) ≤ F(m)/2`** exactly (not just `O(1)`).
* `akhcRec_tau_le_of_P2`: **`τ(m,k,e) ≤ Θ_k − Θ_m = F(k) − F(m)` for `k ≤ m`**, the AK.HC
  analogue of CG's `tauAtScale_special_le_thetaAtScale_sub`, proved from B1's public formula +
  the antitonicity of `sigmaBarSeq`/`sigmaBarStarInvSeq` (`Carrier.ScalarBlocks`) + node 60
  (`Θ ≥ 1`) alone — no `hWeakPrime`, no pigeon.
* `akhcRec_expectedJ_atK_le_of_P2`: combines the two above into `EJ_k ≤ (Θ_k−Θ_m) + F(m)/2`,
  genuinely small.
* `akhcRec_hrec_of_dropBound`: the `θ`-producing IterationCore wrapper, directly from CG's
  `scalar_contraction_of_drop_bound` (any `C > 0`; the coefficient budget is not a defect of
  this wrapper — it lives entirely in how the drop-bound premise gets built, in `RecursionB.lean`).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step3

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-! ## Part 1: the real-number core -/

/-- **Pure real-number core** (mirrors CoarseGraining's own
`half_sum_sub_le_product_drop` in `Section56/SmallContrastAlgebraicDecay/ScalarRecursion.lean`):
for `1 ≤ r`, `r ≤ x`, `r ≤ y`, `½(x−r)+½(y−r) ≤ xy−r²`. -/
theorem akhcRec_half_sum_sub_le_product_drop {r x y : ℝ} (hr : 1 ≤ r) (hx : r ≤ x)
    (hy : r ≤ y) :
    (1 / 2 : ℝ) * (x - r) + (1 / 2 : ℝ) * (y - r) ≤ x * y - r ^ (2 : ℕ) := by
  have hx_nonneg : (0 : ℝ) ≤ x - r := by linarith only [hx]
  have hy_nonneg : (0 : ℝ) ≤ y - r := by linarith only [hy]
  nlinarith only [mul_nonneg hx_nonneg hy_nonneg, hr, hx, hy]

/-- **Weighted AM-GM**, `2√a√b ≤ a/δ + δb` for `a, b ≥ 0`, `δ > 0`. Choosing
`δ` freely (rather than `δ = 1`) is what lets the additivity-defect term's self-reference
coefficient be driven arbitrarily small. -/
theorem akhcRec_weighted_amgm {a b δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    2 * Real.sqrt a * Real.sqrt b ≤ a / δ + δ * b := by
  have hu : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hv : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hstep : 2 * δ * (Real.sqrt a * Real.sqrt b) ≤ a + δ ^ 2 * b := by
    nlinarith only [sq_nonneg (Real.sqrt a - δ * Real.sqrt b), hu, hv]
  have hfin : a / δ + δ * b - 2 * Real.sqrt a * Real.sqrt b =
      (a - 2 * δ * (Real.sqrt a * Real.sqrt b) + δ ^ 2 * b) / δ := by
    field_simp
    ring
  have hnn : 0 ≤ (a - 2 * δ * (Real.sqrt a * Real.sqrt b) + δ ^ 2 * b) / δ :=
    div_nonneg (by linarith only [hstep]) hδ.le
  linarith only [hfin, hnn]

/-- **`2√a√b ≤ 2√A√B` from `a ≤ A`, `b ≤ B`** (`Real.sqrt` is unconditionally monotone, no
nonnegativity of `a, b` needed — negative inputs just make `Real.sqrt` return `0`). Lets the
additivity-defect term be bounded through known-nonnegative upper bounds on `τ` and `EJ_k`
without separately establishing `τ ≥ 0` or `EJ_k ≥ 0`. -/
theorem akhcRec_sqrt_mul_sqrt_le_of_le {a b A B : ℝ} (ha : a ≤ A) (hb : b ≤ B) :
    2 * Real.sqrt a * Real.sqrt b ≤ 2 * Real.sqrt A * Real.sqrt B := by
  have h1 : Real.sqrt a ≤ Real.sqrt A := Real.sqrt_le_sqrt ha
  have h2 : Real.sqrt b ≤ Real.sqrt B := Real.sqrt_le_sqrt hb
  have h1' : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have h2' : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have h3 : Real.sqrt a * Real.sqrt b ≤ Real.sqrt A * Real.sqrt b :=
    mul_le_mul_of_nonneg_right h1 h2'
  have h4 : Real.sqrt A * Real.sqrt b ≤ Real.sqrt A * Real.sqrt B :=
    mul_le_mul_of_nonneg_left h2 (h1'.trans h1)
  linarith only [h3, h4]

/-! ## Part 2: the deterministic cross-scale response identity -/

section CrossScale

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4

/-- **Positivity of the geometric-mean scale `σ̂`**, rederived publicly (package B1's own
copy, `akhc_sigmaHatScalar_pos`, is `private`). -/
theorem akhcRec_sigmaHatScalar_pos (m : ℕ) : 0 < akhc_sigmaHatScalar nu L P m := by
  have hB := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hA := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  unfold akhc_sigmaHatScalar
  exact Real.sqrt_pos.2 (div_pos hB hA)

/-- **The deterministic cross-scale identity.** `EJ(cu_k, p_e(m), q_e(m)) −
EJ(cu_m, p_e(m), q_e(m))`, for the special vectors *fixed at scale `m`* but evaluated at any
scale `k`, via B1's public quadratic-form formula `akhcJB_expectedJ_originCube_eq`. -/
theorem akhcRec_crossScaleJ_sub_eq (k m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (k : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) -
      Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (m : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) =
    (1 / 2 : ℝ) * (sigmaBarStarInvSeq nu L P k - sigmaBarStarInvSeq nu L P m) *
        akhc_sigmaHatScalar nu L P m +
      (1 / 2 : ℝ) * (sigmaBarSeq nu L P k - sigmaBarSeq nu L P m) *
        (akhc_sigmaHatScalar nu L P m)⁻¹ := by
  have hc := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have hk := SuperdiffusionCLT.AKHC61.Step2.akhcJB_expectedJ_originCube_eq hnu P L gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 k
    (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e)
  have hm := SuperdiffusionCLT.AKHC61.Step2.akhcJB_expectedJ_originCube_eq hnu P L gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
    (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e)
  rw [hk, hm]
  have he' : vecDot e e = 1 := he
  have hqq : vecDot (akhc_specialQ nu L P m e) (akhc_specialQ nu L P m e) =
      akhc_sigmaHatScalar nu L P m := by
    unfold akhc_specialQ
    rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, he', mul_one, ← Real.rpow_add hc]
    norm_num
  have hpp : vecDot (akhc_specialP nu L P m e) (akhc_specialP nu L P m e) =
      (akhc_sigmaHatScalar nu L P m)⁻¹ := by
    unfold akhc_specialP
    rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, he', mul_one,
      ← Real.rpow_add hc, show (-(1/2:ℝ)) + (-(1/2:ℝ)) = -(1:ℝ) by norm_num,
      Real.rpow_neg hc.le, Real.rpow_one]
  simp only [vecDot_smul_right, hqq, hpp]
  ring

/-- **`p_e(m) · q_e(m) = 1`** (from `he : vecNormSq e = 1`). -/
theorem akhcRec_specialP_dot_specialQ (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    vecDot (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) = 1 := by
  have hc := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have he' : vecDot e e = 1 := he
  unfold akhc_specialP akhc_specialQ
  rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, ← Real.rpow_add hc,
    show (-(1 / 2 : ℝ)) + (1 / 2 : ℝ) = (0 : ℝ) by norm_num, Real.rpow_zero, one_mul, he']

/-- **`EJ(cu_m, p_e(m), q_e(m)) = r − 1`**, `r := akhc_sigmaHatScalar m * sigmaBarStarInvSeq m`
(the same `r` as `akhcRec_tau_le_of_P2`'s proof, exposed here as an exact value, not just a
difference). -/
theorem akhcRec_expectedJ_atM_eq (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (m : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) =
    akhc_sigmaHatScalar nu L P m * sigmaBarStarInvSeq nu L P m - 1 := by
  have hc := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have hBm := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hAm := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have he' : vecDot e e = 1 := he
  have hEq := SuperdiffusionCLT.AKHC61.Step2.akhcJB_expectedJ_originCube_eq hnu P L gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
    (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e)
  have hqq : vecDot (akhc_specialQ nu L P m e) (akhc_specialQ nu L P m e) =
      akhc_sigmaHatScalar nu L P m := by
    unfold akhc_specialQ
    rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, he', mul_one, ← Real.rpow_add hc]
    norm_num
  have hpp : vecDot (akhc_specialP nu L P m e) (akhc_specialP nu L P m e) =
      (akhc_sigmaHatScalar nu L P m)⁻¹ := by
    unfold akhc_specialP
    rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, he', mul_one,
      ← Real.rpow_add hc, show (-(1/2:ℝ)) + (-(1/2:ℝ)) = -(1:ℝ) by norm_num,
      Real.rpow_neg hc.le, Real.rpow_one]
  have hpq := akhcRec_specialP_dot_specialQ hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m e he
  rw [hEq]
  simp only [vecDot_smul_right, hqq, hpp, hpq]
  have hcsq : (akhc_sigmaHatScalar nu L P m) ^ 2 * sigmaBarStarInvSeq nu L P m =
      sigmaBarSeq nu L P m := by
    have hsq : (akhc_sigmaHatScalar nu L P m) ^ 2 =
        sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m := by
      rw [akhc_sigmaHatScalar, Real.sq_sqrt (div_nonneg hBm.le hAm.le)]
    rw [hsq, div_mul_cancel₀]
    exact hAm.ne'
  have hr_alt : akhc_sigmaHatScalar nu L P m * sigmaBarStarInvSeq nu L P m =
      (akhc_sigmaHatScalar nu L P m)⁻¹ * sigmaBarSeq nu L P m := by
    rw [inv_mul_eq_div, eq_div_iff hc.ne']
    linear_combination hcsq
  linear_combination (-(1 / 2 : ℝ)) * hr_alt

/-- **`EJ(cu_m, p_e(m), q_e(m)) ≤ F m / 2`**, `F m := Θ_m − 1` — genuinely small, not `O(1)`:
`(r-1)^2 ≥ 0` applied to `r² = Θ_m`. This is the piece the earlier (retracted) obstruction
analysis was missing; see the coordinator's correction. -/
theorem akhcRec_expectedJ_atM_le_half_of_P2 (m : ℕ) (e : Vec d) (he : vecNormSq e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (m : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) ≤
    (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
  have heq := akhcRec_expectedJ_atM_eq hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
    hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m e he
  rw [heq]
  have hc := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have hBm := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hAm := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hcsq : (akhc_sigmaHatScalar nu L P m) ^ 2 * sigmaBarStarInvSeq nu L P m =
      sigmaBarSeq nu L P m := by
    have hsq : (akhc_sigmaHatScalar nu L P m) ^ 2 =
        sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m := by
      rw [akhc_sigmaHatScalar, Real.sq_sqrt (div_nonneg hBm.le hAm.le)]
    rw [hsq, div_mul_cancel₀]
    exact hAm.ne'
  have hrsq : (akhc_sigmaHatScalar nu L P m * sigmaBarStarInvSeq nu L P m) ^ 2 =
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    have hexpand : (akhc_sigmaHatScalar nu L P m * sigmaBarStarInvSeq nu L P m) ^ 2 =
        (akhc_sigmaHatScalar nu L P m ^ 2 * sigmaBarStarInvSeq nu L P m) *
          sigmaBarStarInvSeq nu L P m := by ring
    rw [hexpand, hcsq, SuperdiffusionCLT.Frozen.Section4.thetaCutoff]
  nlinarith only [sq_nonneg (akhc_sigmaHatScalar nu L P m * sigmaBarStarInvSeq nu L P m - 1), hrsq]

end CrossScale

/-! ## Part 3: the additivity-defect bound `τ(m,k,e) ≤ F(k) − F(m)` -/

section TauBound

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **`τ(m,k,e) ≤ Θ_k − Θ_m`, `k ≤ m`** — the AK.HC analogue of CoarseGraining's
`tauAtScale_special_le_thetaAtScale_sub`, proved from B1's public
formula (`akhcRec_crossScaleJ_sub_eq`), the antitonicity of `sigmaBarSeq`/`sigmaBarStarInvSeq`
(package A2, `Carrier.ScalarBlocks`) and node 60 (`Θ ≥ 1`) alone. No `hWeakPrime`, no pigeon,
no `Θ ≤ B` bound. -/
theorem akhcRec_tau_le_of_P2 {k m : ℕ} (hkm : k ≤ m) (e : Vec d) (he : vecNormSq e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (k : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) -
      Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (m : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) ≤
    SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k -
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
  have heq := akhcRec_crossScaleJ_sub_eq hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 k m e he
  rw [heq]
  have hc := akhcRec_sigmaHatScalar_pos hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m
  have hBm := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
    hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hAm := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hSigmaAnti : sigmaBarSeq nu L P m ≤ sigmaBarSeq nu L P k :=
    akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hStarAnti : sigmaBarStarInvSeq nu L P m ≤ sigmaBarStarInvSeq nu L P k :=
    akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hΘm1 := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  set c := akhc_sigmaHatScalar nu L P m with hc_def
  have hcsq : c ^ 2 * sigmaBarStarInvSeq nu L P m = sigmaBarSeq nu L P m := by
    have hsq : c ^ 2 = sigmaBarSeq nu L P m / sigmaBarStarInvSeq nu L P m := by
      rw [hc_def, akhc_sigmaHatScalar, Real.sq_sqrt (div_nonneg hBm.le hAm.le)]
    rw [hsq, div_mul_cancel₀]
    exact hAm.ne'
  have hr_alt : c * sigmaBarStarInvSeq nu L P m = c⁻¹ * sigmaBarSeq nu L P m := by
    rw [inv_mul_eq_div, eq_div_iff hc.ne']
    linear_combination hcsq
  have hr_sq : (c * sigmaBarStarInvSeq nu L P m) ^ 2 =
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := by
    have hexpand : (c * sigmaBarStarInvSeq nu L P m) ^ 2 =
        (c ^ 2 * sigmaBarStarInvSeq nu L P m) * sigmaBarStarInvSeq nu L P m := by ring
    rw [hexpand, hcsq, SuperdiffusionCLT.Frozen.Section4.thetaCutoff]
  have hr_pos : 0 < c * sigmaBarStarInvSeq nu L P m := mul_pos hc hAm
  have hr1 : (1 : ℝ) ≤ c * sigmaBarStarInvSeq nu L P m := by
    nlinarith only [hr_pos, hr_sq, hΘm1]
  have hrX : c * sigmaBarStarInvSeq nu L P m ≤ c * sigmaBarStarInvSeq nu L P k :=
    mul_le_mul_of_nonneg_left hStarAnti hc.le
  have hrY : c * sigmaBarStarInvSeq nu L P m ≤ c⁻¹ * sigmaBarSeq nu L P k := by
    rw [hr_alt]
    exact mul_le_mul_of_nonneg_left hSigmaAnti (inv_pos.mpr hc).le
  have hXY : (c * sigmaBarStarInvSeq nu L P k) * (c⁻¹ * sigmaBarSeq nu L P k) =
      SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k := by
    rw [SuperdiffusionCLT.Frozen.Section4.thetaCutoff]
    field_simp
  have hcore := akhcRec_half_sum_sub_le_product_drop hr1 hrX hrY
  rw [hXY, hr_sq] at hcore
  calc (1 / 2 : ℝ) * (sigmaBarStarInvSeq nu L P k - sigmaBarStarInvSeq nu L P m) * c +
        (1 / 2 : ℝ) * (sigmaBarSeq nu L P k - sigmaBarSeq nu L P m) * c⁻¹
      = (1 / 2 : ℝ) * (c * sigmaBarStarInvSeq nu L P k - c * sigmaBarStarInvSeq nu L P m) +
          (1 / 2 : ℝ) * (c⁻¹ * sigmaBarSeq nu L P k - c * sigmaBarStarInvSeq nu L P m) := by
        linear_combination (1 / 2 : ℝ) * hr_alt
    _ ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k -
          SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m := hcore

/-- **`EJ(cu_k, p_e(m), q_e(m)) ≤ (Θ_k − Θ_m) + F(m)/2`, `k ≤ m` — genuinely small, not
`O(1)`.** Combines `akhcRec_tau_le_of_P2` (the additivity defect) with
`akhcRec_expectedJ_atM_le_half_of_P2` (`EJ_m ≤ F(m)/2`) via
`EJ_k = (EJ_k − EJ_m) + EJ_m`. Unlike a bound of `EJ_k` by a *fixed*
constant (from `Θ ≤ 2`), this one is
proportional to `F(k), F(m)`, which is what lets the additivity term absorb into the drop-bound
budget after weighted AM-GM (see `akhcRec_dropBound_of_P2` below). -/
theorem akhcRec_expectedJ_atK_le_of_P2 {k m : ℕ} (hkm : k ≤ m) (e : Vec d)
    (he : vecNormSq e = 1) :
    Homogenization.Book.Ch04.expectedResponseJCubeSet (cutoffLaw (d := d) nu L P)
        (Homogenization.originCube d (k : ℤ))
        (akhc_specialP nu L P m e) (akhc_specialQ nu L P m e) ≤
    (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k -
        SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m) +
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P m - 1) / 2 := by
  have htau := akhcRec_tau_le_of_P2 hnu P L hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm e he
  have hM := akhcRec_expectedJ_atM_le_half_of_P2 hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 m e he
  linarith only [htau, hM]

end TauBound

/-! ## Part 4: the `θ`-producing IterationCore wrapper -/

/-- **The IterationCore `hrec`-shape wrapper**, built directly from CoarseGraining's
`scalar_contraction_of_drop_bound` (`Recurrence.lean:19`): given the drop-bound premise in
exactly its own shape, with the quadratic/source split already performed by the caller, produces
`F m ≤ θ * F k + ((F (q m)) ^ 2 + source m)` with `θ := 4C/(1+4C)`, EXACTLY the RHS
`algebraic_decay_induction_core` (`IterationCore.lean:24`) needs for its `hrec` hypothesis at one
fixed `m`. -/
theorem akhcRec_hrec_of_dropBound {Fm Fk FqSq source C : ℝ} (hC : 0 < C) (hFqSq : 0 ≤ FqSq)
    (hsource0 : 0 ≤ source)
    (hdrop : (1 / 4 : ℝ) * Fm ≤ C * ((Fk - Fm) + (FqSq + source))) :
    Fm ≤ (4 * C) / (1 + 4 * C) * Fk + (FqSq + source) :=
  Homogenization.Book.Ch05.Section56.SmallContrastAlgebraicDecay.scalar_contraction_of_drop_bound
    hC (add_nonneg hFqSq hsource0) hdrop

/-! ## Part 5: `Θ̂_k ≤ 2` from a named Step-2 hypothesis, for E2's clean form -/

section StepTwoBound

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

end StepTwoBound

end

end SuperdiffusionCLT.AKHC61.Step3
