/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoOrderOne
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneC

/-!
# The `L̲²` form of the multiscale line of Step 2

This is the `MeasureTheory.MemLp` form of the Step-2 multiscale second moment:
the multiscale second moment with the continuity
hypothesis `hCont` removed from the term-1 chain and replaced by
`MemLp (hilbertifyVecField (G omega)) 2 (normalizedCubeMeasure (originCube d m))`,
which is what the centred glued flux satisfies
(`GluedField.gluedGradientField` is a sum of indicators of triadic sub-cubes and
is not continuous).  The pointwise input is the `L̲²` form of the truncated
multiscale Poincare inequality,
`ShellHminusEndpointOrderOneC.vecHatNegENormOrderOne_le_depthSum_memLp`, in place of
`ShellHminusEndpointOrderOne.vecHatNegENormOrderOne_le_depthSum`.

The statement is otherwise identical to the continuous form, so the term-1 chain
runs unchanged with `hMemLp` feeding the a priori anchor and the concentration
line.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne)

noncomputable section

/-! ## The multiscale line of Step 2 for an `L̲²` field -/

/-- `ofReal` of the mean square of an `L̲²` field is the square of its `L̲²`
norm. -/
private theorem ofRealVecSqAvgEqCF {d : ℕ} (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q)) :
    ENNReal.ofReal (vecSqAvg Q F) = (vecCubeLpENorm Q 2 F) ^ (2 : ℕ) := by
  have hfin : vecCubeLpENorm Q 2 F ≠ ⊤ := hF.eLpNorm_lt_top.ne
  have h : (vecCubeLpENorm Q 2 F).toReal ^ 2 = vecSqAvg Q F :=
    toReal_cubeLpENorm_two_sq Q hF
  rw [← h, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]


private theorem invNinePowCF (j : ℕ) :
    (((3 : ℝ) ^ j)⁻¹) ^ (2 : ℕ) = ((9 : ℝ) ^ j)⁻¹ := by
  have h : ((3 : ℝ) ^ j) ^ (2 : ℕ) = (9 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  rw [inv_pow, h]

private theorem threeRpowNegTwoNatCF (k : ℕ) :
    (3 : ℝ) ^ (-(2 * (k : ℝ))) = ((9 : ℝ) ^ k)⁻¹ := by
  rw [Real.rpow_neg (by norm_num), show (2 : ℝ) * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, pow_mul]
  norm_num

/-- **The multiscale line of the third display of Step 2 for an `L̲²` field**.  This is
the multiscale second moment with the continuity
hypothesis replaced by `L̲²` membership, which is what the centred glued flux
satisfies: `GluedField.gluedGradientField` is a sum of indicators of triadic
sub-cubes and is not continuous. -/
theorem lintegral_vecHatNegENormOrderOne_sq_le_memLp {d : ℕ} (hd : 2 ≤ d)
    (P : ProbabilityMeasure (ShellSeq d)) (ell m : ℕ) (hlm : ell < m)
    (G : ShellSeq d → Vec d → Vec d)
    (hMemLp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (G omega)) 2
        (normalizedCubeMeasure (originCube d (m : ℤ))))
    (hMeasDepth : ∀ j : ℕ, AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecDepthSqMoment (originCube d (m : ℤ)) j (G omega)))
      P.toMeasure)
    (hMeasL2 : AEMeasurable (fun omega : ShellSeq d =>
      vecCubeLpENorm (originCube d (m : ℤ)) 2 (G omega)) P.toMeasure)
    (Cc : ℝ) (hCc : 1 ≤ Cc)
    (hConcDepth : ∀ j : ℕ,
      (∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (vecDepthSqMoment (originCube d (m : ℤ)) j (G omega))
        ∂P.toMeasure : ℝ≥0∞) ≤
        ENNReal.ofReal (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ)))) *
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecSqAvg (originCube d (m : ℤ)) (G omega))
            ∂P.toMeasure : ℝ≥0∞)) :
    (∫⁻ omega : ShellSeq d,
        (vecHatNegENormOrderOne (originCube d (m : ℤ)) (G omega)) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (12 * multiscaleOrderOneConst d ^ (2 : ℕ) * Cc *
          ((m - ell : ℕ) : ℝ) ^ (2 : ℕ) * (((9 : ℝ) ^ (m - ell))⁻¹)) *
        (∫⁻ omega : ShellSeq d,
            (vecCubeLpENorm (originCube d (m : ℤ)) 2 (G omega)) ^ (2 : ℕ)
          ∂P.toMeasure : ℝ≥0∞) := by
  classical
  set Q : TriadicCube d := originCube d (m : ℤ) with hQdef
  set J : ℕ := m - ell with hJdef
  set c : ℝ := multiscaleOrderOneConst d with hcdef
  have hc1 : (1 : ℝ) ≤ c := one_le_multiscaleOrderOneConst d
  have hc0 : (0 : ℝ) < c := lt_of_lt_of_le one_pos hc1
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hJ1 : 1 ≤ J := by rw [hJdef]; omega
  have hJR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ1
  have hCc0 : (0 : ℝ) ≤ Cc := le_trans zero_le_one hCc
  set T : ℝ≥0∞ := ∫⁻ omega : ShellSeq d,
    (vecCubeLpENorm Q 2 (G omega)) ^ (2 : ℕ) ∂P.toMeasure with hTdef
  have hTeq : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (vecSqAvg Q (G omega)) ∂P.toMeasure : ℝ≥0∞) = T :=
    lintegral_congr fun omega => ofRealVecSqAvgEqCF Q (hMemLp omega)
  -- the pointwise multiscale bound, squared and split by Cauchy-Schwarz
  have hpt : ∀ omega : ShellSeq d,
      (vecHatNegENormOrderOne Q (G omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal (2 * c ^ (2 : ℕ) * ((J : ℝ) + 1)) *
          ((∑ j ∈ Finset.range (J + 1), ENNReal.ofReal
              (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))) +
            ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega))) := by
    intro omega
    have hbase := vecHatNegENormOrderOne_le_depthSum_memLp hd0 Q (hMemLp omega) J
    set S1 : ℝ := ∑ j ∈ Finset.range (J + 1),
      ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j (G omega) with hS1def
    set R : ℝ := ((3 : ℝ) ^ J)⁻¹ * Real.sqrt (vecSqAvg Q (G omega)) with hRdef
    have hS10 : (0 : ℝ) ≤ S1 :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (by positivity) (vecDepthMoment_nonneg Q j _)
    have hR0 : (0 : ℝ) ≤ R :=
      mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    have hterm : ∀ j : ℕ, (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j (G omega)) ^ (2 : ℕ)
        = ((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega) := by
      intro j
      rw [mul_pow, invNinePowCF, vecDepthMoment,
        Real.sq_sqrt (vecDepthSqMoment_nonneg Q j _)]
    have hRsq : R ^ (2 : ℕ) = ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega) := by
      rw [hRdef, mul_pow, invNinePowCF, Real.sq_sqrt (vecSqAvg_nonneg Q _)]
    have hcs : S1 ^ (2 : ℕ) ≤ ((J : ℝ) + 1) *
        ∑ j ∈ Finset.range (J + 1), ((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega) := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (J + 1))
        (f := fun j : ℕ => ((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j (G omega))
      rw [Finset.card_range] at h
      have hrw : ∑ j ∈ Finset.range (J + 1),
          (((3 : ℝ) ^ j)⁻¹ * vecDepthMoment Q j (G omega)) ^ (2 : ℕ) =
          ∑ j ∈ Finset.range (J + 1),
            ((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega) :=
        Finset.sum_congr rfl fun j _ => hterm j
      rw [hrw] at h
      have hcast : (((J + 1 : ℕ)) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
      rwa [hcast] at h
    set Sq : ℝ := ∑ j ∈ Finset.range (J + 1),
      ((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega) with hSqdef
    have hSq0 : (0 : ℝ) ≤ Sq :=
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (by positivity) (vecDepthSqMoment_nonneg Q j _)
    have hRsq0 : (0 : ℝ) ≤ ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega) :=
      mul_nonneg (by positivity) (vecSqAvg_nonneg Q _)
    have hsum : (c * (S1 + R)) ^ (2 : ℕ) ≤
        2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) *
          (Sq + ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) := by
      have hsplit : (S1 + R) ^ (2 : ℕ) ≤ 2 * S1 ^ (2 : ℕ) + 2 * R ^ (2 : ℕ) := by
        nlinarith only [sq_nonneg (S1 - R)]
      have hcs' : 2 * S1 ^ (2 : ℕ) ≤ 2 * (((J : ℝ) + 1) * Sq) := by
        linarith only [hcs]
      have hrem : 2 * R ^ (2 : ℕ) ≤
          2 * (((J : ℝ) + 1) * (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega))) := by
        rw [hRsq]
        nlinarith only [hRsq0, hJR]
      have hcsq : (0 : ℝ) ≤ c ^ (2 : ℕ) := by positivity
      have hkey : (S1 + R) ^ (2 : ℕ) ≤
          2 * ((J : ℝ) + 1) * (Sq + ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) := by
        linarith only [hsplit, hcs', hrem]
      have hmul := mul_le_mul_of_nonneg_left hkey hcsq
      calc (c * (S1 + R)) ^ (2 : ℕ) = c ^ (2 : ℕ) * (S1 + R) ^ (2 : ℕ) := by rw [mul_pow]
        _ ≤ c ^ (2 : ℕ) * (2 * ((J : ℝ) + 1) *
              (Sq + ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega))) := hmul
        _ = 2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) *
              (Sq + ((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) := by ring
    have hsq2 : (vecHatNegENormOrderOne Q (G omega)) ^ (2 : ℕ) ≤
        ENNReal.ofReal ((c * (S1 + R)) ^ (2 : ℕ)) := by
      rw [ENNReal.ofReal_pow (by positivity)]
      exact pow_le_pow_left' hbase 2
    refine le_trans hsq2 ?_
    refine le_trans (ENNReal.ofReal_le_ofReal hsum) (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hSq0 hRsq0, hSqdef,
      ENNReal.ofReal_sum_of_nonneg fun j _ =>
        mul_nonneg (by positivity) (vecDepthSqMoment_nonneg Q j _)]
  -- measurability of the integrands of the split
  have hmeasSq : AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (vecSqAvg Q (G omega))) P.toMeasure := by
    refine AEMeasurable.congr (hMeasL2.pow_const 2) ?_
    exact Filter.Eventually.of_forall fun omega =>
      (ofRealVecSqAvgEqCF Q (hMemLp omega)).symm
  have hmeasR : AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega))) P.toMeasure := by
    refine AEMeasurable.congr (hmeasSq.const_mul (ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹))) ?_
    exact Filter.Eventually.of_forall fun omega =>
      (ENNReal.ofReal_mul (by positivity)).symm
  have hmeasD : ∀ j ∈ Finset.range (J + 1), AEMeasurable (fun omega : ShellSeq d =>
      ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))) P.toMeasure := by
    intro j _
    refine AEMeasurable.congr
      ((hMeasDepth j).const_mul (ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹))) ?_
    exact Filter.Eventually.of_forall fun omega =>
      (ENNReal.ofReal_mul (by positivity)).symm
  -- the split of the integral
  have hsplitint : (∫⁻ omega : ShellSeq d,
      ((∑ j ∈ Finset.range (J + 1), ENNReal.ofReal
          (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))) +
        ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega))) ∂P.toMeasure : ℝ≥0∞) =
      (∑ j ∈ Finset.range (J + 1), ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
        ∂P.toMeasure) +
        ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) ∂P.toMeasure := by
    rw [lintegral_add_right' _ hmeasR, lintegral_finsetSum' _ hmeasD]
  -- the per-scale bound
  have hscale : ∀ j ∈ Finset.range (J + 1),
      (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
      ∂P.toMeasure : ℝ≥0∞) ≤ ENNReal.ofReal (Cc * ((9 : ℝ) ^ J)⁻¹) * T := by
    intro j hj
    have hjJ : j ≤ J := by
      have := Finset.mem_range.1 hj; omega
    have hcongr : (∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
      ∂P.toMeasure : ℝ≥0∞) =
        ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹) * ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (vecDepthSqMoment Q j (G omega)) ∂P.toMeasure := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact lintegral_congr fun omega => ENNReal.ofReal_mul (by positivity)
    rw [hcongr]
    refine le_trans (mul_le_mul' le_rfl (hConcDepth j)) ?_
    rw [hTeq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    -- the arithmetic of the scale weights
    have hk : (m - j - ell : ℕ) = J - j := by rw [hJdef]; omega
    have hdec : (3 : ℝ) ^ (-((d : ℝ) * (((J - j : ℕ)) : ℝ))) ≤
        ((9 : ℝ) ^ (J - j))⁻¹ := by
      rw [← threeRpowNegTwoNatCF (J - j)]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      have hkn : (0 : ℝ) ≤ (((J - j : ℕ)) : ℝ) := Nat.cast_nonneg _
      nlinarith only [hdR, hkn]
    have hpow : ((9 : ℝ) ^ j)⁻¹ * ((9 : ℝ) ^ (J - j))⁻¹ = ((9 : ℝ) ^ J)⁻¹ := by
      rw [← mul_inv, ← pow_add]
      congr 2
      omega
    have h9j : (0 : ℝ) < ((9 : ℝ) ^ j)⁻¹ := by positivity
    calc ((9 : ℝ) ^ j)⁻¹ * (Cc * (3 : ℝ) ^ (-((d : ℝ) * ((m - j - ell : ℕ) : ℝ))))
        = Cc * (((9 : ℝ) ^ j)⁻¹ *
            (3 : ℝ) ^ (-((d : ℝ) * (((J - j : ℕ)) : ℝ)))) := by rw [hk]; ring
      _ ≤ Cc * (((9 : ℝ) ^ j)⁻¹ * ((9 : ℝ) ^ (J - j))⁻¹) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hdec h9j.le) hCc0
      _ = Cc * ((9 : ℝ) ^ J)⁻¹ := by rw [hpow]
  have hrem : (∫⁻ omega : ShellSeq d,
      ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) ∂P.toMeasure : ℝ≥0∞) =
      ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹) * T := by
    rw [← hTeq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun omega => ENNReal.ofReal_mul (by positivity)
  -- assembling
  have hbracket : ((∑ j ∈ Finset.range (J + 1), ∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
      ∂P.toMeasure) +
      ∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((9 : ℝ) ^ J)⁻¹ * vecSqAvg Q (G omega)) ∂P.toMeasure) ≤
      ENNReal.ofReal ((((J : ℝ) + 1) * Cc + 1) * ((9 : ℝ) ^ J)⁻¹) * T := by
    have hsumle : (∑ j ∈ Finset.range (J + 1), ∫⁻ omega : ShellSeq d,
        ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
      ∂P.toMeasure) ≤
        ((J + 1 : ℕ)) • (ENNReal.ofReal (Cc * ((9 : ℝ) ^ J)⁻¹) * T) := by
      have h := Finset.sum_le_card_nsmul (Finset.range (J + 1))
        (fun j : ℕ => ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((9 : ℝ) ^ j)⁻¹ * vecDepthSqMoment Q j (G omega))
        ∂P.toMeasure) (ENNReal.ofReal (Cc * ((9 : ℝ) ^ J)⁻¹) * T) hscale
      rwa [Finset.card_range] at h
    have hcastE : (((J + 1 : ℕ)) : ℝ≥0∞) = ENNReal.ofReal (((J : ℝ) + 1)) := by
      rw [show ((J : ℝ) + 1) = (((J + 1 : ℕ)) : ℝ) by push_cast; ring,
        ENNReal.ofReal_natCast]
    have hnsmul : ((J + 1 : ℕ)) • (ENNReal.ofReal (Cc * ((9 : ℝ) ^ J)⁻¹) * T) =
        ENNReal.ofReal (((J : ℝ) + 1) * (Cc * ((9 : ℝ) ^ J)⁻¹)) * T := by
      rw [nsmul_eq_mul, ← mul_assoc, hcastE,
        ← ENNReal.ofReal_mul (by positivity)]
    rw [hnsmul] at hsumle
    refine le_trans (add_le_add hsumle (le_of_eq hrem)) ?_
    rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) le_rfl
    ring
  have hfinal : (∫⁻ omega : ShellSeq d,
      (vecHatNegENormOrderOne Q (G omega)) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ≤
      ENNReal.ofReal (2 * c ^ (2 : ℕ) * ((J : ℝ) + 1)) *
        (ENNReal.ofReal ((((J : ℝ) + 1) * Cc + 1) * ((9 : ℝ) ^ J)⁻¹) * T) := by
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (le_trans (le_of_eq hsplitint) hbracket)
  refine le_trans hfinal ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have h9 : (0 : ℝ) < ((9 : ℝ) ^ J)⁻¹ := by positivity
  have hcsq : (1 : ℝ) ≤ c ^ (2 : ℕ) := one_le_pow₀ hc1
  have hJ1' : (J : ℝ) + 1 ≤ 2 * (J : ℝ) := by linarith only [hJR]
  have hJCc : (0 : ℝ) ≤ ((J : ℝ) - 1) * Cc :=
    mul_nonneg (by linarith only [hJR]) (le_trans zero_le_one hCc)
  have hb : ((J : ℝ) + 1) * Cc + 1 ≤ 3 * (J : ℝ) * Cc := by
    nlinarith only [hJCc, hCc]
  have hstep : 2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) * ((((J : ℝ) + 1) * Cc + 1)) ≤
      12 * c ^ (2 : ℕ) * Cc * (J : ℝ) ^ (2 : ℕ) := by
    have hA : (0 : ℝ) ≤ 2 * c ^ (2 : ℕ) := by positivity
    have hC : (0 : ℝ) ≤ ((J : ℝ) + 1) * Cc + 1 := by positivity
    have h1 : 2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) ≤ 2 * c ^ (2 : ℕ) * (2 * (J : ℝ)) :=
      mul_le_mul_of_nonneg_left hJ1' hA
    have h2 : 2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) * (((J : ℝ) + 1) * Cc + 1) ≤
        2 * c ^ (2 : ℕ) * (2 * (J : ℝ)) * (((J : ℝ) + 1) * Cc + 1) :=
      mul_le_mul_of_nonneg_right h1 hC
    have h3 : 2 * c ^ (2 : ℕ) * (2 * (J : ℝ)) * (((J : ℝ) + 1) * Cc + 1) ≤
        2 * c ^ (2 : ℕ) * (2 * (J : ℝ)) * (3 * (J : ℝ) * Cc) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    have h4 : 2 * c ^ (2 : ℕ) * (2 * (J : ℝ)) * (3 * (J : ℝ) * Cc) =
        12 * c ^ (2 : ℕ) * Cc * (J : ℝ) ^ (2 : ℕ) := by ring
    linarith only [h2, h3, h4]
  calc 2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) * ((((J : ℝ) + 1) * Cc + 1) * ((9 : ℝ) ^ J)⁻¹)
      = (2 * c ^ (2 : ℕ) * ((J : ℝ) + 1) * ((((J : ℝ) + 1) * Cc + 1))) *
          ((9 : ℝ) ^ J)⁻¹ := by ring
    _ ≤ (12 * c ^ (2 : ℕ) * Cc * (J : ℝ) ^ (2 : ℕ)) * ((9 : ℝ) ^ J)⁻¹ :=
        mul_le_mul_of_nonneg_right hstep h9.le

end

end SuperdiffusionCLT.Section3.Terms