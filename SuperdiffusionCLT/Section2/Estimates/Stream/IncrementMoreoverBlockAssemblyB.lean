/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockAssembly

/-!
# The three-term display of the "Moreover" block and its envelope family

`IncrementMoreoverBlockAssembly` supplies the two
random variables the printed envelope family `X_m` of `e.Xm.deff` is built from: the
depth-weighted window maximum `moreoverWindowMax`, whose `Γ₂` amplitude does not
grow with the scale `m`, and the `L∞` envelope `moreoverLinftyBound` of
`k - (k)_{cu_m}` on `cu_m`. This module assembles the printed three-term display
out of them, term by term, at every sample of the summability guard, and gives
the resulting envelope family a `Γ₂` amplitude uniform in `m`.

The negative-norm term is the multiscale Poincaré bridge of
`Section2/Norms/MultiscalePoincareFullGradient.lean` composed with the depth sum, summed
**depth by depth**: the depth-`j` moments inside the cube are below `(1 ⊔ j)`
times the window maximum, and the depths below the cube are below the `L∞`
envelope, whose geometric weight `3^{-s(m+1)}` is kept. Keeping that weight is
what makes the amplitude uniform: both `moreoverLinftyBound` and the joint
maximum at the full window grow linearly in `m`, and only the depth-by-depth
summation converts that growth into a bounded total.

## Main definitions and results

* `cubeMultiscaleDepthSum_le_moreoverWindow`: the depth sum;
  `matHatNegENorm_centeredStreamField_le`, `shellDerivTail_tsum_eq`: the
  negative-norm and derivative-tail terms.
* `moreoverDisplayBound`, `moreoverDisplay_le`: the display envelope.
* `moreoverEnvelope`, `moreoverEnvelopeConst`,
  `isBigO_gammaSigma_moreoverEnvelope`: the family and its uniform amplitude.

## References: `e.Xm.deff`, `e.bounding.the.diff.of.k.union`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The depth moments against the window maximum -/

/-- **The depth-`j` moment of the limiting centered field on `cu_m`** is below
`(1 ⊔ j)` times the depth-weighted window maximum, for every depth `j ≤ m`. -/
theorem cubeDepthPthMoment_rpow_le_moreoverWindowMax (omega : ShellSeq d)
    {m j : ℕ} (hm : 1 ≤ m) (hjm : j ≤ m) {p : ℝ} (hp : 0 < p)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    cubeDepthPthMoment (originCube d (m : ℤ)) j p
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ^ p⁻¹ ≤
      ((max 1 j : ℕ) : ℝ) * moreoverWindowMax (d := d) m omega := by
  have hh : 0 < max 1 j := lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 j)
  have hhm : max 1 j ≤ m := by omega
  have h1 := cubeDepthPthMoment_rpow_le_centeredScaleCubeMax omega
    (le_max_right 1 j) hhm hp hsum
  exact h1.trans (centeredScaleCubeMax_le_mul_moreoverWindowMax hh omega)

/-! ## The depth sum -/

/-- **The depth sum of the limiting centered field, summed depth by depth.**
The depths inside the cube are fed by the depth-weighted window maximum and the
depths below the cube by the `L∞` envelope, whose geometric weight
`3^{-s(m+1)}` is kept. -/
theorem cubeMultiscaleDepthSum_le_moreoverWindow (omega : ShellSeq d)
    {m : ℕ} (hm : 1 ≤ m) {s p : ℝ} (hs : 0 < s) (hp : 0 < p)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    cubeMultiscaleDepthSum (originCube d (m : ℤ)) s p
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal
        (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
          ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
            ((d : ℝ) * moreoverLinftyBound (d := d) m omega)) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := rpow_neg_nonneg s
  have hr1 : (3 : ℝ) ^ (-s) < 1 := rpow_neg_lt_one hs
  have hrnorm : ‖(3 : ℝ) ^ (-s)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hW0 : (0 : ℝ) ≤ moreoverWindowMax (d := d) m omega :=
    moreoverWindowMax_nonneg m omega
  have hL0 : (0 : ℝ) ≤ moreoverLinftyBound (d := d) m omega :=
    moreoverLinftyBound_nonneg m omega
  have hdL0 : (0 : ℝ) ≤ (d : ℝ) * moreoverLinftyBound (d := d) m omega := by
    positivity
  set r : ℝ := (3 : ℝ) ^ (-s) with hrdef
  set W : ℝ := moreoverWindowMax (d := d) m omega with hWdef
  set L : ℝ := (d : ℝ) * moreoverLinftyBound (d := d) m omega with hLdef
  set g1 : ℕ → ℝ := fun j => r ^ j * (((max 1 j : ℕ) : ℝ) * W) with hg1def
  set g2 : ℕ → ℝ := fun j => if m < j then r ^ j * L else 0 with hg2def
  have hg1nonneg : ∀ j, 0 ≤ g1 j := by
    intro j
    simp only [hg1def]
    have : (0 : ℝ) ≤ ((max 1 j : ℕ) : ℝ) := Nat.cast_nonneg _
    positivity
  have hg2nonneg : ∀ j, 0 ≤ g2 j := by
    intro j
    simp only [hg2def]
    by_cases hj : m < j
    · rw [ite_eq_left hj]
      exact mul_nonneg (pow_nonneg hr0 j) hdL0
    · rw [ite_eq_right hj]
  have hmaj1 : Summable fun j : ℕ => (r ^ j + (j : ℝ) * r ^ j) * W := by
    refine Summable.mul_right _ ?_
    refine (summable_geometric_of_lt_one hr0 hr1).add ?_
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm
  have hg1le : ∀ j, g1 j ≤ (r ^ j + (j : ℝ) * r ^ j) * W := by
    intro j
    simp only [hg1def]
    have hmax : ((max 1 j : ℕ) : ℝ) ≤ 1 + (j : ℝ) := by
      have : (max 1 j : ℕ) ≤ 1 + j := by omega
      exact_mod_cast this
    have hrj : (0 : ℝ) ≤ r ^ j := pow_nonneg hr0 j
    have h1 : ((max 1 j : ℕ) : ℝ) * W ≤ (1 + (j : ℝ)) * W :=
      mul_le_mul_of_nonneg_right hmax hW0
    calc r ^ j * (((max 1 j : ℕ) : ℝ) * W)
        ≤ r ^ j * ((1 + (j : ℝ)) * W) := mul_le_mul_of_nonneg_left h1 hrj
      _ = (r ^ j + (j : ℝ) * r ^ j) * W := by ring
  have hg1sum : Summable g1 :=
    Summable.of_nonneg_of_le hg1nonneg hg1le hmaj1
  have hmaj2 : Summable fun j : ℕ => r ^ j * L :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right _
  have hg2le : ∀ j, g2 j ≤ r ^ j * L := by
    intro j
    simp only [hg2def]
    by_cases hj : m < j
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj]
      exact mul_nonneg (pow_nonneg hr0 j) hdL0
  have hg2sum : Summable g2 := Summable.of_nonneg_of_le hg2nonneg hg2le hmaj2
  have hterm : ∀ j : ℕ,
      (3 : ℝ) ^ (-(s * (j : ℝ))) *
        cubeDepthPthMoment (originCube d (m : ℤ)) j p
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ^ p⁻¹ ≤
      g1 j + g2 j := by
    intro j
    have hpow : (3 : ℝ) ^ (-(s * (j : ℝ))) = r ^ j := by
      rw [hrdef, rpow_neg_mul_natCast_eq_pow]
    have hrj : (0 : ℝ) ≤ r ^ j := pow_nonneg hr0 j
    rcases le_or_gt j m with hj | hj
    · have hbound := cubeDepthPthMoment_rpow_le_moreoverWindowMax omega hm hj hp hsum
      have hzero : g2 j = 0 := by
        simp only [hg2def]
        exact ite_eq_right (Nat.not_lt.2 hj)
      rw [hpow, hzero, add_zero]
      simp only [hg1def]
      exact mul_le_mul_of_nonneg_left hbound hrj
    · have hbound := cubeDepthPthMoment_rpow_le_of_entry_bound
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) m j hp hL0
        (fun y hy i k =>
          abs_entry_centeredStreamField_le_moreoverLinftyBound omega m hsum hy i k)
      have hgj : g2 j = r ^ j * L := by
        simp only [hg2def]
        exact ite_eq_left hj
      rw [hpow, hgj]
      have hstep : r ^ j *
          cubeDepthPthMoment (originCube d (m : ℤ)) j p
            (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ^ p⁻¹ ≤
          r ^ j * L := by
        rw [hLdef]
        exact mul_le_mul_of_nonneg_left hbound hrj
      linarith only [hstep, hg1nonneg j]
  have hmajsum : Summable fun j : ℕ => g1 j + g2 j := hg1sum.add hg2sum
  have hnonneg : ∀ j : ℕ, 0 ≤ g1 j + g2 j :=
    fun j => add_nonneg (hg1nonneg j) (hg2nonneg j)
  have htsum1 : ∑' j : ℕ, g1 j ≤ moreoverDepthWeight s * W := by
    refine le_trans (hg1sum.tsum_le_tsum hg1le hmaj1) ?_
    have hval : ∑' j : ℕ, (r ^ j + (j : ℝ) * r ^ j) * W =
        ((1 - r)⁻¹ + r / (1 - r) ^ 2) * W := by
      rw [tsum_mul_right, Summable.tsum_add (summable_geometric_of_lt_one hr0 hr1)
        (by simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrnorm),
        tsum_geometric_of_lt_one hr0 hr1, tsum_coe_mul_geometric_of_norm_lt_one hrnorm]
    rw [hval, moreoverDepthWeight, ← hrdef]
  have htsum2 : ∑' j : ℕ, g2 j = r ^ (m + 1) * (1 - r)⁻¹ * L := by
    have hshift := hg2sum.sum_add_tsum_nat_add (m + 1)
    have hhead : ∑ i ∈ Finset.range (m + 1), g2 i = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hile : ¬ m < i := by
        have := Finset.mem_range.1 hi
        omega
      simp only [hg2def]
      exact ite_eq_right hile
    have htail : ∀ i : ℕ, g2 (i + (m + 1)) = r ^ (m + 1) * r ^ i * L := by
      intro i
      have hlt : m < i + (m + 1) := by omega
      simp only [hg2def]
      rw [ite_eq_left hlt, pow_add]
      ring
    rw [hhead, zero_add] at hshift
    rw [← hshift]
    have hcongr : (fun i : ℕ => g2 (i + (m + 1))) =
        fun i : ℕ => r ^ i * (r ^ (m + 1) * L) := by
      funext i
      rw [htail i]
      ring
    rw [hcongr, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr1]
    ring
  have hfinal : ∑' j : ℕ, (g1 j + g2 j) ≤
      moreoverDepthWeight s * W + r ^ (m + 1) * (1 - r)⁻¹ * L := by
    rw [Summable.tsum_add hg1sum hg2sum, htsum2]
    linarith only [htsum1]
  calc cubeMultiscaleDepthSum (originCube d (m : ℤ)) s p
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))
      ≤ ∑' j : ℕ, ENNReal.ofReal (g1 j + g2 j) := by
        rw [cubeMultiscaleDepthSum]
        exact ENNReal.tsum_le_tsum fun j => ENNReal.ofReal_le_ofReal (hterm j)
    _ = ENNReal.ofReal (∑' j : ℕ, (g1 j + g2 j)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hmajsum).symm
    _ ≤ ENNReal.ofReal (moreoverDepthWeight s * W +
          r ^ (m + 1) * (1 - r)⁻¹ * L) := ENNReal.ofReal_le_ofReal hfinal


/-! ## The negative-norm term -/

/-- **The third term of `e.Xm.deff` in the volume-normalized carrier.** The
multiscale Poincaré bridge of `Section2/Norms/MultiscalePoincareFullGradient.lean`
contributes the prefactor `3^{s m}`, which cancels the printed `3^{-s m}`
exactly, and the depth sum is the one summed depth by depth. -/
theorem matHatNegENorm_centeredStreamField_le (omega : ShellSeq d)
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
        matHatNegENorm (originCube d (m : ℤ)) s 2
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      matHatNegBridgeConstant d *
        ENNReal.ofReal
          (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
            ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
              ((d : ℝ) * moreoverLinftyBound (d := d) m omega)) := by
  have hcont := continuous_centeredStreamField (m := m) omega hguard
  have hpoincare := matHatNegENorm_le_cubeMultiscaleDepthSum
    (originCube d (m : ℤ)) hs0 hs1 (by norm_num : (1 : ℝ) < 2) hcont
  rw [show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]
    norm_num] at hpoincare
  have hscaleReal : (((originCube d (m : ℤ)).scale : ℤ) : ℝ) = (m : ℝ) := by
    simp only [originCube]
    push_cast
    ring
  rw [hscaleReal] at hpoincare
  have hdepth := cubeMultiscaleDepthSum_le_moreoverWindow omega hm hs0
    (by norm_num : (0 : ℝ) < 2) (hguard m)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (s * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
      ENNReal.ofReal ((3 : ℝ) ^ (s * (m : ℝ))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    norm_num
  calc ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
        matHatNegENorm (originCube d (m : ℤ)) s 2
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))
      ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
          (matHatNegBridgeConstant d *
            ENNReal.ofReal ((3 : ℝ) ^ (s * (m : ℝ))) *
              cubeMultiscaleDepthSum (originCube d (m : ℤ)) s 2
                (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) :=
        mul_le_mul' le_rfl hpoincare
    _ ≤ ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
          (matHatNegBridgeConstant d *
            ENNReal.ofReal ((3 : ℝ) ^ (s * (m : ℝ))) *
              ENNReal.ofReal
                (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
                  ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
                    ((d : ℝ) * moreoverLinftyBound (d := d) m omega))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hdepth)
    _ = (ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
            ENNReal.ofReal ((3 : ℝ) ^ (s * (m : ℝ)))) *
          (matHatNegBridgeConstant d *
            ENNReal.ofReal
              (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
                ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
                  ((d : ℝ) * moreoverLinftyBound (d := d) m omega))) := by
        ring
    _ = matHatNegBridgeConstant d *
          ENNReal.ofReal
            (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
              ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
                ((d : ℝ) * moreoverLinftyBound (d := d) m omega)) := by
        rw [hcancel, one_mul]


/-! ## The derivative-tail term -/

/-- **The derivative-tail term of the printed display is the gauge `shellDerivTailGauge`.** On
the summability guard the `ℝ≥0∞` series of the display is the `ENNReal.ofReal`
of the real series of `shellDerivTailGauge`. -/
theorem shellDerivTail_tsum_eq (omega : ShellSeq d) (m : ℕ)
    (hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    ENNReal.ofReal ((3 : ℝ) ^ m) *
        (∑' k : ℕ, ENNReal.ofReal
          (shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
            (omega (m + 1 + k)))) =
      ENNReal.ofReal (shellDerivTailGauge m omega) := by
  have hshift := summable_shellDerivLinftyNorm_shift hsum m
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun k => shellDerivLinftyNorm_nonneg _ _) hshift,
    ← ENNReal.ofReal_mul (by positivity), shellDerivTailGauge_eq_tsum]

/-! ## The three-term display -/

/-- The explicit real envelope of the printed three-term display of
`e.Xm.deff`. -/
def moreoverDisplayBound (s : ℝ) (m : ℕ) (omega : ShellSeq d) : ℝ :=
  ((m : ℝ))⁻¹ * moreoverLinftyBound (d := d) m omega +
      shellDerivTailGauge m omega +
    (matHatNegBridgeConstant d).toReal *
      (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
        ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
          ((d : ℝ) * moreoverLinftyBound (d := d) m omega))

theorem moreoverDisplayBound_nonneg {s : ℝ} (hs : 0 < s) (m : ℕ)
    (omega : ShellSeq d) : 0 ≤ moreoverDisplayBound (d := d) s m omega := by
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    linarith only [rpow_neg_lt_one hs]
  have hL := moreoverLinftyBound_nonneg (d := d) m omega
  have h1 : (0 : ℝ) ≤ ((m : ℝ))⁻¹ * moreoverLinftyBound (d := d) m omega :=
    mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)) hL
  have h2 : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal *
      (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
        ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
          ((d : ℝ) * moreoverLinftyBound (d := d) m omega)) :=
    mul_nonneg ENNReal.toReal_nonneg
      (add_nonneg (mul_nonneg (moreoverDepthWeight_nonneg hs)
        (moreoverWindowMax_nonneg m omega))
        (mul_nonneg (mul_nonneg (pow_nonneg (rpow_neg_nonneg s) _)
          (inv_nonneg.2 hpos.le)) (mul_nonneg (Nat.cast_nonneg d) hL)))
  rw [moreoverDisplayBound]
  linarith only [h1, h2, shellDerivTailGauge_nonneg m omega]

/-- **The printed three-term display of `e.Xm.deff` is dominated by the
explicit envelope**, at every sample of the summability guard and at every
scale `m ≥ 1`. -/
theorem moreoverDisplay_le (omega : ShellSeq d) {m : ℕ} (hm : 1 ≤ m) {s : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1)
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k)) :
    ENNReal.ofReal (((m : ℝ))⁻¹) *
          cubeLpENorm (originCube d (m : ℤ)) ∞
            (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) +
        ENNReal.ofReal ((3 : ℝ) ^ m) *
          (∑' k : ℕ, ENNReal.ofReal
            (shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
              (omega (m + 1 + k)))) +
      ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
        matHatNegENorm (originCube d (m : ℤ)) s 2
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal (moreoverDisplayBound (d := d) s m omega) := by
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    linarith only [rpow_neg_lt_one hs0]
  have hL := moreoverLinftyBound_nonneg (d := d) m omega
  have hG := shellDerivTailGauge_nonneg m omega
  have hbrackets : (0 : ℝ) ≤
      moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
        ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
          ((d : ℝ) * moreoverLinftyBound (d := d) m omega) :=
    add_nonneg (mul_nonneg (moreoverDepthWeight_nonneg hs0)
      (moreoverWindowMax_nonneg m omega))
      (mul_nonneg (mul_nonneg (pow_nonneg (rpow_neg_nonneg s) _)
        (inv_nonneg.2 hpos.le)) (mul_nonneg (Nat.cast_nonneg d) hL))
  have hfirst : ENNReal.ofReal (((m : ℝ))⁻¹) *
      cubeLpENorm (originCube d (m : ℤ)) ∞
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal (((m : ℝ))⁻¹ * moreoverLinftyBound (d := d) m omega) := by
    refine le_trans (mul_le_mul' le_rfl
      (cubeLpENorm_infty_centeredStreamField_le_moreoverLinftyBound omega m
        (hguard m))) ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hsecond := shellDerivTail_tsum_eq omega m (hguard m)
  have hthird := matHatNegENorm_centeredStreamField_le omega hm hs0 hs1 hguard
  have hCtop : matHatNegBridgeConstant d ≠ ⊤ := (matHatNegBridgeConstant_lt_top d).ne
  have hthird' : ENNReal.ofReal ((3 : ℝ) ^ (-(s * (m : ℝ)))) *
      matHatNegENorm (originCube d (m : ℤ)) s 2
        (centeredStreamField omega (cubeSet (originCube d (m : ℤ)))) ≤
      ENNReal.ofReal ((matHatNegBridgeConstant d).toReal *
        (moreoverDepthWeight s * moreoverWindowMax (d := d) m omega +
          ((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ *
            ((d : ℝ) * moreoverLinftyBound (d := d) m omega))) := by
    refine le_trans hthird (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtop]
  rw [hsecond]
  refine le_trans (add_le_add (add_le_add hfirst le_rfl) hthird') (le_of_eq ?_)
  rw [moreoverDisplayBound, ← ENNReal.ofReal_add (by positivity) hG,
    ← ENNReal.ofReal_add (by positivity) (mul_nonneg ENNReal.toReal_nonneg hbrackets)]


/-! ## The uniform growth of the `L∞` amplitude -/

/-- The uniform growth constant of the `L∞` amplitude: it bounds both
`m⁻¹ moreoverLinftyAmp d m` for `m ≥ 1` and `moreoverLinftyAmp d m / (1 + m)`. -/
def moreoverLinftyGrowthConst (d : ℕ) : ℝ :=
  16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
      (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) + 2 +
    (d : ℝ) * Real.sqrt d * streamDerivTailConst)

theorem moreoverLinftyAmp_eq (d m : ℕ) :
    moreoverLinftyAmp d m =
      16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
          (shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
            largeCubeLinftyConst d * (m : ℝ)) + 2 +
        (d : ℝ) * Real.sqrt d * streamDerivTailConst) := by
  rw [moreoverLinftyAmp, streamCutoffLinftyGammaTwoAmplitude,
    Real.mul_self_sqrt (Nat.cast_nonneg m)]
  ring

theorem moreoverLinftyAmp_nonneg {d : ℕ} (hCl : 0 ≤ largeCubeLinftyConst d)
    (m : ℕ) : 0 ≤ moreoverLinftyAmp d m := by
  have hS := streamCutoffLinftyGammaTwoAmplitude_nonneg hCl d m m
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have h1 : (0 : ℝ) ≤ (1 + (d : ℝ)) *
      streamCutoffLinftyGammaTwoAmplitude (largeCubeLinftyConst d) d m m :=
    mul_nonneg (by positivity) hS
  rw [moreoverLinftyAmp]
  linarith only [h1, hD]

theorem moreoverLinftyGrowthConst_nonneg {d : ℕ}
    (hCl : 0 ≤ largeCubeLinftyConst d) : 0 ≤ moreoverLinftyGrowthConst d := by
  have hG := gammaTriangleConst_two_nonneg
  have hV : (0 : ℝ) ≤ shellValueLargeCubeConst d :=
    le_trans zero_le_one (one_le_shellValueLargeCubeConst d)
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have hbig : (0 : ℝ) ≤ (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
      (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) := by
    have h1 : (0 : ℝ) ≤ (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 :=
      mul_nonneg (by positivity) hG
    exact mul_nonneg h1 (by linarith only [hV, hCl])
  rw [moreoverLinftyGrowthConst]
  linarith only [hbig, hD]

/-- The `L∞` amplitude divided by the scale is uniformly bounded. -/
theorem inv_mul_moreoverLinftyAmp_le {d m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ))⁻¹ * moreoverLinftyAmp d m ≤ moreoverLinftyGrowthConst d := by
  have hG := gammaTriangleConst_two_nonneg
  have hV : (0 : ℝ) ≤ shellValueLargeCubeConst d :=
    le_trans zero_le_one (one_le_shellValueLargeCubeConst d)
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hminv : ((m : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    exact Or.inr hm1
  have hminv0 : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := (inv_pos.2 hmpos).le
  have hsqrt : Real.sqrt (1 + (m : ℝ)) ≤ 2 * (m : ℝ) := by
    have hle : 1 + (m : ℝ) ≤ (2 * (m : ℝ)) ^ 2 := by nlinarith only [hm1]
    calc Real.sqrt (1 + (m : ℝ)) ≤ Real.sqrt ((2 * (m : ℝ)) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 2 * (m : ℝ) := Real.sqrt_sq (by linarith only [hm1])
  have hA : (0 : ℝ) ≤ (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 :=
    mul_nonneg (by positivity) hG
  have hstep : (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
      (shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
        largeCubeLinftyConst d * (m : ℝ)) ≤
      (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
        ((2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) * (m : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    nlinarith only [hV, hsqrt]
  have hmul : ((m : ℝ))⁻¹ * (m : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hmpos)
  have h2D : (0 : ℝ) ≤ 2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    linarith only [hD]
  rw [moreoverLinftyAmp_eq, moreoverLinftyGrowthConst]
  calc ((m : ℝ))⁻¹ * (16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
          (shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
            largeCubeLinftyConst d * (m : ℝ)) + 2 +
        (d : ℝ) * Real.sqrt d * streamDerivTailConst))
      ≤ ((m : ℝ))⁻¹ * (16384 * ((1 + (d : ℝ)) *
            IndependentSums.gammaTriangleConst 2 *
              ((2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) *
                (m : ℝ)) + 2 +
          (d : ℝ) * Real.sqrt d * streamDerivTailConst)) := by
        refine mul_le_mul_of_nonneg_left ?_ hminv0
        linarith only [hstep]
    _ = 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
            (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) *
              (((m : ℝ))⁻¹ * (m : ℝ)) +
          ((m : ℝ))⁻¹ * (2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst)) := by
        ring
    _ = 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
            (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) +
          ((m : ℝ))⁻¹ * (2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst)) := by
        rw [hmul, mul_one]
    _ ≤ 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
            (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) +
          1 * (2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst)) := by
        have := mul_le_mul_of_nonneg_right hminv h2D
        linarith only [this]
    _ = 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
          (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) + 2 +
        (d : ℝ) * Real.sqrt d * streamDerivTailConst) := by ring

/-- The `L∞` amplitude grows at most linearly in the scale. -/
theorem moreoverLinftyAmp_le_mul {d : ℕ} (hCl : 0 ≤ largeCubeLinftyConst d)
    (m : ℕ) :
    moreoverLinftyAmp d m ≤ moreoverLinftyGrowthConst d * (1 + (m : ℝ)) := by
  have hG := gammaTriangleConst_two_nonneg
  have hV : (0 : ℝ) ≤ shellValueLargeCubeConst d :=
    le_trans zero_le_one (one_le_shellValueLargeCubeConst d)
  have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have h0 : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsqrt : Real.sqrt (1 + (m : ℝ)) ≤ 2 * (1 + (m : ℝ)) := by
    have hle : 1 + (m : ℝ) ≤ (2 * (1 + (m : ℝ))) ^ 2 := by nlinarith only [hm0]
    calc Real.sqrt (1 + (m : ℝ)) ≤ Real.sqrt ((2 * (1 + (m : ℝ))) ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = 2 * (1 + (m : ℝ)) := Real.sqrt_sq (by linarith only [hm0])
  have hA : (0 : ℝ) ≤ (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 :=
    mul_nonneg (by positivity) hG
  have hstep : (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
      (shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
        largeCubeLinftyConst d * (m : ℝ)) ≤
      (1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
        ((2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) *
          (1 + (m : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hA
    nlinarith only [hV, hsqrt, hCl, hm0]
  have h2D : (0 : ℝ) ≤ 2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    linarith only [hD]
  have hone : (1 : ℝ) ≤ 1 + (m : ℝ) := by linarith only [hm0]
  rw [moreoverLinftyAmp_eq, moreoverLinftyGrowthConst]
  calc 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
          (shellValueLargeCubeConst d * Real.sqrt (1 + (m : ℝ)) +
            largeCubeLinftyConst d * (m : ℝ)) + 2 +
        (d : ℝ) * Real.sqrt d * streamDerivTailConst)
      ≤ 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
            ((2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) *
              (1 + (m : ℝ))) + 2 +
          (d : ℝ) * Real.sqrt d * streamDerivTailConst) := by
        linarith only [hstep]
    _ ≤ 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
            ((2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) *
              (1 + (m : ℝ))) +
          (2 + (d : ℝ) * Real.sqrt d * streamDerivTailConst) * (1 + (m : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hone h2D
        linarith only [this]
    _ = 16384 * ((1 + (d : ℝ)) * IndependentSums.gammaTriangleConst 2 *
          (2 * shellValueLargeCubeConst d + largeCubeLinftyConst d) + 2 +
        (d : ℝ) * Real.sqrt d * streamDerivTailConst) * (1 + (m : ℝ)) := by ring


/-! ## The envelope family and its uniform amplitude -/

/-- The coefficient of the `L∞` envelope in the printed envelope family. -/
def moreoverDisplayScale (d : ℕ) (s : ℝ) (m : ℕ) : ℝ :=
  ((m : ℝ))⁻¹ + (matHatNegBridgeConstant d).toReal *
    (((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ))

/-- The coefficient of the window maximum in the printed envelope family. -/
def moreoverWindowScale (d : ℕ) (s : ℝ) : ℝ :=
  (matHatNegBridgeConstant d).toReal * moreoverDepthWeight s + 1

/-- **The printed envelope family `X_m` of `e.Xm.deff`**: the envelope of the
three-term display together with the depth-weighted window maximum, which is
what clause (ii) consumes. -/
def moreoverEnvelope (s : ℝ) (m : ℕ) (omega : ShellSeq d) : ℝ :=
  moreoverDisplayBound s m omega + moreoverWindowMax (d := d) m omega

theorem moreoverEnvelope_eq (s : ℝ) (m : ℕ) (omega : ShellSeq d) :
    moreoverEnvelope (d := d) s m omega =
      moreoverDisplayScale d s m * moreoverLinftyBound (d := d) m omega +
        shellDerivTailGauge m omega +
        moreoverWindowScale d s * moreoverWindowMax (d := d) m omega := by
  rw [moreoverEnvelope, moreoverDisplayBound, moreoverDisplayScale,
    moreoverWindowScale]
  ring

theorem measurable_moreoverEnvelope (s : ℝ) (m : ℕ) :
    Measurable (moreoverEnvelope (d := d) s m) := by
  have hfun : moreoverEnvelope (d := d) s m =
      fun omega => moreoverDisplayScale d s m * moreoverLinftyBound (d := d) m omega +
        shellDerivTailGauge m omega +
        moreoverWindowScale d s * moreoverWindowMax (d := d) m omega :=
    funext fun omega => moreoverEnvelope_eq s m omega
  rw [hfun]
  exact (((measurable_moreoverLinftyBound m).const_mul _).add
    (measurable_shellDerivTailGauge m)).add
      ((measurable_moreoverWindowMax m).const_mul _)

/-- The uniform bound on the `L∞` contribution to the amplitude of the
envelope family. -/
def moreoverLinftyUniformBound (d : ℕ) (s : ℝ) : ℝ :=
  moreoverLinftyGrowthConst d *
    (1 + (matHatNegBridgeConstant d).toReal * (1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ) *
      (s * Real.log 3)⁻¹)

theorem moreoverDisplayScale_nonneg (d : ℕ) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    0 ≤ moreoverDisplayScale d s m := by
  have hpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by
    linarith only [rpow_neg_lt_one hs]
  rw [moreoverDisplayScale]
  exact add_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)) (mul_nonneg
    ENNReal.toReal_nonneg (mul_nonneg (mul_nonneg
      (pow_nonneg (rpow_neg_nonneg s) _) (inv_nonneg.2 hpos.le))
      (Nat.cast_nonneg d)))

/-- **The `L∞` contribution to the amplitude is uniform in the scale.** -/
theorem moreoverDisplayScale_mul_moreoverLinftyAmp_le {d : ℕ}
    (hCl : 0 ≤ largeCubeLinftyConst d) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    moreoverDisplayScale d s m * moreoverLinftyAmp d m ≤
      moreoverLinftyUniformBound d s := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-s) := rpow_neg_nonneg s
  have hr1 : (3 : ℝ) ^ (-s) < 1 := rpow_neg_lt_one hs
  have hrpos : (0 : ℝ) < 1 - (3 : ℝ) ^ (-s) := by linarith only [hr1]
  have hC : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal := ENNReal.toReal_nonneg
  have hgrowth := moreoverLinftyGrowthConst_nonneg hCl
  have hamp := moreoverLinftyAmp_nonneg hCl m
  have hfirst : ((m : ℝ))⁻¹ * moreoverLinftyAmp d m ≤
      moreoverLinftyGrowthConst d := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm1
    · subst hm0
      simp only [Nat.cast_zero, inv_zero, zero_mul]
      exact hgrowth
    · exact inv_mul_moreoverLinftyAmp_le hm1
  have hpowamp : ((3 : ℝ) ^ (-s)) ^ (m + 1) * moreoverLinftyAmp d m ≤
      moreoverLinftyGrowthConst d * (s * Real.log 3)⁻¹ := by
    have hstep : ((3 : ℝ) ^ (-s)) ^ (m + 1) * moreoverLinftyAmp d m ≤
        ((3 : ℝ) ^ (-s)) ^ (m + 1) *
          (moreoverLinftyGrowthConst d * (1 + (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (moreoverLinftyAmp_le_mul hCl m)
        (pow_nonneg hr0 _)
    refine hstep.trans ?_
    have hkey := pow_rpow_neg_mul_succ_le hs m
    calc ((3 : ℝ) ^ (-s)) ^ (m + 1) *
          (moreoverLinftyGrowthConst d * (1 + (m : ℝ)))
        = moreoverLinftyGrowthConst d *
            (((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 + (m : ℝ))) := by ring
      _ ≤ moreoverLinftyGrowthConst d * (s * Real.log 3)⁻¹ :=
          mul_le_mul_of_nonneg_left hkey hgrowth
  have hcoef : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal *
      ((1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) := by positivity
  have hsecond : (matHatNegBridgeConstant d).toReal *
        (((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
          moreoverLinftyAmp d m ≤
      (matHatNegBridgeConstant d).toReal * ((1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
        (moreoverLinftyGrowthConst d * (s * Real.log 3)⁻¹) := by
    have := mul_le_mul_of_nonneg_left hpowamp hcoef
    calc (matHatNegBridgeConstant d).toReal *
          (((3 : ℝ) ^ (-s)) ^ (m + 1) * (1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
            moreoverLinftyAmp d m
        = (matHatNegBridgeConstant d).toReal *
            ((1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
              (((3 : ℝ) ^ (-s)) ^ (m + 1) * moreoverLinftyAmp d m) := by ring
      _ ≤ (matHatNegBridgeConstant d).toReal *
            ((1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
              (moreoverLinftyGrowthConst d * (s * Real.log 3)⁻¹) := by
          linarith only [this]
  rw [moreoverDisplayScale, moreoverLinftyUniformBound, add_mul]
  have hgoal : moreoverLinftyGrowthConst d +
      (matHatNegBridgeConstant d).toReal * ((1 - (3 : ℝ) ^ (-s))⁻¹ * (d : ℝ)) *
        (moreoverLinftyGrowthConst d * (s * Real.log 3)⁻¹) =
      moreoverLinftyGrowthConst d *
        (1 + (matHatNegBridgeConstant d).toReal * (1 - (3 : ℝ) ^ (-s))⁻¹ *
          (d : ℝ) * (s * Real.log 3)⁻¹) := by ring
  linarith only [hfirst, hsecond, hgoal]


/-- The uniform `Γ₂` amplitude of the envelope family. -/
def moreoverEnvelopeConst (d : ℕ) (s : ℝ) : ℝ :=
  16384 * (moreoverLinftyUniformBound d s + 1 + (streamDerivTailConst + 1) +
    (moreoverWindowScale d s * moreoverWindowConst d + 1))

/-- **The envelope family of `e.Xm.deff` has a `Γ₂` amplitude that does not
grow with the cube scale.** -/
theorem isBigO_gammaSigma_moreoverEnvelope (hPrefix : ShellLawPrefix d P)
    (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) {s : ℝ} (hs : 0 < s) (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (moreoverEnvelope (d := d) s m) (moreoverEnvelopeConst d s) := by
  classical
  have hstc : (0 : ℝ) ≤ streamDerivTailConst := by
    rw [streamDerivTailConst]; norm_num
  have hCl : (0 : ℝ) ≤ largeCubeLinftyConst d :=
    (largeCubeLinftyConst_pos hPrefix).le
  have hcL := moreoverDisplayScale_nonneg d hs m
  have hcW : (0 : ℝ) ≤ moreoverWindowScale d s := by
    have h2 : (0 : ℝ) ≤ (matHatNegBridgeConstant d).toReal *
        moreoverDepthWeight s :=
      mul_nonneg ENNReal.toReal_nonneg (moreoverDepthWeight_nonneg hs)
    rw [moreoverWindowScale]; linarith only [h2]
  have hwc : (0 : ℝ) ≤ moreoverWindowConst d := by
    have hD : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
      positivity
    have h1 : (0 : ℝ) ≤ centeredCubeAverageConst d := by
      rw [centeredCubeAverageConst]
      linarith only [coarseAverageDiffConst_nonneg d, hD]
    rw [moreoverWindowConst]
    exact mul_nonneg h1 (Real.sqrt_nonneg _)
  have hamp := moreoverLinftyAmp_nonneg hCl m
  set X : Fin 3 → ShellSeq d → ℝ :=
    ![fun omega => moreoverDisplayScale d s m *
        moreoverLinftyBound (d := d) m omega,
      fun omega => shellDerivTailGauge m omega,
      fun omega => moreoverWindowScale d s *
        moreoverWindowMax (d := d) m omega] with hX
  set a : Fin 3 → ℝ :=
    ![moreoverDisplayScale d s m * moreoverLinftyAmp d m + 1,
      streamDerivTailConst + 1,
      moreoverWindowScale d s * moreoverWindowConst d + 1] with ha
  have h0 : (0 : ℝ) ≤ moreoverDisplayScale d s m * moreoverLinftyAmp d m :=
    mul_nonneg hcL hamp
  have h2 : (0 : ℝ) ≤ moreoverWindowScale d s * moreoverWindowConst d :=
    mul_nonneg hcW hwc
  have hapos : ∀ i, 0 < a i := by
    intro i
    fin_cases i
    · show (0 : ℝ) < moreoverDisplayScale d s m * moreoverLinftyAmp d m + 1
      linarith only [h0]
    · show (0 : ℝ) < streamDerivTailConst + 1
      linarith only [hstc]
    · show (0 : ℝ) < moreoverWindowScale d s * moreoverWindowConst d + 1
      linarith only [h2]
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    fin_cases i
    · exact (measurable_moreoverLinftyBound (d := d) m).const_mul _
    · exact measurable_shellDerivTailGauge (d := d) m
    · exact (measurable_moreoverWindowMax (d := d) m).const_mul _
  have hXbig : ∀ i, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2) (X i) (a i) := by
    intro i
    fin_cases i
    · refine ((isBigO_gammaSigma_moreoverLinftyBound hPrefix hJ2 hJ3 hJ4
        m).const_mul hcL).mono_scale ?_
      show moreoverDisplayScale d s m * moreoverLinftyAmp d m ≤
        moreoverDisplayScale d s m * moreoverLinftyAmp d m + 1
      linarith only []
    · refine (isBigO_gammaSigma_shellDerivTailGauge (P := P) hJ3 m).mono_scale ?_
      show streamDerivTailConst ≤ streamDerivTailConst + 1
      linarith only []
    · refine (((SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
        (fun omega => moreoverWindowMax_nonneg m omega)).1
          (isBigOWith_gammaSigma_moreoverWindowMax hPrefix hJ1 hJ2 hJ3 hJ4
            m)).const_mul hcW).mono_scale ?_
      show moreoverWindowScale d s * moreoverWindowConst d ≤
        moreoverWindowScale d s * moreoverWindowConst d + 1
      linarith only []
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finSum_of_one_le
    (mu := P.toMeasure) (N := 3) (X := X) (a := a) (sigma := 2)
    (by norm_num) (by norm_num) hapos hXbig hXmeas
  have hfun : (fun omega : ShellSeq d => ∑ i, X i omega) =
      moreoverEnvelope (d := d) s m := by
    funext omega
    rw [Fin.sum_univ_three, moreoverEnvelope_eq]
    rfl
  rw [hfun] at hsum
  refine hsum.mono_scale ?_
  rw [moreoverEnvelopeConst, Fin.sum_univ_three]
  have hle := moreoverDisplayScale_mul_moreoverLinftyAmp_le hCl hs m
  have hshow : a 0 + a 1 + a 2 =
      moreoverDisplayScale d s m * moreoverLinftyAmp d m + 1 +
        (streamDerivTailConst + 1) +
        (moreoverWindowScale d s * moreoverWindowConst d + 1) := rfl
  rw [hshow]
  have hfinal : moreoverDisplayScale d s m * moreoverLinftyAmp d m + 1 +
      (streamDerivTailConst + 1) +
      (moreoverWindowScale d s * moreoverWindowConst d + 1) ≤
      moreoverLinftyUniformBound d s + 1 + (streamDerivTailConst + 1) +
        (moreoverWindowScale d s * moreoverWindowConst d + 1) := by
    linarith only [hle]
  linarith only [hfinal]


end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
