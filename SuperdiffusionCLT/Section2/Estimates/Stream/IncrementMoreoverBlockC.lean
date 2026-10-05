/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlockB

/-!
# The coarse-average envelope of the centered field

`IncrementMoreoverBlockB` bounds the coarse
average of the limiting centered field `k - (k)_{cu_m}` over **one** scale-`n`
sub-cube of `cu_m` by the coarse-average difference of the infrared cutoff plus
the derivative tail gauge. This module packages that bound as a measurable
envelope `centeredCubeAverageEnvelope` and gives its `Γ₂` tail at the printed
amplitude `C(d) (m-n)^{1/2}` of
`e.bounding.something.that.is.more.complicated.than.it.seems`.

## Main definitions

* `centeredCubeAverageEnvelope`: the envelope of one coarse average.
* `centeredCubeAverageConst`: its explicit amplitude constant.

## Main results

* `measurable_centeredCubeAverageEnvelope`,
  `centeredCubeAverageEnvelope_nonneg`.
* `matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_envelope`: the
  deterministic domination.
* `isBigO_gammaSigma_centeredCubeAverageEnvelope`: the `Γ₂` tail of the
  envelope at `C(d) (m-n)^{1/2}`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The envelope of one coarse average -/

private theorem isBounded_translateSet {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (z : Vec d) :
    Bornology.IsBounded (translateSet z U) := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hU
  refine Metric.isBounded_iff.mpr ⟨R, fun x hx y hy ↦ ?_⟩
  rw [mem_translateSet_iff_sub_mem] at hx hy
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hR hx hy

private theorem measurableSet_translateSet {U : Set (Vec d)}
    (hU : MeasurableSet U) (z : Vec d) :
    MeasurableSet (translateSet z U) := by
  have hpre : translateSet z U = (fun x : Vec d ↦ x - z) ⁻¹' U := by
    ext x
    exact mem_translateSet_iff_sub_mem
  rw [hpre]
  exact (measurable_id.sub_const z) hU

/-- The envelope dominating the coarse average of `k - (k)_{cu_m}` over a
scale-`n` cube centred at `z`: the coarse-average difference of the infrared
cutoff `k_m` plus `d √d` times the derivative tail gauge. -/
def centeredCubeAverageEnvelope (n m : ℕ) (z : Vec d) (omega : ShellSeq d) :
    ℝ :=
  matrixOperatorNorm
      (volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
          (Frozen.Section2.streamCutoff omega m) -
        volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
          (Frozen.Section2.streamCutoff omega m)) +
    (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega

theorem centeredCubeAverageEnvelope_nonneg (n m : ℕ) (z : Vec d)
    (omega : ShellSeq d) :
    0 ≤ centeredCubeAverageEnvelope n m z omega :=
  add_nonneg (matrixOperatorNorm_nonneg _)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Real.sqrt_nonneg _))
      (shellDerivTailGauge_nonneg m omega))

private theorem measurable_cutoffAverageDifference (n m : ℕ) (z : Vec d) :
    Measurable fun omega : ShellSeq d ↦
      volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
          (Frozen.Section2.streamCutoff omega m) -
        volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
          (Frozen.Section2.streamCutoff omega m) := by
  have h1 := measurable_volumeAverageMat_streamCutoff
    (isBounded_translateSet (isBounded_openCubeSet (originCube d (n : ℤ))) z)
    (measurableSet_translateSet (measurableSet_openCubeSet _) z) m
  have h2 := measurable_volumeAverageMat_streamCutoff
    (isBounded_openCubeSet (originCube d (m : ℤ)))
    (measurableSet_openCubeSet _) m
  refine measurable_matrix_of_entries fun i k ↦ ?_
  have he1 : Measurable fun omega : ShellSeq d ↦
      volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
        (Frozen.Section2.streamCutoff omega m) i k :=
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp h1))
  have he2 : Measurable fun omega : ShellSeq d ↦
      volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
        (Frozen.Section2.streamCutoff omega m) i k :=
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp h2))
  have hsub := he1.sub he2
  simp only [Matrix.sub_apply]
  exact hsub

private theorem measurable_matrixOperatorNorm_cutoffAverageDifference
    (n m : ℕ) (z : Vec d) :
    Measurable fun omega : ShellSeq d ↦ matrixOperatorNorm
      (volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
          (Frozen.Section2.streamCutoff omega m) -
        volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
          (Frozen.Section2.streamCutoff omega m)) :=
  ShellField.continuous_matrixOperatorNorm.measurable.comp
    (measurable_cutoffAverageDifference n m z)

theorem measurable_centeredCubeAverageEnvelope (n m : ℕ) (z : Vec d) :
    Measurable (centeredCubeAverageEnvelope (d := d) n m z) :=
  (measurable_matrixOperatorNorm_cutoffAverageDifference n m z).add
    ((measurable_shellDerivTailGauge m).const_mul _)

/-- **The deterministic domination of the limiting coarse average by the
envelope.** -/
theorem matrixOperatorNorm_volumeAverageMat_centeredStreamField_le_envelope
    (omega : ShellSeq d) {n m : ℕ} (hnm : n ≤ m) {Q : TriadicCube d}
    (hQscale : Q.scale = (n : ℤ))
    (hQmem : cubeCenter Q ∈ cubeSet (originCube d (m : ℤ)))
    (hsum : Summable fun k : ℕ ↦
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ))) (omega k)) :
    matrixOperatorNorm
        (volumeAverageMat (cubeSet Q)
          (centeredStreamField omega (cubeSet (originCube d (m : ℤ))))) ≤
      centeredCubeAverageEnvelope n m (cubeCenter Q) omega :=
  matrixOperatorNorm_volumeAverageMat_centeredStreamField_cubeSet_le omega hnm
    hQscale hQmem hsum

/-! ## The `Γ₂` tail of the envelope -/

/-- The explicit amplitude of the envelope of one coarse average: the finite
triangle prefactor `16384` times the sum of the cutoff coarse-average constant,
the derivative-tail constant weighted by `d √d`, and the two units that make
both summands strictly positive. -/
def centeredCubeAverageConst (d : ℕ) : ℝ :=
  16384 *
    (coarseAverageDiffConst d + (d : ℝ) * Real.sqrt d * streamDerivTailConst + 2)

private theorem one_le_sqrt_sub {n m : ℕ} (hnm : n < m) :
    (1 : ℝ) ≤ Real.sqrt ((m - n : ℕ) : ℝ) := by
  have hone : (1 : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
    have : 1 ≤ m - n := by omega
    exact_mod_cast this
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt ((m - n : ℕ) : ℝ) := Real.sqrt_le_sqrt hone

/-- **The `Γ₂` tail of the coarse-average envelope**, at the amplitude
`C(d) (m-n)^{1/2}` of the printed display
`e.bounding.something.that.is.more.complicated.than.it.seems`. -/
theorem isBigO_gammaSigma_centeredCubeAverageEnvelope
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (centeredCubeAverageEnvelope n m z)
      (centeredCubeAverageConst d * Real.sqrt ((m - n : ℕ) : ℝ)) := by
  classical
  have hsqrt := one_le_sqrt_sub hnm
  set X : Fin 2 → ShellSeq d → ℝ :=
    ![fun omega ↦ matrixOperatorNorm
        (volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
            (Frozen.Section2.streamCutoff omega m) -
          volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
            (Frozen.Section2.streamCutoff omega m)),
      fun omega ↦ (d : ℝ) * Real.sqrt d * shellDerivTailGauge m omega] with hX
  set a : Fin 2 → ℝ :=
    ![(coarseAverageDiffConst d + 1) * Real.sqrt ((m - n : ℕ) : ℝ),
      (d : ℝ) * Real.sqrt d * streamDerivTailConst + 1] with ha
  have hDnonneg : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt d * streamDerivTailConst := by
    have : (0 : ℝ) ≤ streamDerivTailConst := by
      rw [streamDerivTailConst]; norm_num
    positivity
  have hapos : ∀ i, 0 < a i := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [ha, Matrix.cons_val_zero]
      have hC : (0 : ℝ) < coarseAverageDiffConst d + 1 := by
        linarith only [coarseAverageDiffConst_nonneg d]
      nlinarith only [hC, hsqrt]
    · simp only [ha, Matrix.cons_val_one, Matrix.cons_val_zero]
      linarith only [hDnonneg]
  have hXmeas : ∀ i, Measurable (X i) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [hX, Matrix.cons_val_zero]
      exact measurable_matrixOperatorNorm_cutoffAverageDifference n m z
    · simp only [hX, Matrix.cons_val_one, Matrix.cons_val_zero]
      exact (measurable_shellDerivTailGauge m).const_mul _
  have hXbig : ∀ i, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2) (X i) (a i) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simp only [hX, ha, Matrix.cons_val_zero]
      have hbase := isBigOWith_gammaSigma_streamCutoffVolumeAverageDifference
        hPrefix hJ1 hJ2 hJ3 hJ4 hnm z
      have hO := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2)
        (fun _ ↦ matrixOperatorNorm_nonneg _)).1 hbase
      refine hO.mono_scale ?_
      have : coarseAverageDiffConst d ≤ coarseAverageDiffConst d + 1 := by
        linarith only []
      exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    · simp only [hX, ha, Matrix.cons_val_one, Matrix.cons_val_zero]
      have hbase := isBigO_gammaSigma_shellDerivTailGauge (P := P) hJ3 m
      have hscaled := hbase.const_mul
        (c := (d : ℝ) * Real.sqrt d)
        (by positivity)
      exact hscaled.mono_scale (by linarith only [])
  have hsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_finSum_of_one_le
    (mu := P.toMeasure) (N := 2) (X := X) (a := a) (sigma := 2)
    (by norm_num) (by norm_num) hapos hXbig hXmeas
  have hfun : (fun omega : ShellSeq d ↦ ∑ i, X i omega) =
      centeredCubeAverageEnvelope (d := d) n m z := by
    funext omega
    rw [Fin.sum_univ_two]
    simp only [hX, Matrix.cons_val_zero, Matrix.cons_val_one,
      centeredCubeAverageEnvelope]
  rw [hfun] at hsum
  refine hsum.mono_scale ?_
  have hsplit : ∑ i, a i =
      (coarseAverageDiffConst d + 1) * Real.sqrt ((m - n : ℕ) : ℝ) +
        ((d : ℝ) * Real.sqrt d * streamDerivTailConst + 1) := by
    rw [Fin.sum_univ_two]
    simp only [ha, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsplit, centeredCubeAverageConst]
  have hkey :
      (coarseAverageDiffConst d + 1) * Real.sqrt ((m - n : ℕ) : ℝ) +
          ((d : ℝ) * Real.sqrt d * streamDerivTailConst + 1) ≤
        (coarseAverageDiffConst d + (d : ℝ) * Real.sqrt d * streamDerivTailConst
            + 2) * Real.sqrt ((m - n : ℕ) : ℝ) := by
    nlinarith only [hsqrt, hDnonneg]
  linarith only [hkey]

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
