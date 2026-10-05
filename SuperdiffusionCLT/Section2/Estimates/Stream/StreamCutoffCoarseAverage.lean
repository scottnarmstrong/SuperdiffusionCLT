/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementMoreoverBlock
public import SuperdiffusionCLT.Section2.Carriers.CenteredStreamField

/-!
# The coarse-average difference in the printed carrier

`IncrementMoreoverBlock`
proves the display
`e.bounding.something.that.is.more.complicated.than.it.seems` for the infrared cutoff
in the shell-average form `∑_{k ≤ m} ((j_k)_{z + cu_n} - (j_k)_{cu_m})`. This
module identifies that finite sum with the printed carrier

> `(k_m)_{z + cu_n} - (k_m)_{cu_m}`,

the difference of two normalized averages of the infrared cutoff
`k_m = ∑_{k ≤ m} j_k`, and restates the display and its witness form there.
The identification is the finite-sum exchange
`Section2.Carriers.volumeAverageMat_streamCutoff_eq_sum` together with the
reading of a shell spatial average as a normalized average over the
translated open cube,
`ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet`.

## What is not here

The printed display is stated for the limiting field `k`, not for the cutoff
`k_m`. Passing from `k_m` to `k` needs two further deterministic steps, which
are carried out in `IncrementMoreoverBlockB`: the exchange of the normalized average
with the defining series of `Section2.Carriers.centeredStreamField` on the summability guard,
and the bound on the resulting tail `∑_{k > m}` by
`shellDerivTailGauge`, whose uniform `Γ₂` amplitude is bounded in
`ShellDerivTailGauge`.

## Main results

* `sum_shellSpatialAverageDifference_eq_streamCutoffAverageDifference`: the
  identification of the carriers.
* `isBigOWith_gammaSigma_streamCutoffVolumeAverageDifference`: the display in
  the printed carrier.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## The printed carrier: the coarse averages of the infrared cutoff -/

private theorem isBounded_translateSet {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (z : Vec d) :
    Bornology.IsBounded (translateSet z U) := by
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.mp hU
  refine Metric.isBounded_iff.mpr ⟨R, fun x hx y hy ↦ ?_⟩
  rw [mem_translateSet_iff_sub_mem] at hx hy
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using hR hx hy

/-- **The shell-average difference is the coarse-average difference of the
infrared cutoff.** For every scale pair and every centre, the finite sum of
shell spatial-average differences over `k ≤ m` is exactly the printed
quantity `(k_m)_{z + cu_n} - (k_m)_{cu_m}`: the average of the cutoff is the
sum of the shell averages (`volumeAverageMat_streamCutoff_eq_sum`), and each
shell spatial average is the normalized average over the translated open cube
(`shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet`). -/
theorem sum_shellSpatialAverageDifference_eq_streamCutoffAverageDifference
    (n m : ℕ) (z : Vec d) (omega : ℕ → ShellField d) :
    ∑ k ∈ Finset.range (m + 1),
        (ShellField.shellSpatialAverage (n : ℤ) z (omega k) -
          ShellField.shellSpatialAverage (m : ℤ) 0 (omega k)) =
      volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
          (Frozen.Section2.streamCutoff omega m) -
        volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
          (Frozen.Section2.streamCutoff omega m) := by
  have hboundN : Bornology.IsBounded
      (translateSet z (openCubeSet (originCube d (n : ℤ)))) :=
    isBounded_translateSet (Carriers.isBounded_openCubeSet_originCube (n : ℤ)) z
  have hboundM : Bornology.IsBounded (openCubeSet (originCube d (m : ℤ))) :=
    Carriers.isBounded_openCubeSet_originCube (m : ℤ)
  have hshell : ∀ (U : Set (Vec d)) (k : ℕ),
      volumeAverageMat U (fun y : Vec d ↦ Cutoff.shellReg omega k y) =
        volumeAverageMat U (omega k) := by
    intro U k
    rfl
  rw [Finset.sum_sub_distrib,
    Carriers.volumeAverageMat_streamCutoff_eq_sum hboundN omega m,
    Carriers.volumeAverageMat_streamCutoff_eq_sum hboundM omega m]
  congr 1
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hshell]
    exact ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet
      (n : ℤ) z (omega k)
  · refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hshell]
    rw [ShellField.shellSpatialAverage_eq_volumeAverageMat_translateSet_openCubeSet
      (m : ℤ) 0 (omega k), translateSet_zero]

/-- **The printed display
`e.bounding.something.that.is.more.complicated.than.it.seems` for the
infrared cutoff**, in the printed carrier: for `n < m` and every centre `z`,

`|(k_m)_{z + cu_n} - (k_m)_{cu_m}| ≤ O_{Γ₂}(C(d) (m - n)^{1/2})`. -/
theorem isBigOWith_gammaSigma_streamCutoffVolumeAverageDifference
    (hPrefix : ShellLawPrefix d P) (hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    {n m : ℕ} (hnm : n < m) (z : Vec d) :
    IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
      (fun omega : ℕ → ShellField d ↦
        matrixOperatorNorm
          (volumeAverageMat (translateSet z (openCubeSet (originCube d (n : ℤ))))
              (Frozen.Section2.streamCutoff omega m) -
            volumeAverageMat (openCubeSet (originCube d (m : ℤ)))
              (Frozen.Section2.streamCutoff omega m)))
      (coarseAverageDiffConst d * Real.sqrt ((m - n : ℕ) : ℝ)) := by
  have h := isBigOWith_gammaSigma_streamCutoffAverageDifference
    hPrefix hJ1 hJ2 hJ3 hJ4 hnm z
  refine h.of_le fun omega ↦ ?_
  rw [sum_shellSpatialAverageDifference_eq_streamCutoffAverageDifference n m z omega]

end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
