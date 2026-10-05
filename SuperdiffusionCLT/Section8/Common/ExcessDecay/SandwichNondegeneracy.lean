/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.CubeMoments

/-!
# The affine geometry of a sandwiched window: the mean minimizes the deviation

`l.iteration.lemma` never assumes its windows are cubes.  Its only stated
geometry is the **sandwich** `x + □_{j-2} ⊆ U_j ⊆ y + □_j` (hypothesis (iii),
scoped to `j ≤ m` per the binding).  The affine geometry of such a window rests on the exact
cube second moment of `CubeMoments.lean` and on the elementary fact that the mean minimizes the
`L̲²` deviation, which is the declaration kept in this module.

## Main results

* `volumeAverage_sub_const_sq` — the expansion of the average of `(f − a)²` around its mean.

## References

* ABK26, `e.grad.stability`; `l.iteration.lemma`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open MeasureTheory
open Homogenization (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeCenter cubeScaleFactor)
open SuperdiffusionCLT.Section8.Common.Support

noncomputable section

variable {d : ℕ}

/-! ### The mean minimizes the `L̲²` deviation -/

/-- Expansion of the average of `(f − a)²`. -/
theorem volumeAverage_sub_const_sq {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) (hfin : volume W ≠ ⊤) {f : Vec d → ℝ}
    (hf : IntegrableOn f W) (hf2 : IntegrableOn (fun x => f x ^ 2) W) (a : ℝ) :
    volumeAverage W (fun x => (f x - a) ^ 2)
      = volumeAverage W (fun x => f x ^ 2) - 2 * a * volumeAverage W f + a ^ 2 := by
  have hB : IntegrableOn (fun x => -(2 * a) * f x) W := hf.const_mul _
  have hAB : IntegrableOn (fun x => f x ^ 2 + -(2 * a) * f x) W := hf2.add hB
  have hC : IntegrableOn (fun _ : Vec d => a ^ 2) W := integrableOn_const hfin
  have hcongr : (∫ x in W, (f x - a) ^ 2)
      = ∫ x in W, (f x ^ 2 + -(2 * a) * f x + a ^ 2) :=
    MeasureTheory.setIntegral_congr_fun hWm (fun x _ => by ring)
  have hVne : (volume W).toReal ≠ 0 := ne_of_gt hW
  unfold volumeAverage
  rw [hcongr, MeasureTheory.integral_add hAB hC, MeasureTheory.integral_add hf2 hB,
    MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const,
    MeasureTheory.measureReal_def, smul_eq_mul]
  field_simp
  ring

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
