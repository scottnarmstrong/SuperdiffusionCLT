/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.SandwichNondegeneracyAttainment

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open MeasureTheory
open Homogenization (Vec vecDot vecNormSq volumeAverage axisCube openCubeSet TriadicCube
  cubeScaleFactor)
open SuperdiffusionCLT.Section8.Common.Support

noncomputable section

variable {d : ℕ}

/-! ### Small measure-theoretic helpers -/

private theorem volume_ne_top_of_toReal_pos {W : Set (Vec d)} (hW : 0 < (volume W).toReal) :
    volume W ≠ ⊤ := by
  intro htop
  rw [htop, ENNReal.toReal_top] at hW
  exact absurd hW (lt_irrefl 0)

/-- **Jensen for the volume-normalized `L²` seminorm**: `|⨍_W f| ≤ ‖f‖_{L̲²(W)}`.

Obtained from the completed-square expansion `volumeAverage_sub_const_sq`: the average of
`(f − (f)_W)²` is `⨍f² − ((f)_W)²`, and it is nonnegative. -/
theorem abs_volumeAverage_le_normalizedL2On {W : Set (Vec d)} (hWm : MeasurableSet W)
    (hW : 0 < (volume W).toReal) {f : Vec d → ℝ} (hf : IntegrableOn f W)
    (hf2 : IntegrableOn (fun x => f x ^ 2) W) :
    |volumeAverage W f| ≤ normalizedL2On W f := by
  have hfin : volume W ≠ ⊤ := volume_ne_top_of_toReal_pos hW
  have hexp := volumeAverage_sub_const_sq hWm hW hfin hf hf2 (volumeAverage W f)
  have hnn : 0 ≤ volumeAverage W (fun x => (f x - volumeAverage W f) ^ 2) :=
    volumeAverage_sq_nonneg W (fun x => f x - volumeAverage W f)
  have hm2 : volumeAverage W f ^ 2 ≤ volumeAverage W (fun x => f x ^ 2) := by
    linarith only [hexp, hnn]
  rw [← Real.sqrt_sq_eq_abs, normalizedL2On]
  exact Real.sqrt_le_sqrt hm2

/-! ### The oscillation -/

/-! ### The endpoint constant -/

/-! ### `hhi`: the excess and the slope are controlled by the oscillation -/

/-! ### `hlo`: the oscillation is controlled by the excess and the slope -/

/-! ### Both comparisons on a sandwiched window -/

/-! ### The `3^{−j}` normalizer -/

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
