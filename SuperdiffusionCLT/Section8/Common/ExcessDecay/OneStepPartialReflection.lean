/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Common.ExcessDecay.OneStepOddPackaging

/-!
# The multi-face odd reflection: commuting face reflections

The multi-face odd reflection is built by iterating the single-face odd extension over the met
faces, which requires that the face reflections in distinct coordinates commute: this is what
keeps the previously unfolded faces odd at every stage.

## Main results

* `coordFaceReflection_comm` — face reflections in distinct coordinates commute, for arbitrary
  pivots.

The iteration itself and the operator reconciliation are not part of this module.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay

open Homogenization SuperdiffusionCLT.Section8.Common.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Distinct coordinate reflections commute -/

/-- Face reflections in distinct coordinates commute, for arbitrary pivots. -/
theorem coordFaceReflection_comm {i j : Fin d} (hij : i ≠ j) (a b : ℝ) (y : Vec d) :
    coordFaceReflection a i (coordFaceReflection b j y)
      = coordFaceReflection b j (coordFaceReflection a i y) := by
  funext l
  simp only [coordFaceReflection_apply]
  by_cases hli : l = i
  · subst hli
    simp [hij]
  · by_cases hlj : l = j
    · subst hlj
      simp [hli]
    · simp [hli, hlj]

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay
