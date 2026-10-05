/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.Cutoff.Euclidean

/-!
# A coordinate hyperplane is Lebesgue-null

A leaf split off from the doubled-window transfer file so that the face-reflection
coefficient files depend only on this one fact.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder

open MeasureTheory
open Homogenization (Vec)

noncomputable section

variable {d : ℕ}

/-- A coordinate hyperplane has Lebesgue measure zero. -/
theorem volume_coordHyperplane_eq_zero (i : Fin d) (a : ℝ) :
    volume {y : Vec d | y i = a} = 0 := by
  classical
  have hset : {y : Vec d | y i = a}
      = Set.univ.pi (fun j : Fin d => if j = i then ({a} : Set ℝ) else Set.univ) := by
    ext y
    constructor
    · intro hy j _
      by_cases hj : j = i
      · subst hj
        simpa using hy
      · simp [hj]
    · intro hy
      have hi := hy i (Set.mem_univ i)
      simpa using hi
  rw [hset, volume_pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
