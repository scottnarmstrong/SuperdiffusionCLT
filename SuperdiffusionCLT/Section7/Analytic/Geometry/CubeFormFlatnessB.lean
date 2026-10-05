/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Geometry.CubeFormDomainsB
public import SuperdiffusionCLT.Section7.Analytic.Regularity.BoundaryDecayChartM
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit

/-!
# Openness of a rescaled domain

`g1f_isOpen_of_rescaled`: if the image of `V` under an affine rescaling `y ↦ c⁻¹ (y - z)` is a
uniformly `C^{1,1}` domain, then `V` is open.
-/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem g1f_isOpen_of_rescaled {V : Set (Vec d)} {c : ℝ} (hc : c ≠ 0) (z : Vec d) {r M₁ M₂ D : ℝ}
    (h : IsUniformC11Domain ((fun y => c⁻¹ • (y - z)) '' V) r M₁ M₂ D) : IsOpen V := by
  have hinj : Function.Injective (fun y : Vec d => c⁻¹ • (y - z)) := by
    intro x y hxy
    have := smul_right_injective (Vec d) (inv_ne_zero hc) hxy
    simpa using this
  have hcont : Continuous (fun y : Vec d => c⁻¹ • (y - z)) :=
    by fun_prop
  have := h.1.preimage hcont
  rwa [hinj.preimage_image] at this

end SuperdiffusionCLT.Section7
