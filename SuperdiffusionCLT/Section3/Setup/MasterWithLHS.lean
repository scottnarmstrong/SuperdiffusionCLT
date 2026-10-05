/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section3.LHSTerm1
public import SuperdiffusionCLT.Section3.Setup.ScaleAssemblyB

/-!
# Supplying the left-hand-side constant in the master inequality

The numeric constant is selected once from the proved dimension-only estimate.
Its display is then supplied to the per-selection assembly of the paper's
master inequality. The right-hand-side displays and testing
identity remain explicit inputs of that assembly.
-/

@[expose] public section

open scoped ENNReal
noncomputable section
namespace SuperdiffusionCLT.Section3.Setup

/-- The dimension-only constant selected from the proved first left-hand-side estimate. -/
def masterWithLHS_lhsConst (d : ℕ) [NeZero d] (hd : 2 ≤ d) : ℝ :=
  Classical.choose (SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst d hd)

/-- The selected left-hand-side constant is at least one. -/
theorem masterWithLHS_lhsConst_ge_one (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    1 ≤ masterWithLHS_lhsConst d hd :=
  (Classical.choose_spec (SuperdiffusionCLT.Frozen.Section3.l_LHS_term1_constFirst d hd)).1

/-- The two project norms agree on unit vectors. -/
theorem masterWithLHS_unitNorm {d : ℕ} {e : Homogenization.Vec d}
    (he : Homogenization.vecNormSq e = 1) : Homogenization.Book.Ch02.vecNorm e = 1 := by
  have hs := Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq e
  rw [he] at hs
  have hn := Homogenization.Book.Ch02.vecNorm_nonneg e
  nlinarith only [hs, hn]

end SuperdiffusionCLT.Section3.Setup
