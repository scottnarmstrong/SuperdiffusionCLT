/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.LocAvgUniformBiform

/-!
# The grid-averaged bilinear form behind `localization_average`

`SuperdiffusionCLT.Frozen.Section2.localization_average`'s conclusion, for
fixed `nu, P, m, n, l, L, omega`, has the shape

`|(card)⁻¹ * ∑ R ∈ grid, blockVecDot Pvec (blockMatVecMul (A R) Pvec)| ≤ X omega`

where `A : X → BlockMat d` (built from `coarseBlockMatrix`, `blockG`, the
annealed matrix, etc.) does **not** depend on `Pvec`. `locAvgU_gridBf grid A`
packages the un-normalized double expression `x ↦ y ↦ (card)⁻¹ * ∑ R, ⟪x, A R
y⟫` as a genuine bi-additive, bi-homogeneous function of `(x, y)`, so
`locAvgU_biform_bound` (`LocAvgUniformBiform.lean`) applies to it directly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization

noncomputable section

/-- The grid-averaged bilinear form `x, y ↦ (card)⁻¹ * ∑ R ∈ grid, ⟪x, A R y⟫`. -/
def locAvgU_gridBf {d : ℕ} {X : Type*} (grid : Finset X) (A : X → BlockMat d)
    (x y : BlockVec d) : ℝ :=
  (grid.card : ℝ)⁻¹ * ∑ R ∈ grid, blockVecDot x (blockMatVecMul (A R) y)

theorem locAvgU_gridBf_add_left {d : ℕ} {X : Type*} (grid : Finset X) (A : X → BlockMat d)
    (x y z : BlockVec d) :
    locAvgU_gridBf grid A (x + y) z = locAvgU_gridBf grid A x z + locAvgU_gridBf grid A y z := by
  unfold locAvgU_gridBf
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  rw [blockVecDot_add_left]

theorem locAvgU_gridBf_add_right {d : ℕ} {X : Type*} (grid : Finset X) (A : X → BlockMat d)
    (x y z : BlockVec d) :
    locAvgU_gridBf grid A x (y + z) = locAvgU_gridBf grid A x y + locAvgU_gridBf grid A x z := by
  unfold locAvgU_gridBf
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  rw [blockMatVecMul_add, blockVecDot_add_right]

theorem locAvgU_gridBf_smul_left {d : ℕ} {X : Type*} (grid : Finset X) (A : X → BlockMat d)
    (c : ℝ) (x y : BlockVec d) :
    locAvgU_gridBf grid A (c • x) y = c * locAvgU_gridBf grid A x y := by
  unfold locAvgU_gridBf
  rw [Finset.sum_congr rfl (fun R (_ : R ∈ grid) => blockVecDot_smul_left c x
    (blockMatVecMul (A R) y)), ← Finset.mul_sum]
  ring

theorem locAvgU_gridBf_smul_right {d : ℕ} {X : Type*} (grid : Finset X) (A : X → BlockMat d)
    (c : ℝ) (x y : BlockVec d) :
    locAvgU_gridBf grid A x (c • y) = c * locAvgU_gridBf grid A x y := by
  unfold locAvgU_gridBf
  have hstep : ∀ R ∈ grid, blockVecDot x (blockMatVecMul (A R) (c • y)) =
      c * blockVecDot x (blockMatVecMul (A R) y) := by
    intro R _
    rw [blockMatVecMul_smul, blockVecDot_smul_right]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  ring

end

end SuperdiffusionCLT.Section4.NewMixing
