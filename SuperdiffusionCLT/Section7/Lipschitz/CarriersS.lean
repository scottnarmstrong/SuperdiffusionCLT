/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.WitnessBdry
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarm

/-!
# The boundary Caccioppoli block with sup-norm bounds on the datum

`LipCaccBdryS` is the form of the boundary Caccioppoli block in which the two norms of the
derivatives of the datum `γ` are replaced by pointwise bounds `G1`, `G2` on the cube.  It follows
from `LipCaccBdry` when the set has finite positive measure (`LipCaccBdry.toS`).
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Boundary Caccioppoli in local form with sup bounds on the datum.** -/
def LipCaccBdryS (a : CoeffField d) (nu s C E : ℝ) (W : Set (Vec d)) (z : Vec d) (j : ℕ) : Prop :=
  ∀ (f γ : Vec d → ℝ) (G1 G2 : ℝ) (u : H1Function (shiftCube z (j : ℤ) ∩ W)), ContDiff ℝ 2 γ →
    0 ≤ G1 → 0 ≤ G2 →
    (∀ x ∈ shiftCube z (j : ℤ) ∩ W, ‖fderiv ℝ γ x‖ ≤ G1) →
    (∀ x ∈ shiftCube z (j : ℤ) ∩ W, ‖fderiv ℝ (fderiv ℝ γ) x‖ ≤ G2) →
    IsWeakSolutionOn a (shiftCube z (j : ℤ) ∩ W) u f (fun _ => 0) →
    LocalizedZeroTraceFunctionOn (shiftCube z (j : ℤ) ∩ W) (shiftCube z (j : ℤ))
      (fun x => u.toFun x - γ x) →
    ENNReal.ofReal nu *
        lpBar (shiftCube z ((j : ℤ) - 1) ∩ W) 2 (fun x => eucNorm (u.grad x)) ^ 2 ≤
      ENNReal.ofReal (C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 (fun x => u.toFun x - γ x) ^ 2 +
        ENNReal.ofReal (C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2) *
          lpBar (shiftCube z (j : ℤ) ∩ W) 2 f ^ 2 +
        ENNReal.ofReal (C * s * G1 ^ 2) +
        ENNReal.ofReal (C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * G2 ^ 2)

/-- Monotonicity in the constants: if the three coefficients of the block for `(s', C')` dominate
those for `(s, C)`, the block for `(s, C)` implies the block for `(s', C')`. -/
theorem LipCaccBdryS.mono {a : CoeffField d} {nu s s' C C' E : ℝ} {W : Set (Vec d)} {z : Vec d}
    {j : ℕ} (h1 : C * s ≤ C' * s') (h2 : C * s⁻¹ ≤ C' * s'⁻¹) (h3 : C ≤ C')
    (h : LipCaccBdryS a nu s C E W z j) : LipCaccBdryS a nu s' C' E W z j := by
  intro f γ G1 G2 u hγ hG1 hG2 hb1 hb2 hu hZ
  refine (h f γ G1 G2 u hγ hG1 hG2 hb1 hb2 hu hZ).trans ?_
  have k1 : C * s * (((3 : ℝ)⁻¹) ^ j) ^ 2 ≤ C' * s' * (((3 : ℝ)⁻¹) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have k2 : C * s⁻¹ * ((3 : ℝ) ^ j) ^ 2 ≤ C' * s'⁻¹ * ((3 : ℝ) ^ j) ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have k3 : C * s * G1 ^ 2 ≤ C' * s' * G1 ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have k4 : C * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * G2 ^ 2 ≤
      C' * ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * G2 ^ 2 := by
    have : 0 ≤ ((j : ℝ) ^ (-E)) ^ 2 * ((3 : ℝ) ^ j) ^ 2 * G2 ^ 2 := by positivity
    nlinarith only [this, h3]
  gcongr

end SuperdiffusionCLT.Section7
