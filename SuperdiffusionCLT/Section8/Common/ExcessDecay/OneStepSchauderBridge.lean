/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Sobolev.Foundations.Cutoff.Euclidean
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# The coordinate identification `Vec d ≃L EuclideanSpace ℝ (Fin d)`

The interior Schauder estimate for the harmonic competitor of
the Schauder gradient-Hölder estimate is proved against Mathlib's
`InnerProductSpace.HarmonicOnNhd`, which lives on `EuclideanSpace ℝ (Fin d)`
with `Metric.ball` and the coordinate-free Laplacian `Δ`.  Every §4 carrier
(`Vec d`, `HolderSeminormBoundOn`) lives on
the CoarseGraining coordinate carrier `Vec d = Fin d → ℝ` with the **sup**
norm.

This module is the definitional dictionary between the two, through the
canonical identification `toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d)`
(the identity on underlying data; only the ambient norm differs):

* `toEuc`, `toEuc_apply`, `toEuc_basisVec`;
* `mem_euclideanBall_toEuc_iff` — the ball dictionary
  `toEuc a ∈ Metric.ball (toEuc b) r ↔ a ∈ euclideanBall b r`;
* `norm_sq_toEuc_sub` — the squared `ℓ²` distance of the avatars;
* `norm_le_norm_toEuc` — the comparison of the sup norm with the `ℓ²` norm, a source of the
  dimensional factors in the Schauder constant.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder

open InnerProductSpace
open scoped Laplacian
open Homogenization (Vec basisVec basisVec_apply euclideanBall euclideanSqDist vecNormSq vecDot)

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. The coordinate identification -/

/-- The canonical identification of the CoarseGraining coordinate carrier `Vec d =
Fin d → ℝ` with the Mathlib inner-product space `EuclideanSpace ℝ (Fin d)`.  It
is the identity on underlying data; only the ambient norm (sup vs.  `ℓ²`)
differs. -/
def toEuc : Vec d ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm

@[simp] theorem toEuc_apply (y : Vec d) (i : Fin d) : (toEuc y) i = y i := rfl

@[simp] theorem toEuc_symm_apply (x : 𝔼) (i : Fin d) :
    (toEuc.symm x) i = x i := rfl

/-- The coordinate basis vector `basisVec i` maps to the orthonormal basis vector
`EuclideanSpace.single i 1`. -/
@[simp] theorem toEuc_basisVec (i : Fin d) :
    toEuc (basisVec i) = EuclideanSpace.single i 1 := by
  ext j
  simp [toEuc_apply, basisVec_apply, PiLp.single_apply]

@[simp] theorem toEuc_symm_single (i : Fin d) :
    toEuc.symm (EuclideanSpace.single i (1 : ℝ)) = (basisVec i : Vec d) := by
  rw [← toEuc_basisVec i, ContinuousLinearEquiv.symm_apply_apply]

/-- The round trip: a function on the `Vec d` carrier, pushed to the Euclidean
carrier and pulled back, is itself. -/
theorem comp_toEuc_symm_toEuc (v : Vec d → ℝ) :
    (v ∘ (toEuc.symm : 𝔼 → Vec d)) ∘ (toEuc : Vec d → 𝔼) = v := by
  funext y
  simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]

/-! ## 2. The ball dictionary -/

/-- The `ℓ²` distance of two coordinate vectors, transported to `EuclideanSpace`,
is the CoarseGraining Euclidean squared distance. -/
theorem norm_sq_toEuc_sub (a b : Vec d) :
    ‖toEuc a - toEuc b‖ ^ 2 = euclideanSqDist a b := by
  rw [← map_sub, EuclideanSpace.norm_sq_eq]
  simp only [toEuc_apply, Real.norm_eq_abs, sq_abs]
  simp only [euclideanSqDist, vecNormSq, vecDot, Pi.sub_apply, pow_two]

/-- **Ball dictionary.**  Under the coordinate identification the Mathlib metric
ball corresponds to the CoarseGraining explicit Euclidean ball. -/
theorem mem_euclideanBall_toEuc_iff (a b : Vec d) {r : ℝ} (hr : 0 < r) :
    toEuc a ∈ Metric.ball (toEuc b) r ↔ a ∈ euclideanBall b r := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hN : ‖toEuc a - toEuc b‖ = Real.sqrt (euclideanSqDist a b) := by
    rw [← norm_sq_toEuc_sub a b, Real.sqrt_sq (norm_nonneg _)]
  rw [hN]
  rw [show (euclideanBall b r : Set (Vec d)) = {x | euclideanSqDist x b < r ^ 2} from rfl,
    Set.mem_ofPred_eq, Real.sqrt_lt' hr]

/-! ## 3. The two-sided norm comparison -/

/-- The sup norm of a coordinate vector is at most its `ℓ²` norm. -/
theorem norm_le_norm_toEuc (y : Vec d) : ‖y‖ ≤ ‖(toEuc y : 𝔼)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [EuclideanSpace.norm_eq]
  have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
  have hsingle : ‖(toEuc y : 𝔼) i‖ ^ 2
      ≤ ∑ j, ‖(toEuc y : 𝔼) j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖(toEuc y : 𝔼) j‖ ^ 2)
      (fun j _ => sq_nonneg _) hmem
  have hrfl : ‖(toEuc y : 𝔼) i‖ = ‖y i‖ := rfl
  rw [hrfl] at hsingle
  have hle := Real.sqrt_le_sqrt hsingle
  rwa [Real.sqrt_sq (norm_nonneg _)] at hle

end

end SuperdiffusionCLT.Section8.Common.ExcessDecay.Schauder
