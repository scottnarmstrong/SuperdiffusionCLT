/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Homogenization.Ambient.CoefficientField
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence
public import SuperdiffusionCLT.Section2.Localization.BlockLoewnerCongruence

/-!
# The unsymmetric conversion

The conversion lemma of the localization proof `ss.localization`
(conjunct `e.skbounds`): from the conjugated Loewner comparison

`hᵗ σ_*^{-1}_L h ≤ c · σ_L`

one concludes the relative bilinear bound

`2 p·h q ≤ √c · (p·σ_*L p + q·σ_L q)`,

which is the reading of the printed bilinear clause used in
`Frozen.Section2.cutoff_localization`: the substitution `u = σ_*^{1/2} p`,
`v = σ_L^{1/2} q` shows this bilinear bound is exactly
`|σ_*L^{-1/2} h σ_L^{-1/2}| ≤ √c`.

## Route

The proof goes through the *generalized* Cauchy-Schwarz inequality for the
quadratic form of a symmetric matrix with nonnegative quadratic form — the
discriminant argument of
`sq_vecDot_matVecMul_le_of_isSymm_of_nonneg` — applied to the `A`-weighted
pairing `x · A y` with `y = B (h q)`:

`(p·h q)² = (p·A(B(hq)))² ≤ (p·A p) · ((h q)·B(h q)) ≤ c (p·A p)(q·E q)`,

where the last step is the hypothesis at `q` transported by the adjunction
`q·(hᵗ B h)q = (h q)·B(h q)`.  No matrix square root is taken: the only square
root appearing in the statements is the *scalar* `Real.sqrt c`, obtained from
Young's inequality `|u| ≤ (√c x + √c y)/2` (`abs_le_add_halves_of_sq_le_mul`),
which is why the `PsdSqrtQuadratic` carrier is not needed here.

The engine is stated with `B` arbitrary subject to `A * B = 1`; the
specialization `B = A⁻¹` (invertible `A`) and the carrier instance at
`sigmaStarCoarse`/`sigmaCoarse` of the `Correspondence` package are the
forms the assembly consumes.

## Main results

* `vecDot_conj_quad_le`: the hypothesis transport, `q·(hᵗ B h)q ≤ c q·E q`.
* `two_vecDot_matVecMul_le_sqrt_mul`: the unsymmetric conversion, from the
  conjugated comparison `hᵗ B h ≤ c • E` (`A * B = 1`) to the bilinear bound.
* `two_vecDot_matVecMul_le_sqrt_mul_inv`: the specialization `B = A⁻¹` for a
  positive semidefinite invertible `A`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- `matVecMul` by the unit matrix is the identity. -/
private theorem matVecMul_one' (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  funext k
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

/-- The hypothesis transport behind the unsymmetric conversion: the quadratic
form of the conjugated matrix `hᵗ B h` is the quadratic form of `B` at `h q`,

`q·(hᵗ B h)q = (h q)·B(h q) ≤ c · q·E q`,

from the block-Loewner-style hypothesis `hᵗ B h ≤ c • E`. -/
theorem vecDot_conj_quad_le {B E : Mat d} {h : Mat d} {c : ℝ}
    (hsand : MatLoewnerLE (matTranspose h * B * h) (c • E)) (q : Vec d) :
    vecDot (matVecMul h q) (matVecMul B (matVecMul h q)) ≤
      c * vecDot q (matVecMul E q) := by
  have hx := hsand q
  rw [smul_matVecMul, vecDot_smul_right] at hx
  have hkey : vecDot (matVecMul h q) (matVecMul B (matVecMul h q))
      = vecDot q (matVecMul (matTranspose h * B * h) q) := by
    calc vecDot (matVecMul h q) (matVecMul B (matVecMul h q))
        = vecDot q (matVecMul (matTranspose h) (matVecMul B (matVecMul h q))) :=
          (vecDot_matVecMul_transpose q (matVecMul B (matVecMul h q)) h).symm
      _ = vecDot q (matVecMul (matTranspose h * B) (matVecMul h q)) := by
          rw [matVecMul_mul (matTranspose h) B (matVecMul h q)]
      _ = vecDot q (matVecMul (matTranspose h * B * h) q) := by
          rw [matVecMul_mul (matTranspose h * B) h q]
  linarith only [hx, hkey]

/-- **The unsymmetric conversion** (C2-S10).  From the conjugated Loewner
comparison `hᵗ B h ≤ c • E`, with `A` symmetric of nonnegative quadratic form
satisfying `A * B = 1`, the bilinear bound

`2 p·h q ≤ √c (p·A p + q·E q)`

follows.  The engine is the generalized Cauchy-Schwarz for the quadratic form
of `A` (`sq_vecDot_matVecMul_le_of_isSymm_of_nonneg`):

`(p·h q)² = (p·A(B(hq)))² ≤ (p·A p)·((h q)·B(h q)) ≤ c (p·A p)(q·E q)`,

and the scalar conclusion is Young's inequality with the weight `√c` on both
factors.  No matrix square root is taken. -/
theorem two_vecDot_matVecMul_le_sqrt_mul {A B E : Mat d} {h : Mat d} {c : ℝ}
    (hAsymm : A.IsSymm) (hAnonneg : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul A v))
    (hAB : A * B = 1)
    (hEnonneg : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul E v))
    (hsand : MatLoewnerLE (matTranspose h * B * h) (c • E))
    (p q : Vec d) :
    2 * vecDot p (matVecMul h q) ≤
      Real.sqrt c * (vecDot p (matVecMul A p) + vecDot q (matVecMul E q)) := by
  have hconv := vecDot_conj_quad_le hsand q
  have hAw : matVecMul A (matVecMul B (matVecMul h q)) = matVecMul h q := by
    rw [matVecMul_mul, hAB, matVecMul_one']
  have hcs : vecDot p (matVecMul h q) ^ 2
      ≤ vecDot p (matVecMul A p) *
        vecDot (matVecMul B (matVecMul h q)) (matVecMul h q) := by
    have hcs' := sq_vecDot_matVecMul_le_of_isSymm_of_nonneg hAsymm hAnonneg p
      (matVecMul B (matVecMul h q))
    rw [hAw] at hcs'
    exact hcs'
  have hwnn : vecDot (matVecMul B (matVecMul h q)) (matVecMul h q)
      ≤ c * vecDot q (matVecMul E q) := by
    rw [vecDot_comm (matVecMul B (matVecMul h q)) (matVecMul h q)]
    exact hconv
  have hxnn : 0 ≤ vecDot p (matVecMul A p) := hAnonneg p
  have hynn : 0 ≤ vecDot q (matVecMul E q) := hEnonneg q
  have hre : vecDot p (matVecMul h q) ^ 2
      ≤ vecDot p (matVecMul A p) * (c * vecDot q (matVecMul E q)) :=
    hcs.trans (mul_le_mul_of_nonneg_left hwnn hxnn)
  rw [mul_add]
  by_cases hc : 0 ≤ c
  · have hsq2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
    have hrearr : vecDot p (matVecMul A p) * (c * vecDot q (matVecMul E q))
        = (Real.sqrt c * vecDot p (matVecMul A p)) *
          (Real.sqrt c * vecDot q (matVecMul E q)) := by
      conv_lhs => rw [← hsq2]
      ring
    have hxy : vecDot p (matVecMul h q) ^ 2
        ≤ (Real.sqrt c * vecDot p (matVecMul A p)) *
          (Real.sqrt c * vecDot q (matVecMul E q)) := by
      rw [← hrearr]
      exact hre
    have hyoung := abs_le_add_halves_of_sq_le_mul hxy
      (mul_nonneg (Real.sqrt_nonneg c) hxnn) (mul_nonneg (Real.sqrt_nonneg c) hynn)
    linarith only [hyoung, le_abs_self (vecDot p (matVecMul h q))]
  · have hcy : c * vecDot q (matVecMul E q) ≤ 0 := by
      have hneg : 0 ≤ -c := le_of_lt (by linarith only [hc])
      have h2 : 0 ≤ -c * vecDot q (matVecMul E q) :=
        mul_nonneg hneg hynn
      linarith only [h2]
    have hu2 : vecDot p (matVecMul h q) ^ 2 ≤ 0 :=
      hre.trans (mul_nonpos_of_nonneg_of_nonpos hxnn hcy)
    have hu0 : vecDot p (matVecMul h q) = 0 := by
      have hu2' : vecDot p (matVecMul h q) ^ 2 = 0 :=
        le_antisymm hu2 (sq_nonneg _)
      exact (sq_eq_zero_iff).mp hu2'
    have hzero : 0 ≤ Real.sqrt c * (vecDot p (matVecMul A p) +
        vecDot q (matVecMul E q)) :=
      mul_nonneg (Real.sqrt_nonneg c) (add_nonneg hxnn hynn)
    linarith only [hu0, hzero]

/-! ## Specializations -/

/-- A positive-semidefinite matrix is symmetric (`Matrix.PosSemidef` carries the
self-adjointness; for real matrices self-adjointness is symmetry). -/
theorem posSemidef_isSymm {A : Mat d} (hA : A.PosSemidef) : A.IsSymm := by
  simpa [Matrix.IsHermitian, Matrix.IsSymm] using hA.isHermitian

/-- The quadratic form of a positive-semidefinite matrix is nonnegative,
converted from the `dotProduct`-form of `Matrix.PosSemidef` to the project
carriers `vecDot`/`matVecMul`. -/
theorem posSemidef_quadratic_nonneg {A : Mat d} (hA : A.PosSemidef) (v : Vec d) :
    0 ≤ vecDot v (matVecMul A v) := by
  simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using
    hA.dotProduct_mulVec_nonneg v

/-- **The unsymmetric conversion at the inverse.**  The specialization of
`two_vecDot_matVecMul_le_sqrt_mul` to `B = A⁻¹` for a symmetric positive
semidefinite invertible `A`: from the conjugated comparison
`hᵗ A⁻¹ h ≤ c • E` the bilinear bound `2 p·h q ≤ √c (p·A p + q·E q)` follows.
This is the shape the assembly consumes, `hᵗ σ_*^{-1}_L h ≤ c · σ_L` with
`A = σ_*L` and `E = σ_L`. -/
theorem two_vecDot_matVecMul_le_sqrt_mul_inv {A E : Mat d} {h : Mat d} {c : ℝ}
    (hA : A.PosSemidef) (hAunit : IsUnit A.det)
    (hEnonneg : ∀ v : Vec d, 0 ≤ vecDot v (matVecMul E v))
    (hsand : MatLoewnerLE (matTranspose h * A⁻¹ * h) (c • E))
    (p q : Vec d) :
    2 * vecDot p (matVecMul h q) ≤
      Real.sqrt c * (vecDot p (matVecMul A p) + vecDot q (matVecMul E q)) :=
  two_vecDot_matVecMul_le_sqrt_mul (posSemidef_isSymm hA)
    (fun v => posSemidef_quadratic_nonneg hA v) (Matrix.mul_nonsing_inv A hAunit)
    hEnonneg hsand p q

end

end SuperdiffusionCLT.Section2.Localization