/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.NewMixing.AssemblyScalarMax
public import SuperdiffusionCLT.Section2.CoarseGraining.Correspondence

/-!
# The bridge from the block energy bound to the scalar response bounds

By `e.Jaas.matform`, at the test vectors
`p = s^{-1/2} e`, `q = s^{1/2} e`, the scalar response `J(p, q)` is half of the block quadratic
form of `bfA` at `(-p, q)` minus `⟪p, q⟫ = |e|^2`, and the adjoint response `J^*(p, q)` is half
of the block quadratic form at `(p, q)` minus the same quantity. A uniform bound
`2 |e|^2 + R` on the block quadratic form at the two sign choices therefore bounds both scalar
responses by `R / 2`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.NewMixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-- The two test vectors `s^{-1/2} e` and `s^{1/2} e` have inner product `|e|^2`, and their
block images at the two signs are the vectors `(σ √(s⁻¹)) e`, `√s e` of the energy bound. -/
theorem newMixAsm_testVectors {d : ℕ} {s : ℝ} (hs : 0 < s) (e : Vec d) :
    vecDot (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e) = vecNormSq e ∧
    Real.sqrt s⁻¹ • e = s ^ (-(1 : ℝ) / 2) • e ∧
    Real.sqrt s • e = s ^ ((1 : ℝ) / 2) • e := by
  have hsqrt : Real.sqrt s = s ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
  have hinv : Real.sqrt s⁻¹ = s ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_inv, hsqrt, ← Real.rpow_neg hs.le]
    congr 1
    ring
  refine ⟨?_, by rw [hinv], by rw [hsqrt]⟩
  rw [vecDot_smul_left, vecDot_smul_right, ← mul_assoc, ← Real.rpow_add hs]
  have : (-(1 : ℝ) / 2) + (1 : ℝ) / 2 = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]
  rfl

/-- **The bridge** `newMixAsm_scalarJ_of_mainBound`: a bound `2 |e|^2 + R` on the block quadratic
form of the coarse block matrix of `a_L + h_0`, at the test vectors
`((σ √(s⁻¹)) e, √s e)` for both signs `σ = ±1`, gives the bound `R / 2` on the scalar response
`J` and on the adjoint response `J^*` at `(s^{-1/2} e, s^{1/2} e)`. -/
theorem newMixAsm_scalarJ_of_mainBound {d : ℕ} [NeZero d] {nu s R : ℝ} (hnu : 0 < nu)
    (hs : 0 < s) (omega : ShellSeq d) (L m : ℕ)
    (h0 : Mat d) (hh0 : matTranspose h0 = -h0)
    (hMain : ∀ e : Vec d, vecNormSq e ≤ 1 → ∀ sigma : ℝ, sigma ^ 2 = 1 →
      blockVecDot ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)
        (blockMatVecMul
          (Homogenization.Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d (m : ℤ)))
            (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
          ((sigma * Real.sqrt s⁻¹) • e, Real.sqrt s • e)) ≤ 2 * vecNormSq e + R) :
    (∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ (cubeDomain (originCube d (m : ℤ)))
          (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
          (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e) ≤ R / 2) ∧
    (∀ e : Vec d, vecNormSq e ≤ 1 →
      responseJ (cubeDomain (originCube d (m : ℤ)))
          (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).transpose
          (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e) ≤ R / 2) := by
  constructor
  · intro e he
    obtain ⟨hdot, hinv, hsq⟩ := newMixAsm_testVectors (d := d) hs e
    have hM := hMain e he (-1) (by norm_num)
    have hvec : ((-1 : ℝ) * Real.sqrt s⁻¹) • e = -(s ^ (-(1 : ℝ) / 2) • e) := by
      rw [neg_one_mul, neg_smul, hinv]
    rw [hvec, hsq] at hM
    have hJ := SuperdiffusionCLT.Section2.CoarseGraining.responseJ_eq_blockQuadratic
      (cubeDomain (originCube d (m : ℤ)))
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
      (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e)
    rw [SuperdiffusionCLT.Section2.CoarseGraining.responseJ_toCoeffField, hdot] at hJ
    linarith only [hJ, hM]
  · intro e he
    obtain ⟨hdot, hinv, hsq⟩ := newMixAsm_testVectors (d := d) hs e
    have hM := hMain e he 1 (by norm_num)
    have hvec : ((1 : ℝ) * Real.sqrt s⁻¹) • e = s ^ (-(1 : ℝ) / 2) • e := by
      rw [one_mul, hinv]
    rw [hvec, hsq] at hM
    have hJ := SuperdiffusionCLT.Section2.CoarseGraining.adjointResponseJ_eq_blockQuadratic
      (cubeDomain (originCube d (m : ℤ)))
      (newMixParam_aLplusH0 nu hnu omega L m h0 hh0)
      (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e)
    rw [hdot] at hJ
    have hJ' : responseJ (cubeDomain (originCube d (m : ℤ)))
          (newMixParam_aLplusH0 nu hnu omega L m h0 hh0).transpose
          (s ^ (-(1 : ℝ) / 2) • e) (s ^ ((1 : ℝ) / 2) • e) =
        (1 / 2 : ℝ) * blockVecDot (s ^ (-(1 : ℝ) / 2) • e, s ^ ((1 : ℝ) / 2) • e)
          (blockMatVecMul (Homogenization.Book.Ch02.coarseBlockMatrix (cubeDomain (originCube d (m : ℤ)))
            (newMixParam_aLplusH0 nu hnu omega L m h0 hh0))
            (s ^ (-(1 : ℝ) / 2) • e, s ^ ((1 : ℝ) / 2) • e)) - vecNormSq e := hJ
    linarith only [hJ', hM]

end
end SuperdiffusionCLT.Section4.NewMixing
