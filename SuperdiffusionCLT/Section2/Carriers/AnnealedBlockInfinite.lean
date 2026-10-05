/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The infinite-volume annealed block matrix 𝐀̄ₘ

The display `e.homs.defs` of the paper
defines the deterministic doubled matrix

`bfAhom_m := [[shom_m, 0], [0, shom_m^{-1}]] := lim_{n → ∞} E[bfA_m(cu_n)]`,

the sentence before the display recording that `bfAhom_m(cu_n)` is monotone
nonincreasing in `n`.

This module supplies the carrier `annealedBlockMatInfinite` for the right-hand
side of that display, the infinite-volume limit of the annealed block matrices
on the origin cubes. Following the convention of
`SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvLimit`, the limit is
taken as an **entrywise infimum**, not as `limUnder`: the infimum is total and
free of choice, and under the standing hypotheses of the block identification
(`[NeZero d]`, `0 < nu`, the prefix and J2–J4) it equals the limit of the
display on every entry, through
the scalar-block identification of `Section2/Annealed/Symmetry.lean` and the
monotone limits of `Section2/Annealed/InfiniteVolume.lean`.

## The block structure

Under the symmetry assumption J4 the two off-diagonal blocks of
`bfA_m(cu_n)` vanish and both diagonal blocks are scalar matrices
(`Section2/Annealed/Symmetry.lean`). The
identification proved here is therefore

`bfAhom_m = [[shom_m • Id, 0], [0, shom_{m,*}^{-1} • Id]]`,

with the two scalars the limits `sigmaBarUpperLimit` and
`sigmaBarStarInvLimit`. That the two scalars are reciprocal is a qualitative
homogenization input; it is not used and not assumed here.

## Main definitions

* `annealedBlockMatInfinite`: 𝐀̄ₘ.

## Main results

* `annealedBlockMatInfinite_upperRight`, `annealedBlockMatInfinite_lowerLeft`:
  the off-diagonal blocks vanish.
* `annealedBlockMatInfinite_upperLeft`, `annealedBlockMatInfinite_lowerRight`:
  the diagonal blocks are the scalar matrices of the two limits.
* `annealedBlockMatInfinite_eq_blockDiag`: the assembled block-diagonal form.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Carriers

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-- **The infinite-volume annealed block matrix 𝐀̄ₘ** of `e.homs.defs`,
realized entrywise as the infimum over the origin cubes of the entries of
`bfAhom_m(cu_n)`. The sequence of block matrices is nonincreasing in the Loewner order, so
each entry of this infimum is the entrywise limit that the display writes. -/
def annealedBlockMatInfinite (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) : BlockMat d :=
  ofFullBlockMat fun alpha beta =>
    ⨅ n : ℕ,
      toFullBlockMat
          (annealedBlockMatrix nu m P (cubeSet (originCube d (n : ℤ))))
        alpha beta

/-- The lower-right block, unfolded. -/
theorem annealedBlockMatInfinite_lowerRight_apply (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (i j : Fin d) :
    (annealedBlockMatInfinite nu m P).lowerRight i j =
      ⨅ n : ℕ,
        (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).lowerRight i j :=
  rfl

/-- The upper-left block, unfolded. -/
theorem annealedBlockMatInfinite_upperLeft_apply (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (i j : Fin d) :
    (annealedBlockMatInfinite nu m P).upperLeft i j =
      ⨅ n : ℕ,
        (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).upperLeft i j :=
  rfl

/-- The upper-right block, unfolded. -/
theorem annealedBlockMatInfinite_upperRight_apply (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (i j : Fin d) :
    (annealedBlockMatInfinite nu m P).upperRight i j =
      ⨅ n : ℕ,
        (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).upperRight i j :=
  rfl

/-- The lower-left block, unfolded. -/
theorem annealedBlockMatInfinite_lowerLeft_apply (nu : ℝ) (m : ℕ)
    (P : ProbabilityMeasure (ShellSeq d)) (i j : Fin d) :
    (annealedBlockMatInfinite nu m P).lowerLeft i j =
      ⨅ n : ℕ,
        (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).lowerLeft i j :=
  rfl

section Blocks

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hJ4 : ShellLawJ4 d P)

include hnu hJ4

/-- **The upper-right block of 𝐀̄ₘ vanishes**, the second half of
`e.homs.defs.U`. -/
theorem annealedBlockMatInfinite_upperRight :
    (annealedBlockMatInfinite nu m P).upperRight = 0 := by
  ext i j
  rw [annealedBlockMatInfinite_upperRight_apply]
  have hpoint : ∀ n : ℕ,
      (annealedBlockMatrix nu m P
        (cubeSet (originCube d (n : ℤ)))).upperRight i j = 0 := by
    intro n
    have h := annealedBlockMatrix_originCube_upperRight_eq_zero hnu m hJ4 (n : ℤ)
    exact congrFun (congrFun h i) j
  rw [iInf_congr hpoint, ciInf_const]
  rfl

/-- **The lower-left block of 𝐀̄ₘ vanishes**, the first half of
`e.homs.defs.U`. -/
theorem annealedBlockMatInfinite_lowerLeft :
    (annealedBlockMatInfinite nu m P).lowerLeft = 0 := by
  ext i j
  rw [annealedBlockMatInfinite_lowerLeft_apply]
  have hpoint : ∀ n : ℕ,
      (annealedBlockMatrix nu m P
        (cubeSet (originCube d (n : ℤ)))).lowerLeft i j = 0 := by
    intro n
    have h := annealedBlockMatrix_originCube_lowerLeft_eq_zero hnu m hJ4 (n : ℤ)
    exact congrFun (congrFun h i) j
  rw [iInf_congr hpoint, ciInf_const]
  rfl

/-- **The lower-right block of 𝐀̄ₘ is the scalar matrix
`shom_{m,*}^{-1} Id`**, with the limit as its scalar. -/
theorem annealedBlockMatInfinite_lowerRight :
    (annealedBlockMatInfinite nu m P).lowerRight =
      sigmaBarStarInvLimit nu m P • (1 : Mat d) := by
  ext i j
  rw [annealedBlockMatInfinite_lowerRight_apply]
  have hpoint : ∀ n : ℕ,
      (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).lowerRight i j =
        sigmaBarStarInvSeq nu m P n * (1 : Mat d) i j := by
    intro n
    have h := sigmaBarStarInv_originCube_eq_smul_one hnu m hJ4 (n : ℤ)
    have hentry := congrFun (congrFun h i) j
    simpa only [sigmaBarStarInv, Matrix.smul_apply, smul_eq_mul,
      sigmaBarStarInvSeq] using hentry
  rw [iInf_congr hpoint, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, mul_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, mul_zero]
    exact ciInf_const

/-- **The upper-left block of 𝐀̄ₘ is the scalar matrix `shom_m Id`**,
with the limit of the upper-left scalars as its scalar. -/
theorem annealedBlockMatInfinite_upperLeft :
    (annealedBlockMatInfinite nu m P).upperLeft =
      sigmaBarUpperLimit nu m P • (1 : Mat d) := by
  ext i j
  rw [annealedBlockMatInfinite_upperLeft_apply]
  have hpoint : ∀ n : ℕ,
      (annealedBlockMatrix nu m P
          (cubeSet (originCube d (n : ℤ)))).upperLeft i j =
        sigmaBarSeq nu m P n * (1 : Mat d) i j := by
    intro n
    have h := annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar hnu m hJ4
      (n : ℤ)
    have hscalar := sigmaBar_originCube_eq_smul_one hnu m hJ4 (n : ℤ)
    have hentry := congrFun (congrFun (h.trans hscalar) i) j
    simpa only [Matrix.smul_apply, smul_eq_mul, sigmaBarSeq] using hentry
  rw [iInf_congr hpoint, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.one_apply_eq, mul_one]
    rfl
  · simp only [Matrix.one_apply_ne hij, mul_zero]
    exact ciInf_const

/-- **The block-diagonal form of 𝐀̄ₘ**: the assertion of `e.homs.defs`
with the two scalars kept separate, since their reciprocity is the qualitative
homogenization input. -/
theorem annealedBlockMatInfinite_eq_blockDiag :
    annealedBlockMatInfinite nu m P =
      Book.Ch02.blockDiag (sigmaBarUpperLimit nu m P • (1 : Mat d))
        (sigmaBarStarInvLimit nu m P • (1 : Mat d)) :=
  blockMat_ext
    (annealedBlockMatInfinite_upperLeft hnu m hJ4)
    (annealedBlockMatInfinite_upperRight hnu m hJ4)
    (annealedBlockMatInfinite_lowerLeft hnu m hJ4)
    (annealedBlockMatInfinite_lowerRight hnu m hJ4)

end Blocks

/-! ## The convergence asserted by `e.homs.defs` -/

section Convergence

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (m : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

end Convergence

end

end SuperdiffusionCLT.Section2.Carriers
