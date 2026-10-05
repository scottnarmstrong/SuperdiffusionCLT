/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.Measurability

/-!
# The annealed block matrices of the cutoff field

The paper, display `e.homs.defs.U.0`, defines the annealed matrices of the infrared cutoff
`a_m` by

`bfAhom_m(U) = E[bfA_m(U)]`,

reading off `shom_{m,*}^{-1}(U)`, `khom_m(U)` and `shom_m(U)` from the blocks
of that expectation. The lower block is therefore the expectation of the
*inverse* matrix `s_{m,*}^{-1}(U)`, and the annealed `s_{m,*}(U)` is its
inverse: the expectation is taken first and the inversion afterwards.
This module writes those definitions down.

The primitive objects are exactly the four blocks of the expectation: `bBar`
(the upper-left block `bhom_m(U)`), `sigmaBarStarInv` (the lower-right block),
and `sigmaBarStarInvKappaMean` (the negative of the lower-left block). The
derived objects `sigmaBarStar`, `kappaBar` and `sigmaBar` are then obtained by
the same algebra as in the deterministic case, matching
`Homogenization.Book.Ch04.annealedSigmaStar`, `annealedKappa` and
`annealedSigma`.

Bochner integration is entrywise, so an entry of an annealed matrix is the
integral of the corresponding entry of the coarse matrix. On triadic cubes
those entries are measurable functions of the shell sequence
(`SuperdiffusionCLT.Section2.Annealed.Measurability`), and the annealed
objects agree with `CoarseGraining`'s Chapter 4 annealed objects at the
pushforward law `cutoffLaw`.

## Main results

* `annealedBlockMatrix`, `sigmaBarStarInv`, `sigmaBarStar`,
  `sigmaBarStarInvKappaMean`, `kappaBar`, `bBar`, `sigmaBar`: the definitions
  of `e.homs.defs.U.0`.
* `sigmaBarStarInv_eq_integral_sigmaStarInvCoarse`: the lower-right block is
  the expectation of `s_{m,*}^{-1}(U; a_m)` itself.
* `sigmaBarStarInv_eq_ch04`, `bBar_eq_ch04`, `sigmaBarStarInvKappaMean_eq_ch04`,
  `sigmaBarStar_eq_ch04`, `kappaBar_eq_ch04`, `sigmaBar_eq_ch04`: the
  definitions agree with `CoarseGraining`'s Chapter 4 annealed matrices at the
  pushforward law.
* `isSymm_coarseBlockMatrix_lowerRight`, `isSymm_coarseBlockMatrix_upperLeft`: symmetry of the
  diagonal blocks of the coarse block matrix.
* `matLoewnerLE_of_integral`: the Loewner order passes to expectations. Positivity of the
  annealed lower block is proved in the symmetry module (`sigmaBarStarInvScalar_pos`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining

noncomputable section

variable {d : ℕ}

/-! ## The definitions of `e.homs.defs.U.0` -/

/-- `bfAhom_m(U) = E[bfA_m(U)]`, the annealed doubled coarse-grained matrix of
the infrared cutoff `a_m`, `e.homs.defs.U.0`. The Bochner integral is taken
entrywise. -/
def annealedBlockMatrix (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
    (U : Set (Vec d)) : BlockMat d where
  upperLeft := fun i j ↦
    ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).upperLeft i j ∂P.toMeasure
  upperRight := fun i j ↦
    ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).upperRight i j ∂P.toMeasure
  lowerLeft := fun i j ↦
    ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerLeft i j ∂P.toMeasure
  lowerRight := fun i j ↦
    ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerRight i j ∂P.toMeasure

section Entries

variable (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (U : Set (Vec d))

@[simp] theorem annealedBlockMatrix_upperLeft_apply (i j : Fin d) :
    (annealedBlockMatrix nu m P U).upperLeft i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).upperLeft i j
        ∂P.toMeasure := rfl

@[simp] theorem annealedBlockMatrix_upperRight_apply (i j : Fin d) :
    (annealedBlockMatrix nu m P U).upperRight i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).upperRight i j
        ∂P.toMeasure := rfl

@[simp] theorem annealedBlockMatrix_lowerLeft_apply (i j : Fin d) :
    (annealedBlockMatrix nu m P U).lowerLeft i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerLeft i j
        ∂P.toMeasure := rfl

@[simp] theorem annealedBlockMatrix_lowerRight_apply (i j : Fin d) :
    (annealedBlockMatrix nu m P U).lowerRight i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerRight i j
        ∂P.toMeasure := rfl

/-- `shom_{m,*}^{-1}(U)`, the lower-right block of `bfAhom_m(U)`. This is the
expectation of the inverse matrix, and it is the primitive object: the annealed
`shom_{m,*}(U)` below is defined as its inverse. -/
def sigmaBarStarInv : Mat d := (annealedBlockMatrix nu m P U).lowerRight

/-- `shom_{m,*}(U)`, the inverse of the annealed lower block. -/
def sigmaBarStar : Mat d := (sigmaBarStarInv nu m P U)⁻¹

/-- `E[(s_{m,*}^{-1} kcg_m)(U)]`, the negative of the lower-left block. -/
def sigmaBarStarInvKappaMean : Mat d := -((annealedBlockMatrix nu m P U).lowerLeft)

/-- `khom_m(U)`, the annealed coupling matrix. -/
def kappaBar : Mat d := sigmaBarStar nu m P U * sigmaBarStarInvKappaMean nu m P U

/-- `bhom_m(U)`, the upper-left block of `bfAhom_m(U)`. -/
def bBar : Mat d := (annealedBlockMatrix nu m P U).upperLeft

/-- `shom_m(U)`, the annealed conductivity matrix, read off from the
upper-left block by the same algebra as in the deterministic case. -/
def sigmaBar : Mat d :=
  bBar nu m P U -
    matTranspose (kappaBar nu m P U) * sigmaBarStarInv nu m P U * kappaBar nu m P U

@[simp] theorem sigmaBarStarInv_apply (i j : Fin d) :
    sigmaBarStarInv nu m P U i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerRight i j
        ∂P.toMeasure := rfl

@[simp] theorem bBar_apply (i j : Fin d) :
    bBar nu m P U i j =
      ∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).upperLeft i j
        ∂P.toMeasure := rfl

@[simp] theorem sigmaBarStarInvKappaMean_apply (i j : Fin d) :
    sigmaBarStarInvKappaMean nu m P U i j =
      -∫ omega, (coarseBlockMatrix U (coefficientCutoff nu omega m).toFun).lowerLeft i j
        ∂P.toMeasure := rfl

end Entries

/-! ## The manuscript reading, and the bridge to `CoarseGraining`

On a triadic cube the four block entries are measurable, so the entrywise
Bochner integrals of `annealedBlockMatrix` are the Chapter 4 annealed
integrals of `CoarseGraining` at the pushforward law `cutoffLaw`. -/

section Bridge

variable {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (Q : TriadicCube d)

include hnu

omit hnu in
/-- Transfer of a scalar expectation from the shell-sequence carrier to the
coefficient carrier. -/
theorem integral_cutoffLaw (F : RegCoeffField d → ℝ)
    (hF : AEStronglyMeasurable F (cutoffLaw (d := d) nu m P)) :
    ∫ a, F a ∂(cutoffLaw (d := d) nu m P) =
      ∫ omega, F (coefficientCutoff nu omega m) ∂P.toMeasure :=
  integral_map (measurable_coefficientCutoff nu m).aemeasurable hF

/-- The annealed lower-right block is `CoarseGraining`'s annealed
`s_*^{-1}(U)` at the cutoff law. -/
theorem sigmaBarStarInv_eq_ch04 :
    sigmaBarStarInv nu m P (cubeSet Q) =
      Book.Ch04.annealedSigmaStarInv (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  ext i j
  rw [Book.Ch04.annealedSigmaStarInv_apply, sigmaBarStarInv_apply]
  exact (integral_cutoffLaw (nu := nu) m P
    (fun a ↦ (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight i j)
    (((restrictionLawCarrier_cutoffLaw hnu m P).aemeasurable_coarseBlockMatrix_lowerRight_apply_cubeSet
        Q i j).aestronglyMeasurable)).symm

/-- The annealed upper-left block is `CoarseGraining`'s annealed `b(U)` at the
cutoff law. -/
theorem bBar_eq_ch04 :
    bBar nu m P (cubeSet Q) =
      Book.Ch04.annealedB (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  ext i j
  rw [Book.Ch04.annealedB_apply, bBar_apply]
  exact (integral_cutoffLaw (nu := nu) m P
    (fun a ↦ (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft i j)
    (((restrictionLawCarrier_cutoffLaw hnu m P).aemeasurable_coarseBlockMatrix_upperLeft_apply_cubeSet
        Q i j).aestronglyMeasurable)).symm

/-- The annealed mixed block is `CoarseGraining`'s
`E[s_*^{-1}(U) k(U)]` at the cutoff law. -/
theorem sigmaBarStarInvKappaMean_eq_ch04 :
    sigmaBarStarInvKappaMean nu m P (cubeSet Q) =
      Book.Ch04.annealedSigmaStarInvKappaMean (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  ext i j
  rw [Book.Ch04.annealedSigmaStarInvKappaMean_apply, sigmaBarStarInvKappaMean_apply]
  refine congrArg Neg.neg ?_
  exact (integral_cutoffLaw (nu := nu) m P
    (fun a ↦ (coarseBlockMatrix (cubeSet Q) a.toFun).lowerLeft i j)
    (((restrictionLawCarrier_cutoffLaw hnu m P).aemeasurable_coarseBlockMatrix_lowerLeft_apply_cubeSet
        Q i j).aestronglyMeasurable)).symm

/-- The annealed `s_*(U)` is `CoarseGraining`'s annealed `s_*(U)`. -/
theorem sigmaBarStar_eq_ch04 :
    sigmaBarStar nu m P (cubeSet Q) =
      Book.Ch04.annealedSigmaStar (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  rw [sigmaBarStar, Book.Ch04.annealedSigmaStar, sigmaBarStarInv_eq_ch04 hnu m P Q]

/-- The annealed coupling matrix is `CoarseGraining`'s annealed `k(U)`. -/
theorem kappaBar_eq_ch04 :
    kappaBar nu m P (cubeSet Q) =
      Book.Ch04.annealedKappa (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  rw [kappaBar, Book.Ch04.annealedKappa, sigmaBarStar_eq_ch04 hnu m P Q,
    sigmaBarStarInvKappaMean_eq_ch04 hnu m P Q]

/-- The annealed conductivity matrix is `CoarseGraining`'s annealed `s(U)`. -/
theorem sigmaBar_eq_ch04 :
    sigmaBar nu m P (cubeSet Q) =
      Book.Ch04.annealedSigma (cutoffLaw (d := d) nu m P) (cubeSet Q) := by
  rw [sigmaBar, Book.Ch04.annealedSigma, bBar_eq_ch04 hnu m P Q,
    kappaBar_eq_ch04 hnu m P Q, sigmaBarStarInv_eq_ch04 hnu m P Q]

/-- **The manuscript reading of the annealed lower block.** It is the
expectation of the coarse matrix `s_{m,*}^{-1}(U; a_m)` itself, on the open
cube where the Chapter 2 vocabulary lives. -/
theorem sigmaBarStarInv_eq_integral_sigmaStarInvCoarse [NeZero d] (i j : Fin d) :
    sigmaBarStarInv nu m P (cubeSet Q) i j =
      ∫ omega, sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega m).toFun i j ∂P.toMeasure := by
  rw [sigmaBarStarInv_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ ?_)
  simp only []
  rw [coarseBlockMatrix_cubeSet_lowerRight_eq
    (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega m) Q]

end Bridge

/-! ## Symmetry of the diagonal blocks

The two diagonal blocks of `bfA(U; a)` are symmetric for every coefficient
field, by inspection of the polarization formulas defining them, so the same
holds after taking expectations. -/

section Symmetry

variable (nu : ℝ) (m : ℕ) (P : ProbabilityMeasure (ShellSeq d)) (U : Set (Vec d))

/-- The lower-right block of `bfA(U; a)` is symmetric. -/
theorem isSymm_coarseBlockMatrix_lowerRight (a : CoeffField d) :
    ((coarseBlockMatrix U a).lowerRight).IsSymm := by
  classical
  ext i j
  rw [Matrix.transpose_apply, coarseBlockMatrix_lowerRight_apply,
    coarseBlockMatrix_lowerRight_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    rw [ite_eq_right hji, ite_eq_right hij,
      add_comm (((0 : Vec d), Pi.single j (1 : ℝ)) : BlockVec d)]
    ring

/-- The upper-left block of `bfA(U; a)` is symmetric. -/
theorem isSymm_coarseBlockMatrix_upperLeft (a : CoeffField d) :
    ((coarseBlockMatrix U a).upperLeft).IsSymm := by
  classical
  ext i j
  rw [Matrix.transpose_apply, coarseBlockMatrix_upperLeft_apply,
    coarseBlockMatrix_upperLeft_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := Ne.symm hij
    rw [ite_eq_right hji, ite_eq_right hij,
      add_comm ((Pi.single j (1 : ℝ), (0 : Vec d)) : BlockVec d)]
    ring

/-- The upper-right block of `bfA(U; a)` is the transpose of the lower-left
block, for every coefficient field. -/
theorem coarseBlockMatrix_upperRight_eq_transpose_lowerLeft (a : CoeffField d) :
    (coarseBlockMatrix U a).upperRight =
      matTranspose ((coarseBlockMatrix U a).lowerLeft) := by
  ext i j
  rw [coarseBlockMatrix_upperRight_apply]
  simp only [matTranspose, Matrix.transpose_apply]
  rw [coarseBlockMatrix_lowerLeft_apply,
    add_comm (((0 : Vec d), Pi.single j (1 : ℝ)) : BlockVec d)]
  ring

/-- The upper-right block of `bfAhom_m(U)` is the transpose of its lower-left
block. -/
theorem annealedBlockMatrix_upperRight_eq_transpose_lowerLeft :
    (annealedBlockMatrix nu m P U).upperRight =
      matTranspose ((annealedBlockMatrix nu m P U).lowerLeft) := by
  ext i j
  simp only [matTranspose, Matrix.transpose_apply, annealedBlockMatrix_upperRight_apply,
    annealedBlockMatrix_lowerLeft_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ ?_)
  exact congrFun (congrFun (coarseBlockMatrix_upperRight_eq_transpose_lowerLeft U
    (coefficientCutoff nu omega m).toFun) i) j

end Symmetry

/-! ## The Loewner order passes to expectations

`e.CG.bounds.1` and `e.CG.bounds.2` are almost-sure Loewner inequalities
between coarse matrices; the annealed matrices inherit them entry by entry
whenever both sides are integrable. -/

section Order

/-- The quadratic form of an entrywise expectation is the expectation of the
quadratic form. -/
theorem vecDot_matVecMul_integral {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A : Omega → Mat d}
    (hA : ∀ i j, Integrable (fun w ↦ A w i j) mu) (x : Vec d) :
    vecDot x (matVecMul (fun i j ↦ ∫ w, A w i j ∂mu) x) =
      ∫ w, vecDot x (matVecMul (A w) x) ∂mu := by
  calc
    vecDot x (matVecMul (fun i j ↦ ∫ w, A w i j ∂mu) x)
        = ∑ i : Fin d, x i * ∑ j : Fin d, (∫ w, A w i j ∂mu) * x j := rfl
    _ = ∑ i : Fin d, x i * ∑ j : Fin d, ∫ w, A w i j * x j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          refine congrArg (fun t ↦ x i * t) (Finset.sum_congr rfl fun j _ ↦ ?_)
          rw [integral_mul_const]
    _ = ∑ i : Fin d, x i * ∫ w, ∑ j : Fin d, A w i j * x j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          refine congrArg (fun t ↦ x i * t) ?_
          rw [integral_finsetSum _ fun j _ ↦ (hA i j).mul_const (x j)]
    _ = ∑ i : Fin d, ∫ w, x i * ∑ j : Fin d, A w i j * x j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [integral_const_mul]
    _ = ∫ w, ∑ i : Fin d, x i * ∑ j : Fin d, A w i j * x j ∂mu := by
          refine (integral_finsetSum _ fun i _ ↦ ?_).symm
          exact (integrable_finsetSum _ fun j _ ↦ (hA i j).mul_const (x j)).const_mul (x i)
    _ = ∫ w, vecDot x (matVecMul (A w) x) ∂mu := rfl

/-- An almost-sure Loewner inequality between integrable matrix observables
passes to their entrywise expectations. -/
theorem matLoewnerLE_of_integral {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {A B : Omega → Mat d}
    (hA : ∀ i j, Integrable (fun w ↦ A w i j) mu)
    (hB : ∀ i j, Integrable (fun w ↦ B w i j) mu)
    (h : ∀ᵐ w ∂mu, MatLoewnerLE (A w) (B w)) :
    MatLoewnerLE (fun i j ↦ ∫ w, A w i j ∂mu) (fun i j ↦ ∫ w, B w i j ∂mu) := by
  intro x
  rw [vecDot_matVecMul_integral hA x, vecDot_matVecMul_integral hB x]
  have hIA : Integrable (fun w ↦ vecDot x (matVecMul (A w) x)) mu :=
    integrable_finsetSum _ fun i _ ↦
      (integrable_finsetSum _ fun j _ ↦ (hA i j).mul_const (x j)).const_mul (x i)
  have hIB : Integrable (fun w ↦ vecDot x (matVecMul (B w) x)) mu :=
    integrable_finsetSum _ fun i _ ↦
      (integrable_finsetSum _ fun j _ ↦ (hB i j).mul_const (x j)).const_mul (x i)
  have hmono : ∫ w, vecDot x (matVecMul (A w) x) ∂mu ≤
      ∫ w, vecDot x (matVecMul (B w) x) ∂mu := by
    refine integral_mono_ae hIA hIB ?_
    filter_upwards [h] with w hw
    linarith only [hw x]
  linarith only [hmono]

end Order

/-! ## The half-open and open cube give the same annealed matrices

The measurability engine of `CoarseGraining` works on the half-open cube, the
Chapter 2 vocabulary on its open core, and the two coarse block matrices agree
on a triadic cube. Nothing in the annealed definitions depends on the choice. -/

end

end SuperdiffusionCLT.Section2.Annealed
