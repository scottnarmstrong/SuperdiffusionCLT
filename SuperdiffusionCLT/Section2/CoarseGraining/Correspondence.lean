/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch02

/-!
# Correspondence with the coarse-graining vocabulary of Section 2.1-2.2

The manuscript builds Sections 3 to 5 on the coarse-grained matrices
`s(U)`, `s_*(U)`, `k(U)`, the block matrix `bfA(U)`, the response functional
`J(U,p,q)` and its adjoint `J^*(U,p,q)`. All of these objects already exist in the
`CoarseGraining` library, in two layers which this module identifies:

* the raw layer of `Homogenization/CoarseGraining/Definitions.lean`, on a bare
  `Set (Vec d)` and a bare `CoeffField d` -- the layer the marginal
  cutoff reaches through `RegCoeffField.toCoeffField`; and
* the public Chapter 2 layer of `Homogenization/Book/Ch02/`, on a `Domain d`
  and a `CoeffOn U`, which is where the unconditional theorems live.

The two layers agree definitionally on a `CoeffOn U`, and this module records
that identification and then restates, on the raw layer and in the
manuscript's own normalization `s_*^{-1}(U) = (s_*(U))^{-1}`, the block
representation `e.J.mat`, its adjoint `e.J.mat.star`, the doubled forms
`e.Jaas.matform` and `e.bfA.by.J`, and the order chain `e.CG.bounds.1`.

The last section proves the algebraic half of the commutation with constant
anti-symmetric matrices, `e.commute.k0`. The companion module
`SuperdiffusionCLT.Section2.CoarseGraining.CutoffCorrespondence` applies
everything here to the marginal cutoff field `a_L = nu Id + k_L`.

## Main results

* `responseJ_toCoeffField`, `sigmaCoarse_toCoeffField`,
  `sigmaStarInvCoarse_toCoeffField`, `kappaCoarse_toCoeffField`: the two
  carriers agree. `sigmaStarInvCoarse_toCoeffField` is the identification the
  other three are built on, since the blocks of `bfA(U)` are written through `s_*^{-1}(U)`.
* `responseJ_eq_blockQuadratic`, `adjointResponseJ_eq_blockQuadratic`:
  `e.Jaas.matform`.
* `coarseBlockMatrix_upperLeft`, `coarseBlockMatrix_upperRight`,
  `coarseBlockMatrix_lowerLeft`, `coarseBlockMatrix_lowerRight`: the blocks of
  `bfA(U)` in the manuscript's normalization, `e.bigA.def`.
* `harmonicMean_le_sigmaStarCoarse`, `sigmaStarCoarse_le_sigmaCoarse`,
  `sigmaCoarse_le_bCoarse`,
  `bCoarse_le_averagedSymmPartPlusCorrection`, `sigmaStarCoarse_posDef`,
  `bCoarse_posDef`: the order chain and positivity of `e.CG.bounds.1` and of `b(U)`.
* `sigmaCoarse_eq_of_responseJ_skewShift`,
  `kappaCoarse_eq_of_responseJ_skewShift`: the coarse-matrix half of
  `e.commute.k0`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.CoarseGraining

open Homogenization

noncomputable section

variable {d : ℕ}

/-! ## The two coarse-graining carriers

`CoarseGraining` defines the coarse-grained objects twice: once on a bare
`Set (Vec d)` together with a bare `CoeffField d`, and once on the public
Chapter 2 pair `Domain d`, `CoeffOn U`. The public layer carries the
unconditional theorems, while the raw layer is the one the marginal
cutoff reaches. The following identifications let a marginal consumer use
either. -/

/-- The raw response functional of the underlying field of a Chapter 2
coefficient object is the public Chapter 2 response functional `J(U,p,q)`. -/
theorem responseJ_toCoeffField (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U)
    (p q : Vec d) :
    Homogenization.ResponseJ (U : Set (Vec d)) p q a.toCoeffField =
      Book.Ch02.responseJ U a p q :=
  rfl

/-- The raw `s_*^{-1}(U)` of the underlying field is the public Chapter 2
matrix. -/
theorem sigmaStarInvCoarse_toCoeffField (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField =
      Book.Ch02.sigmaStarInvCoarse U a :=
  rfl

/-- The raw `k(U)` of the underlying field is the public Chapter 2 matrix. -/
theorem kappaCoarse_toCoeffField (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField =
      Book.Ch02.kappaCoarse U a :=
  rfl

/-- The raw `s(U)` of the underlying field is the public Chapter 2 matrix. -/
theorem sigmaCoarse_toCoeffField (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField =
      Book.Ch02.sigmaCoarse U a :=
  rfl

/-! ## The manuscript's normalization of `s_*(U)`

The manuscript writes `s_*^{-1}(U)` for the inverse of the coarse-grained
lower matrix, while `CoarseGraining` keeps the inverse primitive and defines
`s_*(U)` as its matrix inverse. The two readings agree because the primitive
matrix is invertible. -/

/-- `(s_*(U))^{-1}` is the primitive coarse matrix `s_*^{-1}(U)`. -/
theorem inv_sigmaStarCoarse (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹ =
      Homogenization.sigmaStarInvCoarse (U : Set (Vec d)) a.toCoeffField :=
  Matrix.nonsing_inv_nonsing_inv _ (Book.Ch02.isUnit_det_sigmaStarInvCoarse U a)

/-- `s_*(U)` is invertible. -/
theorem isUnit_det_sigmaStarCoarse (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    IsUnit (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).det :=
  Book.Ch02.isUnit_det_sigmaStarCoarse U a

/-! ## The block representation of `J` and `J^*`

`e.J.mat`, `e.J.mat.star`, `e.Jaas.matform` and `e.bfA.by.J`.
The manuscript's `bfA(U)` of `e.bigA.def` is the public Chapter 2 block matrix
`Book.Ch02.coarseBlockMatrix`; its blocks are recorded below. -/

/-- The Loewner-symmetric pairing of a symmetric matrix. -/
private theorem vecDot_matVecMul_comm_of_isSymm {S : Mat d} (hS : S.IsSymm)
    (x y : Vec d) :
    vecDot x (matVecMul S y) = vecDot y (matVecMul S x) := by
  calc
    vecDot x (matVecMul S y) = vecDot x (matVecMul (matTranspose S) y) := by
      rw [show matTranspose S = S from hS]
    _ = vecDot (matVecMul S x) y := vecDot_matVecMul_transpose x y S
    _ = vecDot y (matVecMul S x) := vecDot_comm _ _

/-- The doubled quadratic form of the block matrix assembled from a coarse
matrix package is the completed square of `e.J.mat.star`. -/
private theorem blockVecDot_blockMatrixOfCoarseMatrices
    (M : Book.Ch02.CoarseMatrices d) (hS : M.sigmaStarInv.IsSymm) (r q : Vec d) :
    blockVecDot (r, q)
        (blockMatVecMul (Book.Ch02.blockMatrixOfCoarseMatrices M) (r, q)) =
      vecDot r (matVecMul M.sigma r) +
        vecDot (q - matVecMul M.kappa r)
          (matVecMul M.sigmaStarInv (q - matVecMul M.kappa r)) := by
  have hmix : vecDot (matVecMul M.kappa r) (matVecMul M.sigmaStarInv q) =
      vecDot q (matVecMul M.sigmaStarInv (matVecMul M.kappa r)) :=
    vecDot_matVecMul_comm_of_isSymm hS _ _
  have hcross : vecDot r (matVecMul (matTranspose M.kappa) (matVecMul M.sigmaStarInv q)) =
      vecDot q (matVecMul M.sigmaStarInv (matVecMul M.kappa r)) := by
    rw [vecDot_matVecMul_transpose, hmix]
  have hquad : vecDot r
        (matVecMul (matTranspose M.kappa) (matVecMul M.sigmaStarInv (matVecMul M.kappa r))) =
      vecDot (matVecMul M.kappa r) (matVecMul M.sigmaStarInv (matVecMul M.kappa r)) :=
    vecDot_matVecMul_transpose _ _ _
  simp only [Book.Ch02.blockMatrixOfCoarseMatrices, blockVecDot, blockMatVecMul,
    Book.Ch02.CoarseMatrices.b, sub_eq_add_neg, add_matVecMul, neg_matVecMul,
    matVecMul_add, matVecMul_neg, ← matVecMul_mul,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right, vecDot_add_left]
  rw [hcross, hquad, hmix]
  ring

/-- The quadratic form of a matrix is even. -/
private theorem vecDot_neg_matVecMul_neg (A : Mat d) (x : Vec d) :
    vecDot (-x) (matVecMul A (-x)) = vecDot x (matVecMul A x) := by
  rw [matVecMul_neg, vecDot_neg_left, vecDot_neg_right, neg_neg]

/-- `e.Jaas.matform`: the doubled form of `e.J.mat`. The
manuscript's `bfA(U)` of `e.bigA.def` is the public coarse block matrix. -/
theorem responseJ_eq_blockQuadratic (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Homogenization.ResponseJ (U : Set (Vec d)) p q a.toCoeffField =
      (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (-p, q))
        - vecDot p q := by
  have hblock := blockVecDot_blockMatrixOfCoarseMatrices
    (Book.Ch02.coarseMatrices U a) (Book.Ch02.sigmaStarInvCoarse_isSymm U a) (-p) q
  have hneg : q - matVecMul (Book.Ch02.kappaCoarse U a) (-p) =
      q + matVecMul (Book.Ch02.kappaCoarse U a) p := by
    rw [matVecMul_neg, sub_neg_eq_add]
  rw [responseJ_toCoeffField,
    Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical U a p q,
    show Book.Ch02.coarseBlockMatrix U a =
      Book.Ch02.blockMatrixOfCoarseMatrices (Book.Ch02.coarseMatrices U a) from rfl,
    hblock]
  simp only [Book.Ch02.coarseMatrices_sigma, Book.Ch02.coarseMatrices_kappa,
    Book.Ch02.coarseMatrices_sigmaStarInv, hneg,
    vecDot_neg_matVecMul_neg]
  ring

/-- `e.Jaas.matform`: the doubled form of `e.J.mat.star`. -/
theorem adjointResponseJ_eq_blockQuadratic (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) (p q : Vec d) :
    Homogenization.ResponseJ (U : Set (Vec d)) p q
        (fun x => matTranspose (a.toCoeffField x)) =
      (1 / 2 : ℝ) * blockVecDot (p, q)
          (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) (p, q))
        - vecDot p q := by
  have hblock := blockVecDot_blockMatrixOfCoarseMatrices
    (Book.Ch02.coarseMatrices U a) (Book.Ch02.sigmaStarInvCoarse_isSymm U a) p q
  rw [show (fun x => matTranspose (a.toCoeffField x)) = a.transpose.toCoeffField from rfl,
    responseJ_toCoeffField,
    (Book.Ch02.responseMagicIdentitiesTheory U a).adjoint_quadratic p q,
    show Book.Ch02.coarseBlockMatrix U a =
      Book.Ch02.blockMatrixOfCoarseMatrices (Book.Ch02.coarseMatrices U a) from rfl,
    hblock]
  simp only [Book.Ch02.coarseMatrices_sigma, Book.Ch02.coarseMatrices_kappa,
    Book.Ch02.coarseMatrices_sigmaStarInv]
  ring

/-! ## The blocks of `bfA(U)` and the matrix `b(U)`

`e.bigA.def`, and the upper-left block `b(U)`. -/

/-- The raw coarse matrix `b(U) = (s + k^t s_*^{-1} k)(U)` of a Chapter 2
coefficient object is the public Chapter 2 matrix. -/
theorem bCoarse_toCoeffField (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    Homogenization.bCoarse (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) =
      Book.Ch02.bCoarse U a := by
  unfold Homogenization.bCoarse
  rw [inv_sigmaStarCoarse]
  rfl

/-- The upper-left block of `bfA(U)` is `b(U) = (s + k^t s_*^{-1} k)(U)`. -/
theorem coarseBlockMatrix_upperLeft (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    (Book.Ch02.coarseBlockMatrix U a).upperLeft =
      Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField +
        matTranspose (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) *
          (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹ *
          Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField := by
  rw [inv_sigmaStarCoarse]
  rfl

/-- The lower-left block of `bfA(U)` is `-(s_*^{-1} k)(U)`. -/
theorem coarseBlockMatrix_lowerLeft (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    (Book.Ch02.coarseBlockMatrix U a).lowerLeft =
      -((Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹ *
        Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField) := by
  rw [inv_sigmaStarCoarse]
  rfl

/-- The lower-right block of `bfA(U)` is `s_*^{-1}(U)`. -/
theorem coarseBlockMatrix_lowerRight (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    (Book.Ch02.coarseBlockMatrix U a).lowerRight =
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)⁻¹ := by
  rw [inv_sigmaStarCoarse]
  rfl

/-! ## The order chain and positivity

`e.CG.bounds.1` and the control of the symmetric part of
`k(U)`, `e.symm.part.k`. Everything here is an application of
the Chapter 2 theorems; nothing is reproved. -/

/-- `s_*(U)` is positive definite; with the ordering below this is the strict
positivity `b(U) >= s_*(U) > 0`. -/
theorem sigmaStarCoarse_posDef (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField).PosDef :=
  Book.Ch02.sigmaStarCoarse_posDef U a

/-- The harmonic-mean lower bound of `e.CG.bounds.1`. -/
theorem harmonicMean_le_sigmaStarCoarse (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    MatLoewnerLE (Book.Ch02.averagedSymmPartInv U a)⁻¹
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField) :=
  Book.Ch02.harmonicMean_le_sigmaStarCoarse U a

/-- `s_*(U) <= s(U)`, the non-obvious ordering of `e.CG.bounds.1`. -/
theorem sigmaStarCoarse_le_sigmaCoarse (U : Book.Ch02.Domain d)
    (a : Book.Ch02.CoeffOn U) :
    MatLoewnerLE (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField) :=
  Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U a

/-- `b(U)` is positive definite, so `b^{-1}(U)` is well
defined. -/
theorem bCoarse_posDef (U : Book.Ch02.Domain d) (a : Book.Ch02.CoeffOn U) :
    (Homogenization.bCoarse
      (Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) a.toCoeffField)
      (Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField)).PosDef := by
  rw [bCoarse_toCoeffField]
  exact Book.Ch02.bCoarse_posDef U a

/-! ## The one-slot maximizer

`e.v.oneslot.def` and the identities
`e.solution.avg.grad.flux.identity` and
`e.solution.p.q.avg.energy`. -/

/-! ## Commutation with a constant anti-symmetric matrix

`e.commute.k0` and `e.commute.coarse.grained.k0`. The
manuscript's argument has two halves: the solution set `A(U;a)` does not change
when a constant anti-symmetric matrix `k_0` is added to `a`, whence
`J(U,p,q;a+k_0) = J(U,p,q+k_0 p;a)`; and then the coarse matrices transform as
displayed. This section proves the second half, as a statement about any two
coefficient objects whose response functionals differ by such a shift. The
gauge matrix `G_h` of `e.G` is `Homogenization.Book.Ch02.blockG h`. -/

section GaugeShift

private theorem vecDot_matVecMul_self_of_skew {k0 : Mat d}
    (hk0 : matTranspose k0 = -k0) (p : Vec d) :
    vecDot p (matVecMul k0 p) = 0 := by
  have h := vecDot_matVecMul_transpose p p k0
  rw [hk0, neg_matVecMul, vecDot_neg_right, vecDot_comm (matVecMul k0 p) p] at h
  linarith only [h]

variable (U : Book.Ch02.Domain d) (a b : Book.Ch02.CoeffOn U) (k0 : Mat d)

/-- The response of the shifted field at `p = 0` is unchanged. -/
private theorem responseJ_zero_left_eq_of_shift
    (hJ : ∀ p q : Vec d, Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p)) (r : Vec d) :
    Book.Ch02.responseJ U b 0 r = Book.Ch02.responseJ U a 0 r := by
  rw [hJ 0 r, matVecMul_zero, add_zero]

/-- `s_*^{-1}(U)` is unchanged by a constant anti-symmetric gauge shift of `J`. -/
private theorem sigmaStarInvCoarse_eq_of_shift
    (hJ : ∀ p q : Vec d, Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p)) :
    Book.Ch02.sigmaStarInvCoarse U b = Book.Ch02.sigmaStarInvCoarse U a := by
  funext i j
  simp only [Book.Ch02.sigmaStarInvCoarse, Book.Ch02.sigmaStarInvEntry,
    responseJ_zero_left_eq_of_shift U a b k0 hJ]

/-- `s_*(U)` is unchanged by a constant anti-symmetric gauge shift of `J`. -/
private theorem sigmaStarCoarse_eq_of_shift
    (hJ : ∀ p q : Vec d, Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p)) :
    Book.Ch02.sigmaStarCoarse U b = Book.Ch02.sigmaStarCoarse U a := by
  simp only [Book.Ch02.sigmaStarCoarse, sigmaStarInvCoarse_eq_of_shift U a b k0 hJ]

/-- `k(U)` picks up exactly `k_0` under a constant anti-symmetric gauge shift
of `J`. -/
private theorem kappaCoarse_eq_of_shift (hk0 : matTranspose k0 = -k0)
    (hJ : ∀ p q : Vec d, Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p)) :
    Book.Ch02.kappaCoarse U b = Book.Ch02.kappaCoarse U a + k0 := by
  have hS := sigmaStarInvCoarse_eq_of_shift U a b k0 hJ
  have hsymm := Book.Ch02.sigmaStarInvCoarse_isSymm U a
  have hzero := Book.Ch02.responseJ_zero_q_eq_sigmaStarInvCoarse U a
  have hmixed : ∀ p q : Vec d, Book.Ch02.mixedResponse U b p q =
      vecDot q (matVecMul (Book.Ch02.sigmaStarInvCoarse U a *
        (Book.Ch02.kappaCoarse U a + k0)) p) := by
    intro p q
    have hstar := Book.Ch02.mixedResponse_eq_sigmaStarInv_kappa U a p (q + matVecMul k0 p)
    have hk := Book.Ch02.mixedResponse_eq_sigmaStarInv_kappa U a p (matVecMul k0 p)
    have hpk : vecDot p (matVecMul k0 p) = 0 := vecDot_matVecMul_self_of_skew hk0 p
    have hcross :
        vecDot (matVecMul k0 p)
            (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) q) =
          vecDot q (matVecMul (Book.Ch02.sigmaStarInvCoarse U a) (matVecMul k0 p)) :=
      vecDot_matVecMul_comm_of_isSymm hsymm _ _
    simp only [Book.Ch02.mixedResponse] at hstar hk ⊢
    rw [hJ p q, hJ p 0, zero_add, responseJ_zero_left_eq_of_shift U a b k0 hJ q,
      ← matVecMul_mul, add_matVecMul]
    simp only [hzero] at hstar hk ⊢
    simp only [vecDot_add_right, vecDot_add_left, matVecMul_add] at hstar hk ⊢
    linarith only [hstar, hk, hpk, hcross]
  have hmat : Book.Ch02.sigmaStarInvKappaCoarse U b =
      Book.Ch02.sigmaStarInvCoarse U a * (Book.Ch02.kappaCoarse U a + k0) := by
    funext i j
    have := hmixed (Pi.single j 1) (Pi.single i 1)
    simpa [Book.Ch02.sigmaStarInvKappaCoarse, vecDot_single_left, matVecMul_single]
      using this
  rw [Book.Ch02.kappaCoarse, hmat, sigmaStarCoarse_eq_of_shift U a b k0 hJ,
    Book.Ch02.sigmaStarCoarse]
  exact Matrix.nonsing_inv_mul_cancel_left _ _ (Book.Ch02.isUnit_det_sigmaStarInvCoarse U a)

/-- `s(U)` is unchanged by a constant anti-symmetric gauge shift of `J`. -/
private theorem sigmaCoarse_eq_of_shift (hk0 : matTranspose k0 = -k0)
    (hJ : ∀ p q : Vec d, Book.Ch02.responseJ U b p q =
      Book.Ch02.responseJ U a p (q + matVecMul k0 p)) :
    Book.Ch02.sigmaCoarse U b = Book.Ch02.sigmaCoarse U a := by
  have hS := sigmaStarInvCoarse_eq_of_shift U a b k0 hJ
  have hK := kappaCoarse_eq_of_shift U a b k0 hk0 hJ
  have hcorr : ∀ p : Vec d, Book.Ch02.canonicalSigmaCorrectedResponse U b p =
      Book.Ch02.canonicalSigmaCorrectedResponse U a p := by
    intro p
    have hJa := Book.Ch02.responseJ_eq_coarseMatrices_formula_canonical U a p
      (matVecMul k0 p)
    have hpk : vecDot p (matVecMul k0 p) = 0 := vecDot_matVecMul_self_of_skew hk0 p
    have hT : vecDot p (matVecMul (matTranspose (Book.Ch02.kappaCoarse U a + k0))
          (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
            (matVecMul (Book.Ch02.kappaCoarse U a + k0) p))) =
        vecDot (matVecMul (Book.Ch02.kappaCoarse U a + k0) p)
          (matVecMul (Book.Ch02.sigmaStarInvCoarse U a)
            (matVecMul (Book.Ch02.kappaCoarse U a + k0) p)) :=
      vecDot_matVecMul_transpose _ _ _
    have hsum : matVecMul (Book.Ch02.kappaCoarse U a + k0) p
        = matVecMul k0 p + matVecMul (Book.Ch02.kappaCoarse U a) p := by
      rw [add_matVecMul, add_comm]
    have hb : Book.Ch02.canonicalSigmaCorrectedResponse U b p =
        (1 / 2 : ℝ) * vecDot p (matVecMul (Book.Ch02.sigmaCoarse U a) p) := by
      rw [Book.Ch02.canonicalSigmaCorrectedResponse, hJ p 0, zero_add, hJa, hK, hS,
        hT, hsum, hpk]
      ring
    rw [hb, Book.Ch02.canonicalSigmaCorrectedResponse_eq_sigmaCoarse U a p]
  funext i j
  simp only [Book.Ch02.sigmaCoarse, Book.Ch02.sigmaEntry, hcorr]

/-- `e.commute.k0`: under a constant anti-symmetric gauge
shift of the response functional, `s(U)` is unchanged. -/
theorem sigmaCoarse_eq_of_responseJ_skewShift {U : Book.Ch02.Domain d}
    {a b : Book.Ch02.CoeffOn U} {k0 : Mat d} (hk0 : matTranspose k0 = -k0)
    (hJ : ∀ p q : Vec d,
      Homogenization.ResponseJ (U : Set (Vec d)) p q b.toCoeffField =
        Homogenization.ResponseJ (U : Set (Vec d)) p (q + matVecMul k0 p)
          a.toCoeffField) :
    Homogenization.sigmaCoarse (U : Set (Vec d)) b.toCoeffField =
      Homogenization.sigmaCoarse (U : Set (Vec d)) a.toCoeffField :=
  sigmaCoarse_eq_of_shift U a b k0 hk0 hJ

/-- `e.commute.k0`: under a constant anti-symmetric gauge
shift of the response functional, `k(U)` picks up exactly `k_0`. -/
theorem kappaCoarse_eq_of_responseJ_skewShift {U : Book.Ch02.Domain d}
    {a b : Book.Ch02.CoeffOn U} {k0 : Mat d} (hk0 : matTranspose k0 = -k0)
    (hJ : ∀ p q : Vec d,
      Homogenization.ResponseJ (U : Set (Vec d)) p q b.toCoeffField =
        Homogenization.ResponseJ (U : Set (Vec d)) p (q + matVecMul k0 p)
          a.toCoeffField) :
    Homogenization.kappaCoarse (U : Set (Vec d)) b.toCoeffField =
      Homogenization.kappaCoarse (U : Set (Vec d)) a.toCoeffField + k0 :=
  kappaCoarse_eq_of_shift U a b k0 hk0 hJ

/-- The lower-right block of `e.commute.coarse.grained.k0`:
adding a constant anti-symmetric matrix leaves `s_*^{-1}(U)`, which is that
block of `bfA(U)`, unchanged.

Only the lower-right block is proved here. The full conjugation
`bfA(U; a + k_0) = G_{-k_0}^t bfA(U; a) G_{-k_0}` is
`coarseBlockMatrix_add_const_skew` of
`SuperdiffusionCLT.Section2.CoarseGraining.SkewShift`. -/
theorem coarseBlockMatrix_lowerRight_eq_of_responseJ_skewShift
    {U : Book.Ch02.Domain d} {a b : Book.Ch02.CoeffOn U} {k0 : Mat d}
    (hJ : ∀ p q : Vec d,
      Homogenization.ResponseJ (U : Set (Vec d)) p q b.toCoeffField =
        Homogenization.ResponseJ (U : Set (Vec d)) p (q + matVecMul k0 p)
          a.toCoeffField) :
    (Book.Ch02.coarseBlockMatrix U b).lowerRight =
      (Book.Ch02.coarseBlockMatrix U a).lowerRight :=
  sigmaStarInvCoarse_eq_of_shift U a b k0 hJ

end GaugeShift

end

end SuperdiffusionCLT.Section2.CoarseGraining
