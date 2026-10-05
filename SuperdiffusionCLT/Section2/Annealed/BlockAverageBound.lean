/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch04.Internal.FixedCompetitorEnergyMeasurability.Integrals
public import SuperdiffusionCLT.Section2.Localization.BlockPerturbation

/-!
# The coarse block matrix is bounded by the volume average of the block field

The paper bounds the coarse-grained block matrix by the average of the pointwise block field,
`e.CG.bounds.2`,

`bfA(U) ≤ ⨍_U bfA(x) dx`,

and then majorizes the pointwise block field by a block-diagonal matrix through
Young's inequality, `e.how.to.upbound.A`,

`[[s₁ + kᵗ s₂ k, -kᵗ s₂], [-s₂ k, s₂]] ≤ [[s₁ + 2 kᵗ s₂ k, 0], [0, 2 s₂]]`.

Both steps are proved here. The first one is the statement that the *constant* doubled field `X ≡ P`
is admissible in the variational problem `e.J.P0.Dirichlet`, whose infimum is `½ P · bfA(U) P`; the
value of the functional at the constant competitor is exactly `⨍_U ½ P · bfA(x) P`. No integrability
is needed for the resulting quadratic-form inequality, because both sides are the literal
definitions.

The second step is elementary: after completing the square the difference of
the two quadratic forms is `(k p + q) · s₂ (k p + q)`.

## Main results

* `blockVecDot_coarseBlockMatrix_le_volumeAverage`: `e.CG.bounds.2`, as a
  quadratic-form inequality, with no integrability hypothesis.
* `blockMatLoewnerLE_blockDiag_young`: `e.how.to.upbound.A`.
* `abs_blockMatEntry_le_of_isSymmetricBlockMat`: every entry of a symmetric
  positive semidefinite block matrix is bounded by the mean of the two
  diagonal entries it sits between.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The doubled quadratic form in terms of the four blocks -/

/-- The doubled quadratic form of a block matrix, written out in the four
blocks. -/
theorem blockQuadratic_eq (A : BlockMat d) (p q : Vec d) :
    blockVecDot (p, q) (blockMatVecMul A (p, q)) =
      vecDot p (matVecMul A.upperLeft p) + vecDot p (matVecMul A.upperRight q)
        + vecDot q (matVecMul A.lowerLeft p) + vecDot q (matVecMul A.lowerRight q) := by
  show vecDot p (matVecMul A.upperLeft p + matVecMul A.upperRight q)
      + vecDot q (matVecMul A.lowerLeft p + matVecMul A.lowerRight q) = _
  rw [vecDot_add_right, vecDot_add_right]
  ring

/-- Polarization of the doubled quadratic form along a one-parameter family. -/
theorem blockQuadratic_add_smul (A : BlockMat d) (X Y : BlockVec d) (c : ℝ) :
    blockVecDot (X + c • Y) (blockMatVecMul A (X + c • Y)) =
      blockVecDot X (blockMatVecMul A X) +
        c * (blockVecDot X (blockMatVecMul A Y) + blockVecDot Y (blockMatVecMul A X)) +
        c ^ 2 * blockVecDot Y (blockMatVecMul A Y) := by
  rw [blockMatVecMul_add, blockMatVecMul_smul, blockVecDot_add_left,
    blockVecDot_add_right, blockVecDot_add_right, blockVecDot_smul_left,
    blockVecDot_smul_left, blockVecDot_smul_right, blockVecDot_smul_right]
  ring

/-- Every entry of a symmetric positive semidefinite block matrix is bounded by
the mean of the two diagonal entries it sits between. -/
theorem abs_blockMatEntry_le_of_isSymmetricBlockMat {A : BlockMat d}
    (hsymm : IsSymmetricBlockMat A)
    (hpos : ∀ X : BlockVec d, 0 ≤ blockVecDot X (blockMatVecMul A X))
    (alpha beta : BlockCoord d) :
    |blockMatEntry A alpha beta| ≤
      (blockMatEntry A alpha alpha + blockMatEntry A beta beta) / 2 := by
  have hsym := hsymm alpha beta
  have hplus := hpos (blockBasis alpha + (1 : ℝ) • blockBasis beta)
  have hminus := hpos (blockBasis alpha + (-1 : ℝ) • blockBasis beta)
  rw [blockQuadratic_add_smul, blockBasis_pairing, blockBasis_pairing,
    blockBasis_pairing, blockBasis_pairing] at hplus hminus
  rw [abs_le]
  constructor
  · linarith only [hplus, hsym]
  · linarith only [hminus, hsym]

/-! ## Young's inequality `e.how.to.upbound.A` -/

private theorem zero_matVecMul (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  funext i
  simp [matVecMul]

private theorem vecDot_transpose_mul (k M : Mat d) (p w : Vec d) :
    vecDot p (matVecMul (matTranspose k * M) w) =
      vecDot (matVecMul k p) (matVecMul M w) := by
  rw [← matVecMul_mul, vecDot_matVecMul_transpose]

/-- **`e.how.to.upbound.A`**: for a symmetric positive semidefinite `s₂` and an arbitrary `k`,

`[[s₁ + kᵗ s₂ k, -kᵗ s₂], [-s₂ k, s₂]] ≤ [[s₁ + 2 kᵗ s₂ k, 0], [0, 2 s₂]]`.

The difference of the two quadratic forms at `(p, q)` is
`(k p + q) · s₂ (k p + q)`. -/
theorem blockMatLoewnerLE_blockDiag_young {s₁ s₂ k : Mat d} (hs₂ : s₂.IsSymm)
    (hpos : ∀ x : Vec d, 0 ≤ vecDot x (matVecMul s₂ x)) :
    BlockMatLoewnerLE
      (BlockMat.mk (s₁ + matTranspose k * s₂ * k) (-(matTranspose k * s₂))
        (-(s₂ * k)) s₂)
      (blockDiag (s₁ + (2 : ℝ) • (matTranspose k * s₂ * k)) ((2 : ℝ) • s₂)) := by
  rintro ⟨p, q⟩
  set t : Vec d := matVecMul k p with ht
  have h1 : vecDot p (matVecMul (matTranspose k * s₂ * k) p) =
      vecDot t (matVecMul s₂ t) := by
    rw [Matrix.mul_assoc, vecDot_transpose_mul, ← matVecMul_mul, ← ht]
  have h2 : vecDot p (matVecMul (matTranspose k * s₂) q) =
      vecDot t (matVecMul s₂ q) := by
    rw [vecDot_transpose_mul, ← ht]
  have h3 : vecDot q (matVecMul (s₂ * k) p) = vecDot q (matVecMul s₂ t) := by
    rw [← matVecMul_mul, ← ht]
  have h4 : vecDot t (matVecMul s₂ q) = vecDot q (matVecMul s₂ t) :=
    vecDot_matVecMul_comm_of_isSymm hs₂ t q
  have hsum : vecDot (t + q) (matVecMul s₂ (t + q)) =
      vecDot t (matVecMul s₂ t) + 2 * vecDot q (matVecMul s₂ t) +
        vecDot q (matVecMul s₂ q) := by
    rw [matVecMul_add, vecDot_add_left, vecDot_add_right, vecDot_add_right, h4]
    ring
  have hnn := hpos (t + q)
  rw [hsum] at hnn
  have hLval : blockVecDot (p, q)
      (blockMatVecMul (BlockMat.mk (s₁ + matTranspose k * s₂ * k)
        (-(matTranspose k * s₂)) (-(s₂ * k)) s₂) (p, q)) =
      vecDot p (matVecMul s₁ p) + vecDot t (matVecMul s₂ t)
        - 2 * vecDot q (matVecMul s₂ t) + vecDot q (matVecMul s₂ q) := by
    rw [blockQuadratic_eq]
    show vecDot p (matVecMul (s₁ + matTranspose k * s₂ * k) p) +
        vecDot p (matVecMul (-(matTranspose k * s₂)) q) +
        vecDot q (matVecMul (-(s₂ * k)) p) + vecDot q (matVecMul s₂ q) = _
    rw [add_matVecMul, vecDot_add_right, h1, neg_matVecMul, vecDot_neg_right, h2,
      neg_matVecMul, vecDot_neg_right, h3, h4]
    ring
  have hRval : blockVecDot (p, q)
      (blockMatVecMul (blockDiag (s₁ + (2 : ℝ) • (matTranspose k * s₂ * k))
        ((2 : ℝ) • s₂)) (p, q)) =
      vecDot p (matVecMul s₁ p) + 2 * vecDot t (matVecMul s₂ t)
        + 2 * vecDot q (matVecMul s₂ q) := by
    rw [blockQuadratic_eq]
    show vecDot p (matVecMul (s₁ + (2 : ℝ) • (matTranspose k * s₂ * k)) p) +
        vecDot p (matVecMul (0 : Mat d) q) +
        vecDot q (matVecMul (0 : Mat d) p) + vecDot q (matVecMul ((2 : ℝ) • s₂) q) = _
    rw [add_matVecMul, vecDot_add_right, smul_matVecMul, vecDot_smul_right, h1,
      smul_matVecMul, vecDot_smul_right, zero_matVecMul, zero_matVecMul,
      vecDot_zero_right, vecDot_zero_right]
    ring
  rw [hLval, hRval]
  linarith only [hnn]

/-! ## The constant competitor in the variational problem -/

/-- The zero field is a potential field with zero trace. -/
theorem potentialZeroTraceFieldOn_zero (U : Domain d) :
    Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d)) (fun _ ↦ (0 : Vec d)) :=
  ⟨MeasureTheory.memLp_const _, ⟨0, Filter.Eventually.of_forall fun _ ↦ rfl⟩⟩

/-- The zero field is a solenoidal field with zero normal trace. -/
theorem solenoidalZeroNormalTraceFieldOn_zero (U : Domain d) :
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn (U : Set (Vec d))
      (fun _ ↦ (0 : Vec d)) := by
  refine ⟨MeasureTheory.memLp_const _, fun phi ↦ ?_⟩
  have hpt : ∀ x : Vec d, vecDot (0 : Vec d) (phi.grad x) = 0 :=
    fun _ ↦ vecDot_zero_left _
  simp only [hpt, MeasureTheory.integral_zero]

/-- The constant doubled field `X ≡ P`, the competitor used in `e.CG.bounds.2`. -/
def constDoubledField (P : BlockVec d) : DoubledField d where
  potential := fun _ ↦ P.1
  flux := fun _ ↦ P.2

/-- The constant field is admissible in the variational problem
`e.J.P0.Dirichlet`: its correction field is identically zero. -/
theorem isDoubledMuAdmissible_constDoubledField (U : Domain d) (P : BlockVec d) :
    IsDoubledMuAdmissible U P (constDoubledField P) := by
  have hp : (fun x : Vec d ↦ (constDoubledField P).potential x - P.1) =
      fun _ : Vec d ↦ (0 : Vec d) := funext fun _ ↦ sub_self _
  have hq : (fun x : Vec d ↦ (constDoubledField P).flux x - P.2) =
      fun _ : Vec d ↦ (0 : Vec d) := funext fun _ ↦ sub_self _
  constructor
  · rw [hp]
    exact potentialZeroTraceFieldOn_zero U
  · rw [hq]
    exact solenoidalZeroNormalTraceFieldOn_zero U

/-- The variational quantity of `e.J.P0.Dirichlet` is at most the value of its
functional at the constant competitor. -/
theorem doubledMu_le_volumeAverage (U : Domain d) (a : CoeffOn U) (P : BlockVec d) :
    doubledMu U a P ≤
      volumeAverage (U : Set (Vec d)) (fun x ↦ (1 / 2 : ℝ) *
        blockVecDot P (blockMatVecMul (blockMatrixField a x) P)) := by
  obtain ⟨X, hX⟩ := (doubledMuTheory U a).minimizer_exists P
  have h1 : doubledMu U a P = doubledMuValue U a X :=
    (IsDoubledMuMinimizer.doubledMuValue_eq_doubledMu hX).symm
  have h2 : doubledMuValue U a X ≤ doubledMuValue U a (constDoubledField P) :=
    hX.2 _ (isDoubledMuAdmissible_constDoubledField U P)
  rw [h1]
  exact h2

/-- **`e.CG.bounds.2`, last inequality**, as a quadratic-form statement:
`P · bfA(U) P ≤ ⨍_U P · bfA(x) P dx` for every block vector `P`. No
integrability hypothesis is needed: both sides are the definitions. -/
theorem blockVecDot_coarseBlockMatrix_le_volumeAverage (U : Domain d)
    (a : CoeffOn U) (P : BlockVec d) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) ≤
      volumeAverage (U : Set (Vec d))
        (fun x ↦ blockVecDot P (blockMatVecMul (blockMatrixField a x) P)) := by
  have hq := (doubledMuTheory U a).mu_quadratic P
  have hle := doubledMu_le_volumeAverage U a P
  rw [hq] at hle
  have hhalf : volumeAverage (U : Set (Vec d)) (fun x ↦ (1 / 2 : ℝ) *
      blockVecDot P (blockMatVecMul (blockMatrixField a x) P)) =
      (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
        (fun x ↦ blockVecDot P (blockMatVecMul (blockMatrixField a x) P)) := by
    unfold volumeAverage
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [hhalf] at hle
  linarith only [hle]

/-! ## The volume average of a block matrix field -/

/-- The bilinear pairing of an entrywise Bochner integral of matrices is the
integral of the pairing. -/
theorem vecDot_matVecMul_integralMat {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {M : Omega → Mat d}
    (hM : ∀ i j, Integrable (fun w ↦ M w i j) mu) (x y : Vec d) :
    vecDot x (matVecMul (fun i j ↦ ∫ w, M w i j ∂mu) y) =
      ∫ w, vecDot x (matVecMul (M w) y) ∂mu := by
  calc
    vecDot x (matVecMul (fun i j ↦ ∫ w, M w i j ∂mu) y)
        = ∑ i : Fin d, x i * ∑ j : Fin d, (∫ w, M w i j ∂mu) * y j := rfl
    _ = ∑ i : Fin d, x i * ∑ j : Fin d, ∫ w, M w i j * y j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          refine congrArg (fun t ↦ x i * t) (Finset.sum_congr rfl fun j _ ↦ ?_)
          rw [integral_mul_const]
    _ = ∑ i : Fin d, x i * ∫ w, ∑ j : Fin d, M w i j * y j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          refine congrArg (fun t ↦ x i * t) ?_
          rw [integral_finsetSum _ fun j _ ↦ (hM i j).mul_const (y j)]
    _ = ∑ i : Fin d, ∫ w, x i * ∑ j : Fin d, M w i j * y j ∂mu := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [integral_const_mul]
    _ = ∫ w, ∑ i : Fin d, x i * ∑ j : Fin d, M w i j * y j ∂mu := by
          refine (integral_finsetSum _ fun i _ ↦ ?_).symm
          exact (integrable_finsetSum _ fun j _ ↦ (hM i j).mul_const (y j)).const_mul (x i)
    _ = ∫ w, vecDot x (matVecMul (M w) y) ∂mu := rfl

/-! ## Integrability of the pointwise block field -/

/-- The two entry functions of a block matrix agree. -/
theorem toFullBlockMat_eq_blockMatEntry (A : BlockMat d) (alpha beta : BlockCoord d) :
    toFullBlockMat A alpha beta = blockMatEntry A alpha beta := by
  cases alpha <;> cases beta <;> rfl

end

end SuperdiffusionCLT.Section2.Annealed
