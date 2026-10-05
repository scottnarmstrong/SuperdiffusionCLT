/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.Term2ScaleComparison
public import SuperdiffusionCLT.Frozen.Section2.LocalizationAverage

/-!
# `p.mixing.P.three.prime#term1-bound`

In the proof of Proposition `p.mixing.P.three.prime`: the localization-term average, from
`l.localization.average` (`Frozen/Section2/LocalizationAverage.lean`),
"testing with `P = bfAhom_ℓ^{-1/2}(cu_n) Q`, taking the supremum over a finite
net of `|Q|=1`, and using `e.Enaught.vs.Ahom.L.crude` together with
`e.good.gaps`". The square-root-free reading of the resulting matrix-norm bound is the
relative bilinear bound `2 p · H q ≤ t (p · Aell p + q · Aell q)`. This file proves the
polarization step turning `l.localization.average`'s per-vector quadratic-form
bound into the wanted cross-term bound. The final normalization step (the "crude"
ellipticity-relative conversion) is carried out separately, in `Term1PolarizedBound.lean`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed

variable {d : ℕ}

/-! ## Symmetry of the localization-term matrix -/

/-- **`coarseBlockMatrix U a` is symmetric**, for every set `U` and coefficient
field `a`, from the diagonal-block symmetry and off-diagonal transpose
relation in `Section2/Annealed/Blocks.lean`. No ellipticity or
well-posedness hypothesis is needed: the polarization identity defining
`coarseBlockMatrix` is symmetric by construction. -/
theorem mixTerms_isSymmetricBlockMat_coarseBlockMatrix (U : Set (Vec d))
    (a : Homogenization.CoeffField d) :
    IsSymmetricBlockMat (Homogenization.coarseBlockMatrix U a) := by
  intro α β
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      have h := (isSymm_coarseBlockMatrix_upperLeft U a).apply i j
      simpa [blockMatEntry] using h.symm
    | inr j =>
      have h := congrArg (fun N : Mat d => N i j) (coarseBlockMatrix_upperRight_eq_transpose_lowerLeft U a)
      simpa [blockMatEntry, matTranspose] using h
  | inr i =>
    cases β with
    | inl j =>
      have h := congrArg (fun N : Mat d => N j i) (coarseBlockMatrix_upperRight_eq_transpose_lowerLeft U a)
      simpa [blockMatEntry, matTranspose] using h.symm
    | inr j =>
      have h := (isSymm_coarseBlockMatrix_lowerRight U a).apply i j
      simpa [blockMatEntry] using h.symm

/-- The gauge conjugate `G_{-h}^t (blockDiag (s•1) (t•1)) G_{-h}` is
symmetric, for every `h : Mat d` and scalars `s t`, by direct inspection of
`mixBelow_gaugeBlockConjugation`'s explicit output. -/
theorem mixTerms_isSymmetricBlockMat_gaugeConjugate_blockDiag (h : Mat d) (s t : ℝ) :
    IsSymmetricBlockMat
      (blockMatMul (blockMatTranspose (blockG (-h)))
        (blockMatMul (blockDiag (s • (1 : Mat d)) (t • (1 : Mat d))) (blockG (-h)))) := by
  rw [mixBelow_gaugeBlockConjugation]
  intro α β
  have hone : ∀ i j : Fin d, (1 : Mat d) i j = (1 : Mat d) j i := by
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      show (s • (1 : Mat d) + t • (matTranspose h * h)) i j =
        (s • (1 : Mat d) + t • (matTranspose h * h)) j i
      have hUL : (matTranspose h * h).IsSymm := by
        ext p q
        simp [matTranspose, Matrix.transpose_apply, Matrix.mul_apply, mul_comm]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hone i j, hUL.apply i j]
    | inr j =>
      show (-(t • matTranspose h)) i j = (-(t • h)) j i
      simp [matTranspose, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply]
  | inr i =>
    cases β with
    | inl j =>
      show (-(t • h)) i j = (-(t • matTranspose h)) j i
      simp [matTranspose, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply]
    | inr j =>
      show (t • (1 : Mat d)) i j = (t • (1 : Mat d)) j i
      simp only [Matrix.smul_apply, smul_eq_mul, hone i j]

/-- **Bilinear symmetry.** If `H` is a symmetric block matrix, its induced
bilinear form is symmetric in its two vector arguments. -/
theorem mixTerms_blockVecDot_comm_of_symm {H : BlockMat d} (hH : IsSymmetricBlockMat H)
    (X Y : BlockVec d) :
    blockVecDot X (blockMatVecMul H Y) = blockVecDot Y (blockMatVecMul H X) := by
  obtain ⟨x1, x2⟩ := X
  obtain ⟨y1, y2⟩ := Y
  have hUL : matTranspose H.upperLeft = H.upperLeft := by
    ext i j
    have h := hH (Sum.inl j) (Sum.inl i)
    simpa [blockMatEntry, matTranspose] using h
  have hLR : matTranspose H.lowerRight = H.lowerRight := by
    ext i j
    have h := hH (Sum.inr j) (Sum.inr i)
    simpa [blockMatEntry, matTranspose] using h
  have hUR : H.upperRight = matTranspose H.lowerLeft := by
    ext i j
    have h := hH (Sum.inl i) (Sum.inr j)
    simpa [blockMatEntry, matTranspose] using h
  have e1 : vecDot x1 (matVecMul H.upperLeft y1) = vecDot y1 (matVecMul H.upperLeft x1) := by
    calc vecDot x1 (matVecMul H.upperLeft y1)
        = vecDot x1 (matVecMul (matTranspose H.upperLeft) y1) := by rw [hUL]
      _ = vecDot (matVecMul H.upperLeft x1) y1 := vecDot_matVecMul_transpose x1 y1 H.upperLeft
      _ = vecDot y1 (matVecMul H.upperLeft x1) := vecDot_comm _ _
  have e2 : vecDot x2 (matVecMul H.lowerRight y2) = vecDot y2 (matVecMul H.lowerRight x2) := by
    calc vecDot x2 (matVecMul H.lowerRight y2)
        = vecDot x2 (matVecMul (matTranspose H.lowerRight) y2) := by rw [hLR]
      _ = vecDot (matVecMul H.lowerRight x2) y2 := vecDot_matVecMul_transpose x2 y2 H.lowerRight
      _ = vecDot y2 (matVecMul H.lowerRight x2) := vecDot_comm _ _
  have e3 : vecDot x1 (matVecMul H.upperRight y2) = vecDot y2 (matVecMul H.lowerLeft x1) := by
    calc vecDot x1 (matVecMul H.upperRight y2)
        = vecDot x1 (matVecMul (matTranspose H.lowerLeft) y2) := by rw [hUR]
      _ = vecDot (matVecMul H.lowerLeft x1) y2 := vecDot_matVecMul_transpose x1 y2 H.lowerLeft
      _ = vecDot y2 (matVecMul H.lowerLeft x1) := vecDot_comm _ _
  have hLL : H.lowerLeft = matTranspose H.upperRight := by
    rw [hUR]
    unfold matTranspose
    rw [Matrix.transpose_transpose]
  have e4 : vecDot x2 (matVecMul H.lowerLeft y1) = vecDot y1 (matVecMul H.upperRight x2) := by
    calc vecDot x2 (matVecMul H.lowerLeft y1)
        = vecDot x2 (matVecMul (matTranspose H.upperRight) y1) := by rw [hLL]
      _ = vecDot (matVecMul H.upperRight x2) y1 := vecDot_matVecMul_transpose x2 y1 H.upperRight
      _ = vecDot y1 (matVecMul H.upperRight x2) := vecDot_comm _ _
  show vecDot x1 (matVecMul H.upperLeft y1 + matVecMul H.upperRight y2) +
      vecDot x2 (matVecMul H.lowerLeft y1 + matVecMul H.lowerRight y2) =
    vecDot y1 (matVecMul H.upperLeft x1 + matVecMul H.upperRight x2) +
      vecDot y2 (matVecMul H.lowerLeft x1 + matVecMul H.lowerRight x2)
  rw [vecDot_add_right, vecDot_add_right, vecDot_add_right, vecDot_add_right, e1, e2, e3, e4]
  ring

/-! ## Polarization -/

/-- **Polarization of the averaged bilinear form.** For a `Finset s`, a
`z`-dependent symmetric block matrix `H z`, and a fixed test pair `(p, q)`,
twice the averaged cross term `p · (H z) q` equals the averaged quadratic
forms at `p + q`, `p`, and `q`. -/
theorem mixTerms_polarization_avg {α : Type*} (s : Finset α) (H : α → BlockMat d)
    (hSymm : ∀ z ∈ s, IsSymmetricBlockMat (H z)) (p q : BlockVec d) :
    2 * ((s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) q)) =
      (s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot (p + q) (blockMatVecMul (H z) (p + q)) -
        (s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) p) -
        (s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot q (blockMatVecMul (H z) q) := by
  have hpt : ∀ z ∈ s,
      2 * blockVecDot p (blockMatVecMul (H z) q) =
        blockVecDot (p + q) (blockMatVecMul (H z) (p + q)) - blockVecDot p (blockMatVecMul (H z) p) -
          blockVecDot q (blockMatVecMul (H z) q) := by
    intro z hz
    have hcomm : blockVecDot q (blockMatVecMul (H z) p) = blockVecDot p (blockMatVecMul (H z) q) :=
      mixTerms_blockVecDot_comm_of_symm (hSymm z hz) q p
    have hexp : blockVecDot (p + q) (blockMatVecMul (H z) (p + q)) =
        blockVecDot p (blockMatVecMul (H z) p) + blockVecDot p (blockMatVecMul (H z) q) +
          (blockVecDot q (blockMatVecMul (H z) p) + blockVecDot q (blockMatVecMul (H z) q)) := by
      rw [blockMatVecMul_add, blockVecDot_add_right, blockVecDot_add_left, blockVecDot_add_left]
      ring
    rw [hexp, hcomm]
    ring
  have hsum : ∑ z ∈ s, 2 * blockVecDot p (blockMatVecMul (H z) q) =
      ∑ z ∈ s, blockVecDot (p + q) (blockMatVecMul (H z) (p + q)) -
        ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) p) -
        ∑ z ∈ s, blockVecDot q (blockMatVecMul (H z) q) := by
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum] at hsum
  rw [show (2 : ℝ) * ((s.card : ℝ)⁻¹ * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) q)) =
      (s.card : ℝ)⁻¹ * (2 * ∑ z ∈ s, blockVecDot p (blockMatVecMul (H z) q)) by ring, hsum]
  ring

end SuperdiffusionCLT.Section4.Mixing
