/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Prereq.HarmonicApprox
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import Homogenization.Book.Ch02.Theorems.MatrixPositivity
public import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities

/-!
# The coarse-grained matrices of a cube are close to a scalar matrix

Deterministic cube form of the `sstar.close` bullet of `l.sharp.scale.inputs`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Matrix Homogenization

section Algebra

variable {d : ℕ}

/-- Symmetric matrices: the bilinear form is symmetric. -/
theorem l8_dot_mulVec_comm {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm) (x y : Fin d → ℝ) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA.eq, dotProduct_comm]

/-- Cauchy--Schwarz for a positive semidefinite symmetric form. -/
theorem l8_cs_of_psd {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm)
    (hpsd : ∀ z : Fin d → ℝ, 0 ≤ z ⬝ᵥ A *ᵥ z) (x y : Fin d → ℝ) :
    (x ⬝ᵥ A *ᵥ y) ^ 2 ≤ (x ⬝ᵥ A *ᵥ x) * (y ⬝ᵥ A *ᵥ y) := by
  have hq : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ A *ᵥ y) * (t * t) + (2 * (x ⬝ᵥ A *ᵥ y)) * t + (x ⬝ᵥ A *ᵥ x) := by
    intro t
    have h := hpsd (x + t • y)
    have e : (x + t • y) ⬝ᵥ A *ᵥ (x + t • y) =
        (y ⬝ᵥ A *ᵥ y) * (t * t) + (2 * (x ⬝ᵥ A *ᵥ y)) * t + (x ⬝ᵥ A *ᵥ x) := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, add_dotProduct,
        dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, l8_dot_mulVec_comm hA y x]
      ring
    rw [e] at h
    exact h
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith only [this]


/-- `w = (Y - 1) v` has `w · Yi w = v · Y v + v · Yi v - 2 v · v` when `Yi` inverts `Y`. -/
theorem l8_form_identity {Y Yi : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm)
    (hYYi : Y * Yi = 1) (v : Fin d → ℝ) :
    ((Y - 1) *ᵥ v) ⬝ᵥ Yi *ᵥ ((Y - 1) *ᵥ v) =
      v ⬝ᵥ Y *ᵥ v + v ⬝ᵥ Yi *ᵥ v - 2 * (v ⬝ᵥ v) := by
  have hYiY : Yi * Y = 1 := mul_eq_one_comm.mp hYYi
  have h1 : Yi *ᵥ (Y *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hYiY, Matrix.one_mulVec]
  have h2 : Y *ᵥ (Yi *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hYYi, Matrix.one_mulVec]
  have h3 : (Y *ᵥ v) ⬝ᵥ Yi *ᵥ v = v ⬝ᵥ v := by
    rw [dotProduct_comm, l8_dot_mulVec_comm hY, h2]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, h1, dotProduct_sub, sub_dotProduct,
    sub_dotProduct, h3, dotProduct_comm v (Y *ᵥ v), dotProduct_comm v (Yi *ᵥ v)]
  ring

theorem l8_aux {Y Yi : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm) (hYYi : Y * Yi = 1)
    (w : Fin d → ℝ) :
    (Y *ᵥ w) ⬝ᵥ Yi *ᵥ w = w ⬝ᵥ w ∧ (Y *ᵥ w) ⬝ᵥ Yi *ᵥ (Y *ᵥ w) = w ⬝ᵥ Y *ᵥ w := by
  have hYiY : Yi * Y = 1 := mul_eq_one_comm.mp hYYi
  constructor
  · rw [dotProduct_comm, l8_dot_mulVec_comm hY, Matrix.mulVec_mulVec, hYYi, Matrix.one_mulVec]
  · rw [Matrix.mulVec_mulVec w Yi Y, hYiY, Matrix.one_mulVec, dotProduct_comm, l8_dot_mulVec_comm hY]

/-- Quadratic control of `Y - 1` from `Y + Y⁻¹ - 2 ≤ 2c`. -/
theorem l8_sq_bound {Y Yi : Matrix (Fin d) (Fin d) ℝ} (hY : Y.IsSymm) (hYi : Yi.IsSymm)
    (hYYi : Y * Yi = 1) (hpsd : ∀ z : Fin d → ℝ, 0 ≤ z ⬝ᵥ Yi *ᵥ z) {c B : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ B)
    (hyp : ∀ u : Fin d → ℝ,
      u ⬝ᵥ Y *ᵥ u + u ⬝ᵥ Yi *ᵥ u - 2 * (u ⬝ᵥ u) ≤ 2 * c * (u ⬝ᵥ u))
    (v : Fin d → ℝ) :
    ((Y - 1) *ᵥ v) ⬝ᵥ ((Y - 1) *ᵥ v) ≤ (4 + 4 * B) * c * (v ⬝ᵥ v) := by
  set w : Fin d → ℝ := (Y - 1) *ᵥ v with hw
  have hi : w ⬝ᵥ Yi *ᵥ w = v ⬝ᵥ Y *ᵥ v + v ⬝ᵥ Yi *ᵥ v - 2 * (v ⬝ᵥ v) :=
    l8_form_identity hY hYYi v
  have hwYi : w ⬝ᵥ Yi *ᵥ w ≤ 2 * c * (v ⬝ᵥ v) := hi ▸ hyp v
  have hwYi0 : 0 ≤ w ⬝ᵥ Yi *ᵥ w := hpsd w
  have hww : 0 ≤ w ⬝ᵥ w := by
    simpa [dotProduct, sq] using Finset.sum_nonneg (fun i _ => mul_self_nonneg (w i))
  have hwY : w ⬝ᵥ Y *ᵥ w ≤ (2 + 2 * B) * (w ⬝ᵥ w) := by
    have h := hyp w
    nlinarith only [h, hwYi0, hww, hc1, mul_nonneg (sub_nonneg.2 hc1) hww]
  -- Cauchy--Schwarz for the form Yi with x = Y w, y = w
  have hcs := l8_cs_of_psd hYi hpsd (Y *ᵥ w) w
  obtain ⟨e1, e2⟩ := l8_aux hY hYYi w
  rw [e1, e2] at hcs
  have hprod : (w ⬝ᵥ w) ^ 2 ≤ ((2 + 2 * B) * (w ⬝ᵥ w)) * (2 * c * (v ⬝ᵥ v)) := by
    refine hcs.trans ?_
    exact mul_le_mul hwY hwYi hwYi0 (by nlinarith only [hww, hc0, hc1])
  rcases hww.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : 0 ≤ v ⬝ᵥ v := by
      simpa [dotProduct, sq] using Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))
    have hB0 : 0 ≤ B := hc0.trans hc1
    have := mul_nonneg (mul_nonneg (by linarith only [hB0] : (0 : ℝ) ≤ 4 + 4 * B) hc0) this
    linarith only [this]
  · have : w ⬝ᵥ w ≤ (2 + 2 * B) * (2 * c * (v ⬝ᵥ v)) := by
      refine le_of_mul_le_mul_left ?_ hpos
      nlinarith only [hprod]
    linarith only [this]

end Algebra


noncomputable section

variable {d : ℕ} [NeZero d]

theorem l8_probe_le (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ}
    (hσ : 0 < σ) (u : Vec d) (hu : vecDot u u = 1) :
    Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
        ((Real.sqrt σ)⁻¹ • u, 0) (Real.sqrt σ • u, 0) ≤
      Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hprobe : blockMatVecMul (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) σ))
      ((Real.sqrt σ)⁻¹ • u, 0) = (Real.sqrt σ • u, 0) := by
    rw [Book.Ch02.constantBlockMatrix_scalarMatrix hσ]
    ext k
    · simp [blockMatVecMul, matVecMul_zero, matVecMul_scalarMatrix]
      field_simp
      rw [Real.sq_sqrt hσ.le]
    · simp [blockMatVecMul, matVecMul_zero, matVecMul_scalarMatrix, matVecMul]
  have hquad : blockVecDot ((Real.sqrt σ)⁻¹ • u, 0)
      (blockMatVecMul (Book.Ch02.constantBlockMatrix (scalarMatrix (d := d) σ))
        ((Real.sqrt σ)⁻¹ • u, 0)) = 1 := by
    rw [hprobe, blockVecDot, vecDot_smul_left, vecDot_smul_right, hu]
    simp [vecDot]
    field_simp
  have hmem0 := Book.Ch02.normalizedBlockResponseValueSet_mem_of_constantBlockQuadratic_eq_one
    (Q := Q) (a := F) (a0 := scalarMatrix (d := d) σ)
    (lam := σ) (Lam := σ) (isEllipticMatrix_scalarMatrix hσ) _ hquad
  rw [hprobe] at hmem0
  unfold Book.Ch02.normalizedBlockResponseMax
  exact le_csSup
    (Book.Ch02.normalizedBlockResponseValueSet_bddAbove_of_mem_descendantsAtScale
      (a := F) (Q := Q) (R := Q) (k := Q.scale) (scalarMatrix (d := d) σ)
      (by simp [descendantsAtScale_self])) hmem0

omit [NeZero d] in
theorem l8_J_formula (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ}
    (hσ : 0 < σ) (u : Vec d) :
    2 * Book.Ch02.doubledResponseJ (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
        ((Real.sqrt σ)⁻¹ • u, 0) (Real.sqrt σ • u, 0) =
      σ⁻¹ * vecDot u (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) +
        σ * vecDot u (matVecMul
          (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) -
        2 * vecDot u u := by
  have hs : 0 < Real.sqrt σ := Real.sqrt_pos.2 hσ
  have hth := Book.Ch02.blockCoarseMatrixTheory (Book.Ch02.cubeDomain Q) (F.coeffOn Q)
  rw [hth.doubled_response_splitting]
  have hstar : Book.Ch02.coarseStarredBlockMatrixInv (Book.Ch02.cubeDomain Q) (F.coeffOn Q) =
      blockReflect (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) :=
    hth.starred_inverse_formula
  rw [hstar]
  have hc2 : Real.sqrt σ * Real.sqrt σ = σ := Real.mul_self_sqrt hσ.le
  have hci : (Real.sqrt σ)⁻¹ * (Real.sqrt σ)⁻¹ = σ⁻¹ := by
    rw [← mul_inv, hc2]
  have hcc : (Real.sqrt σ)⁻¹ * Real.sqrt σ = 1 := inv_mul_cancel₀ hs.ne'
  simp only [blockVecDot, blockMatVecMul, blockReflect, matVecMul_zero, add_zero, vecDot_zero_left,
    vecDot_zero_right, matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
  have hUL : (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).upperLeft =
      Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q) := rfl
  have hLR : (Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) (F.coeffOn Q)).lowerRight =
      Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q) := rfl
  rw [hUL, hLR]
  generalize vecDot u (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) = x
  generalize vecDot u (matVecMul
    (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) = y
  generalize vecDot u u = r
  have e1 : (Real.sqrt σ)⁻¹ * ((Real.sqrt σ)⁻¹ * x) = σ⁻¹ * x := by rw [← mul_assoc, hci]
  have e2 : Real.sqrt σ * (Real.sqrt σ * y) = σ * y := by rw [← mul_assoc, hc2]
  have e3 : Real.sqrt σ * ((Real.sqrt σ)⁻¹ * r) = r := by
    rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [e1, e2, e3]
  ring

theorem l8_E1 (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ}
    (hσ : 0 < σ) (u : Vec d) :
    σ⁻¹ * vecDot u (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) +
        σ * vecDot u (matVecMul
          (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) -
        2 * vecDot u u ≤
      2 * Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) * vecDot u u := by
  have hr0 : 0 ≤ vecDot u u := by
    unfold vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  rcases hr0.eq_or_lt with h0 | hpos
  · have hu : u = 0 := by
      funext i
      have h1 : ∑ j, u j * u j = 0 := h0.symm
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (u j))).1 h1 i
        (Finset.mem_univ i)
      simpa using this
    subst hu
    simp [vecDot, matVecMul]
  · set r := vecDot u u with hr
    have hsr : 0 < Real.sqrt r := Real.sqrt_pos.2 hpos
    have hu' : vecDot ((Real.sqrt r)⁻¹ • u) ((Real.sqrt r)⁻¹ • u) = 1 := by
      rw [vecDot_smul_left, vecDot_smul_right, ← hr, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt
        hpos.le, inv_mul_cancel₀ hpos.ne']
    have h1 := l8_probe_le Q F hσ _ hu'
    have h2 := l8_J_formula Q F hσ ((Real.sqrt r)⁻¹ • u)
    simp only [matVecMul_smul, vecDot_smul_left, vecDot_smul_right, hu'] at h2
    have hrr : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hpos.le]
    generalize vecDot u (matVecMul (Book.Ch02.bCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) = x
      at h2 ⊢
    generalize vecDot u (matVecMul
      (Book.Ch02.sigmaStarInvCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q)) u) = y at h2 ⊢
    generalize Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) = M at h1 ⊢
    have e1 : σ⁻¹ * ((√r)⁻¹ * ((√r)⁻¹ * x)) = r⁻¹ * (σ⁻¹ * x) := by
      rw [← mul_assoc (√r)⁻¹, hrr]; ring
    have e2 : σ * ((√r)⁻¹ * ((√r)⁻¹ * y)) = r⁻¹ * (σ * y) := by
      rw [← mul_assoc (√r)⁻¹, hrr]; ring
    have h3 : r⁻¹ * (σ⁻¹ * x + σ * y) - 2 ≤ 2 * M := by
      linarith only [h1, h2, e1, e2]
    have h4 := mul_le_mul_of_nonneg_left h3 hpos.le
    have h5 : r * (r⁻¹ * (σ⁻¹ * x + σ * y) - 2) = (σ⁻¹ * x + σ * y) - 2 * r := by
      field_simp
    linarith only [h4, h5]

omit [NeZero d] in
theorem l8_matNorm_le {A : Mat d} {K : ℝ}
    (h : ∀ v : Fin d → ℝ, (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ K * (v ⬝ᵥ v)) :
    matNorm A ≤ Real.sqrt ((d : ℝ) * K) := by
  unfold matNorm matNormSq
  apply Real.sqrt_le_sqrt
  have h1 : ∀ j, ∑ i, A i j ^ 2 ≤ K := by
    intro j
    have := h (Pi.single j 1)
    have h1' : (Pi.single j (1 : ℝ) : Fin d → ℝ) ⬝ᵥ (Pi.single j 1) = 1 := by simp
    rw [h1', mul_one] at this
    simpa [Matrix.mulVec_single, dotProduct, sq] using this
  calc ∑ i, ∑ j, A i j ^ 2 = ∑ j, ∑ i, A i j ^ 2 := Finset.sum_comm
    _ ≤ ∑ _j : Fin d, K := Finset.sum_le_sum fun j _ => h1 j
    _ = d * K := by simp

open scoped Matrix.Norms.Frobenius in
omit [NeZero d] in
theorem l8_matNorm_add_le (A B : Mat d) : matNorm (A + B) ≤ matNorm A + matNorm B := by
  rw [matNorm_eq_norm, matNorm_eq_norm, matNorm_eq_norm]
  exact norm_add_le A B

omit [NeZero d] in
theorem l8_form_eq (A : Mat d) (u : Vec d) : vecDot u (matVecMul A u) = u ⬝ᵥ A *ᵥ u := rfl

/-- The Chapter 2 coarse matrices of a cube, normalised by `σ`, in terms of the top-scale
normalised response. -/
theorem l8_ch02_close (Q : TriadicCube d) (F : Book.Ch02.TriadicCoeffFamily d) {σ : ℝ}
    (hσ : 0 < σ)
    {B : ℝ} (hM1 : Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) ≤ B) :
    matNorm (σ⁻¹ • Book.Ch02.sigmaStarCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q) - 1) ≤
        Real.sqrt ((d : ℝ) * ((4 + 4 * B) * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ))) ∧
      matNorm (σ⁻¹ • Book.Ch02.sigmaCoarse (Book.Ch02.cubeDomain Q) (F.coeffOn Q) - 1) ≤
        Real.sqrt ((d : ℝ) * ((4 + 4 * B) * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ))) +
        2 * (Fintype.card (Fin d) : ℝ) * (2 * Book.Ch02.normalizedBlockResponseMax Q F
          (scalarMatrix (d := d) σ)) := by
  set U := Book.Ch02.cubeDomain Q with hU
  set A := F.coeffOn Q with hA
  set M := Book.Ch02.normalizedBlockResponseMax Q F (scalarMatrix (d := d) σ) with hM
  have hM0 : 0 ≤ M := Book.Ch02.normalizedBlockResponseMax_nonneg Q F _
  set s := Book.Ch02.sigmaCoarse U A with hs
  set ss := Book.Ch02.sigmaStarCoarse U A with hss
  set S := Book.Ch02.sigmaStarInvCoarse U A with hS
  set b := Book.Ch02.bCoarse U A with hb
  have hSsymm : S.IsSymm := Book.Ch02.sigmaStarInvCoarse_isSymm U A
  have hssSymm : ss.IsSymm := Book.Ch02.sigmaStarCoarse_isSymm U A
  have hdet := Book.Ch02.isUnit_det_sigmaStarInvCoarse U A
  have hssS : ss * S = 1 := Book.Ch02.sigmaStarCoarse_mul_sigmaStarInvCoarse hdet
  have hYsymm : (σ⁻¹ • ss).IsSymm := hssSymm.smul σ⁻¹
  have hYisymm : (σ • S).IsSymm := hSsymm.smul σ
  have hYYi : (σ⁻¹ • ss) * (σ • S) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hssS, inv_mul_cancel₀ hσ.ne', one_smul]
  have hSpsd : ∀ z : Fin d → ℝ, 0 ≤ z ⬝ᵥ S *ᵥ z := fun z => by
    simpa using (Book.Ch02.sigmaStarInvCoarse_posDef U A).posSemidef.dotProduct_mulVec_nonneg z
  have hYipsd : ∀ z : Fin d → ℝ, 0 ≤ z ⬝ᵥ (σ • S) *ᵥ z := fun z => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hσ.le (hSpsd z)
  have hle1 : ∀ u : Vec d, u ⬝ᵥ ss *ᵥ u ≤ u ⬝ᵥ s *ᵥ u := fun u => by
    have := Book.Ch02.sigmaStarCoarse_le_sigmaCoarse U A u
    change (1 / 2 : ℝ) * (u ⬝ᵥ ss *ᵥ u) ≤ (1 / 2 : ℝ) * (u ⬝ᵥ s *ᵥ u) at this
    linarith only [this]
  have hle2 : ∀ u : Vec d, u ⬝ᵥ s *ᵥ u ≤ u ⬝ᵥ b *ᵥ u := fun u => by
    have := Book.Ch02.sigmaCoarse_le_bCoarse U A u
    change (1 / 2 : ℝ) * (u ⬝ᵥ s *ᵥ u) ≤ (1 / 2 : ℝ) * (u ⬝ᵥ b *ᵥ u) at this
    linarith only [this]
  have hE1 : ∀ u : Vec d, σ⁻¹ * (u ⬝ᵥ b *ᵥ u) + σ * (u ⬝ᵥ S *ᵥ u) - 2 * (u ⬝ᵥ u) ≤
      2 * M * (u ⬝ᵥ u) := fun u => l8_E1 Q F hσ u
  have hY : ∀ u : Vec d, u ⬝ᵥ (σ⁻¹ • ss) *ᵥ u = σ⁻¹ * (u ⬝ᵥ ss *ᵥ u) := fun u => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hYi : ∀ u : Vec d, u ⬝ᵥ (σ • S) *ᵥ u = σ * (u ⬝ᵥ S *ᵥ u) := fun u => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hyp : ∀ u : Vec d, u ⬝ᵥ (σ⁻¹ • ss) *ᵥ u + u ⬝ᵥ (σ • S) *ᵥ u - 2 * (u ⬝ᵥ u) ≤
      2 * M * (u ⬝ᵥ u) := fun u => by
    rw [hY, hYi]
    have h1 := hle1 u
    have h2 := hle2 u
    have h3 := hE1 u
    have h4 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    nlinarith only [h1, h2, h3, h4]
  have hsq := fun v => l8_sq_bound hYsymm hYisymm hYYi hYipsd hM0 hM1 hyp v
  have hnorm1 : matNorm (σ⁻¹ • ss - 1) ≤ Real.sqrt ((d : ℝ) * ((4 + 4 * B) * M)) := by
    refine l8_matNorm_le fun v => ?_
    have := hsq v
    simpa [mul_assoc] using this
  refine ⟨hnorm1, ?_⟩
  have hsSymm : s.IsSymm := Book.Ch02.sigmaCoarse_isSymm U A
  have hD : (σ⁻¹ • s - σ⁻¹ • ss).IsSymm := (hsSymm.smul σ⁻¹).sub (hssSymm.smul σ⁻¹)
  have hform : ∀ u : Vec d, 2 * (u ⬝ᵥ u) ≤
      u ⬝ᵥ (σ⁻¹ • ss) *ᵥ u + u ⬝ᵥ (σ • S) *ᵥ u := fun u => by
    have h1 := l8_form_identity hYsymm hYYi u
    have h2 := hYipsd ((σ⁻¹ • ss - 1) *ᵥ u)
    linarith only [h1, h2]
  have hDpos : (σ⁻¹ • s - σ⁻¹ • ss).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (by simpa using hD) fun x => ?_
    rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have := hle1 x
    have h4 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    nlinarith only [this, h4]
  have hnormD : matNorm (σ⁻¹ • s - σ⁻¹ • ss) ≤
      2 * (Fintype.card (Fin d) : ℝ) * (2 * M) := by
    refine matNorm_le_two_mul_card_mul_of_posSemidef_of_quadratic_le hDpos
      (by positivity) fun x => ?_
    rw [l8_form_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h2 := hle2 x
    have h3 := hE1 x
    have h5 := hform x
    rw [hY, hYi] at h5
    have hn : vecNormSq x = x ⬝ᵥ x := rfl
    rw [hn]
    have h4 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
    nlinarith only [h2, h3, h5, h4]
  have hsplit : σ⁻¹ • s - 1 = (σ⁻¹ • s - σ⁻¹ • ss) + (σ⁻¹ • ss - 1) := by abel
  rw [hsplit]
  refine (l8_matNorm_add_le _ _).trans ?_
  linarith only [hnormD, hnorm1]

end


end SuperdiffusionCLT.Section6
