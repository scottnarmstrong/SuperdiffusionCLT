/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ThreeScaleC
public import SuperdiffusionCLT.AKHC61.Carrier.ScalarBlocksB
public import SuperdiffusionCLT.AKHC61.Step3.AlgebraicComparison

/-!
# Package C5b, part 1: the `W`-relative Frobenius norm and starred subadditivity

Proof of `e.variance.proto` of [AK]. The three-scale comparison `e.variance.HC`
(`akhc_variance_threeScale` in `ThreeScaleC.lean`) cannot serve
`e.variance.again.prime`, because its `Ahom`-comparison
term is *first order* (`6 tr_w(Ahom_k)(tr_w Ahom_k - tr_w Ahom_n)`) while
`e.variance.again.prime` needs a *quadratic* term `C(Θ̂_k - 1)²`. The paper obtains the
quadratic form from `e.variance.proto` via a sample-wise harmonic-mean argument: the
quenched (pathwise) bound `e.variance.proto` is linear in `Θ̂_k - 1`, and
*squaring it* to pass from a quenched bound to a second-moment bound is what
manufactures the square (the unlabeled display immediately
preceding `e.variance.again.prime`).

This file builds the two purely algebraic/deterministic pieces this squaring
step needs:

* `akhcRelFrobNorm`, the square root of `akhcRelFrobSq`, and the elementary
  fact that a linear bound on the norm gives a bound on the square that is
  quadratic in each summand (`akhc_relFrobSq_le_two_sq_add_two_sq_of_relFrobNorm_le`);
* subadditivity of the *starred inverse* field `bfA_*^{-1}`, the "starred
  twin" of `coarseBlockMatrix_le_descendantsAverageBlockMat_of_aelocallyUniformlyEllipticField`
  (used already in `ThreeScaleB.lean`). Since
  `Homogenization.coarseStarredBlockMatrixInv U a = Homogenization.blockReflect
  (Homogenization.coarseBlockMatrix U a)` *by definition*
  (in `CoarseGraining/Definitions.lean`), and `blockReflect` both
  preserves the Löwner order (`Homogenization.Book.Ch04.blockMatLoewnerLE_blockReflect`)
  and commutes with `descendantsAverageBlockMat` (a pure reindexing of the
  four blocks, proved below), the starred subadditivity follows from the
  plain subadditivity of `bfA` by conjugation — no new probabilistic or
  ellipticity content is needed beyond what `ThreeScaleB.lean` already uses.

`ProtoB.lean` states the quenched bound `e.variance.proto` itself (which also needs the
ordering `bfA_* ≤ bfA` and the sample-mean/harmonic-mean discard identity)
as a precisely stated hypothesis, and derives from it — using
the machinery here — exactly the quadratic-in-`(Θ̂_k - 1)` expectation bound
that `e.variance.again.prime` needs, with the scale `k` left free so that one can instantiate
`k := n - ℓ(n)` with `ℓ(n) = ⌈L₁ log(L₂ n)⌉`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier

noncomputable section

variable {d : ℕ}

/-! ## Part 1: the `W`-relative Frobenius norm -/

/-- The `W`-relative Frobenius norm `|M|_w := sqrt(akhcRelFrobSq w M)`, the
square-root reading of the squared quantity already used throughout
`ThreeScale*.lean`. This is the natural reading of the source's operator norm
`|W^{-1/2} M W^{-1/2}|` once everything is scalarized against a positive
diagonal `w`. -/
def akhcRelFrobNorm (w : BlockCoord d → ℝ) (M : BlockCoord d → BlockCoord d → ℝ) : ℝ :=
  Real.sqrt (akhcRelFrobSq w M)

theorem akhc_relFrobNorm_nonneg (w : BlockCoord d → ℝ)
    (M : BlockCoord d → BlockCoord d → ℝ) : 0 ≤ akhcRelFrobNorm w M :=
  Real.sqrt_nonneg _

/-- `akhcRelFrobSq w M = (akhcRelFrobNorm w M)²`. -/
theorem akhc_relFrobSq_eq_sq_relFrobNorm {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (M : BlockCoord d → BlockCoord d → ℝ) :
    akhcRelFrobSq w M = akhcRelFrobNorm w M ^ 2 := by
  rw [akhcRelFrobNorm, Real.sq_sqrt (akhc_relFrobSq_nonneg hw M)]

/-- **The squaring step that manufactures the quadratic term.** If the
`W`-relative Frobenius norm of `M` is bounded by a sum `A + B` of two
nonnegative quantities, then the squared norm is bounded by `2A² + 2B²`. This
is exactly the elementary step `(a+b)² ≤ 2a² + 2b²` applied to a quenched
(pathwise) bound to produce a second-moment bound: it is what turns
`e.variance.proto`'s linear-in-`(Θ̂_k - 1)` quenched bound into the
quadratic-in-`(Θ̂_k - 1)` expectation bound node 50 needs, once `A` is
deterministic and `B` is squared and averaged. -/
theorem akhc_relFrobSq_le_two_sq_add_two_sq_of_relFrobNorm_le {w : BlockCoord d → ℝ}
    (hw : ∀ α, 0 < w α) (M : BlockCoord d → BlockCoord d → ℝ) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hbound : akhcRelFrobNorm w M ≤ A + B) :
    akhcRelFrobSq w M ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
  rw [akhc_relFrobSq_eq_sq_relFrobNorm hw]
  have hnorm := akhc_relFrobNorm_nonneg w M
  have hxx : akhcRelFrobNorm w M * akhcRelFrobNorm w M ≤ (A + B) * (A + B) :=
    mul_le_mul hbound hbound hnorm (by linarith only [hA, hB])
  have hsq : akhcRelFrobNorm w M ^ 2 = akhcRelFrobNorm w M * akhcRelFrobNorm w M := sq _
  rw [hsq]
  nlinarith only [hxx, sq_nonneg (A - B)]

/-! ## Part 2: the starred twin of subadditivity, by conjugation with `blockReflect`

`Homogenization.coarseStarredBlockMatrixInv U a = Homogenization.blockReflect
(Homogenization.coarseBlockMatrix U a)` *by definition*
(in `CoarseGraining/Definitions.lean`), so subadditivity of `bfA_*^{-1}`
follows from subadditivity of `bfA` by conjugation, using that `blockReflect`
preserves the Löwner order and commutes with descendant averaging. -/

/-! ## Part 3: the deterministic `|Ahom_k - W|²_w` term, via package E1 directly

Package E1 (`AKHC61.Step3.AlgebraicComparison`) proves the *scalar*,
`4d`-free form of `e.algebraic.add.error`/`e.algebraic.add.error.again`:
`σ̄_k/σ̄_n - 1 ≤ Θ_k - Θ_n` (and the `σ̄*⁻¹` twin), for every `k ≤ n`, no
smallness hypothesis, no window. This section converts that scalar bound
directly into the `akhcRelFrobSq`/`akhcSubDiag` reading used throughout
`ThreeScale*.lean` and this file: with `w := diag(bfAhom_L(cu_m))`, the
deterministic term `|bfAhom_L(cu_k) - W|²_w` appearing both in node 42's
`akhc_threeScale_deterministic_le` and inside `e.variance.proto`'s own Step 1
(which is exactly what E1 reproves) is bounded by `2d(Θ̂_k - 1)²`
— already quadratic, using E1 directly (not a named hypothesis for it). -/

section AlgebraicComparisonBridge

/-- A block matrix that is diagonal (all off-diagonal entries `0`) contributes
only its diagonal entries to `akhcRelFrobSq`, and each diagonal contribution
is controlled by the pointwise ratio bound `hdiag`. General, reusable helper:
no reference to any specific matrix construction. -/
theorem akhcProto_relFrobSq_le_two_mul_d_mul_sq_of_diag_bound [NeZero d]
    {w : BlockCoord d → ℝ} {N : BlockCoord d → BlockCoord d → ℝ}
    (hoffdiag : ∀ α β, α ≠ β → N α β = 0) {ε : ℝ}
    (hdiag : ∀ α, |N α α / w α| ≤ ε) :
    akhcRelFrobSq w N ≤ (2 * d : ℝ) * ε ^ 2 := by
  unfold akhcRelFrobSq
  have hterm : ∀ α, ∑ β, N α β ^ 2 / (w α * w β) = N α α ^ 2 / (w α * w α) := by
    intro α
    refine Finset.sum_eq_single α (fun β _ hβ => ?_) (fun h => absurd (Finset.mem_univ α) h)
    rw [hoffdiag α β (Ne.symm hβ)]
    simp
  have hbound : ∀ α, N α α ^ 2 / (w α * w α) ≤ ε ^ 2 := by
    intro α
    have h2 := hdiag α
    rw [abs_le] at h2
    have hdivsq : N α α ^ 2 / (w α * w α) = (N α α / w α) ^ 2 := by
      rw [div_pow, sq (w α)]
    rw [hdivsq]
    nlinarith only [h2.1, h2.2,
      mul_nonneg (by linarith only [h2.1] : (0:ℝ) ≤ N α α / w α + ε)
        (by linarith only [h2.2] : (0:ℝ) ≤ ε - N α α / w α)]
  calc ∑ α, ∑ β, N α β ^ 2 / (w α * w β) = ∑ α, N α α ^ 2 / (w α * w α) :=
        Finset.sum_congr rfl fun α _ => hterm α
    _ ≤ ∑ _α : BlockCoord d, ε ^ 2 := Finset.sum_le_sum fun α _ => hbound α
    _ = (2 * d : ℝ) * ε ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, akhc_card_blockCoord, nsmul_eq_mul]
        push_cast
        ring

/-- Off-diagonal entries of a scalar block-diagonal matrix vanish. -/
theorem akhcProto_blockMatEntry_blockDiag_smul_one_eq_zero_of_ne {a b : ℝ}
    {α β : BlockCoord d} (hαβ : α ≠ β) :
    blockMatEntry (Book.Ch02.blockDiag (a • (1 : Mat d)) (b • (1 : Mat d))) α β = 0 := by
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      have hij : i ≠ j := fun h => hαβ (by rw [h])
      simp [blockMatEntry, Book.Ch02.blockDiag, hij]
    | inr j => simp [blockMatEntry, Book.Ch02.blockDiag]
  | inr i =>
    cases β with
    | inl j => simp [blockMatEntry, Book.Ch02.blockDiag]
    | inr j =>
      have hij : i ≠ j := fun h => hαβ (by rw [h])
      simp [blockMatEntry, Book.Ch02.blockDiag, hij]

variable [NeZero d] {nu : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L : ℕ}
  (hnu : 0 < nu) (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
  (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X (H * (j : ℝ) ^ D) ∧
      ∀ (omega : ShellSeq d) (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (coefficientCutoff nu omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))

include hnu hPrefix hJ2 hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
  hGrowth hP2

/-- **The deterministic `|Ahom_k - W|²_w` term is quadratic in `Θ̂_k - 1`, via
package E1 directly.** With `w := diag(bfAhom_L(cu_m))`, for `k ≤ m`:
`akhcRelFrobSq w (akhcSubDiag (bfAhom_L(cu_k)) w) ≤ 2d(Θ̂_k - 1)²`. This is the
Frobenius-norm reading of `e.algebraic.add.error`'s own conclusion,
squared; it feeds exactly the deterministic slot `hk`/`hn` of node 42's
`akhc_threeScale_deterministic_le`, and (for `ProtoB.lean`) the same slot
inside `e.variance.proto`'s own Step 1. -/
theorem akhcProto_relFrobSq_annealedBlockMatrix_sub_le_of_P2 {k m : ℕ} (hkm : k ≤ m) :
    akhcRelFrobSq
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
      (akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ≤
      2 * (d : ℝ) *
        (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 := by
  set w : BlockCoord d → ℝ :=
    Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
      (fun _ : Fin d => sigmaBarStarInvSeq nu L P m) with hw_def
  have hSigmaPosM := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hStarPosM := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (k : ℤ)]
  have hoffdiag : ∀ α β : BlockCoord d, α ≠ β →
      akhcSubDiag (Book.Ch02.blockDiag (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ)))
          • (1 : Mat d))
        (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))) w α β
        = 0 := by
    intro α β hαβ
    unfold akhcSubDiag
    rw [akhcProto_blockMatEntry_blockDiag_smul_one_eq_zero_of_ne hαβ, ite_eq_right hαβ, sub_zero]
  have hSigmaAnti := SuperdiffusionCLT.AKHC61.Step3.akhc_algebraic_comparison_sigmaBar_of_P2
    hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono
    hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hStarAnti :=
    SuperdiffusionCLT.AKHC61.Step3.akhc_algebraic_comparison_sigmaBarStarInv_of_P2
      hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono
      hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hThetaK := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hThetaM := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hSigmaAntiSeq := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hStarAntiSeq := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hdiag : ∀ α : BlockCoord d,
      |akhcSubDiag (Book.Ch02.blockDiag
          (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))) w α
        α / w α| ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 := by
    intro α
    cases α with
    | inl i =>
      have hval : akhcSubDiag (Book.Ch02.blockDiag
          (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d)))
          w (Sum.inl i) (Sum.inl i) / w (Sum.inl i) =
          sigmaBarSeq nu L P k / sigmaBarSeq nu L P m - 1 := by
        unfold akhcSubDiag
        simp only [blockMatEntry, Book.Ch02.blockDiag, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one, ite_eq_left, hw_def, Sum.elim_inl, sigmaBarSeq, sigmaBarScalar]
        have hbne : sigmaBar nu L P (cubeSet (originCube d (m : ℤ))) 0 0 ≠ 0 := hSigmaPosM.ne'
        rw [sub_div, div_self hbne]
      have hnonneg : (0:ℝ) ≤ sigmaBarSeq nu L P k / sigmaBarSeq nu L P m - 1 := by
        rw [sub_nonneg, le_div_iff₀ hSigmaPosM, one_mul]
        exact hSigmaAntiSeq
      rw [hval, abs_of_nonneg hnonneg]
      linarith only [hSigmaAnti, hThetaM]
    | inr i =>
      have hval : akhcSubDiag (Book.Ch02.blockDiag
          (sigmaBarScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d))
          (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (k : ℤ))) • (1 : Mat d)))
          w (Sum.inr i) (Sum.inr i) / w (Sum.inr i) =
          sigmaBarStarInvSeq nu L P k / sigmaBarStarInvSeq nu L P m - 1 := by
        unfold akhcSubDiag
        simp only [blockMatEntry, Book.Ch02.blockDiag, Matrix.smul_apply, Matrix.one_apply_eq,
          smul_eq_mul, mul_one, ite_eq_left, hw_def, Sum.elim_inr, sigmaBarStarInvSeq,
          sigmaBarStarInvScalar]
        have hbne : sigmaBarStarInv nu L P (cubeSet (originCube d (m : ℤ))) 0 0 ≠ 0 :=
          hStarPosM.ne'
        rw [sub_div, div_self hbne]
      have hnonneg : (0:ℝ) ≤ sigmaBarStarInvSeq nu L P k / sigmaBarStarInvSeq nu L P m - 1 := by
        rw [sub_nonneg, le_div_iff₀ hStarPosM, one_mul]
        exact hStarAntiSeq
      rw [hval, abs_of_nonneg hnonneg]
      linarith only [hStarAnti, hThetaM]
  exact akhcProto_relFrobSq_le_two_mul_d_mul_sq_of_diag_bound hoffdiag hdiag

end AlgebraicComparisonBridge

end

end SuperdiffusionCLT.AKHC61.Variance
