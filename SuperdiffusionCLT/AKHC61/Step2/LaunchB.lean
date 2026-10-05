/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Step2.Launch
public import SuperdiffusionCLT.AKHC61.Variance.ThreeScaleC
public import SuperdiffusionCLT.AKHC61.Variance.CFSApplied
public import SuperdiffusionCLT.AKHC61.Variance.Proto

/-!
# Package D1: node 30 of `t.weaker.P3`'s Step 1 pigeonhole launch

Source: the proof of Theorem `t.weaker.P3` of [AK], Step 1.

## Main result

`akhcLaunch_variance_HC_prime` (**node 30**, `e.variance.HC.prime`): C5's
`akhc_variance_threeScale_eps` (`AKHC61/Variance/ThreeScaleC.lean`) applied at
the normalizing scale `w := diag(bfAhom_L(cu_{ktop}))`, C4's
`akhc_CFS_weaker_applied` (`AKHC61/Variance/CFSApplied.lean`) for the `hLinInt`
second-moment input (normalized at the *inner* scale `j` — its `.1` supplies
integrability, converted to the `ktop`-normalization via
`akhc_relFrobSq_le_of_le_mul`), and node 28's sandwich, at two index pairs
`(j, ktop)` and `(n, ktop)`, for the deterministic `hk`/`hn` closeness inputs
(with `ε := 2d·δ₁`, `c := 1+δ₁` for the normalization change).

## Where the `C(d)·δ₁` term comes from

The deterministic closeness inputs `hk`, `hn` of `akhc_variance_threeScale_eps`
need `|bfAhom_L(cu_j) - W|²_W ≤ ε²` (and its `n` twin), `W := diag(bfAhom_L(cu_{ktop}))`.
Package E2 (`Step3/VarianceAgain.lean`) needed an *external*, not-yet-available
`Θ̂_k ≤ B` hypothesis to get such a bound from E1's algebraic comparison alone
(its own "REFUTE-FIRST FINDING"). Node 30 avoids that gap entirely: it
consumes node 28's sandwich bounds directly (an *a priori*, uniform-in-scale
`δ₁`-closeness, not an inductive `Θ̂` bound), so `akhcLaunchB_relFrobSq_diag_le`
below gets the clean bound `2d·δ₁²` with **no extra hypothesis**. This is
exactly the `C(d)·δ₁` (`δ₁ = σ²δ` once composed with nodes 27/28) the task
description asks for: the `51d²(ε+ε²)` term of the final bound, `ε = 2dδ₁`.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Step2

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Carrier
open SuperdiffusionCLT.AKHC61.Variance

noncomputable section

variable {d : ℕ}

/-! ## Entry identification helpers, `akhcMatDiag` against the block-diagonal
identity of package A2 -/

section Entries

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hJ4 : ShellLawJ4 d P)

include hnu hJ4

/-- The upper-left diagonal entry of `bfAhom_L(cu_n)` is `σ̄_n`. -/
theorem akhcLaunchB_blockMatEntry_inl (n : ℕ) (i : Fin d) :
    blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
        (Sum.inl i) (Sum.inl i) =
      sigmaBarSeq nu L P n := by
  rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (n : ℤ)]
  show (Book.Ch02.blockDiag
      (sigmaBarScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d))
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d))).upperLeft
      i i = sigmaBarSeq nu L P n
  rw [Book.Ch02.blockDiag]
  show (sigmaBarScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d)) i i =
    sigmaBarSeq nu L P n
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rfl

/-- The lower-right diagonal entry of `bfAhom_L(cu_n)` is `σ̄*⁻¹_n`. -/
theorem akhcLaunchB_blockMatEntry_inr (n : ℕ) (i : Fin d) :
    blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
        (Sum.inr i) (Sum.inr i) =
      sigmaBarStarInvSeq nu L P n := by
  rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (n : ℤ)]
  show (Book.Ch02.blockDiag
      (sigmaBarScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d))
      (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d))).lowerRight
      i i = sigmaBarStarInvSeq nu L P n
  rw [Book.Ch02.blockDiag]
  show (sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) • (1 : Mat d)) i i =
    sigmaBarStarInvSeq nu L P n
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  rfl

/-- `akhcMatDiag (bfAhom_L(cu_n))` at an upper-left coordinate is `σ̄_n`. -/
theorem akhcLaunchB_matDiag_inl (n : ℕ) (i : Fin d) :
    akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) (Sum.inl i) =
      sigmaBarSeq nu L P n :=
  akhcLaunchB_blockMatEntry_inl hnu L P hJ4 n i

/-- `akhcMatDiag (bfAhom_L(cu_n))` at a lower-right coordinate is `σ̄*⁻¹_n`. -/
theorem akhcLaunchB_matDiag_inr (n : ℕ) (i : Fin d) :
    akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) (Sum.inr i) =
      sigmaBarStarInvSeq nu L P n :=
  akhcLaunchB_blockMatEntry_inr hnu L P hJ4 n i

end Entries

/-! ## The diagonal Frobenius defect at a `δ₁`-sandwiched pair -/

section Diag

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hJ4 : ShellLawJ4 d P)
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

include hnu hJ4 hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2

/-- **The `w_{ktop}`-relative diagonal Frobenius defect of `bfAhom_L(cu_j)` is
quadratic in `δ₁`**, given node 28's upper sandwich bounds (`hAle`, `hBle`) and
the antitone lower bounds (`hAge`, `hBge`) at `(j, ktop)`. No hypothesis beyond
`hnu`, `ShellLawJ4` and the (P2′) clause: this is the ingredient that lets node
30 avoid package E2's external `Θ̂_k ≤ B` gap. -/
theorem akhcLaunchB_relFrobSq_diag_le {j ktop : ℕ} {delta1 : ℝ}
    (hAle : sigmaBarSeq nu L P j ≤ (1 + delta1) * sigmaBarSeq nu L P ktop)
    (hAge : sigmaBarSeq nu L P ktop ≤ sigmaBarSeq nu L P j)
    (hBle : sigmaBarStarInvSeq nu L P j ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P ktop)
    (hBge : sigmaBarStarInvSeq nu L P ktop ≤ sigmaBarStarInvSeq nu L P j) :
    akhcRelFrobSq
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
        (akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
          (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))) ≤
      2 * (d : ℝ) * delta1 ^ 2 := by
  have hApos : 0 < sigmaBarSeq nu L P ktop :=
    akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD
      hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 ktop
  have hBpos : 0 < sigmaBarStarInvSeq nu L P ktop :=
    akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH
      hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 ktop
  have hdelta1_nonneg : 0 ≤ delta1 := by
    have h1 : sigmaBarSeq nu L P ktop ≤ (1 + delta1) * sigmaBarSeq nu L P ktop :=
      hAge.trans hAle
    have h2 : sigmaBarSeq nu L P ktop * 1 ≤ sigmaBarSeq nu L P ktop * (1 + delta1) := by
      rw [mul_one, mul_comm]; exact h1
    have h3 : (1 : ℝ) ≤ 1 + delta1 := le_of_mul_le_mul_left h2 hApos
    linarith only [h3]
  have hoffdiag : ∀ α β : BlockCoord d, α ≠ β →
      akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ))))) α β
        = 0 := by
    intro α β hαβ
    unfold akhcSubDiag
    rw [ite_eq_right hαβ, sub_zero,
      akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (j : ℤ)]
    exact akhcProto_blockMatEntry_blockDiag_smul_one_eq_zero_of_ne hαβ
  have hdiag : ∀ α : BlockCoord d,
      |akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
          (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ))))) α α /
        akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))) α| ≤
        delta1 := by
    intro α
    cases α with
    | inl i =>
        have hval : akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
              (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
              (Sum.inl i) (Sum.inl i) /
            akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ))))
              (Sum.inl i) =
            sigmaBarSeq nu L P j / sigmaBarSeq nu L P ktop - 1 := by
          unfold akhcSubDiag
          rw [ite_eq_left rfl, akhcLaunchB_blockMatEntry_inl hnu L P hJ4 j i,
            akhcLaunchB_matDiag_inl hnu L P hJ4 ktop i, sub_div, div_self hApos.ne']
        have hupper : sigmaBarSeq nu L P j / sigmaBarSeq nu L P ktop - 1 ≤ delta1 := by
          have h1 : sigmaBarSeq nu L P j / sigmaBarSeq nu L P ktop ≤ 1 + delta1 := by
            rw [div_le_iff₀ hApos]; exact hAle
          linarith only [h1]
        have hlower : -delta1 ≤ sigmaBarSeq nu L P j / sigmaBarSeq nu L P ktop - 1 := by
          have h1 : (1 : ℝ) ≤ sigmaBarSeq nu L P j / sigmaBarSeq nu L P ktop := by
            rw [le_div_iff₀ hApos]; linarith only [hAge]
          linarith only [h1, hdelta1_nonneg]
        rw [hval, abs_le]
        exact ⟨hlower, hupper⟩
    | inr i =>
        have hval : akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
              (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
              (Sum.inr i) (Sum.inr i) /
            akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ))))
              (Sum.inr i) =
            sigmaBarStarInvSeq nu L P j / sigmaBarStarInvSeq nu L P ktop - 1 := by
          unfold akhcSubDiag
          rw [ite_eq_left rfl, akhcLaunchB_blockMatEntry_inr hnu L P hJ4 j i,
            akhcLaunchB_matDiag_inr hnu L P hJ4 ktop i, sub_div, div_self hBpos.ne']
        have hupper : sigmaBarStarInvSeq nu L P j / sigmaBarStarInvSeq nu L P ktop - 1 ≤
            delta1 := by
          have h1 : sigmaBarStarInvSeq nu L P j / sigmaBarStarInvSeq nu L P ktop ≤
              1 + delta1 := by
            rw [div_le_iff₀ hBpos]; exact hBle
          linarith only [h1]
        have hlower : -delta1 ≤
            sigmaBarStarInvSeq nu L P j / sigmaBarStarInvSeq nu L P ktop - 1 := by
          have h1 : (1 : ℝ) ≤ sigmaBarStarInvSeq nu L P j / sigmaBarStarInvSeq nu L P ktop := by
            rw [le_div_iff₀ hBpos]; linarith only [hBge]
          linarith only [h1, hdelta1_nonneg]
        rw [hval, abs_le]
        exact ⟨hlower, hupper⟩
  exact akhcProto_relFrobSq_le_two_mul_d_mul_sq_of_diag_bound hoffdiag hdiag

end Diag

/-! ## Node 30: the assembled three-scale variance bound -/

section Assembly

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ) (P : ProbabilityMeasure (ShellSeq d))
  (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ4 : ShellLawJ4 d P) (hd : 2 ≤ d)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hDnn : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowthP2 : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
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
  (beta L1 L2 : ℝ) (m3 : ℕ) (omegaSeq : ℕ → ℝ) (Psi : ℝ → ℝ) (KPsi pPsi : ℝ)
  (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (hL1 : 1 ≤ L1) (hL2 : 1 ≤ L2)
  (homegaPos : ∀ k' : ℕ, 0 < omegaSeq k') (homegaAnti : Antitone omegaSeq)
  (homegaTendsto : Filter.Tendsto omegaSeq Filter.atTop (nhds 0))
  (hPsiMono : StrictMonoOn Psi (Set.Ici 0)) (hPsiOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ Psi t)
  (hKPsi : 1 ≤ KPsi) (hpPsi : (d : ℝ) < pPsi)
  (hGrowthP3 : ∀ p : ℝ, 1 < p → p ≤ pPsi → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsi ^ (3 * ⌈p⌉₊ ^ 2) * (Psi (t * s) / Psi t))
  (hP3 : ∀ j n : ℕ, m3 ≤ n → beta * (j : ℝ) < (n : ℝ) →
    (n : ℝ) < (j : ℝ) - L1 * Real.log (L2 * (n : ℝ)) →
    ∃ X : ShellSeq d → ℝ, Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure Psi X (omegaSeq n) ∧
      ∀ (omega : ShellSeq d) (p q : BlockVec d),
        2 *
            (((descendantsAtDepth (originCube d (j : ℤ)) (j - n)).card : ℝ)⁻¹ *
              ∑ R ∈ descendantsAtDepth (originCube d (j : ℤ)) (j - n),
                blockVecDot p
                  (blockMatVecMul
                    (ofFullBlockMat
                      (toFullBlockMat
                          (coarseBlockMatrix (cubeSet R)
                            (coefficientCutoff nu omega L).toCoeffField) -
                        toFullBlockMat
                          (annealedBlockMatrix nu L P
                            (cubeSet (originCube d (n : ℤ))))))
                    q)) ≤
          X omega *
            (blockVecDot p
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) p) +
              blockVecDot q
                (blockMatVecMul
                  (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) q)))

include hnu hJ4 hPrefix hJ2 hd hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2
  hP2 homegaPos hPsiOne hKPsi hpPsi hGrowthP3 hP3

/-- **Node 30** (`e.variance.HC.prime`): the three-scale variance
bound `akhc_variance_threeScale_eps` (C5), normalized at `w := diag(bfAhom_L(cu_{ktop}))`,
with the `hLinInt` second moment (C4, at the inner scale `j`, window
`β n < j < n - L₁ log(L₂ j)`) converted to the `ktop`-normalization by
`akhc_relFrobSq_le_of_le_mul` (`c := 1+δ₁`), and the deterministic closeness
inputs `hk`, `hn` from `akhcLaunchB_relFrobSq_diag_le` (node 28's sandwich, at
`(j, ktop)` and `(n, ktop)`, `ε := 2d·δ₁`). Composed with nodes 27/28,
`δ₁ = σ²δ`. -/
theorem akhcLaunch_variance_HC_prime
    {ktop j n : ℕ} (hjktop : j ≤ ktop) (hnktop : n ≤ ktop) (hjn : j ≤ n)
    (hm3 : m3 ≤ j) (hwin1 : beta * (n : ℝ) < (j : ℝ))
    (hwin2 : (j : ℝ) < (n : ℝ) - L1 * Real.log (L2 * (j : ℝ)))
    {delta1 : ℝ}
    (hAleJ : sigmaBarSeq nu L P j ≤ (1 + delta1) * sigmaBarSeq nu L P ktop)
    (hBleJ : sigmaBarStarInvSeq nu L P j ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P ktop)
    (hAleN : sigmaBarSeq nu L P n ≤ (1 + delta1) * sigmaBarSeq nu L P ktop)
    (hBleN : sigmaBarStarInvSeq nu L P n ≤ (1 + delta1) * sigmaBarStarInvSeq nu L P ktop) :
    ∫ omega, akhcRelFrobSq
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ))))))
        ∂P.toMeasure ≤
      (3 + 6 * (d : ℝ)) * ((1 + delta1) ^ 2 *
          ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
            omegaSeq j ^ 2)) +
        51 * (d : ℝ) ^ 2 * (2 * (d : ℝ) * delta1 + (2 * (d : ℝ) * delta1) ^ 2) := by
  have hAgeJ : sigmaBarSeq nu L P ktop ≤ sigmaBarSeq nu L P j :=
    akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hjktop
  have hBgeJ : sigmaBarStarInvSeq nu L P ktop ≤ sigmaBarStarInvSeq nu L P j :=
    akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hjktop
  have hAgeN : sigmaBarSeq nu L P ktop ≤ sigmaBarSeq nu L P n :=
    akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hnktop
  have hBgeN : sigmaBarStarInvSeq nu L P ktop ≤ sigmaBarStarInvSeq nu L P n :=
    akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hnktop
  have hdiagJ := akhcLaunchB_relFrobSq_diag_le hnu L P hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hAleJ hAgeJ hBleJ hBgeJ
  have hdiagN := akhcLaunchB_relFrobSq_diag_le hnu L P hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
    hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hAleN hAgeN hBleN hBgeN
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    have h1 : 1 ≤ d := by omega
    exact_mod_cast h1
  have hdelta1_nonneg : 0 ≤ delta1 := by
    have h1 : sigmaBarSeq nu L P ktop ≤ (1 + delta1) * sigmaBarSeq nu L P ktop :=
      hAgeJ.trans hAleJ
    have hApos : 0 < sigmaBarSeq nu L P ktop :=
      akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hDnn
        hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 ktop
    have h2 : sigmaBarSeq nu L P ktop * 1 ≤ sigmaBarSeq nu L P ktop * (1 + delta1) := by
      rw [mul_one, mul_comm]; exact h1
    have h3 : (1 : ℝ) ≤ 1 + delta1 := le_of_mul_le_mul_left h2 hApos
    linarith only [h3]
  have h2d : 2 * (d : ℝ) * delta1 ^ 2 ≤ (2 * (d : ℝ) * delta1) ^ 2 := by
    have hkey : (2 * (d : ℝ) * delta1) ^ 2 - 2 * (d : ℝ) * delta1 ^ 2 =
        2 * (d : ℝ) * delta1 ^ 2 * (2 * (d : ℝ) - 1) := by ring
    have hposFactor : 0 ≤ 2 * (d : ℝ) * delta1 ^ 2 * (2 * (d : ℝ) - 1) :=
      mul_nonneg (mul_nonneg (by positivity) (sq_nonneg delta1)) (by linarith only [hd1])
    linarith only [hkey, hposFactor]
  have hk : akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
      (akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ))))
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))) ≤
      (2 * (d : ℝ) * delta1) ^ 2 := by linarith only [hdiagJ, h2d]
  have hnb : akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
      (akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))
        (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))) ≤
      (2 * (d : ℝ) * delta1) ^ 2 := by linarith only [hdiagN, h2d]
  have hε_nonneg : (0 : ℝ) ≤ 2 * (d : ℝ) * delta1 := by positivity
  have hwpos : ∀ α : BlockCoord d, 0 <
      akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))) α := by
    intro α
    cases α with
    | inl i =>
        rw [akhcLaunchB_matDiag_inl hnu L P hJ4 ktop i]
        exact akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
          hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 ktop
    | inr i =>
        rw [akhcLaunchB_matDiag_inr hnu L P hJ4 ktop i]
        exact akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
          hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 ktop
  have hwjpos : ∀ α : BlockCoord d, 0 <
      akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))) α := by
    intro α
    cases α with
    | inl i =>
        rw [akhcLaunchB_matDiag_inl hnu L P hJ4 j i]
        exact akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
          hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 j
    | inr i =>
        rw [akhcLaunchB_matDiag_inr hnu L P hJ4 j i]
        exact akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
          hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 j
  have hle : ∀ α : BlockCoord d,
      akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))) α ≤
        (1 + delta1) *
          akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))) α := by
    intro α
    cases α with
    | inl i =>
        rw [akhcLaunchB_matDiag_inl hnu L P hJ4 j i, akhcLaunchB_matDiag_inl hnu L P hJ4 ktop i]
        exact hAleJ
    | inr i =>
        rw [akhcLaunchB_matDiag_inr hnu L P hJ4 j i, akhcLaunchB_matDiag_inr hnu L P hJ4 ktop i]
        exact hBleJ
  obtain ⟨hCFSInt, hCFSBound⟩ := akhc_CFS_weaker_applied hnu P hJ4 L hd gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 beta L1 L2 m3
    omegaSeq Psi KPsi pPsi homegaPos hPsiOne hKPsi hpPsi hGrowthP3 hP3 hm3 hwin1 hwin2
  have hIntA1 := akhc_integrable_blockMatEntry_of_P2 d hnu P L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2
  have hLinEntryMeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun omega => akhcCFSLinEntry nu L P j n omega α β) P.toMeasure := by
    intro α β
    unfold akhcCFSLinEntry
    have hSumMeas : AEStronglyMeasurable (fun omega =>
        ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - j),
          (blockMatEntry (coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField) α β -
            blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))) α β))
        P.toMeasure :=
      Finset.aestronglyMeasurable_fun_sum _ fun R _ =>
        (hIntA1 R α β).aestronglyMeasurable.sub aestronglyMeasurable_const
    exact hSumMeas.const_mul _
  have hLinMeas_ktop : AEStronglyMeasurable (fun omega => akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
      (akhcCFSLinEntry nu L P j n omega)) P.toMeasure := by
    unfold akhcRelFrobSq
    refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun β _ => ?_
    exact ((continuous_pow 2).div_const _).comp_aestronglyMeasurable (hLinEntryMeas α β)
  have hLinInt_ktop : Integrable (fun omega => akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
      (akhcCFSLinEntry nu L P j n omega)) P.toMeasure := by
    refine (hCFSInt.const_mul ((1 + delta1) ^ 2)).mono' hLinMeas_ktop
      (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (akhc_relFrobSq_nonneg hwpos _)]
    exact akhc_relFrobSq_le_of_le_mul hwpos hwjpos hle _
  have hLinBound_ktop : ∫ omega, akhcRelFrobSq
      (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
      (akhcCFSLinEntry nu L P j n omega) ∂P.toMeasure ≤
      (1 + delta1) ^ 2 *
        ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) * omegaSeq j ^ 2) := by
    calc ∫ omega, akhcRelFrobSq
            (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (ktop : ℤ)))))
            (akhcCFSLinEntry nu L P j n omega) ∂P.toMeasure
        ≤ ∫ omega, (1 + delta1) ^ 2 * akhcRelFrobSq
              (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))))
              (akhcCFSLinEntry nu L P j n omega) ∂P.toMeasure :=
          integral_mono hLinInt_ktop (hCFSInt.const_mul _) (fun omega =>
            akhc_relFrobSq_le_of_le_mul hwpos hwjpos hle _)
      _ = (1 + delta1) ^ 2 * ∫ omega, akhcRelFrobSq
            (akhcMatDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (j : ℤ)))))
            (akhcCFSLinEntry nu L P j n omega) ∂P.toMeasure := integral_const_mul _ _
      _ ≤ (1 + delta1) ^ 2 *
            ((2 * (d : ℝ)) ^ 2 * ((pPsi / (pPsi - 2)) * KPsi ^ (3 * ⌈pPsi⌉₊ ^ 2)) *
              omegaSeq j ^ 2) :=
          mul_le_mul_of_nonneg_left hCFSBound (by positivity)
  have hC5 := akhc_variance_threeScale_eps hnu P hPrefix hJ2 L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hDnn hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowthP2 hP2 hjn hwpos hLinInt_ktop
    hε_nonneg hk hnb
  refine hC5.trans ?_
  gcongr
  exact hLinBound_ktop

end Assembly

end

end SuperdiffusionCLT.AKHC61.Step2
