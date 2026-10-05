/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.WeakNorms.PrimeH
public import SuperdiffusionCLT.AKHC61.Step2.LaunchB

/-!
# Package C6, part 9: node 30 in the operator-norm fluctuation form

Package D1's `e.variance.HC.prime` (`akhcLaunch_variance_HC_prime`) bounds the expected relative
Frobenius square `Σ_{αβ} (bfA(cu_n) − Ahom_k)_{αβ}² / (w_α w_β)`, `w = diag Ahom_k`. Node 16 and
node 7 use the operator-norm square `|Ahom_k^{-1/2}(bfA(cu_n) − Ahom_k)Ahom_k^{-1/2}|²`
(`akhcFullBlockNormalizedFluctuationAtScale`). Since `Ahom_k = diag(σ̄_k, σ̄*⁻¹_k)` under J4, the
latter is the operator norm of the matrix whose Frobenius square is the former, so it is smaller.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.WeakNorms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.AKHC61.Response

noncomputable section

/-- The Euclidean operator norm is at most the Frobenius norm: `‖M‖² ≤ Σ_{ij} M_{ij}²`. -/
theorem akhcPrime_norm_toEuclideanCLM_sq_le {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) :
    ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 := by
  have hF0 : 0 ≤ ∑ i, ∑ j, M i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hbound : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ ≤
      Real.sqrt (∑ i, ∑ j, M i j ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
    rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul hF0]
    refine Real.sqrt_le_sqrt ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    have hrow : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M x) i =
        ∑ j, M i j * x j := rfl
    rw [Real.norm_eq_abs, sq_abs, hrow]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => M i j) (fun j => x j)
    simpa only [Real.norm_eq_abs, sq_abs] using hcs
  calc ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) M‖ ^ 2 ≤ Real.sqrt (∑ i, ∑ j, M i j ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = ∑ i, ∑ j, M i j ^ 2 := Real.sq_sqrt hF0

/-- The squared diagonal normalization is the reciprocal of the diagonal of `Ahom`. -/
theorem akhcPrime_invSqrtDiag_sq {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (m : ℤ)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d m)))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d m))) (α : BlockCoord d) :
    akhcFullBlockInvSqrtDiag nu L P m α ^ 2 =
      (SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
        (annealedBlockMatrix nu L P (cubeSet (originCube d m))) α)⁻¹ := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 m]
  cases α with
  | inl i =>
    simp only [akhcFullBlockInvSqrtDiag, Book.Ch04.scalarFullBlockInvSqrtDiag,
      SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag, blockMatEntry, Book.Ch02.blockDiag,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, inv_pow, Real.sq_sqrt hb.le]
  | inr i =>
    simp only [akhcFullBlockInvSqrtDiag, Book.Ch04.scalarFullBlockInvSqrtDiag,
      SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag, blockMatEntry, Book.Ch02.blockDiag,
      Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Real.sq_sqrt (inv_pos.2 hc).le]

/-- The full-block entries of `Ahom = diag(σ̄, σ̄*⁻¹)`: diagonal, with diagonal `akhcMatDiag`. -/
theorem akhcPrime_toFullBlockMat_annealed {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (m : ℤ)
    (α β : BlockCoord d) :
    toFullBlockMat (annealedBlockMatrix nu L P (cubeSet (originCube d m))) α β =
      if α = β then SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
        (annealedBlockMatrix nu L P (cubeSet (originCube d m))) α else 0 := by
  rw [SuperdiffusionCLT.AKHC61.Carrier.akhc_annealedBlockMatrix_originCube_eq_blockDiag
    hnu L hJ4 m]
  cases α with
  | inl i =>
    cases β with
    | inl j =>
      by_cases h : i = j
      · subst h
        simp [toFullBlockMat, SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag, blockMatEntry,
          Book.Ch02.blockDiag]
      · simp [toFullBlockMat, Book.Ch02.blockDiag, h]
    | inr j => simp [toFullBlockMat, Book.Ch02.blockDiag]
  | inr i =>
    cases β with
    | inl j => simp [toFullBlockMat, Book.Ch02.blockDiag]
    | inr j =>
      by_cases h : i = j
      · subst h
        simp [toFullBlockMat, SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag, blockMatEntry,
          Book.Ch02.blockDiag]
      · simp [toFullBlockMat, Book.Ch02.blockDiag, h]

/-- **Operator-norm fluctuation ≤ relative Frobenius square.** For any set `U` and field `a`,
`|Ahom_m^{-1/2}(bfA(U) − Ahom_m)Ahom_m^{-1/2}|² ≤ Σ_{αβ} (bfA(U) − Ahom_m)_{αβ}²/(w_α w_β)`. -/
theorem akhcPrime_fl_le_relFrob {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P) (m : ℤ)
    (hb : 0 < sigmaBarScalar nu L P (cubeSet (originCube d m)))
    (hc : 0 < sigmaBarStarInvScalar nu L P (cubeSet (originCube d m)))
    (U : Set (Vec d)) (a : CoeffField d) :
    akhcFullBlockNormalizedFluctuation nu L P m U a ≤
      SuperdiffusionCLT.AKHC61.Variance.akhcRelFrobSq
        (SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
          (annealedBlockMatrix nu L P (cubeSet (originCube d m))))
        (SuperdiffusionCLT.AKHC61.Variance.akhcSubDiag (coarseBlockMatrix U a)
          (SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
            (annealedBlockMatrix nu L P (cubeSet (originCube d m))))) := by
  unfold akhcFullBlockNormalizedFluctuation
  simp only
  refine (akhcPrime_norm_toEuclideanCLM_sq_le _).trans (le_of_eq ?_)
  unfold SuperdiffusionCLT.AKHC61.Variance.akhcRelFrobSq
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply,
    akhcPrime_toFullBlockMat_annealed hnu L hJ4 m α β]
  have hA : toFullBlockMat (coarseBlockMatrix U a) α β = blockMatEntry (coarseBlockMatrix U a) α β := by
    cases α <;> cases β <;> rfl
  rw [hA]
  unfold SuperdiffusionCLT.AKHC61.Variance.akhcSubDiag
  have hα := akhcPrime_invSqrtDiag_sq hnu L hJ4 m hb hc α
  have hβ := akhcPrime_invSqrtDiag_sq hnu L hJ4 m hb hc β
  rw [div_eq_mul_inv, mul_inv, ← hα, ← hβ]
  ring

section Law

variable {d : ℕ} [NeZero d] {nu : ℝ} (hnu : 0 < nu)
  (P : ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) (L : ℕ)
  (gamma H D : ℝ) (m2 : ℕ) (PsiS : ℝ → ℝ) (KPsiS pPsiS : ℝ)
  (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma < 1) (hH : 1 ≤ H) (hD : 0 ≤ D)
  (hPsiSMono : MonotoneOn PsiS (Set.Ici 0)) (hPsiSOne : ∀ t : ℝ, 0 ≤ t → 1 ≤ PsiS t)
  (hKPsiS : 1 ≤ KPsiS) (hpPsiS : 2 < pPsiS)
  (hGrowth : ∀ p : ℝ, 2 ≤ p → p ≤ pPsiS → ∀ t s : ℝ, 1 ≤ t → 1 ≤ s →
    s ^ p ≤ KPsiS ^ (3 * ⌈p⌉₊ ^ 2) * (PsiS (t * s) / PsiS t))
  (hP2 : ∀ j : ℕ, m2 ≤ j →
    ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
      Measurable X ∧
      Homogenization.IndependentSums.IsBigO P.toMeasure PsiS X
        (H * (j : ℝ) ^ D) ∧
      ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
        (Q : Homogenization.TriadicCube d),
        Q.scale ≤ (j : ℤ) →
        Homogenization.cubeCenter Q ∈
            Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)) →
          Homogenization.BlockMatLoewnerLE
            (Homogenization.coarseBlockMatrix (Homogenization.cubeSet Q)
              (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu
                  omega L).toCoeffField)
            ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) *
                  X omega) •
              SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                (Homogenization.cubeSet
                  (Homogenization.originCube d (j : ℤ)))))
  (hJ4 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P)

include hnu hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hJ4 in
/-- **Node 30 feeds node 7.** The expected operator-norm fluctuation of `bfA(cu_n)` at the
normalization of scale `m`, under the cutoff law, is at most the expected relative Frobenius
square of package D1's `e.variance.HC.prime` (`akhcLaunch_variance_HC_prime`, with
`ktop := m`). -/
theorem akhcPrime_integral_fl_le_relFrob (m n : ℕ) :
    ∫ a, akhcFullBlockNormalizedFluctuationAtScale nu L P (m : ℤ) (originCube d (n : ℤ)) a
        ∂(SuperdiffusionCLT.Section2.Annealed.cutoffLaw (d := d) nu L P) ≤
      ∫ omega, SuperdiffusionCLT.AKHC61.Variance.akhcRelFrobSq
        (SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
          (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ)))))
        (SuperdiffusionCLT.AKHC61.Variance.akhcSubDiag
          (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
          (SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
            (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))))
        ∂P.toMeasure := by
  have hb := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D
    m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hc := SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 m
  have hfl := SuperdiffusionCLT.AKHC61.Carrier.akhcSq_integrable_fullBlockNormalizedFluctuationAtScale_of_P2
    hnu P L gamma H D m2 PsiS KPsiS pPsiS hKPsiS hpPsiS hPsiSOne hGrowth hP2 (m : ℤ)
    (originCube d (n : ℤ))
  have hφ := (SuperdiffusionCLT.Section2.Cutoff.measurable_coefficientCutoff (d := d) nu
    L).aemeasurable (μ := P.toMeasure)
  rw [SuperdiffusionCLT.Section2.Annealed.cutoffLaw, integral_map hφ hfl.aestronglyMeasurable]
  have hfl' := (integrable_map_measure hfl.aestronglyMeasurable hφ).mp hfl
  set w := SuperdiffusionCLT.AKHC61.Variance.akhcMatDiag
    (annealedBlockMatrix nu L P (cubeSet (originCube d (m : ℤ))))
  have hEsq := SuperdiffusionCLT.AKHC61.Carrier.akhcSq_integrable_blockMatEntrySq_of_P2 d
    hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
    hpPsiS hGrowth hP2 (originCube d (n : ℤ))
  have hE := SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2 d hnu P L
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 (originCube d (n : ℤ))
  have hR : Integrable (fun omega => SuperdiffusionCLT.AKHC61.Variance.akhcRelFrobSq w
      (SuperdiffusionCLT.AKHC61.Variance.akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) w))
      P.toMeasure := by
    unfold SuperdiffusionCLT.AKHC61.Variance.akhcRelFrobSq
      SuperdiffusionCLT.AKHC61.Variance.akhcSubDiag
    refine integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ => ?_
    set c : ℝ := if α = β then w α else 0
    have hfun : (fun omega => (blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField) α β -
          c) ^ 2 / (w α * w β)) = fun omega =>
        ((blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            α β) ^ 2 - 2 * c * blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
            α β + c ^ 2) / (w α * w β) := by
      funext omega; ring
    rw [hfun]
    exact ((((hEsq α β).sub ((hE α β).const_mul (2 * c))).add
      (integrable_const (c ^ 2))).div_const _)
  refine integral_mono hfl' hR fun omega => ?_
  exact akhcPrime_fl_le_relFrob hnu L hJ4 (m : ℤ) hb hc _ _

end Law

end

end SuperdiffusionCLT.AKHC61.WeakNorms
