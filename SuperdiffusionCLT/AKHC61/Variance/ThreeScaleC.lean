/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ThreeScaleB
public import SuperdiffusionCLT.AKHC61.Carrier.Integrability

/-!
# The three-scale variance comparison `e.variance.HC`

For the cutoff field under the shell law,
scales `k ≤ n`, and a positive diagonal normalization `W = diag w`,

`E |bfA(cu_n) - W|²_w ≤ (3 + 6d) E |avsum_R (bfA(R) - bfAhom(cu_k))|²_w
  + 3 |bfAhom(cu_k) - W|²_w + 6 tr_w(bfAhom(cu_k)) (tr_w(bfAhom(cu_k)) - tr_w(bfAhom(cu_n)))`,

where `|M|²_w = ∑ α β, M_{αβ}² / (w_α w_β)` is the squared Frobenius norm of
`W^{-1/2} M W^{-1/2}` and `tr_w M = ∑ α, M_{αα} / w_α`. The first form carries
the entrywise integrability of the coarse block matrices as a hypothesis; the
second discharges it from the (P2') clause of the main statement, copied
verbatim.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-- Integrability and expectation of the trace defect
`tr_w (avsum_R bfA(R) - bfA(cu_n))`. -/
theorem akhc_integral_relTrace_defect [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (L : ℕ)
    {k n : ℕ} (hkn : k ≤ n) (w : BlockCoord d → ℝ)
    (hInt : ∀ (Q : TriadicCube d) (α β : BlockCoord d), Integrable (fun omega =>
      blockMatEntry (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField) α β) P.toMeasure) :
    Integrable (fun omega => akhcRelTrace w (fun α β =>
        blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
            (fun R => coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField)) α β -
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField) α β)) P.toMeasure ∧
    ∫ omega, akhcRelTrace w (fun α β =>
        blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
            (fun R => coarseBlockMatrix (cubeSet R)
              (coefficientCutoff nu omega L).toCoeffField)) α β -
          blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField) α β) ∂P.toMeasure =
      akhcRelTrace w (blockMatEntry
          (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) -
        akhcRelTrace w (blockMatEntry
          (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ))))) := by
  set D := descendantsAtDepth (originCube d (n : ℤ)) (n - k) with hD
  have hAvgInt : ∀ α β : BlockCoord d, Integrable (fun omega =>
      blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R)
          (coefficientCutoff nu omega L).toCoeffField)) α β) P.toMeasure := by
    intro α β
    simp only [akhc_blockMatEntry_descendantsAverageBlockMat]
    exact (integrable_finsetSum _ fun R _ => hInt R α β).const_mul _
  have hAvgEq : ∀ α β : BlockCoord d, ∫ omega,
      blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R)
          (coefficientCutoff nu omega L).toCoeffField)) α β ∂P.toMeasure =
      blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β := by
    intro α β
    simp only [akhc_blockMatEntry_descendantsAverageBlockMat]
    rw [integral_const_mul, integral_finsetSum _ fun R _ => hInt R α β]
    rw [Finset.sum_congr rfl fun R hR =>
      akhc_integral_blockMatEntry_descendant hnu P hPrefix hJ2 L hkn hR α β]
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
    have hne : ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty _ _)
    rw [inv_mul_cancel₀ hne, one_mul]
  have hTermInt : ∀ α : BlockCoord d, Integrable (fun omega =>
      (blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
          (fun R => coarseBlockMatrix (cubeSet R)
            (coefficientCutoff nu omega L).toCoeffField)) α α -
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) α α) / w α) P.toMeasure :=
    fun α => ((hAvgInt α α).sub (hInt _ α α)).div_const _
  refine ⟨integrable_finsetSum _ fun α _ => hTermInt α, ?_⟩
  unfold akhcRelTrace
  rw [integral_finsetSum _ fun α _ => hTermInt α, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [integral_div, integral_sub (hAvgInt α α) (hInt _ α α), hAvgEq,
    ← akhc_blockMatEntry_annealedBlockMatrix, sub_div]

/-- `∫ ((a A + b) + c X) = a ∫ A + b + c ∫ X` on a probability space. -/
theorem akhc_integral_affine {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A X : Ω → ℝ} (hA : Integrable A μ) (hX : Integrable X μ)
    {a b c : ℝ} :
    ∫ ω, (a * A ω + b) + c * X ω ∂μ = a * ∫ ω, A ω ∂μ + b + c * ∫ ω, X ω ∂μ := by
  have h1 : Integrable (fun ω => a * A ω) μ := hA.const_mul a
  have h2 : Integrable (fun ω => a * A ω + b) μ := h1.add (integrable_const b)
  have h3 : Integrable (fun ω => c * X ω) μ := hX.const_mul c
  rw [integral_add h2 h3, integral_add h1 (integrable_const b), integral_const_mul,
    integral_const_mul, integral_const]
  simp

/-- **`e.variance.HC` for the cutoff field, integrability form.**
For scales `k ≤ n` and a positive diagonal normalization `W = diag w`:
the squared `W`-relative Frobenius norm of `bfA(cu_n) - W` is integrable, and
its expectation is at most `(3 + 6d)` times the second moment of the linear
descendant average `avsum_R (bfA(R) - bfAhom(cu_k))`, plus
`3 |bfAhom(cu_k) - W|²_w + 6 tr_w(bfAhom(cu_k)) (tr_w(bfAhom(cu_k)) - tr_w(bfAhom(cu_n)))`. -/
theorem akhc_variance_threeScale_of_integrable [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (L : ℕ)
    {k n : ℕ} (hkn : k ≤ n) {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hInt : ∀ (Q : TriadicCube d) (α β : BlockCoord d), Integrable (fun omega =>
      blockMatEntry (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField) α β) P.toMeasure)
    (hLinInt : Integrable (fun omega => akhcRelFrobSq w (fun α β =>
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
            (blockMatEntry (coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField) α β -
              blockMatEntry (annealedBlockMatrix nu L P
                (cubeSet (originCube d (k : ℤ)))) α β))) P.toMeasure) :
    Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure ≤
      (3 + 6 * d) * ∫ omega, akhcRelFrobSq w (fun α β =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) ∂P.toMeasure +
        3 * akhcRelFrobSq w (akhcSubDiag
          (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w) +
        6 * akhcRelTrace w (blockMatEntry
            (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) *
          (akhcRelTrace w (blockMatEntry
              (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) -
            akhcRelTrace w (blockMatEntry
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) := by
  obtain ⟨hXInt, hXEq⟩ := akhc_integral_relTrace_defect hnu P hPrefix hJ2 L hkn w hInt
  set c := akhcRelTrace w (blockMatEntry
    (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) with hc
  set G := akhcRelFrobSq w (akhcSubDiag
    (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w) with hG
  have hRHSInt := ((hLinInt.const_mul (3 + 6 * d)).add (integrable_const (3 * G))).add
    (hXInt.const_mul (6 * c))
  have hpt := fun omega => akhc_threeScale_cutoff_pointwise hnu P L hkn hw omega
  have hAn : ∀ α β : BlockCoord d, AEStronglyMeasurable (fun omega =>
      akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w α β) P.toMeasure :=
    fun α β => (hInt _ α β).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hLHSmeas : AEStronglyMeasurable (fun omega => akhcRelFrobSq w (akhcSubDiag
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure := by
    unfold akhcRelFrobSq
    refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
    refine Finset.aestronglyMeasurable_fun_sum _ fun β _ => ?_
    exact ((continuous_pow 2).div_const _).comp_aestronglyMeasurable (hAn α β)
  have hLHSInt : Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure := by
    refine hRHSInt.mono' hLHSmeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (akhc_relFrobSq_nonneg hw _)]
    exact hpt omega
  refine ⟨hLHSInt, ?_⟩
  calc _ ≤ ∫ omega, ((3 + 6 * d) * akhcRelFrobSq w (fun α β =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) + 3 * G) +
        6 * c * akhcRelTrace w (fun α β =>
          blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
              (fun R => coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField)) α β -
            blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
              (coefficientCutoff nu omega L).toCoeffField) α β) ∂P.toMeasure :=
        integral_mono hLHSInt hRHSInt hpt
    _ = _ := by
        rw [akhc_integral_affine hLinInt hXInt, hXEq]

/-- **`e.variance.HC` for the cutoff field, under (P2').** The
entrywise integrability of `akhc_variance_threeScale_of_integrable` is
discharged from the (P2') clause of the main statement (copied verbatim) by
`SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2`. -/
theorem akhc_variance_threeScale [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (L : ℕ)
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
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    {k n : ℕ} (hkn : k ≤ n) {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hLinInt : Integrable (fun omega => akhcRelFrobSq w (fun α β =>
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
            (blockMatEntry (coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField) α β -
              blockMatEntry (annealedBlockMatrix nu L P
                (cubeSet (originCube d (k : ℤ)))) α β))) P.toMeasure) :
    Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure ≤
      (3 + 6 * d) * ∫ omega, akhcRelFrobSq w (fun α β =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) ∂P.toMeasure +
        3 * akhcRelFrobSq w (akhcSubDiag
          (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w) +
        6 * akhcRelTrace w (blockMatEntry
            (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) *
          (akhcRelTrace w (blockMatEntry
              (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ))))) -
            akhcRelTrace w (blockMatEntry
              (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))))) :=
  akhc_variance_threeScale_of_integrable hnu P hPrefix hJ2 L hkn hw
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2 d hnu P L
      gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2)
    hLinInt

/-- **`e.variance.HC` in AK.HC's printed shape**: if `|bfAhom(cu_j) - W|_w ≤ ε`
for `j ∈ {k, n}`, then
`E |bfA(cu_n) - W|²_w ≤ (3 + 6d) E |avsum_R (bfA(R) - bfAhom(cu_k))|²_w + 51 d² (ε + ε²)`. -/
theorem akhc_variance_threeScale_eps [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P) (L : ℕ)
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
                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff nu omega L).toCoeffField)
              ((1 + (3 : ℝ) ^ (-(gamma * ((Q.scale : ℝ) - (j : ℝ)))) * X omega) •
                SuperdiffusionCLT.Section2.Annealed.annealedBlockMatrix nu L P
                  (Homogenization.cubeSet (Homogenization.originCube d (j : ℤ)))))
    {k n : ℕ} (hkn : k ≤ n) {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hLinInt : Integrable (fun omega => akhcRelFrobSq w (fun α β =>
        ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
          ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
            (blockMatEntry (coarseBlockMatrix (cubeSet R)
                (coefficientCutoff nu omega L).toCoeffField) α β -
              blockMatEntry (annealedBlockMatrix nu L P
                (cubeSet (originCube d (k : ℤ)))) α β))) P.toMeasure)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hk : akhcRelFrobSq w (akhcSubDiag
      (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w) ≤ ε ^ 2)
    (hn : akhcRelFrobSq w (akhcSubDiag
      (annealedBlockMatrix nu L P (cubeSet (originCube d (n : ℤ)))) w) ≤ ε ^ 2) :
    ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure ≤
      (3 + 6 * d) * ∫ omega, akhcRelFrobSq w (fun α β =>
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
              (blockMatEntry (coarseBlockMatrix (cubeSet R)
                  (coefficientCutoff nu omega L).toCoeffField) α β -
                blockMatEntry (annealedBlockMatrix nu L P
                  (cubeSet (originCube d (k : ℤ)))) α β)) ∂P.toMeasure +
        51 * (d : ℝ) ^ 2 * (ε + ε ^ 2) := by
  have h := (akhc_variance_threeScale hnu P hPrefix hJ2 L gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn hw hLinInt).2
  have hdet := akhc_threeScale_deterministic_le hw hε hk hn
  linarith only [h, hdet]

end

end SuperdiffusionCLT.AKHC61.Variance
