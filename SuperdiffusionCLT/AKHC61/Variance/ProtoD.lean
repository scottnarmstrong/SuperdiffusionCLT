/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.ProtoB
public import SuperdiffusionCLT.AKHC61.Variance.ProtoC
public import Homogenization.Book.Ch02.Theorems.BlockCoarseMatrix
public import Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# `e.variance.proto`, part 2: the cutoff field

Proof of `e.variance.proto` of [AK]. This file instantiates the
abstract quenched bound of `ProtoC.lean` for the cutoff field and proves the
hypothesis `hVarianceProto` of `ProtoB.lean`, with the normalizer
`w = diag(bfAhom_L(cu_m))` of the source, for every `k ≤ n` and `k ≤ m`:

`|bfA(cu_n) - W|_w ≤ 4d(Θ̂_k - 1) + 3|avsum_z(bfA(z + cu_k) - bfAhom_k)|_w`,

which is stronger than the printed `16d(Θ̂_k - 1) + 4|…|` and needs no
smallness hypothesis (the printed `e.smallness.ass` is used in the source only
to bound `|bfAhom_{*,m}^{1/2} bfAhom_{*,k}^{-1} bfAhom_m^{1/2}|² ≤ 2`; testing
the doubled response against `B⁻¹ R x` instead of forming the harmonic mean
gives the factor `1/(b_α² w_{Rα}/w_α) ≤ 1` directly).

The two structural inputs are
* subadditivity `bfA(cu_n) ≤ avsum_z bfA(z + cu_k)` (CoarseGraining Ch04);
* the doubled-response positivity
  `0 ≤ J(P, Q) = ½ P·bfA P + ½ Q·bfA_*^{-1} Q - P·Q` with
  `bfA_*^{-1} = R bfA R` (CoarseGraining Ch02 `BlockCoarseMatrixTheory`),
  which is the ordering `bfA_* ≤ bfA` of the paper in inverse-free form.
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-! ## Bridges from `BlockMat` to the entrywise quadratic form -/

theorem akhcProtoD_toFullBlockMat_apply (A : BlockMat d) (α β : BlockCoord d) :
    toFullBlockMat A α β = blockMatEntry A α β := by
  cases α <;> cases β <;> rfl

theorem akhcProtoD_qf_eq_blockVecDot (A : BlockMat d) (x : BlockCoord d → ℝ) :
    akhcProtoCQf (blockMatEntry A) x =
      blockVecDot (ofFullBlockVec x) (blockMatVecMul A (ofFullBlockVec x)) := by
  rw [blockVecDot_blockMatVecMul_eq_toLinearMap₂', toFullBlockVec_ofFullBlockVec,
    Matrix.toLinearMap₂'_apply']
  unfold akhcProtoCQf
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, akhcProtoD_toFullBlockMat_apply]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  ring

theorem akhcProtoD_qf_le_of_loewner {A B : BlockMat d} (h : BlockMatLoewnerLE A B)
    (x : BlockCoord d → ℝ) :
    akhcProtoCQf (blockMatEntry A) x ≤ akhcProtoCQf (blockMatEntry B) x := by
  rw [akhcProtoD_qf_eq_blockVecDot, akhcProtoD_qf_eq_blockVecDot]
  have := h (ofFullBlockVec x)
  linarith only [this]

theorem akhcProtoD_blockVecDot_swap (x y : BlockCoord d → ℝ) :
    blockVecDot (ofFullBlockVec x) ((ofFullBlockVec y).2, (ofFullBlockVec y).1) =
      ∑ α, x α * y (Sum.swap α) := by
  rw [Fintype.sum_sum_type]
  simp only [blockVecDot, vecDot, ofFullBlockVec, Sum.swap_inl, Sum.swap_inr]

/-- **The doubled-response inequality `2 x·R y ≤ x·A x + y·A y`** for the
coarse block matrix of the cutoff field on any triadic cube: this is
`J(P, Q) ≥ 0` with `bfA_*^{-1} = R bfA R`. -/
theorem akhcProtoD_doubled_cutoff [NeZero d] {nu : ℝ} (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (Q : TriadicCube d) (x y : BlockCoord d → ℝ) :
    2 * ∑ α, x α * y (Sum.swap α) ≤
      akhcProtoCQf (blockMatEntry (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField)) x +
        akhcProtoCQf (blockMatEntry (coarseBlockMatrix (cubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField)) y := by
  set b := (Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (coefficientCutoff nu omega L)
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)).coeffOn Q
  have hA : coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toCoeffField =
      Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q) b :=
    coarseBlockMatrix_cubeSet_coefficientCutoff_eq_ch02 hnu omega L Q
  have hT := Book.Ch02.blockCoarseMatrixTheory (Book.Ch02.cubeDomain Q) b
  have h0 := Book.Ch02.doubledResponseJ_nonneg (Book.Ch02.cubeDomain Q) b
    (ofFullBlockVec x) ((ofFullBlockVec y).2, (ofFullBlockVec y).1)
  rw [hT.doubled_response_splitting, hT.starred_inverse_formula,
    blockVecDot_blockMatVecMul_blockReflect, akhcProtoD_blockVecDot_swap] at h0
  rw [hA, akhcProtoD_qf_eq_blockVecDot, akhcProtoD_qf_eq_blockVecDot]
  linarith only [h0]

/-! ## Scalar bookkeeping -/

theorem akhcProtoD_blockMatEntry_blockDiag (a c : ℝ) (α β : BlockCoord d) :
    blockMatEntry (Book.Ch02.blockDiag (a • (1 : Mat d)) (c • (1 : Mat d))) α β =
      if α = β then Sum.elim (fun _ : Fin d => a) (fun _ : Fin d => c) α else 0 := by
  by_cases h : α = β
  · subst h
    cases α <;> simp [blockMatEntry, Book.Ch02.blockDiag]
  · rw [ite_eq_right h]
    exact akhcProto_blockMatEntry_blockDiag_smul_one_eq_zero_of_ne h

/-- `sqrt(2d ε²) ≤ 2d ε`. -/
theorem akhcProtoD_relFrobNorm_le_of_sq_le [NeZero d] {w : BlockCoord d → ℝ}
    {M : BlockCoord d → BlockCoord d → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (h : akhcRelFrobSq w M ≤ 2 * (d : ℝ) * ε ^ 2) :
    akhcRelFrobNorm w M ≤ 2 * (d : ℝ) * ε := by
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hsq : 2 * (d : ℝ) * ε ^ 2 ≤ (2 * (d : ℝ) * ε) ^ 2 := by
    have h2 : 2 * (d : ℝ) ≤ (2 * (d : ℝ)) ^ 2 := by nlinarith only [hd]
    have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ε)
    calc 2 * (d : ℝ) * ε ^ 2 ≤ (2 * (d : ℝ)) ^ 2 * ε ^ 2 := this
      _ = (2 * (d : ℝ) * ε) ^ 2 := by ring
  unfold akhcRelFrobNorm
  calc Real.sqrt (akhcRelFrobSq w M) ≤ Real.sqrt ((2 * (d : ℝ) * ε) ^ 2) :=
        Real.sqrt_le_sqrt (h.trans hsq)
    _ = 2 * (d : ℝ) * ε := Real.sqrt_sq (by positivity)

/-- The diagonal error `E = diag(b - 1/(b∘R))` relative to `w`: each entry is
`(Θ_k - 1)/(b_{Rα} w_α) ∈ [0, Θ_k - 1]`. -/
theorem akhcProtoD_diag_ratio_le {sm tm sk tk : ℝ} (hsm : 0 < sm) (htm : 0 < tm)
    (hsk : 0 < sk) (htk : 0 < tk) (hΘm : 1 ≤ sm * tm) (hΘk : 1 ≤ sk * tk)
    (hs : sm ≤ sk) (ht : tm ≤ tk) :
    |(sk - tk⁻¹) / sm| ≤ sk * tk - 1 ∧ |(tk - sk⁻¹) / tm| ≤ sk * tk - 1 := by
  have hnum : 0 ≤ sk * tk - 1 := sub_nonneg.mpr hΘk
  have e1 : (sk - tk⁻¹) / sm = (sk * tk - 1) / (tk * sm) := by
    field_simp
  have e2 : (tk - sk⁻¹) / tm = (sk * tk - 1) / (sk * tm) := by
    field_simp
  have d1 : 1 ≤ tk * sm := by
    have := mul_le_mul_of_nonneg_right ht hsm.le
    linarith only [this, hΘm]
  have d2 : 1 ≤ sk * tm := by
    have := mul_le_mul_of_nonneg_right hs htm.le
    linarith only [this, hΘm]
  rw [e1, e2, abs_of_nonneg (div_nonneg hnum (by positivity)),
    abs_of_nonneg (div_nonneg hnum (by positivity))]
  exact ⟨div_le_self hnum d1, div_le_self hnum d2⟩

/-- `w_α ≤ b_α² w_{Rα}`: `s_m ≤ s_k² t_m` and `t_m ≤ t_k² s_m`. -/
theorem akhcProtoD_comp {sm tm sk : ℝ} (hsm : 0 < sm) (htm : 0 < tm) (hΘm : 1 ≤ sm * tm)
    (hs : sm ≤ sk) : sm ≤ sk ^ 2 * tm := by
  have h1 : sm * sm ≤ sk * sk := mul_self_le_mul_self hsm.le hs
  have h2 := mul_le_mul_of_nonneg_right h1 htm.le
  have h3 : sm * 1 ≤ sm * (sm * tm) := mul_le_mul_of_nonneg_left hΘm hsm.le
  calc sm = sm * 1 := (mul_one sm).symm
    _ ≤ sm * (sm * tm) := h3
    _ = sm * sm * tm := by ring
    _ ≤ sk * sk * tm := h2
    _ = sk ^ 2 * tm := by ring


/-! ## The quenched bound for the cutoff field -/

section Cutoff

open SuperdiffusionCLT.AKHC61.Carrier

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

/-- **`e.variance.proto` for the cutoff field, sharp constants.**
With `w = diag(bfAhom_L(cu_m))`, for `k ≤ n` and `k ≤ m`, samplewise:
`|bfA(cu_n) - W|_w ≤ 4d(Θ̂_k - 1) + 3|avsum_z(bfA(z + cu_k) - bfAhom_k)|_w`. -/
theorem akhcProtoD_variance_proto_sharp {k n m : ℕ} (hkn : k ≤ n) (hkm : k ≤ m)
    (omega : ShellSeq d) :
    akhcRelFrobNorm
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ≤
      4 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) +
        3 * akhcRelFrobNorm
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
          (akhcProtoLinearAvg nu P L k n omega) := by
  set sm := sigmaBarSeq nu L P m with hsm_def
  set tm := sigmaBarStarInvSeq nu L P m with htm_def
  set sk := sigmaBarSeq nu L P k with hsk_def
  set tk := sigmaBarStarInvSeq nu L P k with htk_def
  set w : BlockCoord d → ℝ := Sum.elim (fun _ : Fin d => sm) (fun _ : Fin d => tm) with hw_def
  set b : BlockCoord d → ℝ := Sum.elim (fun _ : Fin d => sk) (fun _ : Fin d => tk) with hb_def
  have hsm : 0 < sm := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have htm : 0 < tm := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hsk : 0 < sk := akhc_sigmaBarSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS
    hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have htk : 0 < tk := akhc_sigmaBarStarInvSeq_pos_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hΘm : 1 ≤ sm * tm := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 m
  have hΘk : 1 ≤ sk * tk := akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k
  have hs : sm ≤ sk := akhc_antitone_sigmaBarSeq_of_P2 hnu hPrefix hJ2 hJ4 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have ht : tm ≤ tk := akhc_antitone_sigmaBarStarInvSeq_of_P2 hnu hPrefix hJ2 gamma H D m2
    PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkm
  have hθk : SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k = sk * tk := rfl
  have hw : ∀ α, 0 < w α := fun α => by cases α <;> simp [hw_def, hsm, htm]
  have hb : ∀ α, 0 < b α := fun α => by cases α <;> simp [hb_def, hsk, htk]
  have hcomp : ∀ α, w α ≤ b α ^ 2 * w (Sum.swap α) := by
    intro α
    cases α with
    | inl i => exact akhcProtoD_comp hsm htm hΘm hs
    | inr i =>
      have hΘm' : 1 ≤ tm * sm := by linarith only [hΘm, mul_comm sm tm]
      exact akhcProtoD_comp htm hsm hΘm' ht
  have hAnS : ∀ α β, blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (coefficientCutoff nu omega L).toCoeffField) α β =
      blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (coefficientCutoff nu omega L).toCoeffField) β α :=
    isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L _
  have hAbarS : ∀ α β,
      blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField))
          α β =
      blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField))
          β α := by
    intro α β
    rw [akhc_blockMatEntry_descendantsAverageBlockMat,
      akhc_blockMatEntry_descendantsAverageBlockMat]
    congr 1
    exact Finset.sum_congr rfl fun R _ =>
      isSymmetricBlockMat_coarseBlockMatrix_coefficientCutoff hnu omega L R α β
  have hsubL : BlockMatLoewnerLE
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ))) (coefficientCutoff nu omega L).toCoeffField)
      (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField)) := by
    have h :=
      Book.Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_of_aelocallyUniformlyEllipticField
        (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L)
        (show ((k : ℤ)) ≤ (n : ℤ) by exact_mod_cast hkn)
    have hdepth : Int.toNat ((n : ℤ) - (k : ℤ)) = n - k := by omega
    rw [hdepth] at h
    exact h
  have hmain := akhcProtoC_quenched_abstract hw hb hcomp hAnS hAbarS
    (akhcProtoD_qf_le_of_loewner hsubL) (akhcProtoD_doubled_cutoff hnu omega L _)
  have hB : ∀ α β, blockMatEntry
      (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β =
        if α = β then b α else 0 := by
    intro α β
    rw [akhc_annealedBlockMatrix_originCube_eq_blockDiag hnu L hJ4 (k : ℤ),
      akhcProtoD_blockMatEntry_blockDiag]
    rfl
  have hX : akhcProtoLinearAvg nu P L k n omega = fun α β =>
      blockMatEntry (descendantsAverageBlockMat (originCube d (n : ℤ)) (n - k)
        (fun R => coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField))
          α β - if α = β then b α else 0 := by
    funext α β
    unfold akhcProtoLinearAvg
    rw [akhc_avg_sub_const, hB]
  have hBW : akhcSubDiag (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) w =
      fun α β => (if α = β then b α else 0) - if α = β then w α else 0 := by
    funext α β
    unfold akhcSubDiag
    rw [hB]
  have hε : 0 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 := by
    rw [hθk]
    exact sub_nonneg.mpr hΘk
  have hT3 : akhcRelFrobNorm w
      (fun α β => (if α = β then b α else 0) - if α = β then w α else 0) ≤
      2 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) := by
    rw [← hBW]
    exact akhcProtoD_relFrobNorm_le_of_sq_le hε
      (akhcProto_relFrobSq_annealedBlockMatrix_sub_le_of_P2 hnu hPrefix hJ2 hJ4 gamma H D
        m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth
        hP2 hkm)
  have hratio := akhcProtoD_diag_ratio_le hsm htm hsk htk hΘm hΘk hs ht
  have hT1 : akhcRelFrobNorm w
      (fun α β => if α = β then b α - (b (Sum.swap α))⁻¹ else 0) ≤
      2 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) := by
    refine akhcProtoD_relFrobNorm_le_of_sq_le hε
      (akhcProto_relFrobSq_le_two_mul_d_mul_sq_of_diag_bound
        (fun α β hαβ => ite_eq_right hαβ) fun α => ?_)
    rw [ite_eq_left rfl, hθk]
    cases α with
    | inl i => exact hratio.1
    | inr i => exact hratio.2
  have hLHS : akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
      (coefficientCutoff nu omega L).toCoeffField) w = fun α β =>
        blockMatEntry (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) α β - if α = β then w α else 0 := rfl
  rw [hLHS, hX]
  linarith only [hmain, hT1, hT3]

/-- **`hVarianceProto` of `ProtoB.lean`, proved**, with the source's
normalizer `w = diag(bfAhom_L(cu_m))`, for `k ≤ n` and `k ≤ m`. -/
theorem akhcProtoD_hVarianceProto {k n m : ℕ} (hkn : k ≤ n) (hkm : k ≤ m) :
    ∀ omega : ShellSeq d, akhcRelFrobNorm
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
            (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ≤
      16 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) +
        4 * akhcRelFrobNorm
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
          (akhcProtoLinearAvg nu P L k n omega) := by
  intro omega
  have h := akhcProtoD_variance_proto_sharp hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS
    pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn hkm omega
  have hΘ := SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4
    gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
    hGrowth hP2 k
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h12 : 0 ≤ 12 * (d : ℝ) *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) :=
    mul_nonneg (by linarith only [hd]) (sub_nonneg.mpr hΘ)
  have hN := akhc_relFrobNorm_nonneg
    (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
      (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
    (akhcProtoLinearAvg nu P L k n omega)
  linarith only [h, h12, hN]

/-- **`e.variance.proto`'s quadratic form with `hVarianceProto` discharged**:
`akhcProto_variance_quadratic` at `w = diag(bfAhom_L(cu_m))`, `k ≤ n`,
`k ≤ m`. The only remaining input is the integrability `hLinInt` of the
squared linear average, which `ProtoB.lean` already carried. -/
theorem akhcProtoD_variance_quadratic {k n m : ℕ} (hkn : k ≤ n) (hkm : k ≤ m)
    (hLinInt : Integrable (fun omega => akhcRelFrobSq
      (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
        (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
      (akhcProtoLinearAvg nu P L k n omega)) P.toMeasure) :
    Integrable (fun omega => akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m)))) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq
        (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
          (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
        (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField)
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))) ∂P.toMeasure ≤
      512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * ∫ omega, akhcRelFrobSq
          (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
            (fun _ : Fin d => sigmaBarStarInvSeq nu L P m))
          (akhcProtoLinearAvg nu P L k n omega) ∂P.toMeasure := by
  have hw : ∀ α, 0 < (Sum.elim (fun _ : Fin d => sigmaBarSeq nu L P m)
      (fun _ : Fin d => sigmaBarStarInvSeq nu L P m) : BlockCoord d → ℝ) α := by
    intro α
    cases α with
    | inl i =>
      exact SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarSeq_pos_of_P2 hnu hJ4
        gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS
        hpPsiS hGrowth hP2 m
    | inr i =>
      exact SuperdiffusionCLT.AKHC61.Carrier.akhc_sigmaBarStarInvSeq_pos_of_P2
        hnu hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne
        hKPsiS hpPsiS hGrowth hP2 m
  exact akhcProto_variance_quadratic hnu P L gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1
    hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn hw
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_one_le_thetaCutoff_of_P2 hnu hJ4 gamma H D
      m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 k)
    hLinInt
    (akhcProtoD_hVarianceProto hnu hPrefix hJ2 hJ4 gamma H D m2 PsiS KPsiS pPsiS hgamma0
      hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS hGrowth hP2 hkn hkm)

end Cutoff

end

end SuperdiffusionCLT.AKHC61.Variance
