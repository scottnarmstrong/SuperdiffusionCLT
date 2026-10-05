/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.AKHC61.Variance.Proto

/-!
# Package C5b, part 2: `e.variance.proto` and the quadratic form for `e.variance.again.prime`

Proof of `e.variance.proto` of [AK]. This file
states the quenched (pathwise) `W`-relative Frobenius-norm bound that is
`e.variance.proto` as a precisely named hypothesis, and derives from it,
using `Proto.lean`'s squaring machinery, exactly the quadratic-in-`(Θ̂_k - 1)`
expectation bound that `e.variance.again.prime` needs. The hypothesis is proved in
`ProtoD.lean` (`akhcProtoD_hVarianceProto`).

## The quenched bound (`hVarianceProto`)

The quenched bound (in the `akhcRelFrobNorm`/`akhcSubDiag` reading,
`w := diag(bfAhom_L(cu_m))`, using the normalization convention of `e.variance.HC`):

`|bfA(cu_n) - W|_w ≤ 16d(Θ̂_k - 1) + 4|avsum_z (bfA(z+cu_k) - bfAhom_k)|_w`

for `k ≤ n`. Proving it needs:

1. **subadditivity of `bfA`** — already available and used in `ThreeScaleB.lean`
   (`Homogenization.Book.Ch04.coarseBlockMatrix_le_descendantsAverageBlockMat_of_aelocallyUniformlyEllipticField`);
2. **subadditivity of `bfA_*⁻¹`** — the "starred twin" of item 1;
3. **the ordering `bfA_* ≤ bfA`** — not found anywhere in
   `CoarseGraining` under any name; not proved here;
4. **the sample-mean/harmonic-mean discard identity**: for the
   sample mean `M := avsum bfA_*(z+cu_k)` and harmonic mean
   `H := (avsum bfA_*⁻¹(z+cu_k))⁻¹`, and any symmetric `B̃`,
   `M = H + avsum[(bfA_*(z) - B̃) bfA_*⁻¹(z) (bfA_*(z) - B̃)] - (H - B̃)H⁻¹(H - B̃)`,
   discarding the last (nonnegative) term — a nontrivial multivariate matrix
   identity; not proved in this file;
5. **`bfA_*⁻¹ = R·bfA·R`** — available by *definition*
   (`Homogenization.coarseStarredBlockMatrixInv U a = Homogenization.blockReflect
   (Homogenization.coarseBlockMatrix U a)`, in `CoarseGraining/Definitions.lean`);
6. **`e.algebraic.add.error`** (the deterministic comparison of
   `bfAhom(cu_k)` with `bfAhom(cu_m)`, used to bound the cross terms) — proved
   as package E1 (`AKHC61.Step3.AlgebraicComparison`), used
   directly (not as a hypothesis) in `Proto.lean`'s
   `akhcProto_relFrobSq_annealedBlockMatrix_sub_le_of_P2`, which gives exactly
   the quadratic reading `|Ahom_k - W|²_w ≤ 2d(Θ̂_k - 1)²` that a full proof of
   `hVarianceProto` would need for its own deterministic term.

Items 3 and 4 are the substantial pieces, treated in `ProtoC.lean` and `ProtoD.lean`.
Items 1, 2, 5, and item 6 (via E1) are proved in `Proto.lean`.

## What this file proves

`akhcProto_variance_quadratic_of_pointwise`: **given** `hVarianceProto`, the
squared/expectation form
`E|bfA(cu_n) - W|²_w ≤ 512 d²(Θ̂_k - 1)² + 32 E|avsum(bfA(z+cu_k) - bfAhom_k)|²_w`
— exactly node 50's shape, `k` left free so package E2 can instantiate
`k := n - ℓ(n)` with `ℓ(n) = ⌈L₁ log(L₂ n)⌉` (`akhcProtoLag`, at the end of
this file).
-/

@[expose] public section

namespace SuperdiffusionCLT.AKHC61.Variance

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed

noncomputable section

variable {d : ℕ}

/-- The linear descendant average term appearing on both sides of
`e.variance.proto` and in node 50's target: `avsum_z (bfA(z+cu_k) -
bfAhom_k)`, entrywise, exactly as used in `ThreeScaleC.lean`'s `hLinInt`. -/
def akhcProtoLinearAvg [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
    (k n : ℕ) (omega : ShellSeq d) : BlockCoord d → BlockCoord d → ℝ :=
  fun α β => ((descendantsAtDepth (originCube d (n : ℤ)) (n - k)).card : ℝ)⁻¹ *
    ∑ R ∈ descendantsAtDepth (originCube d (n : ℤ)) (n - k),
      (blockMatEntry (coarseBlockMatrix (cubeSet R) (coefficientCutoff nu omega L).toCoeffField)
          α β -
        blockMatEntry (annealedBlockMatrix nu L P (cubeSet (originCube d (k : ℤ)))) α β)

/-- **The squared/expectation form of `e.variance.proto`, given the quenched
bound as a hypothesis.** This is what node 50/package E2 consumes: `k` and
`n` are free with `k ≤ n`, so E2 instantiates `k := n - ℓ(n)`. -/
theorem akhcProto_variance_quadratic_of_pointwise [NeZero d] {nu : ℝ}
    (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ) {k n : ℕ}
    {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hTheta1 : 1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k)
    (hInt : ∀ (Q : TriadicCube d) (α β : BlockCoord d), Integrable (fun omega =>
      blockMatEntry (coarseBlockMatrix (cubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField) α β) P.toMeasure)
    (hLinInt : Integrable
      (fun omega => akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega)) P.toMeasure)
    (hVarianceProto : ∀ omega : ShellSeq d, akhcRelFrobNorm w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ≤
      16 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) +
        4 * akhcRelFrobNorm w (akhcProtoLinearAvg nu P L k n omega)) :
    Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure ≤
      512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * ∫ omega, akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega) ∂P.toMeasure := by
  have hA : (0:ℝ) ≤ 16 * (d : ℝ) *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) := by
    have hd0 : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hthm1 : (0:ℝ) ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1 :=
      sub_nonneg.mpr hTheta1
    have h16d : (0:ℝ) ≤ 16 * (d : ℝ) := by linarith only [hd0]
    exact mul_nonneg h16d hthm1
  have hptwise : ∀ omega : ShellSeq d, akhcRelFrobSq w (akhcSubDiag
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w) ≤
      512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega) := by
    intro omega
    have hB : (0:ℝ) ≤ 4 * akhcRelFrobNorm w (akhcProtoLinearAvg nu P L k n omega) := by
      have := akhc_relFrobNorm_nonneg w (akhcProtoLinearAvg nu P L k n omega)
      linarith only [this]
    have hstep := akhc_relFrobSq_le_two_sq_add_two_sq_of_relFrobNorm_le hw
      (akhcSubDiag (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w) hA hB (hVarianceProto omega)
    have heq : akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega) =
        akhcRelFrobNorm w (akhcProtoLinearAvg nu P L k n omega) ^ 2 :=
      akhc_relFrobSq_eq_sq_relFrobNorm hw _
    rw [heq]
    nlinarith only [hstep]
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
  have hRHSInt : Integrable (fun omega => 512 * (d : ℝ) ^ 2 *
      (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega)) P.toMeasure :=
    (integrable_const _).add (hLinInt.const_mul _)
  have hLHSInt : Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
      (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
        (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure := by
    refine hRHSInt.mono' hLHSmeas (Filter.Eventually.of_forall fun omega => ?_)
    rw [Real.norm_of_nonneg (akhc_relFrobSq_nonneg hw _)]
    exact hptwise omega
  refine ⟨hLHSInt, ?_⟩
  calc ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure
      ≤ ∫ omega, (512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
            32 * akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega)) ∂P.toMeasure :=
        integral_mono hLHSInt hRHSInt hptwise
    _ = 512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * ∫ omega, akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega) ∂P.toMeasure := by
        rw [integral_add (integrable_const _) (hLinInt.const_mul _), integral_const,
          integral_const_mul]
        simp

/-- **`e.variance.proto`'s quadratic form, discharging entrywise integrability
from the (P2') clause of the main statement (package A1), matching the pattern
of `ThreeScaleC.lean`'s `akhc_variance_threeScale`.** -/
theorem akhcProto_variance_quadratic [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (L : ℕ)
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
    {k n : ℕ} (_hkn : k ≤ n) {w : BlockCoord d → ℝ} (hw : ∀ α, 0 < w α)
    (hTheta1 : 1 ≤ SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k)
    (hLinInt : Integrable
      (fun omega => akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega)) P.toMeasure)
    (hVarianceProto : ∀ omega : ShellSeq d, akhcRelFrobNorm w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ≤
      16 * (d : ℝ) * (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) +
        4 * akhcRelFrobNorm w (akhcProtoLinearAvg nu P L k n omega)) :
    Integrable (fun omega => akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w)) P.toMeasure ∧
    ∫ omega, akhcRelFrobSq w (akhcSubDiag
        (coarseBlockMatrix (cubeSet (originCube d (n : ℤ)))
          (coefficientCutoff nu omega L).toCoeffField) w) ∂P.toMeasure ≤
      512 * (d : ℝ) ^ 2 *
          (SuperdiffusionCLT.Frozen.Section4.thetaCutoff nu L P k - 1) ^ 2 +
        32 * ∫ omega, akhcRelFrobSq w (akhcProtoLinearAvg nu P L k n omega) ∂P.toMeasure :=
  akhcProto_variance_quadratic_of_pointwise P L hw hTheta1
    (SuperdiffusionCLT.AKHC61.Carrier.akhc_integrable_blockMatEntry_of_P2 d hnu P L
      gamma H D m2 PsiS KPsiS pPsiS hgamma0 hgamma1 hH hD hPsiSMono hPsiSOne hKPsiS hpPsiS
      hGrowth hP2)
    hLinInt hVarianceProto

/-! ## The lag, ready for package E2 to instantiate `k := n - ℓ(n)` -/

/-- `ℓ(n) := ⌈L₁ log(L₂ n)⌉`, the lag from `e.variance.again.prime`
(`n - ⌈L₁ log(L₂ n)⌉`). Package E2 instantiates
`akhcProto_variance_quadratic` with `k := n - akhcProtoLag L1 L2 n`. -/
noncomputable def akhcProtoLag (L1 L2 : ℝ) (n : ℕ) : ℕ :=
  ⌈L1 * Real.log (L2 * n)⌉₊

end

end SuperdiffusionCLT.AKHC61.Variance
