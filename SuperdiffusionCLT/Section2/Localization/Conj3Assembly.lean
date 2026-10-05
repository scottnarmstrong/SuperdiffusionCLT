/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.Conj3WindowRoute
public import SuperdiffusionCLT.Section2.Localization.Conj3Degenerate
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerClause
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerPremises
public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerBridges
public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly

/-!
# The window-amplitude assembly of the third localization conjunct

The degenerate scale `m = L` of `e.localization.minimizers` is proved with no
residual by `cutoffLocalizationConjunct3_selfCoincident`
(`Conj3Degenerate.lean`).  This module supplies the window-amplitude ingredients for the
remaining scale `m < L`, using the centered cutoff-pair perturbation bound of
`Conj3WindowRoute.lean`.

The window amplitude `cutoffPairEtaWindow` is an explicit **product** with the window,
so that the amplitude premises reduce to a single window-smallness condition
`cutoffPairThetaWindow ≤ 1 / 8` together with the constant domination
`(45 / 4) c(d) ≤ C`; neither mentions a gauge amplitude.

## Main results

* `vecNormSq_centeredFiniteShellIncrement_le_window`: the pointwise bound on the centered
  finite shell increment at the window amplitude.
* `relSkewBound_centeredCutoffPair_window`,
  `blockQuadraticSandwich_centeredCutoffPair_window`: the pointwise perturbation
  bounds at the window amplitude.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The pointwise quadratic bound at the window -/

/-- **The pointwise quadratic bound of the centered finite shell increment at
the window**: at every point of a Chapter 2 domain inside `cu_n` the quadratic
form of the volume-average centered increment is bounded by the square of the
window bound `matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le_window`,
i.e. `(matrixOperatorNorm_diamConst d * 3^n * W)^2`, times `|w|^2`. -/
theorem vecNormSq_centeredFiniteShellIncrement_le_window
    (omega : ShellSeq d) (m L n : ℕ)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) (w : Vec d) :
    vecNormSq (matVecMul (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) w) ≤
      (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        anchorDerivSup m L n omega) ^ 2 * vecNormSq w := by
  have hM : 0 ≤ matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      anchorDerivSup m L n omega :=
    mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (anchorDerivSup_nonneg m L n omega)
  have hop :=
    matrixOperatorNorm_finiteShellIncrement_sub_volumeAverage_le_window omega m L n U
      hU x hx
  refine (vecNormSq_matVecMul_le_operatorNormSq_mul_vecNormSq
    (finiteShellIncrement omega m L x -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y)) w).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg w)
  exact pow_le_pow_left₀ (matrixOperatorNorm_nonneg _) hop 2

/-! ## The pointwise relative skew bound at the window amplitude -/

/-- **The pointwise relative skew bound at the window amplitude**: the
perturbation between the two-cutoff-centered field and the level-`m` cutoff
field has symmetric part `ν Id` and satisfies the bilinear estimate with
`θ = cutoffPairThetaWindow`.  This is the window counterpart of
`relSkewBound_centeredCutoffPair` (`CenteredIncrementQuadratic`), whose gauge
constant is replaced by the window. -/
theorem relSkewBound_centeredCutoffPair_window
    (nu : ℝ) (omega : ShellSeq d) (m L n : ℕ) (hmL : m ≤ L) (hnu : 0 < nu)
    (U : Book.Ch02.Domain d)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ)))
    (x : Vec d) (hx : x ∈ (U : Set (Vec d))) (p r : Vec d) :
    2 * vecDot r (matVecMul
        (centeredPairField nu omega m L (U : Set (Vec d)) x -
          (coefficientCutoff nu omega m).toCoeffField x) p) ≤
      cutoffPairThetaWindow d nu n m L omega *
        (vecDot p (matVecMul
            (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) p) +
          vecDot r (matVecMul
            (symmPart ((coefficientCutoff nu omega m).toCoeffField x)) r)) := by
  have hM0 : 0 ≤ matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
      anchorDerivSup m L n omega :=
    mul_nonneg (mul_nonneg (matrixOperatorNorm_diamConst_nonneg d)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) n))
      (anchorDerivSup_nonneg m L n omega)
  have hsplit : centeredPairField nu omega m L (U : Set (Vec d)) x -
      (coefficientCutoff nu omega m).toCoeffField x =
    finiteShellIncrement omega m L x -
      volumeAverageMat (U : Set (Vec d))
        (fun y => finiteShellIncrement omega m L y) := by
    rw [show centeredPairField nu omega m L (U : Set (Vec d)) x =
        (coefficientCutoff nu omega L).toCoeffField x -
          volumeAverageMat (U : Set (Vec d))
            (fun y => finiteShellIncrement omega m L y) from rfl,
      ← coefficientCutoff_toCoeffField_sub nu omega hmL x]
    abel
  rw [hsplit]
  have hnorm : ∀ w : Vec d,
      vecNormSq (matVecMul (finiteShellIncrement omega m L x -
        volumeAverageMat (U : Set (Vec d))
          (fun y => finiteShellIncrement omega m L y)) w) ≤
      (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        anchorDerivSup m L n omega) ^ 2 * vecNormSq w :=
    vecNormSq_centeredFiniteShellIncrement_le_window omega m L n U hU x hx
  have hsymm : symmPart ((coefficientCutoff nu omega m).toCoeffField x) =
      nu • (1 : Mat d) :=
    symmPart_coefficientCutoff nu omega m x
  rw [hsymm]
  simpa only [cutoffPairThetaWindow] using
    relSkewBound_of_symmPart_eq_smul_one hnu hM0 rfl hnorm p r

/-! ## The anti-symmetry of the cutoff-pair perturbation -/

/-- A difference of two matrices with the same symmetric part `ν Id` is
anti-symmetric. -/
private theorem matTranspose_sub_of_symmPart_eq_assembly {nu : ℝ} {X Y : Mat d}
    (hx : symmPart X = nu • (1 : Mat d)) (hy : symmPart Y = nu • (1 : Mat d)) :
    matTranspose (X - Y) = -(X - Y) := by
  ext i k
  have hxi := congrFun (congrFun hx i) k
  have hxk := congrFun (congrFun hx k) i
  have hyi := congrFun (congrFun hy i) k
  have hyk := congrFun (congrFun hy k) i
  simp only [symmPart, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] at hxi hxk
  simp only [symmPart, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul] at hyi hyk
  show X k i - Y k i = -(X i k - Y i k)
  linarith only [hxi, hxk, hyi, hyk]

/-- The perturbation of the cutoff pair at `x`, `â x - a_m x`, is
anti-symmetric: both fields have symmetric part `ν Id`. -/
private theorem matTranspose_centeredPairSub_assembly (nu : ℝ) (omega : ShellSeq d)
    (m L : ℕ) (U : Set (Vec d)) (x : Vec d) :
    matTranspose (centeredPairField nu omega m L U x -
        (coefficientCutoff nu omega m).toCoeffField x) =
      -(centeredPairField nu omega m L U x -
        (coefficientCutoff nu omega m).toCoeffField x) :=
  matTranspose_sub_of_symmPart_eq_assembly
    (symmPart_centeredPairField_eq_smul_one nu omega m L U x)
    (symmPart_coefficientCutoff nu omega m x)

/-! ## The pointwise ratio sandwich at the window amplitude -/

/-- **The two pointwise ratio sandwiches at the centered cutoff pair, at the
window amplitude `cutoffPairEtaWindow`**: the block form of `a_m` is dominated
by that of `â` and conversely, each with the relative amplitude
`cutoffPairEtaWindow`. -/
theorem blockQuadraticSandwich_centeredCutoffPair_window
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (n m L : ℕ) (hmL : m ≤ L)
    (hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) :
    ∀ x : Vec d, x ∈ (U : Set (Vec d)) →
      (∀ W : BlockVec d,
        blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
              ((coefficientCutoff nu omega m).toCoeffField x)) W) ≤
          blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
                (centeredPairField nu omega m L (U : Set (Vec d)) x)) W) +
            cutoffPairEtaWindow d nu n m L omega *
              blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
                (centeredPairField nu omega m L (U : Set (Vec d)) x)) W)) ∧
      (∀ W : BlockVec d,
        blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
              (centeredPairField nu omega m L (U : Set (Vec d)) x)) W) ≤
          blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
                ((coefficientCutoff nu omega m).toCoeffField x)) W) +
            cutoffPairEtaWindow d nu n m L omega *
              blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
                ((coefficientCutoff nu omega m).toCoeffField x)) W)) := by
  intro x hx
  have hEq : (coefficientCutoff nu omega m).toCoeffField x +
      (centeredPairField nu omega m L (U : Set (Vec d)) x -
        (coefficientCutoff nu omega m).toCoeffField x) =
    centeredPairField nu omega m L (U : Set (Vec d)) x := by
    simp only [centeredPairField]
    abel
  have hH := matTranspose_centeredPairSub_assembly nu omega m L (U : Set (Vec d)) x
  have hθ := cutoffPairThetaWindow_nonneg nu hnu n m L omega
  have hb := relSkewBound_centeredCutoffPair_window nu omega m L n hmL hnu U hU x hx
  have hA := isEllipticMatrix_coefficientCutoff_domain U nu hnu omega m x hx
  have hAH : IsEllipticMatrix nu
      (((d : ℝ) * (d : ℝ) * centeredPairEntryBound U nu omega m L ^ 2 + nu ^ 2) /
        nu)
      ((coefficientCutoff nu omega m).toCoeffField x +
        (centeredPairField nu omega m L (U : Set (Vec d)) x -
          (coefficientCutoff nu omega m).toCoeffField x)) := by
    rw [hEq]
    exact isEllipticMatrix_centeredPairField_domain U nu hnu omega m L hmL x hx
  refine ⟨fun W => ?_, fun W => ?_⟩
  · have h0 : blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
          ((coefficientCutoff nu omega m).toCoeffField x)) W) ≤
      (1 + cutoffPairEtaWindow d nu n m L omega) *
        blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
          ((coefficientCutoff nu omega m).toCoeffField x +
            (centeredPairField nu omega m L (U : Set (Vec d)) x -
              (coefficientCutoff nu omega m).toCoeffField x))) W) := by
      exact blockQuadratic_le_blockQuadratic_add_skew hAH hH hθ hb W
    rw [hEq] at h0
    exact h0.trans (le_of_eq (by ring))
  · have h0 : blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
          ((coefficientCutoff nu omega m).toCoeffField x +
            (centeredPairField nu omega m L (U : Set (Vec d)) x -
              (coefficientCutoff nu omega m).toCoeffField x))) W) ≤
      (1 + cutoffPairEtaWindow d nu n m L omega) *
        blockVecDot W (blockMatVecMul (blockMatrixOfCoeff
          ((coefficientCutoff nu omega m).toCoeffField x)) W) := by
      exact blockQuadratic_add_skew_le hA hH hθ hb W
    rw [hEq] at h0
    exact h0.trans (le_of_eq (by ring))

/-! ## The block premise at the window amplitude -/

/-! ## Conjunct 3 at the window amplitude with every input named -/

/-! ## The amplitude bookkeeping at the window amplitude -/

/-! ## The full conjunct: the degenerate case and the window route combined -/

end

end SuperdiffusionCLT.Section2.Localization
