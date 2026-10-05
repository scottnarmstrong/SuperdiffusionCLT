/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.DeterministicConsume
public import SuperdiffusionCLT.Section2.Localization.SkewQuadratic
public import SuperdiffusionCLT.Section2.Localization.Conj3CoincidentBranch
public import SuperdiffusionCLT.Section2.Localization.CutoffLocalizationAssembly
public import SuperdiffusionCLT.Section2.Localization.LargeEtaPrinted
public import Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# The third conjunct, proved from the deterministic route

`CutoffLocalizationAssembly.cutoff_localization_proved` consumes its third
conjunct as the hypothesis `hconj3`, and states it in the shape of the third
conjunct of `Frozen.Section2.cutoff_localization`.  This module prepares the
supply of `hconj3` (completed in `Conj3EndgameMinimizerEnergy`) at the constant
`localizationMaxConst d` that the assembly already chooses.

The route is the deterministic one.  At the coincident scale `m = L` the two
carriers coincide and the inequality is `0 ≤ 0`
(`Conj3CoincidentBranch.cutoffLocalizationConjunct3_coincidentBranch`).  At the
strict scale `m < L` the window amplitude `θ` of the cutoff pair is split:

* `θ ≥ 1 / 2`: the printed large-amplitude display at its amplitude-free form
  (`LargeEtaPrinted.printed_largeEta_energy_coarse`), `⨍ ν‖∇u − ∇v‖² ≤
  4 (P·𝐀(U;a_m)P + P·𝐀(U;ã)P)`, with the two coarse loading quadratics turned
  into the bracket of the statement by `coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot`;
* `θ ≤ 1 / 2`: the deterministic chain.  Its block-level bound
  (`Conj3EndgameMinimizerEnergy.conj3DeterministicFromBlock_min_cutoff_minimizerEnergy`) is
  read at the **minimizers' own energies** — the `η²` term of the pure-skew piece is
  bounded at the perturbed minimizer's energy rather than at the constant
  loading, which is the printed absorption in the proof of
  `e.minimizers.gradient.from.block` — and the block
  bound is transferred to the gradient difference by `e.iden.AP`.

The transfer is the point of the module.  `e.iden.AP`
(`BlockScalarCorrespondence.blockVecDot_blockMatrixOfCoeff_adjointPair`) applied
to the adjoint pair of the two slope differences, composed with the bridge
identity (`LocalizationCore.adjointPair_gradDiff_eq_two_smul_split`), identifies
the block quadratic of `Z − Z̃₀` with `ν / 2` times the sum of the two squared
gradient differences, at the carriers, whose symmetric part is exactly
`ν Id`.  That identity — not a triangle inequality — is what spans the gap
between the deterministic route's block field and the gradient
conclusion.

Everything is averaged, and every constant is that of the statement:
`localizationMaxConst d ≥ 16 * matrixOperatorNorm_diamConst d`, which is what
both branches require.  No remainder slot is introduced: the centered one is
refuted at `η = 0`, the shifted one is true but too weak, and the engine built
on it is false.  Dimension one is out of scope; the binders `[NeZero d]`
and `2 ≤ d` of the statement are carried verbatim.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The localization constant dominates the route constant `16 c(d)` -/

/-- **`16 * matrixOperatorNorm_diamConst d ≤ localizationMaxConst d`.**  The
localization constant dominates `localizationConst d`, the quadratic `2 · 16384 · (K +
K²)` in `K = 16384 * c(d)`; its linear term alone dominates `16 c(d)` for
`c(d) ≥ 0`.  The constant `16` is the one the two branches of this module need (a weakening
of `25 / 2`). -/
theorem sixteen_mul_diamConst_le_localizationMaxConst (d : ℕ) :
    16 * matrixOperatorNorm_diamConst d ≤ localizationMaxConst d := by
  have hseal : localizationConst d ≤ localizationMaxConst d := by
    rw [localizationMaxConst]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  refine le_trans ?_ hseal
  have hc : 0 ≤ matrixOperatorNorm_diamConst d := matrixOperatorNorm_diamConst_nonneg d
  have h1 : gammaTriangleConst (1 : ℝ) = 16384 :=
    gammaTriangleConst_eq_of_one_le (le_refl (1 : ℝ))
  have h2 : gammaTriangleConst (2 : ℝ) = 16384 :=
    gammaTriangleConst_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [localizationConst, gaugeAmplitudeConst, h1, h2]
  have hgoal : 2 * 16384 *
      ((matrixOperatorNorm_diamConst d * 16384) +
        (matrixOperatorNorm_diamConst d * 16384) ^ 2) =
      32768 * (16384 * matrixOperatorNorm_diamConst d) +
        32768 * (matrixOperatorNorm_diamConst d * 16384) ^ 2 := by
    ring
  rw [hgoal]
  have hconst : (0 : ℝ) ≤ 32768 * 16384 - 16 := by norm_num
  have hlin : 16 * matrixOperatorNorm_diamConst d ≤
      32768 * (16384 * matrixOperatorNorm_diamConst d) := by
    have hmul : 0 ≤ matrixOperatorNorm_diamConst d * (32768 * 16384 - 16) :=
      mul_nonneg hc hconst
    linarith only [hmul]
  have hsq : (0 : ℝ) ≤ 32768 * (matrixOperatorNorm_diamConst d * 16384) ^ 2 := by
    positivity
  linarith only [hlin, hsq]

/-! ## The `e.iden.AP` bridge: the block field against the gradient difference

`BlockScalarCorrespondence.blockVecDot_blockMatrixOfCoeff_adjointPair` is the
pointwise identity `e.iden.AP`; `LocalizationCore.adjointPair_gradDiff_eq_two_smul_split`
identifies the adjoint pair of the two slope differences with twice the print's
`Z − Z̃₀`.  Composing them gives the transfer this module needs: at the
carriers the block quadratic of `Z − Z̃₀` is exactly `ν / 2` times the sum of the
two squared gradient differences.  No triangle inequality is used, and no
remainder slot is introduced. -/

/-- The bridge identity's skew-correction slot, at the route's carriers, is the
route's pure-skew piece.  A definitional identification of the two slots of the
print's `Z̃₁`. -/
theorem skewCorrectionField_apply_eq_conj3PureSkewPiece {d : ℕ} (U : Book.Ch02.Domain d)
    (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) (x : Vec d) :
    skewCorrectionField U (levelMCoeffOn U nu hnu omega m)
        (centeredPairCoeffOn U nu hnu omega m L hmL) p q u x =
      conj3PureSkewPiece U nu hnu omega m L hmL p q u x :=
  rfl

/-- **`e.iden.AP` at the route's carriers.**  The block quadratic of the print's
`Z − Z̃₀` is `ν / 2` times the sum of the two squared gradient differences of the
carriers and of their transpose response maximizers.  The symmetric part
`s = ν Id` is what makes the printed `2 e · s e` a `ν`-multiple of `‖e‖²`. -/
theorem conj3SkewFreeDifference_pointwise {d : ℕ} (U : Book.Ch02.Domain d) (nu : ℝ)
    (hnu : 0 < nu) (omega : ShellSeq d) (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d))) (U : Set (Vec d)))
    (x : Vec d) :
    averagedBlockQuadratic ((coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL p q v u x) =
      (1 / 2 : ℝ) * nu *
        (vecNormSq (v.toH1.grad x - u.toH1.grad x) +
          vecNormSq
            ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
              (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
                p (-q)).toH1.grad x)) := by
  have hskew : ∀ y : Vec d, matTranspose
      ((centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField y -
        (levelMCoeffOn U nu hnu omega m).toCoeffField y) =
      -((centeredPairCoeffOn U nu hnu omega m L hmL).toCoeffField y -
        (levelMCoeffOn U nu hnu omega m).toCoeffField y) := by
    intro y
    have h := conj3SkewRemainderField_skew nu omega m L (U : Set (Vec d)) y
    simpa only [conj3SkewRemainderField, levelMCoeffOn_toCoeffField,
      centeredPairCoeffOn_toCoeffField] using h
  have hpair := adjointPair_gradDiff_eq_two_smul_split (levelMCoeffOn U nu hnu omega m)
    (centeredPairCoeffOn U nu hnu omega m L hmL) p q v u hskew x
  have hsplit := congrFun (conj3SkewFreeDifference_eq_split U nu hnu omega m L hmL p q v u) x
  have hD : conj3SkewFreeDifference U nu hnu omega m L hmL p q v u x =
      (1 / 2 : ℝ) • (((v.toH1.grad x - u.toH1.grad x) +
          ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
            (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
              p (-q)).toH1.grad x),
        matVecMul ((levelMCoeffOn U nu hnu omega m).toCoeffField x)
            (v.toH1.grad x - u.toH1.grad x) -
          matVecMul (matTranspose ((levelMCoeffOn U nu hnu omega m).toCoeffField x))
            ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
              (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
                p (-q)).toH1.grad x)) : BlockVec d) := by
    have h2 : (((v.toH1.grad x - u.toH1.grad x) +
          ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
            (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
              p (-q)).toH1.grad x),
        matVecMul ((levelMCoeffOn U nu hnu omega m).toCoeffField x)
            (v.toH1.grad x - u.toH1.grad x) -
          matVecMul (matTranspose ((levelMCoeffOn U nu hnu omega m).toCoeffField x))
            ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
              (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
                p (-q)).toH1.grad x)) : BlockVec d) =
        (2 : ℝ) • conj3SkewFreeDifference U nu hnu omega m L hmL p q v u x := by
      rw [hpair, hsplit,
        skewCorrectionField_apply_eq_conj3PureSkewPiece U nu hnu omega m L hmL p q u x]
      congr 1
    rw [h2, smul_smul]
    norm_num
  have hD' : conj3SkewFreeDifference U nu hnu omega m L hmL p q v u x =
      (1 / 2 : ℝ) • (((v.toH1.grad x - u.toH1.grad x) +
          ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
            (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
              p (-q)).toH1.grad x),
        matVecMul ((coefficientCutoff nu omega m).toCoeffField x)
            (v.toH1.grad x - u.toH1.grad x) -
          matVecMul (matTranspose ((coefficientCutoff nu omega m).toCoeffField x))
            ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
              (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
                p (-q)).toH1.grad x)) : BlockVec d) := by
    simpa only [levelMCoeffOn_toCoeffField] using hD
  have hkey := blockVecDot_half_adjointPair_eq_smul_vecNormSq
    ((coefficientCutoff nu omega m).toCoeffField x) hnu.ne'
    (symmPart_coefficientCutoff nu omega m x)
    (v.toH1.grad x - u.toH1.grad x)
    ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
      (transposeResponseMaximizer U (centeredPairCoeffOn U nu hnu omega m L hmL)
        p (-q)).toH1.grad x)
  rw [← hD'] at hkey
  simpa only [averagedBlockQuadratic, levelMCoeffOn_toCoeffField] using hkey

/-! ## The large-window branch of the third conjunct

The printed large-amplitude display in the proof of `e.minimizers.gradient.from.block`
is proved in amplitude-free
form by `LargeEtaPrinted.printed_largeEta_energy_coarse`: the averaged
`nu`-weighted squared gradient difference of the two carriers is at most
`4 (P·𝐀(U;a_m)P + P·𝐀(U;â_m^L)P)`.  By `e.Jaas.matform`
(`SlopeBoundRoute.coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot`) the
coarse bracket is exactly twice the response bracket, so the
conclusion follows as soon as the window amplitude pays for the constant:
`8 c(d) ≤ C θ`.  At the localization constant, `C ≥ 16 c(d)`, this holds for every
`θ ≥ 1 / 2`.  No response bridge, no gradient carrier and no slope datum enters:
the two coarse loading quadratics are the response bracket outright. -/

/-- The window amplitude against `nu`: `θ * ν = c(d) 3^n W`. -/
private theorem thetaWindow_mul_nu {d : ℕ} (nu : ℝ) (hnu : 0 < nu) (n m L : ℕ)
    (omega : ShellSeq d) :
    cutoffPairThetaWindow d nu n m L omega * nu =
      matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by
  rw [cutoffPairThetaWindow]
  field_simp

/-- `ν ^ (-(2 : ℝ)) = ν⁻¹ ν⁻¹`. -/
private theorem rpow_neg_two_local {nu : ℝ} (hnu : 0 < nu) :
    nu ^ (-(2 : ℝ)) = nu⁻¹ * nu⁻¹ := by
  rw [Real.rpow_neg hnu.le, Real.rpow_two, pow_two, mul_inv]

/-- **The window budget.**  From `8 c(d) ≤ C θ` — which `θ ≥ 1 / 2` and
`C ≥ 16 c(d)` give — follows `8 ν⁻¹ ≤ C ν^(-2) 3^n W`, the constant the large
branch needs.  The two exponentials are kept as `ν ^ (-(2 : ℝ))` and moved only
by associativity and commutativity, so no `rpow` arithmetic is consulted. -/
theorem eight_mul_inv_nu_le_of_thetaWindow_half {d : ℕ} {C nu : ℝ} (hnu : 0 < nu)
    (n m L : ℕ) (omega : ShellSeq d)
    (hC : 16 * matrixOperatorNorm_diamConst d ≤ C)
    (hθ : (1 / 2 : ℝ) ≤ cutoffPairThetaWindow d nu n m L omega) :
    8 * nu⁻¹ ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by
  have hc0 : 0 ≤ matrixOperatorNorm_diamConst d := matrixOperatorNorm_diamConst_nonneg d
  have hCn : 0 ≤ C := le_trans (by linarith only [hc0]) hC
  have hcne : matrixOperatorNorm_diamConst d ≠ 0 := by
    intro hzero
    have h0 : cutoffPairThetaWindow d nu n m L omega = 0 := by
      rw [cutoffPairThetaWindow, hzero]
      ring
    linarith only [hθ, h0]
  have hθν := thetaWindow_mul_nu nu hnu n m L omega
  have h8c : 8 * matrixOperatorNorm_diamConst d ≤
      C * cutoffPairThetaWindow d nu n m L omega := by
    have hprod : C * (1 / 2 : ℝ) ≤ C * cutoffPairThetaWindow d nu n m L omega :=
      mul_le_mul_of_nonneg_left hθ hCn
    linarith only [hC, hprod]
  have hmul : 8 * matrixOperatorNorm_diamConst d * nu ≤
      C * cutoffPairThetaWindow d nu n m L omega * nu :=
    mul_le_mul_of_nonneg_right h8c hnu.le
  have hcpos : 0 < matrixOperatorNorm_diamConst d := lt_of_le_of_ne hc0 (Ne.symm hcne)
  have hmul' : matrixOperatorNorm_diamConst d * (8 * nu) ≤
      matrixOperatorNorm_diamConst d *
        (C * ((3 : ℝ) ^ n * SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega)) := by
    have h1 : 8 * matrixOperatorNorm_diamConst d * nu =
        matrixOperatorNorm_diamConst d * (8 * nu) := by ring
    have h2 : C * cutoffPairThetaWindow d nu n m L omega * nu =
        matrixOperatorNorm_diamConst d *
          (C * ((3 : ℝ) ^ n * SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega)) := by
      calc C * cutoffPairThetaWindow d nu n m L omega * nu
          = C * (cutoffPairThetaWindow d nu n m L omega * nu) := by ring
        _ = C * (matrixOperatorNorm_diamConst d * (3 : ℝ) ^ n *
              SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega) := by
              rw [hθν]
        _ = matrixOperatorNorm_diamConst d *
              (C * ((3 : ℝ) ^ n *
                SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega)) := by ring
    rwa [h1, h2] at hmul
  have h8nu : 8 * nu ≤
      C * ((3 : ℝ) ^ n * SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega) :=
    le_of_mul_le_mul_left hmul' hcpos
  have hinv : 0 ≤ nu⁻¹ * nu⁻¹ := mul_nonneg (inv_nonneg.2 hnu.le) (inv_nonneg.2 hnu.le)
  have hstep : (8 * nu) * (nu⁻¹ * nu⁻¹) ≤
      (C * ((3 : ℝ) ^ n * SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega)) *
        (nu⁻¹ * nu⁻¹) :=
    mul_le_mul_of_nonneg_right h8nu hinv
  have hleft : (8 * nu) * (nu⁻¹ * nu⁻¹) = 8 * nu⁻¹ := by
    have hone : nu * nu⁻¹ = 1 := mul_inv_cancel₀ hnu.ne'
    calc (8 * nu) * (nu⁻¹ * nu⁻¹) = 8 * (nu * nu⁻¹) * nu⁻¹ := by ring
      _ = 8 * nu⁻¹ := by rw [hone]; ring
  rw [hleft] at hstep
  have hright : nu⁻¹ * nu⁻¹ = nu ^ (-(2 : ℝ)) := (rpow_neg_two_local hnu).symm
  rw [hright] at hstep
  calc 8 * nu⁻¹ ≤
      (C * ((3 : ℝ) ^ n * SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega)) *
        nu ^ (-(2 : ℝ)) := hstep
    _ = C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by ring

/-- **The third conjunct on the large-window branch `θ ≥ 1 / 2`.**  The
statement is the third conjunct of `Frozen.Section2.cutoff_localization`
(`e.localization.minimizers`) at its carriers and at every constant
dominating the localization constant.  The energy half is
`LargeEtaPrinted.printed_largeEta_energy_coarse` (amplitude free, its two
hypotheses being the two forward maximizers themselves), and the
conversion of its coarse loading bracket into the response bracket is the
identity `e.Jaas.matform`.  The branch condition `θ ≥ 1 / 2` is a case split of
the proof, not a hypothesis of the statement; the constant `c(d)` is
`matrixOperatorNorm_diamConst`, so the branch pays for itself at the
localization constant. -/
theorem cutoffLocalizationConjunct3_largeWindow (d : ℕ) (C : ℝ) (nu : ℝ)
    (hnu : 0 < nu) (_hnu1 : nu ≤ 1) (m n L : ℕ) (_hnm : n ≤ m) (_hmL : m ≤ L)
    (U : Book.Ch02.Domain d)
    (_hU : (U : Set (Vec d)) ⊆ openCubeSet (originCube d (n : ℤ))) (omega : ShellSeq d)
    (p q : Vec d)
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d)))
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
      (U : Set (Vec d)))
    (hu : ∀ w : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (centeredPairField nu omega m L (U : Set (Vec d))) p q u))
    (hv : ∀ w : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField
        (U : Set (Vec d)),
      volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q w) ≤
        volumeAverage (U : Set (Vec d))
          (scalarResponseIntegrand (U : Set (Vec d))
            (coefficientCutoff nu omega m).toCoeffField p q v))
    (hmLt : m < L) (hC : localizationMaxConst d ≤ C)
    (hθ : (1 / 2 : ℝ) ≤ cutoffPairThetaWindow d nu n m L omega) :
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega *
        (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) := by
  have hcoeff : 16 * matrixOperatorNorm_diamConst d ≤ C :=
    le_trans (sixteen_mul_diamConst_le_localizationMaxConst d) hC
  have hquad :=
    printed_largeEta_energy_coarse U nu hnu omega m L hmLt p q u v hu hv
  have hmatA := coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot U
    (levelMCoeffOn U nu hnu omega m) p q
  have hmatAt := coarseBlockVecDot_negLoading_eq_responseJ_add_vecDot U
    (centeredPairCoeffOn U nu hnu omega m L hmLt.le) p q
  rw [levelMCoeffOn_toCoeffField] at hmatA
  rw [centeredPairCoeffOn_toCoeffField] at hmatAt
  set S : ℝ := ResponseJ (U : Set (Vec d)) p q
        (centeredPairField nu omega m L (U : Set (Vec d))) +
      ResponseJ (U : Set (Vec d)) p q (coefficientCutoff nu omega m).toCoeffField +
      2 * vecDot p q with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact responseJ_centeredPair_add_nonneg nu hnu m L U omega p q
  have hgrad : volumeAverage (U : Set (Vec d))
        (fun x => nu * vecNormSq (u.toH1.grad x - v.toH1.grad x)) =
      nu * volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) :=
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul
      (U : Set (Vec d)) nu (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x))
  have hstep : nu * volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤ 8 * S := by
    rw [← hgrad, hSdef]
    refine hquad.trans ?_
    rw [hmatA, hmatAt]
    have hthis : 4 * ((2 * ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField + 2 * vecDot p q) +
          (2 * ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) + 2 * vecDot p q)) =
        8 * (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField + 2 * vecDot p q) := by
      ring
    rw [hthis]
  have hout : volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤ 8 * nu⁻¹ * S := by
    have hmul := mul_le_mul_of_nonneg_left hstep (inv_nonneg.2 hnu.le)
    have hcancel : nu⁻¹ * (nu * volumeAverage (U : Set (Vec d))
          (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x))) =
        volumeAverage (U : Set (Vec d))
          (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) := by
      rw [← mul_assoc, inv_mul_cancel₀ hnu.ne', one_mul]
    rw [hcancel] at hmul
    calc volumeAverage (U : Set (Vec d))
          (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤ nu⁻¹ * (8 * S) := hmul
      _ = 8 * nu⁻¹ * S := by ring
  have hbudget := eight_mul_inv_nu_le_of_thetaWindow_half hnu n m L omega hcoeff hθ
  calc volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤ 8 * nu⁻¹ * S := hout
    _ ≤ (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega) * S :=
        mul_le_mul_of_nonneg_right hbudget hSnn
    _ = C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega * S := by ring
    _ = C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega *
        (ResponseJ (U : Set (Vec d)) p q
            (centeredPairField nu omega m L (U : Set (Vec d))) +
          ResponseJ (U : Set (Vec d)) p q
            (coefficientCutoff nu omega m).toCoeffField +
          2 * vecDot p q) := by rw [hSdef]

/-! ## The graded transfer of `e.iden.AP`

The pointwise identity `conj3SkewFreeDifference_pointwise` is the print's
`e.iden.AP` at the route's carriers: the block quadratic of `Z − Z̃₀` is
`ν / 2` times the sum of the two squared gradient differences.  The two lemmas
below average it.  They are what turns a bound on a *block* quadratic into a
bound on the left-hand side of the conjunct, and they are the whole of the
block-quadratic-to-gradient-difference step: no triangle inequality, no
remainder slot and no maximality statement is consumed. -/

/-- The squared norm of a difference is symmetric in its two arguments. -/
private theorem vecNormSq_sub_swap {d : ℕ} (a b : Vec d) :
    vecNormSq (a - b) = vecNormSq (b - a) := by
  simp only [vecNormSq, vecDot, Pi.sub_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **`e.iden.AP` averaged.**  The averaged block quadratic of `Z − Z̃₀` is
`ν / 2` times the sum of the two averaged squared gradient differences.  The
averaging uses only that the integrands agree on `U` and the additivity and
scalar extraction of the normalized volume average on integrable functions;
integrability of the two squared gradient differences is
`CutoffMinimizerPremises.gradientDifference_integrableOn`. -/
theorem averagedBlockQuadraticOn_skewFreeDifference_eq_gradientSum {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) :
    averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL p q v u) =
      (1 / 2 : ℝ) * nu *
        (volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) +
          volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq
              ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
                (transposeResponseMaximizer U
                  (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x))) := by
  have hF : IntegrableOn (fun x => vecNormSq (v.toH1.grad x - u.toH1.grad x))
      (U : Set (Vec d)) volume := gradientDifference_integrableOn _ v u
  have hG : IntegrableOn (fun x => vecNormSq
      ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
        (transposeResponseMaximizer U
          (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x))
      (U : Set (Vec d)) volume := gradientDifference_integrableOn _ _ _
  have hswap : volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (v.toH1.grad x - u.toH1.grad x)) =
      volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) :=
    volumeAverage_congr_on U.measurableSet (fun x _ => vecNormSq_sub_swap _ _)
  unfold averagedBlockQuadraticOn
  rw [volumeAverage_congr_on (U := (U : Set (Vec d))) U.measurableSet
      (fun x _ => conj3SkewFreeDifference_pointwise U nu hnu omega m L hmL p q v u x),
    SuperdiffusionCLT.Section2.Estimates.Stream.volumeAverage_const_mul,
    volumeAverage_add_of_integrableOn hF hG, hswap]

/-- **The block energy dominates the gradient difference.**  Dropping the
transpose carriers' nonnegative squared gradient difference from the identity
above leaves `ν / 2` times the left-hand side of the conjunct inside the block quadratic
of `Z − Z̃₀`. -/
theorem gradientDifference_le_skewFreeDifference {d : ℕ}
    (U : Book.Ch02.Domain d) (nu : ℝ) (hnu : 0 < nu) (omega : ShellSeq d)
    (m L : ℕ) (hmL : m ≤ L) (p q : Vec d)
    (v : AHarmonicFunction (coefficientCutoff nu omega m).toCoeffField (U : Set (Vec d)))
    (u : AHarmonicFunction (centeredPairField nu omega m L (U : Set (Vec d)))
      (U : Set (Vec d))) :
    volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      (2 / nu) * averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL p q v u) := by
  have hGnn : (0 : ℝ) ≤ volumeAverage (U : Set (Vec d))
      (fun x => vecNormSq
        ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
          (transposeResponseMaximizer U
            (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x)) :=
    volumeAverage_nonneg_of_nonneg_on U.measurableSet (fun x _ => vecNormSq_nonneg _)
  have hkey := averagedBlockQuadraticOn_skewFreeDifference_eq_gradientSum U nu hnu omega
    m L hmL p q v u
  have hstep : (1 / 2 : ℝ) * nu * volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
      averagedBlockQuadraticOn (U : Set (Vec d))
        (fun x => (coefficientCutoff nu omega m).toCoeffField x)
        (conj3SkewFreeDifference U nu hnu omega m L hmL p q v u) := by
    rw [hkey]
    have h0 : (0 : ℝ) ≤ (1 / 2) * nu * volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq
          ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
            (transposeResponseMaximizer U
              (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x)) :=
      mul_nonneg (mul_nonneg (by norm_num) hnu.le) hGnn
    have hring : (1 / 2 : ℝ) * nu *
        (volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) +
          volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq
              ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
                (transposeResponseMaximizer U
                  (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x))) =
        (1 / 2 : ℝ) * nu * volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) +
          (1 / 2 : ℝ) * nu * volumeAverage (U : Set (Vec d))
            (fun x => vecNormSq
              ((transposeResponseMaximizer U (levelMCoeffOn U nu hnu omega m) p (-q)).toH1.grad x -
                (transposeResponseMaximizer U
                  (centeredPairCoeffOn U nu hnu omega m L hmL) p (-q)).toH1.grad x)) := by
      ring
    rw [hring]
    linarith only [h0]
  have hpos : (0 : ℝ) ≤ 2 / nu := div_nonneg (by norm_num) hnu.le
  have hle := mul_le_mul_of_nonneg_left hstep hpos
  have hcancel : (2 / nu) * ((1 / 2 : ℝ) * nu * volumeAverage (U : Set (Vec d))
      (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x))) =
      volumeAverage (U : Set (Vec d))
        (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) := by
    field_simp
  rwa [hcancel] at hle

/-! ## The localization constant dominates `32 c(d)` -/

/-- **`32 * matrixOperatorNorm_diamConst d ≤ localizationMaxConst d`.**  The
small-window branch pays its linear budget out of the same linear term of
`localizationConst d` that `sixteen_mul_diamConst_le_localizationMaxConst` uses; the
threshold of that branch is `C ≥ 32 c(d)`. -/
theorem thirtytwo_mul_diamConst_le_localizationMaxConst (d : ℕ) :
    32 * matrixOperatorNorm_diamConst d ≤ localizationMaxConst d := by
  have hseal : localizationConst d ≤ localizationMaxConst d := by
    rw [localizationMaxConst]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  refine le_trans ?_ hseal
  have hc : 0 ≤ matrixOperatorNorm_diamConst d := matrixOperatorNorm_diamConst_nonneg d
  have h1 : gammaTriangleConst (1 : ℝ) = 16384 :=
    gammaTriangleConst_eq_of_one_le (le_refl (1 : ℝ))
  have h2 : gammaTriangleConst (2 : ℝ) = 16384 :=
    gammaTriangleConst_eq_of_one_le (by norm_num : (1 : ℝ) ≤ 2)
  rw [localizationConst, gaugeAmplitudeConst, h1, h2]
  have hgoal : 2 * 16384 *
      ((matrixOperatorNorm_diamConst d * 16384) +
        (matrixOperatorNorm_diamConst d * 16384) ^ 2) =
      32768 * (16384 * matrixOperatorNorm_diamConst d) +
        32768 * (matrixOperatorNorm_diamConst d * 16384) ^ 2 := by
    ring
  rw [hgoal]
  have hconst : (0 : ℝ) ≤ 32768 * 16384 - 32 := by norm_num
  have hlin : 32 * matrixOperatorNorm_diamConst d ≤
      32768 * (16384 * matrixOperatorNorm_diamConst d) := by
    have hmul : 0 ≤ matrixOperatorNorm_diamConst d * (32768 * 16384 - 32) :=
      mul_nonneg hc hconst
    linarith only [hmul]
  have hsq : (0 : ℝ) ≤ 32768 * (matrixOperatorNorm_diamConst d * 16384) ^ 2 := by
    positivity
  linarith only [hlin, hsq]

/-! ## The window budget of the graded branch -/

/-- **The window budget.**  From `16 η c(d) ≤ C θ` follows
`16 η ν⁻¹ ≤ C ν^(-2) 3ⁿ W`.  The identity used is `θ ν = c(d) 3ⁿ W`
(`thetaWindow_mul_nu`), together with `ν ^ (-(2 : ℝ)) = ν⁻¹ ν⁻¹`; when
`c(d) = 0` the amplitude `θ`, and with it `η`, vanishes and the budget is
trivial.  `0 ≤ C` is supplied by the caller, who has `32 c(d) ≤ C`. -/
theorem sixteen_eta_window_budget {d : ℕ} {C nu : ℝ} (hnu : 0 < nu) (hCnn : 0 ≤ C)
    (n m L : ℕ) (omega : ShellSeq d)
    (hpay : 16 * cutoffPairEtaWindow d nu n m L omega * matrixOperatorNorm_diamConst d ≤
      C * cutoffPairThetaWindow d nu n m L omega) :
    16 * cutoffPairEtaWindow d nu n m L omega * nu⁻¹ ≤
      C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by
  by_cases hc : matrixOperatorNorm_diamConst d = 0
  · have hθ0 : cutoffPairThetaWindow d nu n m L omega = 0 := by
      rw [cutoffPairThetaWindow, hc]
      ring
    have hη0 : cutoffPairEtaWindow d nu n m L omega = 0 := by
      rw [cutoffPairEtaWindow, hθ0]
      ring
    rw [hη0]
    have hnn : (0 : ℝ) ≤ C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by
      have hW : 0 ≤ SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega :=
        SuperdiffusionCLT.Section3.Terms.anchorDerivSup_nonneg m L n omega
      have h3n : (0 : ℝ) ≤ (3 : ℝ) ^ n := pow_nonneg (by norm_num) n
      have hrp : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
      have h1 : 0 ≤ C * nu ^ (-(2 : ℝ)) := mul_nonneg hCnn hrp
      have h2 : 0 ≤ C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n := mul_nonneg h1 h3n
      exact mul_nonneg h2 hW
    linarith only [hnn]
  · have hc0 : 0 ≤ matrixOperatorNorm_diamConst d := matrixOperatorNorm_diamConst_nonneg d
    have hcpos : 0 < matrixOperatorNorm_diamConst d := lt_of_le_of_ne hc0 (Ne.symm hc)
    have hθν := thetaWindow_mul_nu nu hnu n m L omega
    have hXnn : (0 : ℝ) ≤ nu⁻¹ / matrixOperatorNorm_diamConst d :=
      div_nonneg (inv_nonneg.2 hnu.le) hcpos.le
    have hm := mul_le_mul_of_nonneg_right hpay hXnn
    have e1 : (16 * cutoffPairEtaWindow d nu n m L omega * matrixOperatorNorm_diamConst d) *
        (nu⁻¹ / matrixOperatorNorm_diamConst d) =
        16 * cutoffPairEtaWindow d nu n m L omega * nu⁻¹ := by
      field_simp
    have e2 : (C * cutoffPairThetaWindow d nu n m L omega) *
          (nu⁻¹ / matrixOperatorNorm_diamConst d) =
        C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ n *
          SuperdiffusionCLT.Section3.Terms.anchorDerivSup m L n omega := by
      rw [cutoffPairThetaWindow, rpow_neg_two_local hnu]
      field_simp
    rwa [e1, e2] at hm

/-! ## The strict-scale branch `m < L`

At `m < L` the window amplitude `θ` is split once more.  For `θ ≥ 1 / 2` the
printed large-amplitude display closes the conjunct
(`cutoffLocalizationConjunct3_largeWindow`, unconditionally).  For `θ < 1 / 2`
the deterministic chain bounds the block quadratic of `Z − Z̃₀` by the response
bracket plus one `η²` term, and `gradientDifference_le_skewFreeDifference` carries
that block bound to the left-hand side of the conjunct.  The `η²` term is read at
the minimizer's own energy, as the print does in the proof of
`e.minimizers.gradient.from.block`; this is carried out in `Conj3EndgameMinimizerEnergy`
(`conj3DeterministicFromBlock_min_cutoff_minimizerEnergy`). -/

/-- **The `η²` budget of the strict branch.**  From `32 c(d) ≤ C` and
`0 ≤ θ ≤ 1` follows `16 η c(d) ≤ C θ`, the hypothesis of
`sixteen_eta_window_budget`.  The amplitude identity is `η = θ (1 + θ)`, so
`16 η = 16 θ (1 + θ) ≤ 32 θ` on `θ ≤ 1`. -/
theorem sixteen_etaWindow_mul_diamConst_le {d : ℕ} {C nu : ℝ} (n m L : ℕ) (omega : ShellSeq d)
    (hC : 32 * matrixOperatorNorm_diamConst d ≤ C)
    (hθ0 : 0 ≤ cutoffPairThetaWindow d nu n m L omega)
    (hθ1 : cutoffPairThetaWindow d nu n m L omega ≤ 1) :
    16 * cutoffPairEtaWindow d nu n m L omega * matrixOperatorNorm_diamConst d ≤
      C * cutoffPairThetaWindow d nu n m L omega := by
  have hc0 : 0 ≤ matrixOperatorNorm_diamConst d := matrixOperatorNorm_diamConst_nonneg d
  have hη : cutoffPairEtaWindow d nu n m L omega =
      cutoffPairThetaWindow d nu n m L omega *
        (1 + cutoffPairThetaWindow d nu n m L omega) := rfl
  have h1θ : 1 + cutoffPairThetaWindow d nu n m L omega ≤ 2 := by linarith only [hθ1]
  have hstep : cutoffPairEtaWindow d nu n m L omega ≤
      2 * cutoffPairThetaWindow d nu n m L omega := by
    rw [hη]
    calc cutoffPairThetaWindow d nu n m L omega *
          (1 + cutoffPairThetaWindow d nu n m L omega) ≤
        cutoffPairThetaWindow d nu n m L omega * 2 :=
          mul_le_mul_of_nonneg_left h1θ hθ0
      _ = 2 * cutoffPairThetaWindow d nu n m L omega := by ring
  have hA : 16 * cutoffPairEtaWindow d nu n m L omega * matrixOperatorNorm_diamConst d ≤
      32 * cutoffPairThetaWindow d nu n m L omega * matrixOperatorNorm_diamConst d := by
    have h16 : 16 * cutoffPairEtaWindow d nu n m L omega ≤
        16 * (2 * cutoffPairThetaWindow d nu n m L omega) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    calc 16 * cutoffPairEtaWindow d nu n m L omega * matrixOperatorNorm_diamConst d ≤
          (16 * (2 * cutoffPairThetaWindow d nu n m L omega)) * matrixOperatorNorm_diamConst d :=
          mul_le_mul_of_nonneg_right h16 hc0
      _ = 32 * cutoffPairThetaWindow d nu n m L omega * matrixOperatorNorm_diamConst d := by ring
  have hB : 32 * cutoffPairThetaWindow d nu n m L omega * matrixOperatorNorm_diamConst d ≤
      C * cutoffPairThetaWindow d nu n m L omega := by
    have hmul : 32 * matrixOperatorNorm_diamConst d * cutoffPairThetaWindow d nu n m L omega ≤
        C * cutoffPairThetaWindow d nu n m L omega :=
      mul_le_mul_of_nonneg_right hC hθ0
    calc 32 * cutoffPairThetaWindow d nu n m L omega * matrixOperatorNorm_diamConst d =
          (32 * matrixOperatorNorm_diamConst d) * cutoffPairThetaWindow d nu n m L omega := by ring
      _ ≤ C * cutoffPairThetaWindow d nu n m L omega := hmul
  exact le_trans hA hB

/-! ## `hconj3` in the shape `CutoffLocalizationAssembly` consumes

The statement below is the third conjunct exactly as
`CutoffLocalizationAssembly.cutoff_localization_proved` consumes it
(see `Conj3EndgameMinimizerEnergy.cutoffLocalizationConjunct3_hconj3_minimizerEnergy`), copied
binder for binder: the carriers are written out as the explicit centered lambda,
the window as the raw `sSup` over `Option {x // x ∈ openCubeSet ...}`, and the
hypotheses `ShellLawPrefix`, `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`,
`ShellLawJ4` are carried verbatim.  Those five and `nu ≤ 1` are hypotheses of
the statement, and no branch consults them. -/

/-! ## The strict branch's hypotheses at a nonzero loading

The strict branch is not a statement about an empty hypothesis set.  At `m < L`
and `p ≠ 0` the two carriers have response maximizers by Book Chapter 2's
existence theory, and the loading `(-p, q)` is nonzero; every statement above is
therefore about a genuinely nonzero averaged loading, and the inequality
it concludes is the conjunct's own. -/

end

end SuperdiffusionCLT.Section2.Localization
