/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.Mixing.MixBaseGaugeAbsorb
public import SuperdiffusionCLT.Frozen.Section2.CutoffLocalization
public import SuperdiffusionCLT.Section4.Mixing.AnnealedFinal
public import SuperdiffusionCLT.Section4.Mixing.TermTailEllipticity

/-!
# `t_ell ≤ (1 + CE) * t_L`, at a single shared `d`-dependent amplitude

The scale comparison from the cutoff localization
gives `t_ell ≤ t_L + nu⁻¹ * gammaMomentConst 1 * (C * nu^(-2) * 3^(-(ell-n)))`
for *some* `C ≥ 1`, freshly extracted (via `obtain ⟨C0, hC0⟩ :=
cutoff_localization d hd`) on *every call*. `Section4/Mixing/MixBaseGaugeAbsorb.lean`'s
`mixBase_gaugeE_absorb` absorbs exactly this leftover into `CE * t_L`, given a
gap `K0 * log(nu⁻¹ L) ≤ ell - n` for its own `K0 = 5 / log 3` (a bare numeral,
independent of the amplitude constant `Cf` fed to it) — but only for a *fixed*
`Cf` chosen before the call. Composing the two wrapper theorems naively fails
to typecheck: each fresh call to that comparison produces
its own opaque `C`, not syntactically (nor provably, from the wrapper's type
alone) equal to any other call's `C`, even though both trace to the exact same
underlying witness `cutoff_localization d hd` and so are
*mathematically* the same real number.

This file resolves the composition by extracting `C0` **once**, at the very
top (before quantifying over `nu, ell, L, n`), and inlining
the ~120-line derivation of that comparison
(in `mixBase_raw_uniform`) against that single shared `C0`,
so that the same `Cfixed := max C0 1` feeds both the raw bound and
`mixBase_gaugeE_absorb`'s absorption guarantee, and the returned `K0, CE` are
genuinely global (not merely "the same real number" without a Lean-visible
proof of it). -/

@[expose] public section

namespace SuperdiffusionCLT.Section4.Mixing

open Homogenization
open Homogenization.Book.Ch02 (cubeDomain cubeDomain_coe)
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2 (coefficientCutoff)
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)

noncomputable section

variable {d : ℕ}

/-! ## Entry-extraction helpers -/

private theorem mixBaseTEll_vecDot_single_matVecMul_single [NeZero d] (M : Mat d) :
    vecDot (Pi.single (0 : Fin d) 1) (matVecMul M (Pi.single (0 : Fin d) 1)) = M 0 0 := by
  have hentry : ∀ i : Fin d, matVecMul M (Pi.single (0 : Fin d) 1) i = M i 0 := by
    intro i
    show (fun j ↦ M i j) ⬝ᵥ (Pi.single (0 : Fin d) (1 : ℝ)) = M i 0
    rw [dotProduct_single_one]
  show (Pi.single (0 : Fin d) (1 : ℝ)) ⬝ᵥ (matVecMul M (Pi.single (0 : Fin d) 1)) = M 0 0
  rw [show matVecMul M (Pi.single (0 : Fin d) 1) = fun i ↦ M i 0 from funext hentry]
  exact single_one_dotProduct 0 (fun i ↦ M i 0)

private theorem mixBaseTEll_matLoewnerLE_apply_zero_zero [NeZero d] {A B : Mat d}
    (h : MatLoewnerLE A B) : A 0 0 ≤ B 0 0 := by
  have hx := h (Pi.single (0 : Fin d) 1)
  rw [mixBaseTEll_vecDot_single_matVecMul_single, mixBaseTEll_vecDot_single_matVecMul_single] at hx
  linarith only [hx]

private theorem mixBaseTEll_zero_lt_sigmaStarInvCoarse_apply_zero_zero [NeZero d] {U : Set (Vec d)}
    {a : CoeffField d} (hPD : (sigmaStarInvCoarse U a).PosDef) :
    0 < sigmaStarInvCoarse U a 0 0 := by
  have hx : (0 : Vec d) ≠ Pi.single (0 : Fin d) (1 : ℝ) := by
    intro h
    have := congrFun h (0 : Fin d)
    simp at this
  have hpos := hPD.dotProduct_mulVec_pos (x := Pi.single (0 : Fin d) 1) (Ne.symm hx)
  have heq : (star (Pi.single (0 : Fin d) (1 : ℝ)) : Vec d) ⬝ᵥ
      Matrix.mulVec (sigmaStarInvCoarse U a) (Pi.single (0 : Fin d) 1) =
      sigmaStarInvCoarse U a 0 0 := by
    show vecDot (Pi.single (0 : Fin d) 1) (matVecMul (sigmaStarInvCoarse U a)
      (Pi.single (0 : Fin d) 1)) = sigmaStarInvCoarse U a 0 0
    exact mixBaseTEll_vecDot_single_matVecMul_single _
  rwa [heq] at hpos

/-! ## The globally-shared-constant combination -/

/-- **The raw `t_ell` versus `t_L` bound at one shared amplitude.** The constant `Cfixed` is
extracted once from `cutoff_localization` and does not depend on `nu, P, ell, L, n`. -/
theorem mixBase_raw_uniform (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ Cfixed : ℝ, 1 ≤ Cfixed ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ (ell L n : ℕ), n ≤ ell → ell ≤ L →
                sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ≤
                  sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) +
                    nu⁻¹ * gammaMomentConst 1 *
                      (Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) := by
  obtain ⟨C0, hC0⟩ := SuperdiffusionCLT.Frozen.Section2.cutoff_localization d hd
  set Cfixed : ℝ := max C0 1 with hCfixeddef
  have hCfixed1 : (1 : ℝ) ≤ Cfixed := le_max_right _ _
  refine ⟨Cfixed, hCfixed1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n hnell hellL
  set Q : Homogenization.TriadicCube d := originCube d (n : ℤ) with hQdef
  have hUsub : ((cubeDomain Q : Homogenization.Book.Ch02.Domain d) : Set (Vec d)) ⊆
      openCubeSet Q := by
    rw [cubeDomain_coe]
  obtain ⟨⟨X, hXm, hXO0, hLoewner⟩, -, -⟩ :=
    hC0 nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell n L hnell hellL (cubeDomain Q) hUsub
  have hArgpos : (0 : ℝ) < Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) := by
    have hCpos : (0 : ℝ) < Cfixed := lt_of_lt_of_le one_pos hCfixed1
    have : (0 : ℝ) < nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)) :=
      mul_pos (Real.rpow_pos_of_pos hnu _) (Real.rpow_pos_of_pos (by norm_num) _)
    positivity
  have hC0leCfixed : C0 ≤ Cfixed := le_max_left C0 1
  have hXO : IsBigO P.toMeasure (gammaSigma 1) X
      (Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) := by
    refine hXO0.mono_scale ?_
    gcongr
  have hInt : MeasureTheory.Integrable X P.toMeasure :=
    mixFin_integrable_of_isBigO_gammaSigma (by norm_num) hArgpos hXm hXO
  have hEllBound : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0 ≤ nu⁻¹ := by
    intro omega
    have h := mixTail_sigmaStarInvCoarse_le_inv_smul_one nu hnu omega ell n
    have h00 := mixBaseTEll_matLoewnerLE_apply_zero_zero h
    rwa [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h00
  have hEllPos : ∀ omega : ShellSeq d,
      0 < sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0 := by
    intro omega
    have hPD := posDef_coarseBlockMatrix_lowerRight_coefficientCutoff hnu ell (n : ℤ) omega
    rw [coarseBlockMatrix_cubeSet_lowerRight_eq
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega ell) Q] at hPD
    exact mixBaseTEll_zero_lt_sigmaStarInvCoarse_apply_zero_zero hPD
  have hConj3 : ∀ omega : ShellSeq d,
      MatLoewnerLE
        ((1 - X omega) •
          sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun)
        (sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun) := by
    intro omega
    have h := (hLoewner omega).2.2.1
    rwa [cubeDomain_coe] at h
  have hDiffBound : ∀ omega : ShellSeq d,
      sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0 -
          sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun 0 0 ≤
        nu⁻¹ * |X omega| := by
    intro omega
    have h00 := mixBaseTEll_matLoewnerLE_apply_zero_zero (hConj3 omega)
    rw [Matrix.smul_apply, smul_eq_mul] at h00
    have hMell0 := (hEllPos omega).le
    have hMellUp := hEllBound omega
    have hXle : X omega * sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega ell).toFun 0 0 ≤
        |X omega| * (nu⁻¹) := by
      have h1 : X omega * sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega ell).toFun 0 0 ≤
          |X omega| * sigmaStarInvCoarse (openCubeSet Q)
            (coefficientCutoff nu omega ell).toFun 0 0 :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hMell0
      have h2 : |X omega| * sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega ell).toFun 0 0 ≤ |X omega| * nu⁻¹ :=
        mul_le_mul_of_nonneg_left hMellUp (abs_nonneg _)
      linarith only [h1, h2]
    nlinarith only [h00, hXle]
  have hIntEll : MeasureTheory.Integrable
      (fun omega ↦ sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0)
      P.toMeasure := by
    refine (integrable_coarseBlockMatrix_lowerRight_apply hnu ell Q hPrefix hJ2 hJ3 hJ4 0 0).congr
      (Filter.Eventually.of_forall fun omega ↦ ?_)
    show (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega ell).toFun).lowerRight 0 0 =
      sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0
    rw [coarseBlockMatrix_cubeSet_lowerRight_eq
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega ell) Q]
  have hIntL : MeasureTheory.Integrable
      (fun omega ↦ sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun 0 0)
      P.toMeasure := by
    refine (integrable_coarseBlockMatrix_lowerRight_apply hnu L Q hPrefix hJ2 hJ3 hJ4 0 0).congr
      (Filter.Eventually.of_forall fun omega ↦ ?_)
    show (coarseBlockMatrix (cubeSet Q) (coefficientCutoff nu omega L).toFun).lowerRight 0 0 =
      sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun 0 0
    rw [coarseBlockMatrix_cubeSet_lowerRight_eq
      (aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega L) Q]
  have hIntDiff := hIntEll.sub hIntL
  have hIntG : MeasureTheory.Integrable (fun omega ↦ nu⁻¹ * |X omega|) P.toMeasure :=
    hInt.abs.const_mul nu⁻¹
  have hmono := MeasureTheory.integral_mono hIntDiff hIntG hDiffBound
  simp only [Pi.sub_apply] at hmono
  have hEqEll : sigmaBarStarInvScalar nu ell P (cubeSet Q) =
      ∫ omega, sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega ell).toFun 0 0
        ∂P.toMeasure := by
    show sigmaBarStarInv nu ell P (cubeSet Q) 0 0 = _
    exact sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu ell P Q 0 0
  have hEqL : sigmaBarStarInvScalar nu L P (cubeSet Q) =
      ∫ omega, sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toFun 0 0
        ∂P.toMeasure := by
    show sigmaBarStarInv nu L P (cubeSet Q) 0 0 = _
    exact sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu L P Q 0 0
  rw [MeasureTheory.integral_sub hIntEll hIntL, ← hEqEll, ← hEqL] at hmono
  have hgammabound := mixMain_integral_abs_le_of_isBigO_gammaSigma (μ := P.toMeasure) (X := X)
    (A := Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ))) (σ := 1) (by norm_num)
    hArgpos hXm.aemeasurable hXO
  rw [MeasureTheory.integral_const_mul] at hmono
  have hnuinv : (0 : ℝ) ≤ nu⁻¹ := by positivity
  have hgscaled : nu⁻¹ * ∫ omega, |X omega| ∂P.toMeasure ≤
      nu⁻¹ * (gammaMomentConst 1 *
        (Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hgammabound hnuinv
  have hfinal : sigmaBarStarInvScalar nu ell P (cubeSet Q) - sigmaBarStarInvScalar nu L P (cubeSet Q) ≤
      nu⁻¹ * (gammaMomentConst 1 *
        (Cfixed * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((ell - n : ℕ) : ℕ) : ℝ)))) :=
    hmono.trans hgscaled
  linarith only [hfinal]

/-- **`t_ell ≤ (1 + CE) * t_L`, at a single `K0, CE` shared across every
`(nu, ell, L, n, P)` instance.** `K0 = 5 / log 3` (from `mixBase_gaugeE_absorb`,
independent of the amplitude constant); `CE` is the same theorem's absorption
constant at the one shared `Cfixed := max C0 1` derived from
`cutoff_localization d hd` extracted exactly once. -/
theorem mixBase_tEll_le_scaled_tL (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ K0 CE : ℝ, 1 ≤ K0 ∧ K0 ≤ 5 ∧ 0 ≤ CE ∧
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (ShellSeq d)),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
            ShellLawJ4 d P →
              ∀ (ell L n : ℕ), 1 ≤ L → n ≤ ell → ell ≤ L →
                K0 * Real.log (nu⁻¹ * (L : ℝ)) ≤ (((ell - n : ℕ) : ℕ) : ℝ) →
                sigmaBarStarInvScalar nu ell P (cubeSet (originCube d (n : ℤ))) ≤
                  (1 + CE) * sigmaBarStarInvScalar nu L P (cubeSet (originCube d (n : ℤ))) := by
  obtain ⟨Cfixed, hCfixed1, hrawU⟩ := mixBase_raw_uniform d hd
  obtain ⟨K0, CE, hK01, hK05, hCEnn, habs⟩ := mixBase_gaugeE_absorb d Cfixed hCfixed1
  refine ⟨K0, CE, hK01, hK05, hCEnn, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n hL1 hnell hellL hgap
  have hraw := hrawU nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 ell L n hnell hellL
  have hEabs := habs nu hnu hnu1 L hL1 ell n hgap P hPrefix hJ2 hJ3 hJ4 (n : ℤ) (by positivity)
  linarith only [hraw, hEabs]

end

end SuperdiffusionCLT.Section4.Mixing
