/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingConjunct2
public import SuperdiffusionCLT.Section2.Annealed.MixingAnchorClose

/-!
# The final mixing minscale anchor

This file removes the localization-anchor and sign premises from the assembly
`sigmaStarInv_mixing_minscale_of_anchors_midpoint`.  The localization packaging constant is
absorbed into a fixed positive choice of `CL`, and the sign of the first-conjunct constant is
deduced from its domination hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

/-! ## The corrected step binders, and the closure of the anchor

The two outer step binders carried by the assembly
`sigmaStarInv_mixing_minscale_of_anchors_midpoint` do not match the sharp forms of the
manuscript's Steps E and D:

* the Step-E binder quantifies a free intermediate cutoff `m` with
  `h < m → m ≤ n` for the whole family `(h, n)`, whereas the `m`-free Step-E
  exists only at the printed fixed scale `n' = (n + h + 1) / 2`; at the free upper end `m = n`
  no such witness exists;
* the Step-D binder carries only `ShellLawPrefix` and `ShellLawJ2`, whereas the
  sharp Step-D `stepD_exists_sharp_printed` consumes `ShellLawJ3` (its capped `Gamma_2`
  first-moment estimate) and `ShellLawJ4` (the scalarization of `sigmaBarStarInv` on the
  origin cube), and `ShellLawJ2` is only the independence of the coordinates.

The theorems below restate the two binder-corrected interfaces at the printed
scale, and `sigmaStarInv_mixing_minscale_closed` closes the main statement from
the discharges `stepE_printedScale_closed` and `stepD_binder_sharp_printed`, at the named
constants `stepEAmplitudeConstMFree d` and `stepDSharpConst d`. -/

/-- **The balanced conjunct at the printed intermediate scale.**  The balanced
conjunct of the mixing minscale, with the Step-E hypothesis narrowed to the printed fixed
scale `(n + h + 1) / 2`
of the manuscript and carrying the `ShellLawJ1Restriction`, `ShellLawJ3`, `ShellLawJ4`
binders its form consumes, and the Step-D hypothesis widened by
`ShellLawJ3` and `ShellLawJ4`. -/
theorem mixing_minscale_conjunct2_of_anchors_printed (d : ℕ) [NeZero d]
    {CL CM CFluc CDet : ℝ}
    (hCL : 0 < CL) (hCFluc : 0 < CFluc) (hCDet : 0 < CDet)
    (hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL)
    (hCM : 0 ≤ CM)
    (hdom : mixingAmpConst CL CFluc CDet ≤ CM)
    (hStepE : ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
          ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h n : ℕ, h < n →
            ∃ XFluc : ShellSeq d → ℝ,
              Measurable XFluc ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) XFluc
                  (CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
                      (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R)
                        (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField))
                    (sigmaBarStarInv nu ((n + h + 1) / 2) P
                        (cubeSet (originCube d (h : ℤ))) + XFluc omega • (1 : Mat d)))
    (hStepD : ∀ (nu : ℝ), 0 < nu →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h m l : ℕ, h < m → m ≤ l →
            ∃ Y : ShellSeq d → ℝ,
              Measurable Y ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Y
                  (CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))))
                    (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                      Y omega • (1 : Mat d))) :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
        ShellLawJ4 d P →
        ∀ h n l L : ℕ, h < n → n < l → l < L →
          ∃ X1 X2 : ShellSeq d → ℝ,
            Measurable X1 ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X1
              (mixingConjunct2Const d CM * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                sigmaBarStarInvScalar nu L P (cubeSet (originCube d (h : ℤ)))) ∧
            Measurable X2 ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X2
              (mixingConjunct2Const d CM * nu ^ (-(2 : ℝ)) *
                ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ (omega : ShellSeq d) (p q : Vec d),
              2 * vecDot p (matVecMul
                  (volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                    (fun y => finiteShellIncrement omega l L y)) q) ≤
                (X1 omega + X2 omega) *
                  (vecDot p (matVecMul
                    (Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                      (coefficientCutoff nu omega L).toCoeffField) p) +
                   vecDot q (matVecMul
                    (Homogenization.sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                      (coefficientCutoff nu omega L).toCoeffField) q)) := by
  refine mixing_minscale_conjunct2_of_conjunct1 d hCM ?_
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n L hhn hnl
  have hhm : h < (n + h + 1) / 2 := by omega
  have hmn : (n + h + 1) / 2 ≤ n := by omega
  have hmid : (2 : ℝ) * ((((n + h + 1) / 2 - h : ℕ) : ℕ) : ℝ) ≥
      (((n - h : ℕ) : ℕ) : ℝ) := by
    exact_mod_cast (show (2 : ℕ) * ((n + h + 1) / 2 - h) ≥ n - h by omega)
  exact sigmaStarInv_mixing_minscale_of_anchors_midpoint (nu := nu) (CL := CL) (CM := CM)
    (CFluc := CFluc) (CDet := CDet) (P := P) (h := h) (n := n) (l := L)
    (mm := (n + h + 1) / 2) hnu hCL hCFluc hCDet hPrefix hJ2 hdom
    (SuperdiffusionCLT.Section3.Terms.term3_locAnchor_of_conjunct1 d CL hloc nu hnu
      hnu1 P hJ3)
    hhm hmn hmid (hStepE nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n hhn)
    (hStepD nu hnu P hPrefix hJ2 hJ3 hJ4) hnl

/-- **The mixing minscale from its corrected inputs.**  The mixing
minscale conclusion with the corrected Step-E and Step-D binders above: conjunct 1 is the
assembly `sigmaStarInv_mixing_minscale_of_anchors_midpoint` instantiated at the printed
scale `mm = (n + h + 1) / 2`, conjunct 2 is
`mixing_minscale_conjunct2_of_anchors_printed`, both at the shared constant
`max CM (mixingConjunct2Const d CM)`. -/
theorem sigmaStarInv_mixing_minscale_of_anchor_inputs_printed (d : ℕ) [NeZero d]
    {CL CM CFluc CDet : ℝ}
    (hCL : 0 < CL) (hCFluc : 0 < CFluc) (hCDet : 0 < CDet)
    (hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL)
    (hCM : 0 ≤ CM)
    (hdom : mixingAmpConst CL CFluc CDet ≤ CM)
    (hStepE : ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
          ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h n : ℕ, h < n →
            ∃ XFluc : ShellSeq d → ℝ,
              Measurable XFluc ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) XFluc
                  (CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
                      (fun R => Homogenization.sigmaStarInvCoarse (cubeSet R)
                        (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField))
                    (sigmaBarStarInv nu ((n + h + 1) / 2) P
                        (cubeSet (originCube d (h : ℤ))) + XFluc omega • (1 : Mat d)))
    (hStepD : ∀ (nu : ℝ), 0 < nu →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h m l : ℕ, h < m → m ≤ l →
            ∃ Y : ShellSeq d → ℝ,
              Measurable Y ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Y
                  (CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))))
                    (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                      Y omega • (1 : Mat d))) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          (∀ h n L : ℕ, h < n → n ≤ L →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X
                    (C * nu ^ (-(2 : ℝ)) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.MatLoewnerLE
                      (Homogenization.sigmaStarInvCoarse
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (n : ℤ)))
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                            nu omega L).toCoeffField)
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInv
                          nu L P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (h : ℤ))) +
                        X omega • (1 : Homogenization.Mat d))) ∧
            ∀ h n l L : ℕ, h < n → n < l → l < L →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X1
                    (C * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar
                        nu L P
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (h : ℤ)))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X2
                    (C * nu ^ (-(2 : ℝ)) * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.Vec d),
                    2 * Homogenization.vecDot p
                        (Homogenization.matVecMul
                          (Homogenization.volumeAverageMat
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (n : ℤ)))
                            (fun y =>
                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega l L y))
                          q) ≤
                      (X1 omega + X2 omega) *
                        (Homogenization.vecDot p
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) p) +
                          Homogenization.vecDot q
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) q)) := by
  refine ⟨max CM (mixingConjunct2Const d CM), ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4
  refine ⟨?_, ?_⟩
  · -- conjunct 1: the assembly at the printed midpoint scale
    intro h n L hhn hnl
    have hhm : h < (n + h + 1) / 2 := by omega
    have hmn : (n + h + 1) / 2 ≤ n := by omega
    have hmid : (2 : ℝ) * ((((n + h + 1) / 2 - h : ℕ) : ℕ) : ℝ) ≥
        (((n - h : ℕ) : ℕ) : ℝ) := by
      exact_mod_cast (show (2 : ℕ) * ((n + h + 1) / 2 - h) ≥ n - h by omega)
    obtain ⟨X, hXM, hXO, hXL⟩ :=
      sigmaStarInv_mixing_minscale_of_anchors_midpoint (nu := nu) (CL := CL) (CM := CM)
        (CFluc := CFluc) (CDet := CDet) (P := P) (h := h) (n := n) (l := L)
        (mm := (n + h + 1) / 2) hnu hCL hCFluc hCDet hPrefix hJ2 hdom
        (SuperdiffusionCLT.Section3.Terms.term3_locAnchor_of_conjunct1 d CL hloc nu hnu
          hnu1 P hJ3)
        hhm hmn hmid (hStepE nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n hhn)
        (hStepD nu hnu P hPrefix hJ2 hJ3 hJ4) hnl
    have hnu2nn : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
    have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    exact ⟨X, hXM, hXO.mono_scale (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hnu2nn) h3nn), hXL⟩
  · -- conjunct 2: the balanced conjunct, at the shared constant
    intro h n l L hhn hnl hlL
    obtain ⟨X1, X2, hX1M, hX1O, hX2M, hX2O, hpair⟩ :=
      mixing_minscale_conjunct2_of_anchors_printed d hCL hCFluc hCDet hloc hCM hdom
        hStepE hStepD nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 h n l L hhn hnl hlL
    have hscnn : (0 : ℝ) ≤
        SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar
          nu L P (Homogenization.cubeSet (Homogenization.originCube d (h : ℤ))) :=
      (sigmaBarStarInvScalar_pos_cutoff hnu L hPrefix hJ2 hJ3 hJ4 (h : ℤ)).le
    have hrnn : (0 : ℝ) ≤ ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hnu2nn : (0 : ℝ) ≤ nu ^ (-(2 : ℝ)) := Real.rpow_nonneg hnu.le _
    have h3nn : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4)) :=
      Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
    exact ⟨X1, X2, hX1M,
      hX1O.mono_scale (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hrnn) hscnn),
      hX2M,
      hX2O.mono_scale (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hnu2nn) hrnn) h3nn),
      hpair⟩

/-- The mixing minscale conclusion, with only the two matrix-level
inputs not discharged by the localization and conjunct-2 results, at the binder
shapes the sharp forms of Steps E and D consume: the Step-E binder at
the printed fixed scale `(n + h + 1) / 2`
with the five `J`-binders, and the Step-D binder widened by `ShellLawJ3` and
`ShellLawJ4`. -/
theorem sigmaStarInv_mixing_minscale_final (d : ℕ) [NeZero d]
    {CFluc CDet CM : ℝ}
    (hCFluc : 0 < CFluc) (hCDet : 0 < CDet)
    (hdom : mixingAmpConst
      (max (SuperdiffusionCLT.Section2.Localization.localizationConst d) 1)
      CFluc CDet ≤ CM)
    (hStepE : ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
          ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h n : ℕ, h < n →
            ∃ XFluc : ShellSeq d → ℝ,
              Measurable XFluc ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) XFluc
                  (CFluc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
                      (fun R => sigmaStarInvCoarse (cubeSet R)
                        (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField))
                    (sigmaBarStarInv nu ((n + h + 1) / 2) P
                        (cubeSet (originCube d (h : ℤ))) + XFluc omega • (1 : Mat d)))
    (hStepD : ∀ (nu : ℝ), 0 < nu →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
          ∀ h m l : ℕ, h < m → m ≤ l →
            ∃ Y : ShellSeq d → ℝ,
              Measurable Y ∧
              IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Y
                  (CDet * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
                ∀ omega : ShellSeq d,
                  MatLoewnerLE
                    (sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))))
                    (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                      Y omega • (1 : Mat d))) :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : ProbabilityMeasure (ShellSeq d),
          ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P → ShellLawJ3 d P →
          ShellLawJ4 d P →
          (∀ h n L : ℕ, h < n → n ≤ L →
              ∃ X : ShellSeq d → ℝ,
                Measurable X ∧
                IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
                    (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ omega : ShellSeq d,
                    MatLoewnerLE
                      (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                        (coefficientCutoff nu omega L).toCoeffField)
                      (sigmaBarStarInv nu L P (cubeSet (originCube d (h : ℤ))) +
                        X omega • (1 : Mat d))) ∧
            (∀ h n l L : ℕ, h < n → n < l → l < L →
              ∃ X1 X2 : ShellSeq d → ℝ,
                Measurable X1 ∧
                IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X1
                  (C * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                    sigmaBarStarInvScalar nu L P
                      (cubeSet (originCube d (h : ℤ)))) ∧
                Measurable X2 ∧
                IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X2
                  (C * nu ^ (-(2 : ℝ)) * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                    (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                ∀ (omega : ShellSeq d) (p q : Vec d),
                  2 * vecDot p (matVecMul
                    (volumeAverageMat (cubeSet (originCube d (n : ℤ)))
                      (fun y => finiteShellIncrement omega l L y)) q) ≤
                    (X1 omega + X2 omega) *
                      (vecDot p (matVecMul
                        (sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                          (coefficientCutoff nu omega L).toCoeffField) p) +
                       vecDot q (matVecMul
                        (sigmaStarCoarse (cubeSet (originCube d (n : ℤ)))
                          (coefficientCutoff nu omega L).toCoeffField) q))) := by
  let CL : ℝ := max (SuperdiffusionCLT.Section2.Localization.localizationConst d) 1
  have hCL : 0 < CL := by
    dsimp [CL]
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hloc : SuperdiffusionCLT.Section2.Localization.localizationConst d ≤ CL := by
    dsimp [CL]
    exact le_max_left _ _
  have hdom' : mixingAmpConst CL CFluc CDet ≤ CM := by
    simpa only [CL] using hdom
  have hCM : 0 ≤ CM :=
    (mixingAmpConst_nonneg hCL hCFluc hCDet).trans hdom'
  exact sigmaStarInv_mixing_minscale_of_anchor_inputs_printed (d := d) (CL := CL)
    (CM := CM) (CFluc := CFluc) (CDet := CDet) hCL hCFluc hCDet hloc hCM hdom'
    hStepE hStepD

/-- **The mixing minscale anchor, closed.**  The conclusion is the
statement `SuperdiffusionCLT.Frozen.Section2.sigmaStarInv_mixing_minscale`
verbatim, with **no** step hypotheses:
the corrected Step-E binder is filled by `stepE_printedScale_closed`
at `CFluc := stepEAmplitudeConstMFree d` (so
`0 < CFluc` is `stepEAmplitudeConstMFree_pos`), and
the corrected Step-D binder is filled by `stepD_binder_sharp_printed`
at `CDet := stepDSharpConst d` (so `0 < CDet` is
`stepDSharpConst_pos`).  The localization packaging constant is
`CL := max (localizationConst d) 1` and the shared constant is
`CM := mixingAmpConst CL (stepEAmplitudeConstMFree d) (stepDSharpConst d)`, with
`mixingAmpConst CL CFluc CDet ≤ CM` by `le_rfl`.  The printed-scale
bookkeeping (`stepEColorSet_amplitude_le`) holds for **every** `d ≥ 1`, so
`[NeZero d]` alone suffices and no separate `2 ≤ d` is carried. -/
theorem sigmaStarInv_mixing_minscale_closed (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
        ∀ P : MeasureTheory.ProbabilityMeasure
            (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          (∀ h n L : ℕ, h < n → n ≤ L →
              ∃ X : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X
                    (C * nu ^ (-(2 : ℝ)) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d,
                    Homogenization.MatLoewnerLE
                      (Homogenization.sigmaStarInvCoarse
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (n : ℤ)))
                        (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                            nu omega L).toCoeffField)
                      (SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInv
                          nu L P
                          (Homogenization.cubeSet
                            (Homogenization.originCube d (h : ℤ))) +
                        X omega • (1 : Homogenization.Mat d))) ∧
            ∀ h n l L : ℕ, h < n → n < l → l < L →
              ∃ X1 X2 : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable X1 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 2) X1
                    (C * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      SuperdiffusionCLT.Section2.Annealed.sigmaBarStarInvScalar
                        nu L P
                        (Homogenization.cubeSet
                          (Homogenization.originCube d (h : ℤ)))) ∧
                Measurable X2 ∧
                Homogenization.IndependentSums.IsBigO P.toMeasure
                    (Homogenization.IndependentSums.gammaSigma 1) X2
                    (C * nu ^ (-(2 : ℝ)) * ((L - l : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
                      (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
                  ∀ (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
                    (p q : Homogenization.Vec d),
                    2 * Homogenization.vecDot p
                        (Homogenization.matVecMul
                          (Homogenization.volumeAverageMat
                            (Homogenization.cubeSet
                              (Homogenization.originCube d (n : ℤ)))
                            (fun y =>
                              SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement
                                omega l L y))
                          q) ≤
                      (X1 omega + X2 omega) *
                        (Homogenization.vecDot p
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) p) +
                          Homogenization.vecDot q
                            (Homogenization.matVecMul
                              (Homogenization.sigmaStarCoarse
                                (Homogenization.cubeSet
                                  (Homogenization.originCube d (n : ℤ)))
                                (SuperdiffusionCLT.Frozen.Section2.coefficientCutoff
                                    nu omega L).toCoeffField) q)) := by
  have hCFluc : 0 < stepEAmplitudeConstMFree d :=
    stepEAmplitudeConstMFree_pos d (Nat.one_le_iff_ne_zero.mpr (NeZero.ne d))
  have hCDet : 0 < stepDSharpConst d := stepDSharpConst_pos (d := d)
  exact sigmaStarInv_mixing_minscale_final (d := d)
    (CFluc := stepEAmplitudeConstMFree d) (CDet := stepDSharpConst d)
    (CM := mixingAmpConst
      (max (SuperdiffusionCLT.Section2.Localization.localizationConst d) 1)
      (stepEAmplitudeConstMFree d) (stepDSharpConst d))
    hCFluc hCDet le_rfl (stepE_printedScale_closed d) (stepD_binder_sharp_printed d)

end

end SuperdiffusionCLT.Section2.Annealed
