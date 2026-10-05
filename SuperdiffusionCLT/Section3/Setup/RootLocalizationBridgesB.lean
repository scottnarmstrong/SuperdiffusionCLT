/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.QuenchedLowerBoundB
public import SuperdiffusionCLT.Section3.Setup.RootLocalizationBridges
public import SuperdiffusionCLT.Section3.Setup.ScaleAssemblyB

/-!
# The quenched root bracket with the localization bridges discharged

The files `ScaleAssemblyB` and `QuenchedLowerBoundB` assemble the two brackets of
Proposition `p.sstar.lower.bound` up to explicit bridges: the master
inequality, the two balanced localization comparisons `hLocal1`, `hLocal2`, the
annealed comparison `hLocal` and its absorption `hEta`.  `RootLocalizationBridges`
derives the last four from the conclusion of the single statement
`Frozen.Section2.cutoff_localization` (`e.localization.s.star`).  This file
composes the two for the quenched bracket.

## What the theorem still carries

`sstar_lower_bound_quenched_of_anchors` carries

* `hLocAnchor` — the third and fourth Loewner conjunct of the first component
  of the conclusion of `Frozen.Section2.cutoff_localization`, at every admissible triple
  of scales, with the binders of that statement and a positive constant `CL`;
* `hAnn`, the annealed lower bound at cutoff `R`, which is the annealed conclusion of the
  root theorem at `L := R`, `m̄ := n₀`;
* `hMix`, the first conjunct of the conclusion of the statement in
  `Frozen/Section2/MixingMinscale.lean`; and
* the print's own data: the largeness of `C` and of `K`, and the thresholds
  `Ceta ≤ ν⁻¹L` and `6 log(ν⁻¹L) ≤ n₀ log 3` for the localization error.

The theorem does not import these statements; each of their conclusions appears as
an explicit hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section3.Terms

noncomputable section

/-! ## The scale-offset largeness -/

/-- The offset `a = ⌈K log(ν⁻¹L)⌉` with `K` large
(here `8056 ≤ K log 3`) satisfies `6 log(ν⁻¹L) ≤ a log 3`, the threshold that
`localization_error_le_one` needs to absorb `η_L` into the constant. -/
theorem six_log_le_scaleOffset_mul_log_three {K nu : ℝ} {L : ℕ}
    (hKlog3 : 8056 ≤ K * Real.log 3)
    (hlog : (0 : ℝ) ≤ Real.log (nu⁻¹ * (L : ℝ))) :
    6 * Real.log (nu⁻¹ * (L : ℝ)) ≤
      ((scaleOffset K nu L : ℕ) : ℝ) * Real.log 3 := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 :=
    Real.log_nonneg (by norm_num)
  have haK : K * Real.log (nu⁻¹ * (L : ℝ)) ≤ ((scaleOffset K nu L : ℕ) : ℝ) :=
    le_scaleOffset K nu L
  have h1 : K * Real.log (nu⁻¹ * (L : ℝ)) * Real.log 3 ≤
      ((scaleOffset K nu L : ℕ) : ℝ) * Real.log 3 :=
    mul_le_mul_of_nonneg_right haK hlog3
  have h2 : 8056 * Real.log (nu⁻¹ * (L : ℝ)) ≤
      K * Real.log 3 * Real.log (nu⁻¹ * (L : ℝ)) :=
    mul_le_mul_of_nonneg_right hKlog3 hlog
  linarith only [h1, h2, hlog]

/-! ## The annealed bracket -/

/-! ## The quenched bracket -/

/-- **The root's second bracket with the localization bridges discharged**.

This is `sstar_lower_bound_quenched` with `hLocal` and `hEta` replaced by the
conclusion of `Frozen.Section2.cutoff_localization` (`hLocAnchor`) and the two thresholds
`Ceta ≤ ν⁻¹L`, `6 log(ν⁻¹L) ≤ n₀ log 3`, through
`quenched_annealed_localization` and `quenched_localization_eta_le_one`.

The two bridges that remain are `hAnn` — the annealed lower bound
`e.sstar.lower.bound` at cutoff `R = 2⌊m/2⌋` and spatial scale `n₀`, i.e. the
annealed bound of the root theorem read at `L := R`,
`m̄ := n₀` — and `hMix`, the first conjunct of the conclusion of
`Frozen.Section2.sigmaStarInv_mixing_minscale`. -/
theorem sstar_lower_bound_quenched_of_anchors {d : ℕ} [NeZero d]
    {nu cStar c CL Ceta CM C : ℝ} {P : ProbabilityMeasure (ShellSeq d)} {L m : ℕ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hcStar : 0 < cStar) (hc : 0 < c)
    (hCM : 0 ≤ CM) (hCMC : CM ≤ C) (hquench : quenchedConst c ≤ C)
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (hm : 2 ≤ m) (hmL : m ≤ L)
    (hlog : 0 < Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)))
    (hCL : 0 < CL)
    (hCeta : IndependentSums.gammaMomentConst 1 * CL * (crudeLowerConst d)⁻¹ ≤ Ceta)
    (hCT : Ceta ≤ nu⁻¹ * (L : ℝ))
    (hk : 6 * Real.log (nu⁻¹ * (L : ℝ)) ≤
      ((quenchedInnerScale m : ℕ) : ℝ) * Real.log 3)
    (hAnn : c * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
          ((quenchedInnerScale m : ℕ) : ℝ) ^ ((1 : ℝ) / 2) *
          Real.log (nu⁻¹ * ((quenchedInnerScale m : ℕ) : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
        sigmaBarStarScalar nu (quenchedCutoffScale m) P
          (cubeSet (originCube d ((quenchedInnerScale m : ℕ) : ℤ))))
    (hLocAnchor : ∀ mm nn LL : ℕ, nn ≤ mm → mm ≤ LL →
        ∀ U : Book.Ch02.Domain d,
          (U : Set (Vec d)) ⊆ openCubeSet (originCube d (nn : ℤ)) →
          ∃ X : ShellSeq d → ℝ,
            Measurable X ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1) X
                (CL * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((mm - nn : ℕ) : ℝ))) ∧
              ∀ omega : ShellSeq d,
                MatLoewnerLE
                    ((1 - X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField)
                    (sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega LL).toCoeffField) ∧
                  MatLoewnerLE
                    (sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega LL).toCoeffField)
                    ((1 + X omega) • sigmaStarInvCoarse (U : Set (Vec d))
                      (coefficientCutoff nu omega mm).toCoeffField))
    (hMix : ∀ h n l : ℕ, h < n → n ≤ l →
        ∃ X : ShellSeq d → ℝ,
          Measurable X ∧
          IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
              (CM * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (sigmaStarInvCoarse (cubeSet (originCube d (n : ℤ)))
                  (coefficientCutoff nu omega l).toCoeffField)
                (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                  X omega • (1 : Mat d))) :
    ∃ X : ShellSeq d → ℝ,
      Measurable X ∧
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) X
          (C * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ (-((m : ℝ) / 8))) ∧
        ∀ omega : ShellSeq d,
          MatLoewnerLE
            (sigmaStarInvCoarse (cubeSet (originCube d (m : ℤ)))
              (coefficientCutoff nu omega L).toCoeffField)
            ((C * nu ^ (-(2 : ℝ)) * cStar ^ (-((3 : ℝ) / 2)) *
                  (m : ℝ) ^ (-((1 : ℝ) / 2)) *
                  Real.log (nu⁻¹ * (m : ℝ)) ^ ((9 : ℝ) / 2)) • (1 : Mat d) +
              X omega • (1 : Mat d)) := by
  have hL : 1 ≤ L := by omega
  have hRL : quenchedCutoffScale m ≤ L := by
    have h := quenchedInnerScale_le m
    simp only [quenchedCutoffScale, quenchedInnerScale] at h ⊢
    omega
  have hCeta0 : (0 : ℝ) ≤ Ceta := by
    have hcl := crudeLowerConst_pos d
    have hg := IndependentSums.gammaMomentConst_pos (σ := (1 : ℝ)) one_pos
    have hnn : (0 : ℝ) ≤ IndependentSums.gammaMomentConst 1 * CL *
        (crudeLowerConst d)⁻¹ := by positivity
    linarith only [hnn, hCeta]
  have hLocal := quenched_annealed_localization hnu hnu1 hCL hL hmL hPrefix hJ2
    hJ3 hJ4 hCeta
    (hLocAnchor (quenchedCutoffScale m) (quenchedInnerScale m) L
      (quenchedInnerScale_le_quenchedCutoffScale m) hRL)
  have hEta := quenched_localization_eta_le_one (m := m) hnu hnu1 hL hCeta0 hCT hk
  exact sstar_lower_bound_quenched (Ceta := Ceta) hnu hcStar hc hCM hCMC hquench
    hPrefix hJ2 hJ3 hJ4 hm hmL hlog hAnn hLocal hEta hMix

/-! ## `e.pigeon.scalar` at the cutoff `L'`, at the selected scales -/

end

end SuperdiffusionCLT.Section3.Setup
