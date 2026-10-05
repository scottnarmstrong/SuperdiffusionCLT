/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.MixingConjunct2
public import SuperdiffusionCLT.Section2.Annealed.MixingLoewnerSteps
public import SuperdiffusionCLT.Section2.Annealed.MixingStepDSharp
public import SuperdiffusionCLT.Section2.Annealed.MixingStepEAmplitudeB

/-!
# Closing the mixing anchor: the printed-scale Step-E and the discharge of `hStepD`

The main statement `sigmaStarInv_mixing_minscale` (the printed lemma `l.mixing.minscale` of the
paper, with its proof) is reached below from the two outer hypotheses that the assembly
`sigmaStarInv_mixing_minscale_of_anchors_midpoint` and `sigmaStarInv_mixing_minscale_final` still
carry: the Step-E and Step-D binders.  What this file proves:

* `stepD_binder_sharp_printed` — the `hStepD` conclusion of that chain at the `nu`-free
  constant `stepDSharpConst d`, discharged from `stepD_exists_sharp_printed`.  The sharp Step-D
  needs `ShellLawJ3` (its `Gamma_2` first-moment estimate) and `ShellLawJ4` (the scalarization
  of `sigmaBarStarInv` on the origin cube), while every `hStepD` binder of the chain supplies
  only `ShellLawPrefix` and `ShellLawJ2`; since `ShellLawJ2` is only the independence of the
  coordinates, it implies neither `J3` nor `J4`, so the binder must be widened by exactly those
  two hypotheses.  That widened binder is the statement below.

* `stepE_printedScale` — the Step-E conclusion **fully discharged** at the printed fixed
  intermediate scale `n' = ceil((n + h) / 2) = (n + h + 1) / 2`, at the `m`-free constant
  `stepEAmplitudeConstMFree d`, with the witness
  `omega |-> || s^-1_{L',*}(cu_n) - shom^-1_{L',*}(cu_h) ||_op` of
  `measurable_matrixOperatorNorm_fluctuation` and `matLoewnerLE_add_operatorNorm_sub`.  No
  `Gamma_2` amplitude, no colouring and no entry-level bookkeeping is left open at that scale.

* `stepE_printedScale_closed` — the same conclusion in the binder shape that the assembly
  consumes: the Step-E hypothesis moved *inside* the `J`-binders (`ShellLawPrefix`,
  `ShellLawJ1Restriction`, `ShellLawJ2`, `ShellLawJ3`, `ShellLawJ4`), at the printed scale determined by
  `h` and `n`, with the `m`-free constant.

* `stepEAmplitudeConstMFree_pos` — the positivity of the `m`-free Step-E constant, so that the
  closure `sigmaStarInv_mixing_minscale_closed` of `MixingAnchorFinal` can fix
  `CFluc := stepEAmplitudeConstMFree d`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Annealed

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Localization

noncomputable section

/-! ## The `hStepD` binder at the sharp constant, with the two `J`-binders it needs -/

/-- **`hStepD` of the chain at `CDet = stepDSharpConst d`.**  The conclusion is the `hStepD`
binder of `sigmaStarInv_mixing_minscale_of_anchor_inputs_printed` and of
`sigmaStarInv_mixing_minscale_final`, at the `nu`-free constant `stepDSharpConst d` and the
printed rate `3^-((m - h) / 2)`; the witness is `stepD_exists_sharp_printed`.  The two
hypotheses `ShellLawJ3` and `ShellLawJ4` are exactly what that lemma consumes: `ShellLawJ3` is
the capped `Gamma_2` first moment `stepDCapWitness_moment` behind `stepD_scalarGap_sharp`, and
`ShellLawJ4` is the scalarization `sigmaBarStarInv_originCube_eq_smul_one` used by
`stepD_exists_of_scalar_gap`; neither follows from the `ShellLawJ2` of the original binder,
which is only the independence of the coordinates. -/
theorem stepD_binder_sharp_printed (d : ℕ) [NeZero d] :
    ∀ (nu : ℝ), 0 < nu →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ h m l : ℕ, h < m → m ≤ l →
          ∃ Y : ShellSeq d → ℝ,
            Measurable Y ∧
            IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) Y
                (stepDSharpConst d * nu ^ (-(2 : ℝ)) *
                  (3 : ℝ) ^ (-(((m - h : ℕ) : ℝ) / 2))) ∧
              ∀ omega : ShellSeq d,
                MatLoewnerLE
                  (sigmaBarStarInv nu m P (cubeSet (originCube d (h : ℤ))))
                  (sigmaBarStarInv nu l P (cubeSet (originCube d (h : ℤ))) +
                    Y omega • (1 : Mat d)) := by
  intro nu hnu P _hPrefix _hJ2 hJ3 hJ4 h m l hhm hml
  exact stepD_exists_sharp_printed hnu P hJ3 hJ4 hhm hml

/-! ## The Step-E conclusion at the printed scale, discharged -/

/-- **The printed-scale Step-E, fully discharged.**  At the printed fixed
intermediate scale `n' = (n + h + 1) / 2` the descendant average of
the coarse matrix at cutoff `n'` is below `shom^-1_{n',*}(cu_h)` plus an
explicit operator-norm fluctuation that is `O_{Gamma_2}` at the `m`-free
amplitude `stepEAmplitudeConstMFree d * nu^-2 * 3^-((n - h) / 4)`.

The witness is `omega |-> || D omega - shom^-1_{n',*}(cu_h) ||_op`; its
measurability is `measurable_matrixOperatorNorm_fluctuation` and the per-`omega`
comparison is the operator-norm sandwich `matLoewnerLE_add_operatorNorm_sub`.
The `Gamma_2` amplitude comes from the printed colour partition
`stepEColorPartition_printed` through the entry-level estimate
`isBigO_gammaSigma_descendantAverage_entry_of_colorPartition` and the `d^2` union bound
`isBigO_gammaSigma_operatorNorm_of_entrywise_uniform`; the amplitude bookkeeping is the
`m`-free `hAmpl_printedScale`, which is where the printed `3^-((n - h) / 4)` is paid.  That
bookkeeping (`stepEColorSet_amplitude_le`) holds for **every** `d ≥ 1`, i.e. under `[NeZero d]`
alone; `nu ∈ (0, 1]` is the standing range of the main statement. -/
theorem stepE_printedScale (d : ℕ) [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (P : ProbabilityMeasure (ShellSeq d))
    (hJ1 : ShellLawJ1Restriction d P) (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    ∀ h n : ℕ, h < n →
      ∃ XFluc : ShellSeq d → ℝ, Measurable XFluc ∧
        IsBigO P.toMeasure (gammaSigma 2) XFluc
            (stepEAmplitudeConstMFree d * nu ^ (-(2 : ℝ)) *
              (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
        ∀ omega : ShellSeq d,
          MatLoewnerLE
            (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
              (fun R => sigmaStarInvCoarse (cubeSet R)
                (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField))
            (sigmaBarStarInv nu ((n + h + 1) / 2) P
                (cubeSet (originCube d (h : ℤ))) +
              XFluc omega • (1 : Mat d)) := by
  intro h n hhn
  classical
  have hhm : h < (n + h + 1) / 2 := by omega
  have hmn : (n + h + 1) / 2 ≤ n := by omega
  obtain ⟨hne, hdisj, hcover, hclsne, hsep, -⟩ :=
    stepEColorPartition_printed (d := d) (n := n) (h := h) hhn
  have hNpos : (0 : ℝ) <
      ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) := by
    rw [SuperdiffusionCLT.Section2.Localization.card_descendantsAtDepth_originCube]
    positivity
  have hApos : 0 < gammaTriangleConst 2 *
      Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
        (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
      (nu⁻¹ + nu⁻¹) := by
    have hQpos : (0 : ℝ) < ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) :=
      by exact_mod_cast Finset.card_pos.mpr hne
    have hKpos : (0 : ℝ) < nu⁻¹ + nu⁻¹ := by linarith only [inv_pos.2 hnu]
    have h1 : (0 : ℝ) <
        Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) :=
      Real.sqrt_pos.2 hQpos
    have h2 : (0 : ℝ) <
        Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) :=
      div_pos (Real.sqrt_pos.2 hNpos) hNpos
    exact mul_pos (mul_pos (mul_pos (IndependentSums.gammaTriangleConst_pos (σ := 2))
      SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos)
      (mul_pos h1 h2)) hKpos
  have hMmeas : ∀ p : Fin d × Fin d, Measurable
      (fun omega : ShellSeq d =>
        (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
            (fun R => sigmaStarInvCoarse (cubeSet R)
              (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField) -
          sigmaBarStarInv nu ((n + h + 1) / 2) P
            (cubeSet (originCube d (h : ℤ)))) p.1 p.2) := by
    intro p
    simp only [Matrix.sub_apply]
    exact (measurable_descendantsAverageMat_entry hnu ((n + h + 1) / 2) n h p.1 p.2).sub
      measurable_const
  have hconc : ∀ p : Fin d × Fin d, IsBigO P.toMeasure (gammaSigma 2)
      (fun omega : ShellSeq d =>
        (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
            (fun R => sigmaStarInvCoarse (cubeSet R)
              (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField) -
          sigmaBarStarInv nu ((n + h + 1) / 2) P
            (cubeSet (originCube d (h : ℤ)))) p.1 p.2)
      (gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
        (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
          (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
            ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
        (nu⁻¹ + nu⁻¹)) := by
    intro p
    simpa only [Matrix.sub_apply] using
      isBigO_gammaSigma_descendantAverage_entry_of_colorPartition hnu ((n + h + 1) / 2) P
        hJ1 hPrefix hJ2 hJ3 hJ4 hhm hmn
        (descendantColorSet d ((n + h + 1) / 2 - h) n h)
        (descendantColorClass d ((n + h + 1) / 2 - h) n h)
        hne hdisj hcover hclsne hsep p.1 p.2
  have hop := isBigO_gammaSigma_operatorNorm_of_entrywise_uniform (μ := P.toMeasure)
    (σ := 2)
    (A := gammaTriangleConst 2 * Homogenization.Book.Ch04.gammaSigmaIndependentSumConst 2 *
      (Real.sqrt ((descendantColorSet d ((n + h + 1) / 2 - h) n h).card : ℝ) *
        (Real.sqrt ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ) /
          ((descendantsAtDepth (originCube d (n : ℤ)) (n - h)).card : ℝ))) *
      (nu⁻¹ + nu⁻¹))
    (by norm_num) hApos
    (fun omega : ShellSeq d =>
      descendantsAverageMat (originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField) -
        sigmaBarStarInv nu ((n + h + 1) / 2) P
          (cubeSet (originCube d (h : ℤ))))
    hMmeas hconc
  refine ⟨fun omega : ShellSeq d => matrixOperatorNorm
      (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
          (fun R => sigmaStarInvCoarse (cubeSet R)
            (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField) -
        sigmaBarStarInv nu ((n + h + 1) / 2) P
          (cubeSet (originCube d (h : ℤ)))),
    measurable_matrixOperatorNorm_fluctuation hnu ((n + h + 1) / 2) P n h, ?_, ?_⟩
  · exact hop.mono_scale (hAmpl_printedScale hnu hnu1 h n hhn)
  · intro omega
    exact matLoewnerLE_add_operatorNorm_sub _ _

/-! ## The printed-scale Step-E in the binder shape the assembly consumes -/

/-- **The printed-scale Step-E inside the `J`-binders.**  The Step-E hypothesis
of the chain is stated *outside* the `∀ P` binder, and so carries only `ShellLawPrefix` and
`ShellLawJ2`; the printed-scale Step-E needs `ShellLawJ1Restriction` (the
restriction-lane range of dependence), `ShellLawJ3` and `ShellLawJ4` besides
(`isBigO_gammaSigma_descendantAverage_entry_of_colorPartition`), all of which the statement
provides inside its `∀ P` scope.  This is the corrected binder: the same conclusion, at
the printed scale `(n + h + 1) / 2` determined by `h` and `n`, at the `m`-free
constant `stepEAmplitudeConstMFree d`, with the five `J`-binders. -/
theorem stepE_printedScale_closed (d : ℕ) [NeZero d] :
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
      ∀ P : ProbabilityMeasure (ShellSeq d),
        ShellLawPrefix d P → ShellLawJ1Restriction d P → ShellLawJ2 d P →
        ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ h n : ℕ, h < n →
          ∃ XFluc : ShellSeq d → ℝ, Measurable XFluc ∧
            IsBigO P.toMeasure (gammaSigma 2) XFluc
                (stepEAmplitudeConstMFree d * nu ^ (-(2 : ℝ)) *
                  (3 : ℝ) ^ (-(((n - h : ℕ) : ℝ) / 4))) ∧
            ∀ omega : ShellSeq d,
              MatLoewnerLE
                (descendantsAverageMat (originCube d (n : ℤ)) (n - h)
                  (fun R => sigmaStarInvCoarse (cubeSet R)
                    (coefficientCutoff nu omega ((n + h + 1) / 2)).toCoeffField))
                (sigmaBarStarInv nu ((n + h + 1) / 2) P
                    (cubeSet (originCube d (h : ℤ))) +
                  XFluc omega • (1 : Mat d)) := by
  intro nu hnu hnu1 P hPrefix hJ1 hJ2 hJ3 hJ4 h n hhn
  exact stepE_printedScale d hnu hnu1 P hJ1 hPrefix hJ2 hJ3 hJ4 h n hhn

/-! ## The printed midpoint is the balanced midpoint of the assembly -/

/-! ## Positivity of the `m`-free Step-E constant -/

private theorem one_le_static_cast (d : ℕ) : (1 : ℝ) ≤ (((d + 1) ^ d : ℕ) : ℝ) := by
  have hnat : 1 ≤ (d + 1) ^ d := one_le_pow₀ (show (1 : ℕ) ≤ d + 1 by omega)
  exact_mod_cast hnat

/-- **Positivity of the `m`-free Step-E amplitude constant.**  Every factor of
`stepEAmplitudeConstMFree d` is positive for `d ≥ 1`: the two
`gammaTriangleConst 2` factors and `gammaSigmaIndependentSumConst 2` by the
positivity lemmas, `d * d` by `d ≥ 1`, and `stepEColorFactor d =
sqrt(((d + 1)^d : ℕ)) * 3^(1/4)` by `(d + 1)^d ≥ 1`.  This is the sign
hypothesis `0 < CFluc` of the chain at `CFluc := stepEAmplitudeConstMFree
d`. -/
theorem stepEAmplitudeConstMFree_pos (d : ℕ) (hd : 1 ≤ d) :
    0 < stepEAmplitudeConstMFree d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt ((((d + 1) ^ d : ℕ) : ℝ)) :=
    Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one (one_le_static_cast d))
  have h3 : 0 < (3 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hfac : 0 < stepEColorFactor d := by
    unfold stepEColorFactor
    exact mul_pos hsqrt h3
  unfold stepEAmplitudeConstMFree
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num)
    (IndependentSums.gammaTriangleConst_pos (σ := 2))) (mul_pos hd0 hd0))
    (IndependentSums.gammaTriangleConst_pos (σ := 2)))
    SuperdiffusionCLT.Probability.gammaSigmaIndependentSumConst_two_pos) hfac

/-! ## The statement from the two outer step binders -/

end

end SuperdiffusionCLT.Section2.Annealed
