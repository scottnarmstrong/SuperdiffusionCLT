/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.CutoffMinimizerPremises
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1WeakHessian

/-!
# `l.RHS.term1` in a shortened form

The statement `SuperdiffusionCLT.Frozen.Section3.rhs_term1` (`e.RHS.term1` of the
paper) is proved here with its conclusion **verbatim** and with a short list of
named hypotheses.

## The chain

* `RHSTerm1FrozenReduction.term1_of_obligations` proves the conclusion
  with sixteen obligation binders, and a first reduction brings that to nine: the
  weak-Hessian binder `HD`, the two `w`-carrier
  measurabilities `_hMeasH1` and `_hMeasHminus`, the localization clause
  `_hLocMin`, the difference-Jensen input `_hJensen`, the sublattice
  concentration `_hConcDepth`, and the three section constants `Cloc`,
  `hCloc`, `Cc`.
* `RHSTerm1WeakHessian.term1_of_residueB` removes `HD` (the divergence-form
  Calderón-Zygmund endpoint produces it, so the binder is no longer assumed;
  `_hMeasH1` is restated against the resulting canonical witness, which is the
  same obligation by the selection-freeness of the `H̲¹` carrier), discharges
  `_hQTilde` at the printed proxy, and removes the `1 ≤ Cc` gate.  It leaves
  eight binders.
* This file removes the last section gate: the localization clause at *any* real
  constant `Cloc` yields it at `max 1 Cloc`, because the clause's right side is
  `Cloc * R * F` with `R ≥ 0` (the window prefactor) and `F ≥ 0` (the response
  factor, `locMinResponseFactor_nonneg` below, from
  `responseJ_centeredPair_add_nonneg`).  So `hCloc` is not a hypothesis of
  `term1_final`; the clause is carried at the bare constant `Cloc` and upgraded
  inside the proof.  Seven binders remain.

## The hypotheses of `term1_final`

* `Cloc`, `Cc` — the section constants of `_hLocMin` and of `_hConcDepth`.  Both
  enter ungated.  They are constants of the two clauses, not gates on the
  statement: no inequality of the form `1 ≤ Cloc` or `1 ≤ Cc` is assumed.
* `_hMeasH1` — the `ω`-measurability of the `H̲¹(cu_m)` carrier of the response,
  stated at the canonical weak Hessian.
  `Section3.Setup.aemeasurable_vecCubeH1ENorm_grad_of_hessian` reduces it to the
  `ω`-measurability of `ω ↦ ‖D²w_ω‖_{L²(cu_m)}`.
* `_hMeasHminus` — the `ω`-measurability of `ω ↦ ‖a_ℓ ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`.
  That carrier is an uncountable supremum over test fields
  (`Section2.Norms.vecHatNegENormOrderOne`).
* `_hLocMin` — the minimizer clause of the cutoff localization statement of
  `Frozen.Section2`, at the constant `Cloc`.
* `_hJensen` — at the pinned proxy this is the *difference*-Jensen bound, not a
  Jensen bound on one annealed average.  Writing
  `q̃ = qVector hnu P S.ell S.ell S.n S.m F` and
  `q = qVector hnu P S.LPrime S.ell S.n S.m F`, the two are the annealed
  `cu_ℓ`-averages of `a_ℓ ∇ũ_ℓ` and of `a_ℓ ∇ũ_{L'}` (the coefficient scale is
  the *second* argument of `qVector`), so `q̃ − q` is the annealed average of
  `a_ℓ (∇ũ_ℓ − ∇ũ_{L'})` — the very field whose annealed `L²` energy is the
  right side of the binder, up to the sign of the difference, which the cube
  `L²` carrier does not see.  The two Jensen steps
  (`ofReal_vecNormSq_integral_le`, `ofReal_vecNormSq_volumeAverageVec_le`)
  therefore prove the binder as soon as the difference of the two Bochner
  integrals is the Bochner integral of the pointwise difference, which needs
  both annealed averages to be integrable (the same joint measurability that
  `GluedField.qVector_apply` carries as an explicit hypothesis).  The total
  convention for the Bochner integral makes the mixed case — one average
  integrable and the other not — irreducible without it.
* `_hConcDepth` — the sublattice concentration of `a_ℓ ∇ũ_n − q̃` at `Cc`, the
  printed clause of `e.RHS.term1`.  `SublatticeConcentrationDepth` proves
  the per-sublattice rule for the flux block averages and the annealed envelope of
  the proxy.

## Main results

* `locMinResponseFactor_nonneg`: the response factor of the localization clause
  is nonnegative, unconditionally.
* `locMinConstant_mono`: the localization clause's right side is monotone in the
  clause constant.
* `term1_final`: the `l.RHS.term1` conclusion verbatim, from the seven
  named hypotheses above.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (vecHatNegENormOrderOne)

noncomputable section

/-! ## The two halves of the localization clause's monotonicity -/

/-- **The response factor of the localization clause is nonnegative.**

The factor is `J(U, p, q; â) + J(U, p, q; a_ℓ) + 2 p·q` at the centered pair
field `â = a_{L'} − (k_{L'} − k_ℓ)_U`.
`Section2.Localization.responseJ_centeredPair_add_nonneg` proves its
nonnegativity from the two Chapter 2 coarse block forms being positive
semidefinite; the only content here is the definitional identification of the
clause's first `ResponseJ` argument with `centeredPairField`.  This is
what makes the gate `1 ≤ Cloc` free. -/
theorem locMinResponseFactor_nonneg {d : ℕ} (nu : ℝ) (hnu : 0 < nu)
    (S : ScaleSelection) (U : Book.Ch02.Domain d) (omega' : ShellSeq d) (p q : Vec d) :
    0 ≤ ResponseJ (U : Set (Vec d)) p q
          (fun x : Vec d =>
            (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
        ResponseJ (U : Set (Vec d)) p q
          (coefficientCutoff nu omega' S.ell).toCoeffField +
        2 * vecDot p q := by
  have h := SuperdiffusionCLT.Section2.Localization.responseJ_centeredPair_add_nonneg
    nu hnu S.ell S.LPrime U omega' p q
  unfold SuperdiffusionCLT.Section2.Localization.centeredPairField at h
  exact h

/-- **The localization clause's right side is monotone in its constant.**

The right side is `Cloc * R * F` with `R = ν^{-2} 3^n ‖∇(k_{L'} − k_ℓ)‖_{L^∞(cu_n)}`
the window prefactor and `F` the response factor.  With `R ≥ 0` and `F ≥ 0`
(`locMinResponseFactor_nonneg`) the product is monotone in `Cloc`, so the clause
holds at every larger constant. -/
theorem locMinConstant_mono {d : ℕ} {nu Cloc Cloc' : ℝ} (S : ScaleSelection)
    (omega' : ShellSeq d) (F : ℝ) (hnu : 0 ≤ nu) (hF : 0 ≤ F) (hle : Cloc ≤ Cloc') :
    Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n omega' * F ≤
      Cloc' * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
        anchorDerivSup S.ell S.LPrime S.n omega' * F := by
  refine mul_le_mul_of_nonneg_right ?_ hF
  refine mul_le_mul_of_nonneg_right ?_ (anchorDerivSup_nonneg S.ell S.LPrime S.n omega')
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) S.n)
  exact mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hnu (-(2 : ℝ)))

/-! ## The statement from the seven named hypotheses -/

/-- **`l.RHS.term1` from seven named hypotheses.**

The binders and the conclusion are those of
`SuperdiffusionCLT.Frozen.Section3.rhs_term1` verbatim; the only additions
are the section constants `Cloc` and `Cc` (the constants of the two clauses, both
entering ungated) and the five named obligations `_hMeasH1`, `_hMeasHminus`,
`_hLocMin`, `_hJensen` and `_hConcDepth`, attached after the `_hw` binder
and before the `_hPigeon` side condition, exactly as in
`RHSTerm1WeakHessian.term1_of_residueB`.

Three premises that the earlier reduction carried are gone:

* `HD`, the weak-Hessian witness of the response — produced by the
  divergence-form endpoint (`RHSTerm1WeakHessian.canonicalResponseHessian`), so
  `_hMeasH1` is stated against the canonical witness;
* the gate `1 ≤ Cc` of the concentration — free by
  `hConcDepth_gate_upgrade`;
* the gate `1 ≤ Cloc` of the localization — free by
  `locMinResponseFactor_nonneg` and `locMinConstant_mono` (the clause is
  upgraded to `max 1 Cloc` inside the proof).

See the module header for the standing of each remaining binder. -/
theorem term1_final (d : ℕ) [NeZero d] (_hd : 2 ≤ d) (Cloc : ℝ) (Cc : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (hnu : 0 < nu) (_hnu1 : nu ≤ 1)
        (P : ProbabilityMeasure (ShellSeq d))
        (_hPrefix : ShellLawPrefix d P) (_hJ1V2 : ShellLawJ1Restriction d P)
        (_hJ2 : ShellLawJ2 d P) (_hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1)
        (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (_hw : ∀ omega : ShellSeq d,
          IsDirichletResponse omega S.LPrime S.ellPrime S.m
            (testVector nu S.LPrime P S.n e) (w omega))
        (_hMeasH1 : AEMeasurable (fun omega : ShellSeq d =>
          vecCubeH1ENorm (originCube d (S.m : ℤ)) (w omega).toH1Function.grad
            (fun x => fun i j =>
              (canonicalResponseHessian d _hd S nu P e w _hw omega).hess i j x))
          P.toMeasure)
        (_hMeasHminus : AEMeasurable (fun omega : ShellSeq d =>
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (gluedGradientField hnu S.ell S.n S.m
                (fluxSlot nu S.LPrime P S.n e) omega x) -
                qVector hnu P S.ell S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e))) P.toMeasure)
        (_hLocMin : ∀ U : Book.Ch02.Domain d,
            (U : Set (Vec d)) ⊆ openCubeSet (originCube d (S.n : ℤ)) →
            ∀ (omega' : ShellSeq d) (p q : Vec d)
              (u : AHarmonicFunction
                (fun x : Vec d =>
                  (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                    volumeAverageMat (U : Set (Vec d))
                      (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                (U : Set (Vec d)))
              (v : AHarmonicFunction
                (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d))),
              (∀ w : AHarmonicFunction
                  (fun x : Vec d =>
                    (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                      volumeAverageMat (U : Set (Vec d))
                        (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                  (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y))
                        p q u)) →
              (∀ w : AHarmonicFunction
                  (coefficientCutoff nu omega' S.ell).toCoeffField (U : Set (Vec d)),
                  volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q w) ≤
                    volumeAverage (U : Set (Vec d))
                      (scalarResponseIntegrand (U : Set (Vec d))
                        (coefficientCutoff nu omega' S.ell).toCoeffField p q v)) →
                volumeAverage (U : Set (Vec d))
                    (fun x => vecNormSq (u.toH1.grad x - v.toH1.grad x)) ≤
                  Cloc * nu ^ (-(2 : ℝ)) * (3 : ℝ) ^ S.n *
                      anchorDerivSup S.ell S.LPrime S.n omega' *
                    (ResponseJ (U : Set (Vec d)) p q
                        (fun x : Vec d =>
                          (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
                            volumeAverageMat (U : Set (Vec d))
                              (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
                      ResponseJ (U : Set (Vec d)) p q
                        (coefficientCutoff nu omega' S.ell).toCoeffField +
                      2 * vecDot p q))
        (_hJensen : ENNReal.ofReal (Real.sqrt (vecNormSq
              (qVector hnu P S.ell S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e) -
                qVector hnu P S.LPrime S.ell S.n S.m
                  (fluxSlot nu S.LPrime P S.n e)))) ≤
          (∫⁻ omega : ShellSeq d,
              (vecCubeLpENorm (originCube d (S.ell : ℤ)) 2
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x -
                    gluedGradientField hnu S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e) omega x))) ^ (2 : ℕ)
            ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2))
        (_hConcDepth : ∀ j : ℕ,
          (∫⁻ omega : ShellSeq d,
              ENNReal.ofReal (vecDepthSqMoment (originCube d (S.m : ℤ)) j
                (fun x => matVecMul
                  ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                    qVector hnu P S.ell S.ell S.n S.m
                      (fluxSlot nu S.LPrime P S.n e)))
            ∂P.toMeasure : ℝ≥0∞) ≤
            ENNReal.ofReal (Cc *
                (3 : ℝ) ^ (-((d : ℝ) * ((S.m - j - S.ell : ℕ) : ℝ)))) *
              (∫⁻ omega : ShellSeq d,
                  ENNReal.ofReal (vecSqAvg (originCube d (S.m : ℤ))
                    (fun x => matVecMul
                      ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (gluedGradientField hnu S.ell S.n S.m
                        (fluxSlot nu S.LPrime P S.n e) omega x) -
                        qVector hnu P S.ell S.ell S.n S.m
                          (fluxSlot nu S.LPrime P S.n e)))
              ∂P.toMeasure : ℝ≥0∞))
        (_hPigeon : 2 * S.h ≤ S.m),
        |∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun x => vecDot ((w omega).toH1Function.grad x)
                (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (gluedGradientField hnu S.LPrime S.n S.m
                    (fluxSlot nu S.LPrime P S.n e) omega x) -
                  qVector hnu P S.LPrime S.ell S.n S.m
                    (fluxSlot nu S.LPrime P S.n e))) ∂P.toMeasure| ≤
          C * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) := by
  obtain ⟨C, hC1, hmain⟩ :=
    term1_of_residueB d _hd (max 1 Cloc) (le_max_left 1 Cloc) Cc
  refine ⟨C, hC1, ?_⟩
  intro nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hMeasH1 hMeasHminus hLocMin hJensen hConcDepth hPigeon
  refine hmain nu hnu hnu1 P hPrefix hJ1V2 hJ2 hJ3 hJ4 S hSorder e he w hw
    hMeasH1 hMeasHminus ?_ hJensen hConcDepth hPigeon
  intro U hU omega' p q u v hu hv
  exact le_trans (hLocMin U hU omega' p q u v hu hv)
    (locMinConstant_mono (nu := nu) S omega'
      (ResponseJ (U : Set (Vec d)) p q
          (fun x : Vec d =>
            (coefficientCutoff nu omega' S.LPrime).toCoeffField x -
              volumeAverageMat (U : Set (Vec d))
                (fun y => finiteShellIncrement omega' S.ell S.LPrime y)) +
        ResponseJ (U : Set (Vec d)) p q
          (coefficientCutoff nu omega' S.ell).toCoeffField +
        2 * vecDot p q)
      hnu.le (locMinResponseFactor_nonneg nu hnu S U omega' p q) (le_max_right 1 Cloc))

end

end SuperdiffusionCLT.Section3.Terms
